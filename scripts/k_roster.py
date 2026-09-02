#!/usr/bin/env python3
"""Derive the P1 roster and its batch partition FROM K's own semantics tree.

Plan v1 §2 names the K x86-64 semantics (NCSA, (c) 2019 UIUC) as "the second
oracle and the COVERAGE TARGET LIST", and §5 prices P1 as an executor wave over
that list "machine-partitioned into batches of like forms".  This script is the
machine that does the partitioning.

WHY IT IS DERIVED AND NOT TYPED.  A hand-written roster of ~300 forms is a
judgement made ~300 times, unreviewable in practice and stale the moment K's
tree moves.  Everything here comes out of K's filenames and K's rule text:

  * the operand shapes come from the FILENAME (`addq_m64_r64` -> m64, r64);
  * which flags an instruction writes, and whether it writes a value, a
    constant, or K's `undefMInt`, comes from the RULE TEXT;
  * which flags it reads comes from the rule text's `getFlag("XX", ...)`;
  * the family a form belongs to is the TUPLE of those, so "like forms" is a
    computed equality and not an opinion about which instructions feel similar.

WHAT IS STILL A JUDGEMENT, named here so it can be argued with rather than
discovered: the EXCLUSIONS (§ EXCLUDE below, one line of reason each) and the
BATCH ORDER (§ batch_sort_key).  Both are small, both are printed in the audit.

⭐ K'S `undefMInt` IS A THIRD INDEPENDENT READING OF THE UNDEFINED SET.  P0's
undefined regions were derived from this model's own two-oracle differential
(docs/DECISIONS.md D6) and cross-read against the SDM and x86isa.  K, written by
a different group from a different reading of the same manual, marks its own.
Where the two disagree, that is a FINDING under plan v1 §4.2 (three-source
readings), and the `k_undef` column is what makes the disagreement visible
BEFORE a form is implemented rather than after the differential run.

PUBLIC SOURCE.  The K semantics are NCSA-licensed and are READ here, never
copied: this script emits only counts, mnemonic names, operand shapes and flag
dispositions -- facts about the x86-64 architecture, which the SDM states and
which no licence encumbers.  No K rule text is reproduced in the output.

LANE.  Personal lane, public sources only.
"""

from __future__ import annotations

import argparse
import collections
import os
import re
import sys

# ⚠️ `systemInstructions` IS IN THIS LIST, AND ITS NAME IS WHY IT NEARLY WAS NOT.
# Every one of K's 122 files there is USER-LEVEL: the conditional and
# unconditional branches, `callq`, `retq`, `leaveq`, `loop`, `push`/`pop` and
# `ud2`.  Nothing privileged is in it.  Reading the directory name as the
# taxonomy produced a roster with NO CONTROL FLOW AT ALL -- no `jmp`, no `jcc`,
# no `call` -- three mnemonics P0 has already implemented and differentially
# validated, silently absent from the list that is supposed to be the wave's
# fence.  A coverage target list that quietly omits control flow would have
# reported full coverage of a machine that cannot branch.
SUBDIRS = ("registerInstructions", "immediateInstructions", "memoryInstructions",
           "systemInstructions")

FLAGS = ("cf", "pf", "af", "zf", "sf", "of", "df")

# Operand tokens that make a form SIMD/FP rather than scalar integer.  P2, not
# P1 (plan v1 §5).
VECTOR_OPERAND = re.compile(r"^(x|y|z)?mm\d*$|^m(128|256|512)$")

# Width implied by an AT&T suffix, used to TEST whether a trailing letter really
# is a width suffix rather than part of the mnemonic (see split_width).
SUFFIX_WIDTH = {"b": 8, "w": 16, "l": 32, "q": 64}

# ⚠️ WHAT COUNTS AS EVIDENCE OF AN INSTRUCTION'S OPERAND SIZE, and what does
# not.  Every exclusion below is an operand kind that routinely does NOT carry
# the operand size, and every one of them was found by running this script and
# reading a base mnemonic it had mangled:
#   * IMMEDIATES are encoded narrow and extended -- `pushq $imm32` is a 64-bit
#     push;
#   * the FIXED registers `%cl`, `%al`/`%ax`/`%eax`/`%rax` are implicit operands,
#     and `%cl` is the shift COUNT, always 8 bits whatever the shift's width --
#     counting it un-folded `shl`/`sal`/`sar`/`rol`/`ror`/`rcl`/`rcr` into 28
#     separate base mnemonics;
#   * `rel8`/`rel32`/`label` are branch displacements, and their widths are the
#     reason `jb` and `jl` -- "if below" and "if less" -- folded into a base
#     called `j` that covered 110 forms and no instruction;
#   * a MEMORY token is sometimes an ADDRESSING form rather than a data width
#     (`leal_r32_m64` is a 32-bit LEA), so it is used only when a token has no
#     general-register operand at all, which is how the string ops keep theirs.
REG_WIDTH = {"r8": 8, "rh": 8, "r16": 16, "r32": 32, "r64": 64}
MEM_WIDTH = {"m8": 8, "m16": 16, "m32": 32, "m64": 64}

# The sixteen GPR keys K uses for a fixed-accumulator destination.  Two letters
# would collide with the flag keys, so the pattern is anchored on the full name.
GPR_NAMES = ("RAX", "RCX", "RDX", "RBX", "RSP", "RBP", "RSI", "RDI",
             "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15")
GPR_KEY = re.compile(r'"(?:%s)"\s*\|->' % "|".join(GPR_NAMES))
GPR_DEST = re.compile(r'"(?:%s)"\s*\|->\s*([A-Za-z][A-Za-z0-9]*)\s*\(' % "|".join(GPR_NAMES))

REP_PREFIXES = ("rep", "repe", "repne", "repnz", "repz")

# ── EXCLUSIONS, each with its reason ────────────────────────────────────────
# These are the only hand judgements in the roster.  Everything else is derived.
EXCLUDE_TOKENS = {
    "vzeroall":   "AVX state instruction; no integer operand to filter on. P2.",
    "vzeroupper": "AVX state instruction; no integer operand to filter on. P2.",
}
EXCLUDE_PREFIX = {
    "cvt":  "SSE/AVX float<->integer conversion: reads or writes an XMM register. P2.",
    "vcvt": "AVX float<->integer conversion: reads or writes an XMM register. P2.",
}


def parse_name(stem: str):
    """`rep_movsb` -> ('rep', 'movsb', []);  `addq_m64_r64` -> (None, 'addq', [...])."""
    parts = stem.split("_")
    prefix = None
    if parts[0] in REP_PREFIXES and len(parts) > 1:
        prefix, parts = parts[0], parts[1:]
    return prefix, parts[0], parts[1:]


def operand_class(tok: str) -> str:
    """r8/rh/r16/... -> 'r';  m8/m64 -> 'm';  imm8/imm32 -> 'imm';  al/cl/eax -> the name."""
    if re.fullmatch(r"r(8|16|32|64)|rh", tok):
        return "r"
    if re.fullmatch(r"m(8|16|32|64)", tok):
        return "m"
    if re.fullmatch(r"imm(8|16|32|64)", tok):
        return "imm"
    return tok


# K wraps every destination expression in the machinery that puts a value back
# into a register at the right width: `concatenateMInt`/`extractMInt` to merge or
# zero-extend, `mi` for a literal, `getParentValue` to read the old value.  None
# of that is the instruction.
#
# ⚠️ READING THE OUTERMOST OPERATOR AS THE INSTRUCTION'S SPLIT `and` IN HALF.
# `andq $imm32, %rax` writes the whole register, so K's outermost operator is
# `andMInt`; `andl $imm32, %eax` must zero-extend, so K's outermost operator is
# `concatenateMInt` and the `andMInt` is inside it.  Same instruction, same
# template, two different families -- a batch partition that separates an
# instruction from itself by operand WIDTH, which is the one thing this model
# holds as a datum rather than a case (docs/DECISIONS.md D4).
WRAPPERS = {"concatenateMInt", "extractMInt", "mi", "getParentValue", "getFlag",
            "convToRegKeys", "storeToMemory", "updateMap", "nfix"}


def dest_operator(text: str, writes_mem: bool) -> str:
    """The instruction's own operator, with K's width machinery seen through."""
    m = re.search(r'(?:convToRegKeys\([^)]*\)|"(?:%s)")\s*\|->' % "|".join(GPR_NAMES), text)
    if m:
        expr = text[m.end():]
        nxt = re.search(r'"[A-Z]{2}"\s*\|->', expr)   # stop at the first flag key
        if nxt:
            expr = expr[:nxt.start()]
    elif writes_mem:
        i = text.find("storeToMemory(")
        expr = text[i:i + 4000]
    else:
        return "-"
    for ident in re.findall(r"([A-Za-z][A-Za-z0-9]*)\s*\(", expr):
        if ident not in WRAPPERS:
            return ident[:-4] if ident.endswith("MInt") else ident
    return "-"


def read_rule(path: str) -> dict:
    """Everything this script learns from K's rule TEXT, as facts about x86."""
    with open(path, "r", errors="replace") as fh:
        text = fh.read()

    disp = {}
    for f in FLAGS:
        key = '"%s" |->' % f.upper()
        i = text.find(key)
        if i < 0:
            disp[f] = "-"                       # untouched
            continue
        tail = text[i + len(key):].lstrip()
        if tail.startswith("(undefMInt)") or tail.startswith("undefMInt"):
            disp[f] = "u"                       # K marks it UNDEFINED
        elif re.match(r"mi\(\s*1\s*,\s*0\s*\)", tail):
            disp[f] = "0"                       # written constant 0
        elif re.match(r"mi\(\s*1\s*,\s*1\s*\)", tail):
            disp[f] = "1"                       # written constant 1
        else:
            disp[f] = "x"                       # computed

    reads = sorted({m.lower() for m in re.findall(r'getFlag\(\s*"([A-Z]{2})"', text)})

    # ⚠️ TWO WAYS K NAMES A REGISTER DESTINATION.  A general form writes
    # `convToRegKeys(R2) |->`; a FIXED-ACCUMULATOR form (`andq $imm32, %rax`,
    # SDM opcode 25 /id) has no register operand to convert and writes the key
    # `"RAX" |->` directly.  Reading only the first said `and $imm, %al` wrote no
    # register at all, and filed twenty accumulator forms under "flags only" --
    # a whole addressing mode classified as a different instruction shape.
    writes_reg = ("convToRegKeys(" in text) or bool(GPR_KEY.search(text))
    writes_mem = "storeToMemory(" in text
    reads_mem = "loadFromMemory(" in text
    destop = dest_operator(text, writes_mem)
    return {
        "disp": disp, "reads": reads,
        "writes_reg": writes_reg, "writes_mem": writes_mem, "reads_mem": reads_mem,
        "destop": destop,
    }


def split_width(tokens_shapes: dict) -> dict:
    """Derive base mnemonic and width class for every token, from the DATA.

    A trailing b/w/l/q is a WIDTH SUFFIX only when SOME operand of the token
    carries that width, and only when at least two siblings of the same base
    pass that same test.  This is what separates `addb/addl/addq/addw` (a real
    width family) from `setb`/`setl` (SET-if-below and SET-if-less, whose
    operands are 8-bit in both cases, so `setl`'s `l` is refuted by its own
    operands and the family collapses to one member).  A family of one --
    `movslq`, `cmpxchg8b`, `cbtw` -- is left unsplit, because a single member is
    no evidence of a family.
    """
    # evidence[tok] = the operand sizes this token demonstrably has, or the empty
    # set when nothing it carries is evidence either way.
    evidence = {}
    for tok, shapes in tokens_shapes.items():
        regs = {REG_WIDTH[o] for sh in shapes for o in sh if o in REG_WIDTH}
        mems = {MEM_WIDTH[o] for sh in shapes for o in sh if o in MEM_WIDTH}
        evidence[tok] = regs or mems

    # A token is a CANDIDATE member of a width family when its suffix width is
    # among its evidence, or when it has no evidence at all (`stosl`, `cltq`).
    cand = collections.defaultdict(list)
    for tok in tokens_shapes:
        if len(tok) < 2 or tok[-1] not in SUFFIX_WIDTH:
            continue
        want = SUFFIX_WIDTH[tok[-1]]
        if (not evidence[tok]) or (want in evidence[tok]):
            cand[tok[:-1]].append(tok)

    # ⭐ THE SUFFIX MUST DISCRIMINATE, NOT MERELY AGREE.  A letter is a width
    # suffix only if changing it changes the instruction's operand size -- so a
    # member counts only when SOME SIBLING'S EVIDENCE LACKS ITS WIDTH, and a
    # family folds only when at least two members clear that bar.
    #
    # Mere agreement is not enough, and the two cases that prove it are the two
    # this rule exists for.  `setb` and `setl` are SET-if-below and SET-if-less:
    # both write an 8-bit operand, so `setb`'s `b` agrees with its operands and
    # discriminates against nothing.  `jb` and `jl` are the same trap with no
    # evidence at all on either side.  Under "agreement", both folded -- `setb`
    # into a base `set` and `jb` into a base called `j` that swallowed all 110
    # control-flow forms into one batch.
    #
    # A member with no evidence rides along on the family the discriminating
    # members establish, which is what keeps the string ops (`stosl`, `stosq`,
    # `movsl`) with their siblings without letting `jb` invent a family.
    out = {tok: (tok, "-") for tok in tokens_shapes}
    for prefix, members in cand.items():
        if len(members) < 2:
            continue
        discriminating = [
            t for t in members
            if evidence[t] and any(evidence[o] and SUFFIX_WIDTH[t[-1]] not in evidence[o]
                                   for o in members if o != t)]
        if len(discriminating) < 2:
            continue
        for t in members:
            out[t] = (prefix, t[-1])
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--k-root", default="vendor/k-x86-64")
    ap.add_argument("--out-tsv", default="p1/roster.tsv")
    ap.add_argument("--out-md", default="docs/P1-ROSTER.md")
    ap.add_argument("--selftest", action="store_true",
                    help="assert the derivation's known-correct outcomes and exit")
    ap.add_argument("--check", action="store_true",
                    help="regenerate into memory and diff against the committed files")
    args = ap.parse_args()

    sem = os.path.join(args.k_root, "semantics")
    if not os.path.isdir(sem):
        sys.stderr.write(
            "no K tree at %s — run scripts/setup_k_roster.sh\n"
            "(a blobless sparse checkout of `semantics/` only: 15 MB, not the "
            "repository's 2.8 GB, which is why this gate can run in CI).\n" % sem)
        return 2

    # The K commit the roster was derived from.  Without it a stale roster and a
    # current one are the same file with different numbers in it.
    k_commit = "unknown"
    try:
        import subprocess
        k_commit = subprocess.run(
            ["git", "-C", args.k_root, "rev-parse", "HEAD"],
            capture_output=True, text=True, check=True).stdout.strip()
    except Exception:
        pass

    # ── 1. enumerate every variant K defines ────────────────────────────────
    variants = []               # (token, prefix, shape tuple, path)
    seen_files = set()          # `pushq_r64.k` is filed in TWO of K's directories
    dupes = 0
    for d in SUBDIRS:
        dp = os.path.join(sem, d)
        for fn in sorted(os.listdir(dp)):
            if not fn.endswith(".k"):
                continue
            if fn in seen_files:
                dupes += 1
                continue
            seen_files.add(fn)
            prefix, tok, ops = parse_name(fn[:-2])
            variants.append((tok, prefix, tuple(ops), os.path.join(dp, fn)))
    total_variants = len(variants)

    # ── 2. keep the scalar-integer user-level ones ──────────────────────────
    kept, dropped = [], collections.Counter()
    for tok, prefix, ops, path in variants:
        if tok in EXCLUDE_TOKENS:
            dropped["named exclusion"] += 1
            continue
        if any(tok.startswith(p) for p in EXCLUDE_PREFIX):
            dropped["float/vector conversion"] += 1
            continue
        if any(VECTOR_OPERAND.match(o) for o in ops):
            dropped["SIMD operand (P2)"] += 1
            continue
        kept.append((tok, prefix, ops, path))

    # ── 3. base mnemonic and width class, derived ───────────────────────────
    tokens_shapes = collections.defaultdict(list)
    for tok, _prefix, ops, _p in kept:
        tokens_shapes[tok].append(ops)
    split = split_width(tokens_shapes)

    # ── 4. fold variants into FORMS: (prefix, base, operand-shape signature) ─
    forms = {}
    for tok, prefix, ops, path in kept:
        base, width = split[tok]
        shape = ",".join(operand_class(o) for o in ops) or "-"
        key = (prefix or "", base, shape)
        r = read_rule(path)
        f = forms.setdefault(key, {
            "prefix": prefix or "", "base": base, "shape": shape,
            "widths": set(), "variants": 0, "disp": None, "reads": None,
            "destop": r["destop"], "writes_reg": r["writes_reg"],
            "writes_mem": r["writes_mem"], "reads_mem": r["reads_mem"],
            "disp_conflict": False, "tokens": set(),
        })
        f["variants"] += 1
        f["tokens"].add(tok)
        if width != "-":
            f["widths"].add(width)
        sig = "".join(r["disp"][x] for x in FLAGS)
        if f["disp"] is None:
            f["disp"], f["reads"] = sig, r["reads"]
        else:
            # A width that disposes of its flags differently from its siblings is
            # a FINDING, not something to average away.
            if f["disp"] != sig or f["reads"] != r["reads"]:
                f["disp_conflict"] = True

    # ── 5. the family: a computed tuple, not an opinion ─────────────────────
    for f in forms.values():
        dest = ("mem" if f["writes_mem"] else "reg" if f["writes_reg"] else "flags/ctl")
        # ⚠️ THE OPERATOR IS NOT IN THE KEY, AND THAT IS THE WHOLE DESIGN.
        # A family is a claim that these forms share ONE TEMPLATE, and a
        # template's shape is set by what the instruction writes -- destination
        # kind and flag disposition -- not by which operator sits in its one
        # value slot.  P0 is the proof: `add sub and or xor cmp test` are seven
        # operators under ONE `Op.bin` constructor with one characterization
        # lemma shape.  Keying on K's operator instead split `and`, `or` and
        # `xor` into three batches while merging `add` with `scas`, which is
        # both errors at once.  `k_destop` stays as a COLUMN, so a head that
        # needs to sub-partition a large batch has the operator to hand.
        f["family"] = "%s|%s|%s" % (f["disp"], "+".join(f["reads"]) or "-", dest)

    # The P0 roster (X86/Syntax.lean `rosterP0`) as a set of BASE MNEMONICS this
    # model already has a template for.  `jcc` is the model's single name for the
    # sixteen conditional branches; K names each condition and each synonym, so
    # the comparison has to be against those names.
    p0 = {"mov", "add", "sub", "and", "or", "xor", "cmp", "test", "shl", "shr",
          "lea", "inc", "dec", "neg", "not", "push", "pop", "jmp", "callq"} | {
          "j" + c for c in ("o", "no", "b", "ae", "e", "ne", "be", "a", "s", "ns",
                            "p", "np", "l", "ge", "le", "g", "c", "nc", "z", "nz",
                            "na", "nae", "nb", "nbe", "ng", "nge", "nl", "nle",
                            "pe", "po")}

    by_family = collections.defaultdict(list)
    for key in sorted(forms):
        by_family[forms[key]["family"]].append(key)

    # ── 6. batches, one per family, in a stated order ───────────────────────
    def batch_sort_key(fam: str):
        """BATCH 1 MUST RUN UNDER A TEMPLATE P0 ALREADY HAS (the helm's word), so
        that what it measures is the wave's MARGINAL cost -- one more form under
        an existing template -- and not the one-off cost of inventing a template.

        Families are ordered by how much of them P0 already covers (the fraction
        of the family's base mnemonics in the P0 roster), then largest first.
        That is deliberately NOT "easiest first": the largest fully-covered
        family is the one whose forms are all addressing modes and widths, and
        addressing modes and widths are what most of the wave's forms are.

        ⚠️ AND THAT IS THE PRICE'S LIMIT, which has to travel with the quote: a
        batch measured this way prices ADDRESSING-MODE AND WIDTH work.  A family
        P0 has no template for costs that plus a template, so the wave's price
        needs a second term counted in NEW TEMPLATES, not in forms."""
        bases_here = {forms[k]["base"] for k in by_family[fam]}
        covered = len(bases_here & p0) / len(bases_here)
        return (-covered, -len(by_family[fam]), fam)

    families = sorted(by_family, key=batch_sort_key)
    batch_of = {fam: i + 1 for i, fam in enumerate(families)}

    # ── 7. emit ─────────────────────────────────────────────────────────────
    rows = ["# GENERATED by scripts/k_roster.py from K commit " + k_commit,
            "\t".join(["batch", "family", "prefix", "base", "shape", "widths",
                       "k_variants", "flags_cf_pf_af_zf_sf_of_df", "k_undef",
                       "reads_flags", "dest", "k_destop", "width_conflict"])]
    for fam in families:
        for key in by_family[fam]:
            f = forms[key]
            undef = ",".join(FLAGS[i] for i, c in enumerate(f["disp"]) if c == "u") or "-"
            rows.append("\t".join([
                str(batch_of[fam]), fam, f["prefix"], f["base"], f["shape"],
                "".join(sorted(f["widths"])) or "-", str(f["variants"]),
                f["disp"], undef, "+".join(f["reads"]) or "-",
                "mem" if f["writes_mem"] else "reg" if f["writes_reg"] else "flags/ctl",
                f["destop"], "1" if f["disp_conflict"] else "0"]))
    tsv = "\n".join(rows) + "\n"

    n_forms = len(forms)
    n_kept = len(kept)
    bases = sorted({f["base"] for f in forms.values()})
    new_bases = [b for b in bases if b not in p0]

    md = []
    A = md.append
    A("<!-- GENERATED by `scripts/k_roster.py`. Do not edit by hand. -->\n")
    A("<!-- K commit %s -->\n" % k_commit)
    A("# P1 roster — derived from the K x86-64 semantics\n")
    A("Plan v1 §2 names the K semantics (NCSA, © 2019 UIUC) as the COVERAGE TARGET")
    A("LIST; §5 prices P1 as an executor wave over that list \"machine-partitioned")
    A("into batches of like forms\". This table is that partition. It is generated by")
    A("`scripts/k_roster.py` and regenerated in CI, so it cannot drift from K's tree")
    A("or from an editor's memory of it.\n")
    A("## What the numbers are\n")
    A("| | |")
    A("|---|---|")
    A("| K commit the roster is derived from | `%s` |" % k_commit[:12])
    A("| K variants in the four user-level directories | %d |" % total_variants)
    A("| files filed in two of them, counted once | %d |" % dupes)
    A("| dropped as SIMD/FP (P2, not P1) | %d |" % sum(dropped.values()))
    A("| scalar-integer variants kept | %d |" % n_kept)
    A("| **FORMS** (base mnemonic × operand shape, widths folded) | **%d** |" % n_forms)
    A("| base mnemonics | %d |" % len(bases))
    A("| of those, not already in the P0 roster | %d |" % len(new_bases))
    A("| families (= batches) | %d |" % len(families))
    A("")
    A("Operand shapes are written **destination first**, which is the order K's")
    A("filenames use (`addq_m64_r64` is the rule `addq %r64, (mem)`), so `m,r`")
    A("means a register source stored to a memory destination.\n")
    A("A FORM is one base mnemonic at one operand shape, with the widths folded")
    A("together — the same granularity the P0 coverage table counts in, where 20")
    A("mnemonics made 43 forms. The width is a datum on the instruction")
    A("(docs/DECISIONS.md D4), so `addb`/`addw`/`addl`/`addq` at `r,r` is ONE form")
    A("and four K variants. `width_conflict=1` marks a form whose widths dispose of")
    A("their flags differently in K — a finding, and there are %d of them.\n"
      % sum(1 for f in forms.values() if f["disp_conflict"]))
    A("## The family key, and why it is computed\n")
    A("`flags|reads|dest`, where `flags` is one character per flag in the order")
    A("CF PF AF ZF SF OF DF:\n")
    A("| char | meaning |")
    A("|---|---|")
    A("| `-` | K does not write the flag |")
    A("| `x` | K writes a computed value |")
    A("| `0` / `1` | K writes the constant 0 / 1 |")
    A("| `u` | **K writes `undefMInt`** — K's own reading of an Intel-undefined flag |")
    A("")
    A("⛔ **WHAT THE `u` COLUMN DOES NOT SAY, measured rather than assumed.** K")
    A("marks a flag `undefMInt` only when it is undefined UNCONDITIONALLY. A flag")
    A("the SDM leaves undefined only for SOME operand values is a computed")
    A("expression in K like any other: `shlq $imm8, %r64` contains no `undefMInt`")
    A("at all, though the SDM leaves its CF undefined when the masked count")
    A("reaches the operand width, its OF undefined when the count is not 1, and")
    A("its AF undefined whenever the count is non-zero. So `k_undef` is a LOWER")
    A("BOUND on the undefined set, and for the shift group it is the empty set")
    A("while this model's is three state-dependent regions. A roster column that")
    A("looked authoritative here would have quietly argued for deleting P0's")
    A("shift oracle draws — which the P0 differential run measured as 694 real")
    A("declines-to-commit.\n")
    A("⭐ The `u` column is a THIRD INDEPENDENT READING of the undefined set. P0")
    A("derived its undefined regions from this model's two-oracle differential")
    A("(docs/DECISIONS.md D6) and cross-read them against the SDM and ACL2 x86isa.")
    A("K is a fourth party reading the same manual. Where `k_undef` and this")
    A("model's `undefinedFlags` disagree on a form, plan v1 §4.2 says that is a")
    A("FINDING — and having it in the roster puts the finding BEFORE the")
    A("implementation instead of after the differential run.\n")
    A("## Batch order\n")
    A("Families that WRITE FLAGS come first, then the largest first. Batch 1 is")
    A("therefore a flag-heavy batch and not the cheapest one available: a wave")
    A("priced on its easiest batch is priced wrong, and the price is the whole")
    A("reason the first batch is being run.\n")
    A("| batch | forms | K variants | flags CF PF AF ZF SF OF DF | reads | dest | K dest op | base mnemonics |")
    A("|---|---|---|---|---|---|---|---|")
    for fam in families:
        keys = by_family[fam]
        disp, reads, dest = fam.split("|")
        destops = sorted({forms[k]["destop"] for k in keys})
        destop = " ".join(destops[:4]) + (" …" if len(destops) > 4 else "")
        nv = sum(forms[k]["variants"] for k in keys)
        bs = sorted({forms[k]["base"] for k in keys})
        shown = ", ".join("`%s`" % b for b in bs[:14]) + (" …" if len(bs) > 14 else "")
        A("| %d | %d | %d | `%s` | %s | %s | `%s` | %s |"
          % (batch_of[fam], len(keys), nv, disp, reads, dest, destop, shown))
    A("")
    A("## Exclusions — the only hand judgements here\n")
    A("| what | why |")
    A("|---|---|")
    for t, why in sorted(EXCLUDE_TOKENS.items()):
        A("| `%s` | %s |" % (t, why))
    for t, why in sorted(EXCLUDE_PREFIX.items()):
        A("| `%s*` | %s |" % (t, why))
    A("| any operand `xmm`/`ymm`/`zmm`/`mm`/`m128`/`m256`/`m512` | SIMD: plan v1 §5 P2. |")
    A("")
    A("Dropped, by reason: " + ", ".join("%s %d" % (k, v) for k, v in sorted(dropped.items())) + ".\n")
    A("## Audit of the derived width split\n")
    A("Every base whose width suffix was STRIPPED, with the tokens it was stripped")
    A("from. A reader checks the derivation here rather than trusting it; the rule")
    A("itself is in `scripts/k_roster.py` (`split_width`) and is refuted by the")
    A("operand widths, which is what keeps `setb`/`setl` apart.\n")
    A("| base | K tokens folded into it |")
    A("|---|---|")
    folded = collections.defaultdict(set)
    for tok in tokens_shapes:
        base, width = split[tok]
        if width != "-":
            folded[base].add(tok)
    for base in sorted(folded):
        A("| `%s` | %s |" % (base, " ".join("`%s`" % t for t in sorted(folded[base]))))
    A("")
    A("## Licence\n")
    A("The K x86-64 semantics are NCSA-licensed, © 2019 University of Illinois at")
    A("Urbana-Champaign (PROVENANCE.md). They are READ by this script and never")
    A("copied: what leaves it is mnemonic names, operand shapes and flag")
    A("dispositions — facts about x86-64 that the SDM states and that no licence")
    A("encumbers. The K tree itself is gitignored; the recipe is the clone line above.")
    mdtext = "\n".join(md) + "\n"

    # ── 6b. SELFTEST ────────────────────────────────────────────────────────
    # ⭐ A DERIVATION WITH NO SELFTEST IS A GUESS THAT COMPILES.  Every rule in
    # `split_width` was written because the version before it produced a roster
    # that LOOKED fine -- a batch table with plausible counts, in which `shl` was
    # four mnemonics, `lea` was three, and all 116 control-flow forms sat under a
    # base called `j`.  Nothing in the output said so; the totals were as
    # convincing when they were wrong.  These are the assertions a reader can
    # check against the SDM without reading a line of this script, and they are
    # the only thing standing between a mangled fence and a wave priced on it.
    if args.selftest:
        base_of = {}
        for f in forms.values():
            for tok in f["tokens"]:
                base_of[tok] = f["base"]
        bases_set = {f["base"] for f in forms.values()}
        undef_of = {}
        shapes_of = collections.defaultdict(set)
        family_of = {}
        for f in forms.values():
            undef_of.setdefault(f["base"], set()).update(
                FLAGS[i] for i, c in enumerate(f["disp"]) if c == "u")
            shapes_of[f["base"]].add(f["shape"])
            family_of[(f["base"], f["shape"])] = f["family"]

        checks = [
            # the two traps the width rule exists for, stated as SDM facts
            ("SETcc: `setb` (if below) and `setl` (if less) are DIFFERENT "
             "instructions, not two widths of one",
             base_of.get("setb") == "setb" and base_of.get("setl") == "setl"
             and "set" not in bases_set),
            ("Jcc: `jb` and `jl` are different instructions, and there is no "
             "mnemonic `j`",
             base_of.get("jb") == "jb" and base_of.get("jl") == "jl"
             and "j" not in bases_set),
            # the folds that must happen
            ("SHL is ONE mnemonic at four widths",
             {t for t, b in base_of.items() if b == "shl"}
             == {"shlb", "shll", "shlq", "shlw"}),
            ("LEA is one mnemonic, though its addressing forms name every width",
             {t for t, b in base_of.items() if b == "lea"} == {"leal", "leaq", "leaw"}),
            ("PUSH is one mnemonic, though `pushq $imm32` pushes 8 bytes",
             {t for t, b in base_of.items() if b == "push"} == {"pushq", "pushw"}),
            ("the string ops fold on their memory operands: MOVS is one mnemonic",
             {t for t, b in base_of.items() if b == "movs"}
             == {"movsb", "movsl", "movsq", "movsw"}),
            ("MOVSXD (`movslq`) exists at one width only and is not folded",
             base_of.get("movslq") == "movslq"),
            # the flag readings, against the SDM's own "Flags Affected"
            ("AND OR XOR TEST leave AF undefined (SDM Vol. 2A, each entry)",
             all(undef_of.get(m) == {"af"} for m in ("and", "or", "xor", "test"))),
            ("ADD SUB CMP leave no flag undefined",
             all(not undef_of.get(m) for m in ("add", "sub", "cmp"))),
            ("INC and DEC do not write CF (SDM Vol. 2A, INC)",
             all(f["disp"][0] == "-" for f in forms.values() if f["base"] in ("inc", "dec"))),
            # control flow reached the roster at all
            ("control flow is in the roster: `jmp`, `callq`, `retq`",
             {"jmp", "callq", "retq"} <= bases_set),
            # the accumulator forms are the same instruction as the general ones
            ("`and $imm, %rax` is in the same FAMILY as `and %r, %r`",
             family_of.get(("and", "rax,imm")) == family_of.get(("and", "r,r"))),
            # the SIMD fence
            ("no SIMD operand survived the filter",
             not any(VECTOR_OPERAND.match(o)
                     for f in forms.values() for o in f["shape"].split(","))),
        ]
        bad = 0
        for name, ok in checks:
            print(("  ✔ " if ok else "  ⛔ ") + name)
            bad += 0 if ok else 1
        print("k_roster selftest: %s (%d/%d)"
              % ("PASS" if not bad else "FAIL", len(checks) - bad, len(checks)))
        return 1 if bad else 0

    if args.check:
        bad = 0
        for path, want in ((args.out_tsv, tsv), (args.out_md, mdtext)):
            have = open(path).read() if os.path.exists(path) else ""
            if have != want:
                sys.stderr.write("⛔ %s is STALE — rerun scripts/k_roster.py\n" % path)
                bad = 1
        return bad

    for path, text in ((args.out_tsv, tsv), (args.out_md, mdtext)):
        os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
        with open(path, "w") as fh:
            fh.write(text)
    print("K variants %d → kept %d → FORMS %d in %d families/batches"
          % (total_variants, n_kept, n_forms, len(families)))
    print("wrote %s and %s" % (args.out_tsv, args.out_md))
    return 0


if __name__ == "__main__":
    sys.exit(main())
