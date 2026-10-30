#!/usr/bin/env python3
"""⭐⭐ THE DEMAND-SIDE CENSUS (desk ES, council 09/03).

WHAT THIS ANSWERS.  Every coverage number this repository publishes is
SUPPLY-side: how much of a roster the model implements.  The roster is K's
grammar of encodable forms, and an instruction set's grammar is not its usage —
a mnemonic nothing emits and a mnemonic in every function count the same there.
This tool measures the other side: **what fraction of the instructions in real
x86-64 binaries does the model already cover**, and which mnemonics it does not
cover are worth having, ranked by how often they actually occur.

THE CORPUS.  Public binaries only, downloaded from Debian and never vendored:
coreutils (small C programs), glibc (hand-written assembly and hot library
code), and a compiler's own binary, cc1 (large, machine-generated-looking C++).
⛔ **A kernel is counted in its OWN COLUMN and never pooled with them.**  vmlinux
is privileged code — its `mov %cr3`, `wrmsr`, `iret` and `swapgs` are not
absent from the model by oversight, they are outside its stated scope — so
pooling it would report a coverage number for a corpus the model never claimed,
in the direction that makes the model look worse and the census look thorough.
The kernel's own column is the input to a separate question: whether to open a
system-mode fork at all.

⚠️ THE MAPPING FAILS CLOSED, AND ITS RESIDUE IS PRINTED.  Going from an
objdump mnemonic to a roster name is where a census inflates itself: strip
suffixes too eagerly and `movsbl` becomes `movs`, which is a different
instruction the model DOES have, and the coverage number goes up for a form
nobody executed.  So every mapping rule is explicit, anything unmapped counts as
NOT COVERED, and the unmapped bucket is printed with its top entries — because
"conservative" is a direction, not a margin, and a reader has to be able to see
what is in it ([[feedback-conservative-is-a-direction-not-a-margin]]).

LANE.  Personal lane.  The binaries are public; GPL code is COUNTED, never
copied, and nothing from them enters this repository.

Usage:  demand_census.py --corpus DIR [--out docs/DEMAND-CENSUS.md]
        demand_census.py --selftest
"""
import os, re, io, sys, json, contextlib, subprocess, collections, argparse

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# ── the model's roster, read from the model, never restated ────────────────
# ⚖️⚖️ D337 — COUNT MECHANISMS, NOT VOICES (the helm's D332 ruling, extended to
# this census by paris, 2026-10-10).  Since D330 the model also implements
# mnemonics that NO differential vector can test — x86isa refuses them — and that
# a PROCESSOR referees instead (`hwprobe/`, rows derived from the SDM's rules, run
# on two vendors' silicon; the model pinned to the same rows by `decide`).  They
# are the rows of `siliconTable` in `X86/Coverage.lean`, and `docs/COVERAGE.md`
# prints them in their own section.  Reading every mnemonic row of that file, this
# census pooled them into "covered" from D335 on — 70,115 instructions of the
# assembly class credited on a processor's word, and P2-ROSTER dropped the eleven
# from its ranking as a result.
# ⇒ THREE CLASSES: (a) covered by a DIFFERENTIALLY tested mnemonic — the headline,
# alone; (b) implemented and SILICON-refereed only — its own labelled line, never
# summed into (a); (c) not modelled.  `Model` below is the differential set AS A
# SET, so every `r in model` in this file means (a) without anyone remembering to
# subtract; `.names` is every implemented mnemonic and is what the MAPPING uses, so
# a silicon instruction is classified (b) rather than mis-filed as "unmapped".
# ⛔ And it is CHECKED, not asserted: `check_no_pooling` recomputes (a) with a model
# that cannot even name a silicon mnemonic and the run exits 3 if anything moved.
SILICON_REFEREES = (
    ("D334", ("AMD EPYC 7763", "Intel Core i7-8700B")),
    ("D335", ("AMD EPYC 9V45", "Intel Core i7-8700B")),
    # D342 (V4): AES-NI / VPCLMULQDQ / the VEX shuffles (hwprobe runs 38814323211, 38814623311).
    ("D342", ("AMD EPYC 7763", "AMD EPYC 9V45", "Intel Core i7-8700B")),
    # D345 (V7): the VEX-silicon path (hwprobe runs 38995460544, 39014709807); the AMD legs by CPUID signature only.
    ("D345", ("AMD CPUID feda3203", "Intel Core i7-8700B")),
    # D348 (V8b): the second VEX-silicon path (hwprobe run 39368903666); the AMD leg NAMED by /proc/cpuinfo.
    ("D348", ("AMD EPYC 7763", "Intel Core i7-8700B")),
    # D350 (V8c): the VEX memory-operand path (hwprobe run 39464224033); the AMD leg named by /proc/cpuinfo.
    ("D350", ("AMD EPYC 9V74", "Intel Core i7-8700B")),
)
SILICON_PAIRS = "; ".join(" + ".join(rs) + " (" + d + ")" for d, rs in SILICON_REFEREES)
SILICON_LABEL = ("silicon-refereed only (AMD + Intel hwprobe: " + SILICON_PAIRS
                 + ") — NOT a semantic oracle")
VEX_LABEL = ("Implemented in the VEX table only (VEX.128 and, since D344, VEX.256, differentially tested against "
             "x86isa — D341; NOT in the published 199-mnemonic figures)")


class Model(frozenset):
    """The DIFFERENTIAL mnemonics, as the set itself (class (a)); `.names` is
    every mnemonic the model implements (the mapping's vocabulary) and
    `.silicon` the `siliconTable` mnemonics (class (b)).  ⛔ A plain set passed
    where a `Model` is expected behaves as a model with no silicon rows, which
    is exactly the reference pass `check_no_pooling` needs."""
    def __new__(cls, names, silicon=(), vex=(), silicon256=(), lockable=()):
        sil = frozenset(silicon)
        self = super().__new__(cls, frozenset(names) - sil)
        self.names = frozenset(names)
        self.silicon = sil
        # ⭐ D342 (a): the VEX table's mnemonics (COVERAGE.md's VEX section, D341) — a THIRD population,
        # differentially tested but outside the published figures, credited on its own line (never in (a)).
        self.vex = frozenset(vex)
        # ⭐ D345 (V7): the `siliconTable` rows modelled at VEX.256 too (their note declares it), so a `%ymm`
        # spelling of one maps to itself and lands in the silicon line (b), never in (a).
        self.silicon256 = frozenset(silicon256) & sil
        # ⭐ D367: the mnemonics `x86lean-diff coverage` DERIVES from `Op.lockable` over the vectors
        # (COVERAGE.md's "Lockable" line). Only a differential mnemonic can be credited, so it is cut to (a).
        self.lockable = frozenset(lockable) & (frozenset(names) - sil)
        return self


def names_of(model):
    """Every mnemonic a model can be MAPPED to (its `.names`, or the set itself)."""
    return getattr(model, "names", model)


def silicon_of(model):
    return getattr(model, "silicon", frozenset())


def silicon256_of(model):
    """⭐ D345: the silicon rows modelled at VEX.256, or nothing for a plain set."""
    return getattr(model, "silicon256", frozenset())


def lockable_of(model):
    """⭐ D367: the derived lockable mnemonics, or nothing for a plain set (LOCK stays refused there)."""
    return getattr(model, "lockable", frozenset())


def vex_of(model):
    """⭐ D342 (a): the VEX table's mnemonics, or nothing for a plain set (the no-pooling reference)."""
    return getattr(model, "vex", frozenset())


def silicon_mnemonics():
    """The `mnemonic := "…"` strings of `def siliconTable` (X86/Coverage.lean),
    read from the tree by `primitive_census.silicon_mnemonics`'s rule (the
    definition runs to its first blank line, and its list closes there) — never
    a hand list.  ⛔ This file imports nothing local (oracle_availability and
    p2_roster import IT), so the rule is restated here and `--selftest` checks it
    agrees with primitive_census's reader on the tree."""
    src = open(os.path.join(root, "X86", "Coverage.lean"), encoding="utf-8").read()
    m = re.search(r'^def siliconTable\b.*?(?=\n[ \t]*\n)', src, re.M | re.S)
    if not m or not m.group(0).rstrip().endswith("]"):
        print("⛔ silicon: `def siliconTable` not found in X86/Coverage.lean")
        sys.exit(2)
    mn = re.findall(r'mnemonic := "([^"]+)"', m.group(0))
    if not mn:
        print("⛔ silicon: `siliconTable` has no rows — refusing, not reading zero")
        sys.exit(2)
    return frozenset(mn)


def silicon256_mnemonics():
    """⭐ D345 (V7): the `siliconTable` rows whose `note` declares `VEX.256` — the rows the model implements at
    both lengths — read row by row from the same definition `silicon_mnemonics` reads, never a hand list.  A
    row whose note does not name VEX.256 is not credited at `%ymm`, which is the conservative direction."""
    src = open(os.path.join(root, "X86", "Coverage.lean"), encoding="utf-8").read()
    m = re.search(r'^def siliconTable\b.*?(?=\n[ \t]*\n)', src, re.M | re.S)
    if not m:
        print("⛔ silicon: `def siliconTable` not found in X86/Coverage.lean")
        sys.exit(2)
    rows = re.findall(r'mnemonic := "([^"]+)", shapes := "[^"]*", note := "([^"]*)"', m.group(0))
    return frozenset(mn for mn, note in rows if "VEX.256" in note)


SILICON_SECTION = "## Implemented, refereed by a processor, NOT differentially tested"

def lockable_mnemonics(text=None):
    """⭐ D367: the `Lockable:` line of the GENERATED COVERAGE.md (derived from `Op.lockable` over the vectors).
    ⛔ A COVERAGE.md without it is stale, and a census that read its absence as "nothing is lockable" would
    report the old residue as a measurement, so it REFUSES."""
    if text is None:
        text = open(os.path.join(root, "docs", "COVERAGE.md"), encoding="utf-8").read()
    lk = re.findall(r'^Lockable: (.*)$', text, re.M)
    lockable = re.findall(r'`([a-z0-9]+)`', lk[0]) if len(lk) == 1 else []
    if not lockable:
        print("⛔ LOCK: docs/COVERAGE.md has no (or more than one) `Lockable:` line, or it names nothing — "
              "refusing, not reading zero. Regenerate: lake exe x86lean-diff coverage docs/COVERAGE.md")
        sys.exit(2)
    return lockable


def model_mnemonics():
    """The mnemonics the model implements, as a `Model` (D337).  ⚠️ Read from
    the GENERATED coverage table, which CI already fails on if it is stale —
    not from a list here, which would be a copy that drifts.  The silicon split
    is read from `siliconTable`, and the run REFUSES if COVERAGE.md's processor
    section names a different set: two artifacts that must agree are compared,
    never assumed to."""
    path = os.path.join(root, "docs", "COVERAGE.md")
    text = open(path, encoding="utf-8").read()
    lockable = lockable_mnemonics(text)
    # ⭐ V3 (D341): the VEX.128 twins are a THIRD population, published in a section of their
    # own and NOT counted in this census's model. ⭐ D342 (a): they are now read — into the
    # Model's `.vex`, credited on a separately labelled line beside the silicon one, never in (a).
    text, _sep, vtext = text.partition("\n## VEX.128 register twins")
    vex = re.findall(r'^\| `([a-z0-9]+)` \|', vtext, re.M)
    if _sep and not vex:
        print("⛔ VEX: docs/COVERAGE.md has a VEX section and no mnemonic rows in it — refusing, not reading zero")
        sys.exit(2)
    ms = re.findall(r'^\| `([a-z0-9]+)` \|', text, re.M)
    if not ms:
        print("⛔ no mnemonics read from docs/COVERAGE.md; a census with no "
              "model to compare against is not a measurement.")
        sys.exit(2)
    sil = silicon_mnemonics()
    i = text.find(SILICON_SECTION)
    sect = set(re.findall(r'^\| `([a-z0-9]+)` \|', text[i:], re.M)) if i >= 0 else set()
    if sect != set(sil) or not sil <= set(ms):
        print("⛔ silicon: docs/COVERAGE.md's processor section and `siliconTable` "
              f"disagree — only in COVERAGE.md: {sorted(sect - sil)}; only in "
              f"siliconTable: {sorted(set(sil) - sect)}. Regenerate COVERAGE.md.")
        sys.exit(2)
    return Model(ms, sil, vex, silicon256_mnemonics(), lockable)

# ── objdump mnemonic -> roster name ────────────────────────────────────────
CC = ("o no b c nae ae nb nc e z ne nz be na a nbe s ns p pe np po l nge "
      "ge nl le ng g nle").split()
SUFFIXED = {"mov","add","sub","and","or","xor","cmp","test","shl","shr","sar",
            "lea","inc","dec","neg","not","push","pop","adc","sbb","rol","ror",
            "rcl","rcr","bt","bts","btr","btc","xchg","bswap","mul","imul",
            "div","idiv","cmpxchg","xadd","shld","shrd","popcnt","lzcnt",
            "tzcnt","bsf","bsr","blsi","movbe","sarx","shlx","shrx","nop",
            "cmpxchg8b",
            # ⭐ D337: objdump prints these GPR forms with an l/q suffix
            # (`andnl`, `rorxq`, `movntiq`, `adcxq`) and nothing here named
            # them, so their demand read as "not mapped at all" while the model
            # implemented every one.  adcx/adox are differential rows; the rest
            # are `siliconTable` rows and land in the silicon line, not "covered".
            "adcx","adox","mulx","andn","bextr","blsmsk","blsr","bzhi","pdep",
            "pext","rorx","movnti"}
STRING  = {"movs","stos","lods","cmps","scas"}
REPS    = {"rep","repe","repz","repne","repnz"}
EXACT = {
    "retq":"retq", "ret":"retq", "leaveq":"leaveq", "leave":"leaveq",
    "ud2":"ud2", "nop":"nop", "nopw":"nop", "nopl":"nop", "nopq":"nop",
    "cltq":"cltq", "cwtl":"cwtl", "cbtw":"cbtw", "cqto":"cqto",
    "cltd":"cltd", "cwtd":"cwtd",
    "clc":"clc", "stc":"stc", "cmc":"cmc", "cld":"cld", "std":"std",
    "jmp":"jmp", "jmpq":"jmp", "call":"call", "callq":"call",
    "loop":"loop", "loope":"loope", "loopz":"loope",
    "loopne":"loopne", "loopnz":"loopne",
    "jrcxz":"jrcxz", "jecxz":"jecxz",
    "cmpxchg8b":"cmpxchg8b", "cmpxchg16b":None,
    # ⭐ `movabsq $imm64, %r64` IS `mov` IN THE ROSTER.  P2 batch 3 landed it and
    # changed no semantics: `Operand.imm` has carried a full `BitVec 64` since
    # P0, so the form reaches `step` as the shape `movq $imm32, %r64` already
    # did.  Nothing here mapped the mnemonic, so 20,053 instructions of this
    # corpus were counted as a gap the model had already closed.
    "movabsq":"mov", "movabs":"mov",
}

def to_roster(m, ext=None, model=None):
    """objdump mnemonic -> roster name, or None if this tool will not claim it.

    ⭐⭐ `model` IS NOT OPTIONAL POLISH — IT IS THE FIX FOR D98.  Before it, the
    vector half of this mapping was a SECOND HAND-MAINTAINED LIST that had to
    grow every time the roster did, and it never did: `to_roster` returned
    `None` for `movdqa`, `paddd`, `pxor` and nineteen more mnemonics the model
    HAD, so the census reported +0.0% after a batch that added them and went on
    ranking them as the top items of "what the model does NOT cover".  The
    identity rule below is that list, DERIVED: a mnemonic the model names maps
    to itself, and the list cannot go stale because there is no list.

    ⚠️ ORDER MATTERS AND THE DANGEROUS RULE IS LAST.  `movsbl`, `movswq`,
    `movzbl` are the width-changing moves (`movsx`/`movzx`); `movsb`/`movsq` are
    the STRING move.  Stripping a trailing size letter first would turn
    `movsbl` into `movsb` and then into the string `movs` — a different
    instruction the model has, so the census would silently claim it.  The
    width-changing forms are matched BEFORE any suffix stripping.

    ⛔ AND `ext` DECIDES THE ONE COLLISION.  `movq` is TWO instructions: the
    64-bit GPR move (roster `mov`, via the suffix rule below) and the SSE2
    move between an XMM register and a GPR or memory (roster `movq`, a P2
    batch-5 row).  Resolving it by mnemonic alone must pick one and be wrong
    about the other, so the operand's register file — already classified once,
    by `isa_bucket`, and passed in here as `ext` rather than re-read from the
    operand string — settles it.  A second reading of the operands would be a
    second rule that can disagree with the first.

    ⚠️ ORDER MATTERS AND THE DANGEROUS RULE IS LAST.  `movsbl`, `movswq`,
    `movzbl` are the width-changing moves (`movsx`/`movzx`); `movsb`/`movsq` are
    the STRING move.  Stripping a trailing size letter first would turn
    `movsbl` into `movsb` and then into the string `movs` — a different
    instruction the model has, so the census would silently claim it.  The
    """
    # ⭐ the vector spelling wins where the operands ARE vector: see `ext` above.
    # ⚖️ D337: the MAPPING's vocabulary is every implemented mnemonic
    # (`names_of`), silicon-refereed ones included; whether the mapped name is
    # COVERED is `_decide`'s question, and it asks the differential set alone.
    if model is not None and ext in XMM_EXT and (m in names_of(model) or m in vex_of(model)):
        return m
    # ⭐ D344 (V6): every VEX-table row is also modelled at VEX.256, so a `%ymm` spelling that IS a VEX-table
    # row maps to itself. A legacy name never does: no legacy SSE form names a YMM register.
    if model is not None and ext == YMM and m in vex_of(model):
        return m
    # ⚠️ D345 (V7) needs no rule here: a `%ymm` spelling of a siliconTable mnemonic already maps to itself through
    # the identity rule below (a name the model has), and `_decide` decides its class. A branch added here was
    # dead code, found by `census_redprobe.py` (its mutation changed nothing), and removed.
    if m in EXACT:
        return EXACT[m]
    # the width-changing moves: movs/movz + src width + dst width
    g = re.fullmatch(r"mov([sz])([bwl])([wlq])", m)
    if g:
        return "movsx" if g.group(1) == "s" else "movzx"
    if m == "movslq":
        return "movsx"
    # jcc / setcc / cmovcc families
    for pre, name in (("j","jcc"), ("set","setcc"), ("cmov","cmovcc")):
        if m.startswith(pre):
            rest = m[len(pre):]
            if rest in CC:
                return name
            if name != "jcc" and rest[:-1] in CC and rest[-1] in "bwlq":
                return name
    # the string group, with or without a size letter
    g = re.fullmatch(r"(movs|stos|lods|cmps|scas)([bwlq])?", m)
    if g and g.group(1) in STRING:
        return g.group(1)
    if m in REPS:
        return {"repz":"repe","repnz":"repne"}.get(m, m)
    # ordinary size suffixes, only onto a base the roster actually names
    if m[:-1] in SUFFIXED and m[-1] in "bwlq":
        return m[:-1]
    if m in SUFFIXED:
        return m
    # ⭐⭐ THE IDENTITY RULE, LAST AND DERIVED FROM THE MODEL (D98).  Every rule
    # above is a REWRITE — objdump's spelling differs from the roster's — and
    # each is written out because getting one wrong claims a form nobody
    # executed.  What was missing was the case where the two spellings AGREE,
    # which is every SSE mnemonic the model has ever gained.  It fires last, so
    # no rewrite above can be overridden by it, and it claims nothing the model
    # does not name.
    if model is not None and m in names_of(model):
        return m
    return None

INSN_RE = re.compile(r"^\s*([0-9a-f]+):\s+([a-z][a-z0-9.]*)\s*(.*)")
# ⛔⛔ TWO WAYS A MNEMONIC-LEVEL CENSUS OVER-CLAIMS, BOTH MEASURED RATHER THAN
# FOOTNOTED.  This tool maps an objdump MNEMONIC to a roster name, but the model
# covers FORMS -- so an instruction whose mnemonic the model has can still be
# one the model cannot execute:
#   * `movq %xmm0, %rax` is spelled `movq` and moves a VECTOR register.  Measured
#     before this rule existed: 0.636% of cc1 and 0.121% of glibc, every one of
#     them `movq`.
#   * `mov %fs:0x28, %rax` -- the stack-protector load in most compiled
#     functions -- carries a SEGMENT PREFIX, and `Ea` had no segment field
#     because segmentation was out of scope by declaration.  Measured: 0.244% of
#     cc1, 2.655% of glibc, 0.802% of the kernel.
#
# ⛔⛔ AND BOTH OF THOSE SENTENCES ARE NOW HISTORY, WHICH IS THE OTHER HALF OF
# D98.  This paragraph read "Both now count as NOT COVERED" for twenty-two
# batches after both stopped being true: P2 batch 1 put the FS/GS base on `Ea`
# and P2 batch 5 gave the model `movq` between an XMM register and a GPR.  The
# rules those sentences describe went on excluding both forms — 76,591 and
# 33,839 instructions of this corpus — and the prose went on explaining why
# that was rigorous.  ⇒ 🔑 A JUSTIFICATION OUTLIVES THE CONDITION IT WAS TRUE
# OF, and it reads as a reason not to look.  What is true now is decided by
# `EXT_SCOPE`, which is a partition rather than a paragraph, and by the rules
# half of the staleness stamp, which moves when it moves.
#
# ⚠️ THEY DO NOT MAKE THE NUMBER EXACT, AND THE LIMIT IS STATED IN THE
# GENERATED DOCUMENT: an addressing mode or operand shape the model lacks is
# still counted as covered if the mnemonic matches.  What is claimed here is an
# UPPER BOUND on form-level coverage, and these two rules move it toward the
# truth rather than to it.
# ⛔⛔ AND `%mm0`-`%mm7` WERE MISSING FROM THIS PATTERN UNTIL THE ASSEMBLY
# COLUMN CLASS ARRIVED (the Captain's 09/03 16:5x word).  `%[xyz]mm` does not
# match `%mm0` — the `%` must be followed by `x`, `y` or `z` — so every MMX
# instruction whose objdump mnemonic happens to map to a roster name was counted
# as COVERED.  `movq %mm0, %mm3` is spelled `movq`, maps to `mov`, and this model
# has no MMX register file at all.
# ⚠️ IT WAS SILENT ON THE OLD CORPUS AND LOUD ON THE NEW ONE: `%mm[0-7]` occurs
# 0 times in glibc and 0 times in cc1 (x86-64 compilers do not emit MMX), and
# 15 690 times in libx264 and 421 in libvpx.  A gap in a declared exclusion list
# is invisible in a corpus that does not exercise it, and the direction it falls
# is the flattering one ([[feedback-a-declared-list-inherits-its-default]]).
VECTOR_RE  = re.compile(r"%[xyz]mm|%mm[0-7]\b|%k[0-7]\b|%st")
# ⛔ ONLY `%fs:` AND `%gs:` ARE SEGMENT OVERRIDES IN 64-BIT MODE.  The first
# version of this rule matched all six, and the output said so: `nop (segment
# operand)` was the 2nd-ranked "uncovered" mnemonic in three of the four
# columns, and `rep (segment operand)` the 7th in the kernel.  Neither is a
# segment access.  The canonical multi-byte NOP is spelled `nopw %cs:0x0(...)`,
# and a string op's destination is architecturally `%es:(%rdi)` -- notation, not
# an override.  In long mode CS/DS/ES/SS are ignored for address computation;
# FS and GS are the two that are not.
# ⇒ 🔑 AN OVER-BROAD EXCLUSION IS AN UNDER-CLAIM, AND AN UNDER-CLAIM IN A
# COVERAGE NUMBER LOOKS LIKE RIGOUR.  It was found by READING the ranked list
# the tool prints, which is the only reason the list is printed.
SEGMENT_RE = re.compile(r"%(?:fs|gs):")
# ⛔⛔ AND `int3` IN A RUN IS PADDING, NOT CODE.  The first kernel column read
# "covered 40.7%" -- and `int3` was 58.19% of it, 3.88 million of them.  0xCC is
# the inter-function padding byte, and a disassembler reports a run of them as
# instructions because that is what the bytes decode to.  A number that would
# have gone into a fork decision for the Captain was, in the majority, filler.
# ⇒ 🔑 A DISASSEMBLER HAS NO CONCEPT OF "NOT CODE", so a static census must
# supply one, and the one it supplies has to be stated.  A run of two or more
# consecutive `int3` is counted as PADDING and excluded from the denominator; a
# LONE `int3` is a real breakpoint and is counted.
#
# ⛔⛔ AND `lock` IS PRINTED ON ITS OWN LINE, which was costing the census twice
# over.  objdump renders a LOCK-prefixed instruction as two lines --
# `lock` at one address and `incl 0x34(%rcx)` at the next -- so a naive counter
# scores the prefix as an instruction (it is not) AND scores the instruction it
# prefixes as COVERED (it is not: this model has no LOCK, which is exactly why
# D25 declines `xchg` at memory).  9 029 of them in the kernel, 0.32%, in the
# direction that flatters.  A `lock` line now marks the NEXT instruction
# out-of-scope and is not itself counted.

# ══════════════════════════════════════════════════════════════════════════
# ⭐⭐ THE HAND-WRITTEN-ASSEMBLY COLUMN CLASS (the Captain, 09/03 16:5x).
#
# His words: *"we should look at code that is written in assembly, I believe
# VLC has a lot of it."*  Compiler output and hand-written assembly are TWO
# DEMANDS, and pooling them hides the second: hand-written codec kernels are
# SIMD in forms no compiler emits, so a census that averages them into cc1 and
# coreutils reports a coverage number for a corpus nobody writes.
#
# ⛔⛔ THE ATTRIBUTION IS PER FUNCTION AND IT GETS TWO INDEPENDENT ROUTES,
# because a single route here is a declared list whose every gap falls the same
# way ([[feedback-a-declared-list-inherits-its-default]]):
#
#   THE NAME ROUTE — the symbol carries an ISA token as a `_`-delimited
#   component (`_sse2`, `_ssse3`, `_avx2`, `_avx512icl`, `_mmxext`, `_xop`,
#   `_fma3`).  This is the convention ffmpeg, x264, dav1d and libvpx all use for
#   their nasm entry points.  Its blind spot is a nasm function with NO ISA
#   suffix, which reads as compiler output.
#
#   THE BODY ROUTE — the function's own instructions: PACKED-SIMD density at or
#   above 50% over at least 8 instructions.  Its blind spot is hand-written
#   GPR-only assembly (`rep movsb` variants), and its false positive is a C
#   function doing nothing but scalar double arithmetic — which is why the
#   packed test EXCLUDES the scalar `…ss`/`…sd` forms and the GPR↔xmm transfers.
#
# ⇒ 🔑 THE TWO ROUTES ARE PUBLISHED AS A CONFUSION MATRIX, NOT COLLAPSED INTO A
# NUMBER.  The agreement cells are the split; the two disagreement cells are the
# measurement of what each route's blind spot costs, and they are printed with
# their top symbols so a reader can look ([[feedback-two-readings-are-not-two-witnesses]]).
#
# ⛔ AND THE CONTROLS RIDE IN THE SAME RUN, PRE-REGISTERED BEFORE THE CORPUS WAS
# DOWNLOADED: `cc1` must read ~0% hand-written (a C++ compiler's own binary) and
# `glibc` must read substantially hand-written (its ifunc string/memory variants
# are exactly this pattern).  A codec column's number means nothing if those two
# do not come out that way ([[feedback-a-probe-must-create-its-condition]]).
#
# ⛔⛔ THE DISTRO BINARIES ARE STRIPPED, AND THAT NEARLY KILLED THE NAME ROUTE
# SILENTLY.  `objdump -d` prints `<sym>:` headers from `.dynsym`, which holds
# only EXPORTED symbols: measured on this corpus, ISA-suffixed names among them
# = 0 in every column, glibc and dav1d included, while libdav1d's `.symtab` (via
# its dbgsym package) carries 2 780 function symbols of which 1 808 are
# ISA-suffixed.  Shipping the name route against `.dynsym` would have printed
# "0% hand-written" for every codec column — a green that is an instrument
# failure wearing a result's clothes.  So symbols come from the DEBUG files,
# matched to each binary BY BUILD-ID, and a column whose binaries have no
# symbol map is reported as UNATTRIBUTED rather than counted as compiler output.
# ⇒ 🔑 A ROUTE THAT CANNOT SEE ITS SUBJECT REPORTS THE DEFAULT, AND THE DEFAULT
# LOOKS LIKE AN ANSWER.

ISA_COMPONENT = re.compile(
    r"^(mmx[a-z0-9]*|sse[0-9]*[ab]?|ssse3|avx512[a-z0-9]*|avx2|avx|xop|"
    r"fma[34]?|3dnow[a-z]*|aes|pclmul)$")

def name_route(sym):
    """symbol name -> 'A' (hand-written) or 'C'.  Component-EXACT, never a
    substring: `sse` must be its own `_`-delimited component, so a C function
    with `assert` in its name cannot be captured by it."""
    for comp in re.split(r"[._@]", sym):
        if ISA_COMPONENT.match(comp):
            return "A"
    return "C"

SCALAR_FP = re.compile(r"(ss|sd)$")
# ⛔ D260 (QUEUE PACKED-SCALAR-CONV): `(ss|sd)$` is a rule about SPELLING, and a
# scalar conversion's spelling ends wherever its SUFFIX puts it — `cvtsi2sdl`,
# `cvttsd2si`, `cvtss2si`.  Only the bare `cvtsi2sd` matched, and it was the
# only spelling an arm tested.  Every other one counted as packed SIMD and
# pulled its function body toward the hand-written route.  This names the
# scalar conversions by MEANING: a scalar source or destination on each side.
SCALAR_CONV = re.compile(r"v?(cvtt?s[sd]2si|cvtsi2s[sd])[lq]?")
XFER = {"movd", "movq", "movl", "vmovd", "vmovq"}

def is_packed(mn, ops):
    """PACKED SIMD, as distinct from 'touches a vector register'.

    ⚠️ THE DISTINCTION IS THE WHOLE POINT.  A C function doing double-precision
    arithmetic is 100% `%xmm` and 0% packed — `addsd`, `mulsd`, `cvtsi2sd` are
    SCALAR floating point in a vector register.  Counting those as SIMD would
    make every math-heavy C function read as hand-written assembly."""
    if re.search(r"%zmm|%ymm|%mm[0-7]\b|%k[0-7]\b", ops):
        return True
    if "%xmm" not in ops:
        return False
    if SCALAR_FP.search(mn) or SCALAR_CONV.fullmatch(mn) or mn in XFER:
        return False
    return True

BODY_MIN_INSNS = 8
BODY_PACKED_FRACTION = 0.5

def body_route(n_insns, n_packed):
    if n_insns < BODY_MIN_INSNS:
        return "C"
    return "A" if n_packed / n_insns >= BODY_PACKED_FRACTION else "C"

# ── ISA-extension buckets for the uncovered mnemonics ──────────────────────
# ⛔ THE VECTOR BUCKETS ARE COMPUTED FROM THE OPERANDS, NOT DECLARED.  Register
# width is what a Lean model has to pay for, and it is readable off every line,
# so those buckets have no list to fall out of.  Only the GPR extensions need a
# table — and that table's default is a PRINTED `unclassified` bucket with its
# top entries, never a silent fold into "other".
GPR_EXT = {
    "popcnt": "POPCNT", "lzcnt": "LZCNT", "tzcnt": "BMI1",
    "andn": "BMI1", "bextr": "BMI1", "blsi": "BMI1", "blsmsk": "BMI1",
    "blsr": "BMI1",
    "bzhi": "BMI2", "mulx": "BMI2", "pdep": "BMI2", "pext": "BMI2",
    "rorx": "BMI2", "sarx": "BMI2", "shlx": "BMI2", "shrx": "BMI2",
    "crc32": "SSE4.2",
    "endbr64": "CET-IBT", "endbr32": "CET-IBT",
    "movbe": "MOVBE", "adcx": "ADX", "adox": "ADX",
    "rdtsc": "TSC", "rdtscp": "TSC", "xgetbv": "XSAVE", "xsave": "XSAVE",
    "xrstor": "XSAVE", "cmpxchg16b": "CMPXCHG16B", "pause": "SSE2 (pause)",
    "prefetcht0": "PREFETCH", "prefetcht1": "PREFETCH",
    "prefetcht2": "PREFETCH", "prefetchnta": "PREFETCH",
    "sfence": "SSE (fence)", "lfence": "SSE2 (fence)", "mfence": "SSE2 (fence)",
    "movnti": "SSE2 (nt store)", "rdrand": "RDRAND", "rdseed": "RDSEED",
    "bswap": "486", "cpuid": "CPUID", "syscall": "SYSCALL",
    # ⚠️ operand-free AVX state instructions: the width rules cannot see them,
    # because there are no operands to read a width off.
    "vzeroupper": "AVX (state)", "vzeroall": "AVX (state)",
    "vzeroupperq": "AVX (state)",
    # ⚠️ D259: the MXCSR load/store names only a MEMORY operand, so the width
    # rules file it under "GPR/other" too.  It is SSE STATE, the same shape as the
    # AVX state row above; since B0 (D267) `Cpu` holds that state, so it is in scope.
    "ldmxcsr": "SSE (MXCSR state)", "stmxcsr": "SSE (MXCSR state)",
    "vldmxcsr": "SSE (MXCSR state)", "vstmxcsr": "SSE (MXCSR state)",
}

# ── operand-silent instructions: the register file is in the MNEMONIC ─────
# ⛔⛔ D259 (QUEUE CENSUS-SILENT-OPERANDS).  `isa_bucket` reads the register file
# off the operand TEXT, and three families name none there: `emms` (no
# operands), x87 forms that load from or store to MEMORY or take no operands
# (`fldl (%rax)`, `fnstsw %ax`, `fld1`), and a float->int conversion whose
# source is MEMORY (`cvttsd2si (%rbx),%eax`).  All of them fell to "GPR/other".
# Measured on the committed census at 35c5c15: that bucket's uncovered demand
# was 218 instructions over 16 mnemonics, and NOT ONE was a GPR form; the 32
# `cvtts*` among them were the reason sub-group A′ was priced at 898 and not 930.
# ⚠️ WHAT IT MOVED WAS ATTRIBUTION, NOT COVERAGE: every one of the 218 reads
# `unmapped` in `_decide`, so the scope flag was never consulted for them.
# ✅ THE RULE BELOW RUNS ONLY WHERE THE OPERAND RULE HAS NOTHING TO READ — it is
# consulted after every register test, so an instruction that names `%st`,
# `%mm`, `%xmm` or wider is bucketed exactly as before.
# ⛔ THE x87 SET IS AN EXPLICIT LIST (SDM Vol. 1 ch. 8, the x87 FPU instruction
# set), NEVER AN `f` PREFIX: `fxsave` saves x87 AND SSE state and is not a stack
# form, and a prefix rule would also capture any future `f…` GPR mnemonic.
# ⚠️ WHAT STAYS IN "GPR/other", DECLARED: the whole-state saves (`fxsave`,
# `fxrstor`, `xsavec`, `xrstors64` …) name no single register file, and the
# system and CET forms (`hlt`, `rdsspq`, `rdpkru`, `xtest` …) are not a register
# file this census partitions by.  The MXCSR load/store is a `GPR_EXT` row.
X87_BARE = frozenset("""
    f2xm1 fabs fchs fclex fnclex fcos fdecstp fincstp finit fninit fld1 fldl2t
    fldl2e fldlg2 fldln2 fldpi fldz fnop fpatan fprem fprem1 fptan frndint fscale fsin
    fsincos fsqrt ftst fxam fxtract fyl2x fyl2xp1 fcompp fucompp wait fwait
    ffree ffreep fxch fucom fucomp fucomi fucomip fcomi fcomip
    fcmovb fcmove fcmovbe fcmovu fcmovnb fcmovne fcmovnbe fcmovnu
    fldcw fldenv fnstcw fstcw fnstenv fstenv fnstsw fstsw fnsave fsave frstor
    fbld fbstp faddp fsubp fsubrp fmulp fdivp fdivrp
""".split())
# the forms that take a SIZED memory operand, which AT&T spells with a suffix:
# `s` (float32 / int16), `l` (float64 / int32), `t` (float80), `ll` (int64)
X87_SIZED = frozenset("""
    fld fst fstp fadd fsub fsubr fmul fdiv fdivr fcom fcomp
    fild fist fistp fisttp fiadd fisub fisubr fimul fidiv fidivr ficom ficomp
""".split())
X87_SUFFIXES = ("ll", "s", "l", "t")
MMX_SILENT = frozenset({"emms"})
_SILENT_CVT_RE = re.compile(r"(v?)cvtt?s[sd]2si[lq]?")

def silent_operand_bucket(mn):
    """The bucket an instruction's MNEMONIC names, for the families whose
    operands may name no register file; `None` for everything else."""
    if mn in MMX_SILENT:
        return "MMX (mm)"
    m = _SILENT_CVT_RE.fullmatch(mn)
    if m:
        return "VEX-128 (v… xmm)" if m.group(1) else "SSE-legacy (xmm)"
    if mn in X87_BARE or mn in X87_SIZED:
        return "x87 (st)"
    for suf in X87_SUFFIXES:
        if mn.endswith(suf) and mn[:-len(suf)] in X87_SIZED:
            return "x87 (st)"
    return None

# the closed domain the staleness stamp hashes the bucket rule over (see
# `model_stamp`): every silent spelling, plus operand shapes of every register
# file, so a change to ANY branch of `isa_bucket` over these names moves it
_SILENT_DOMAIN = (MMX_SILENT | X87_BARE | X87_SIZED
                  | {b + s for b in X87_SIZED for s in X87_SUFFIXES}
                  | {v + "cvt" + t + "s" + f + "2si" + w
                     for v in ("", "v") for t in ("", "t") for f in "sd"
                     for w in ("", "l", "q")})
# D260: every spelling `SCALAR_CONV` names, so the stamp sees the packed rule on each
_SCALAR_CONV_DOMAIN = {v + c + w for v in ("", "v")
                       for c in ("cvtss2si", "cvtsd2si", "cvttss2si", "cvttsd2si",
                                 "cvtsi2ss", "cvtsi2sd")
                       for w in ("", "l", "q")}
_BUCKET_PROBE_OPS = ("", "(%rbx)", "(%rbx),%eax", "%ax", "%rax, %rbx",
                     "%xmm0,%eax", "%mm1, %mm0", "%st(1)", "%ymm0, %ymm1",
                     "%zmm0, %zmm1", "%fs:0x28, %rax")

# ⭐ D367: the LOCK bucket's name, ONE spelling, so `_decide` and `isa_bucket` cannot drift apart.
LOCK_BUCKET = "LOCK prefix (P2 addition 2)"

def isa_bucket(mn, ops, kind="plain"):
    """⛔ THE BUCKET IS THE REASON THE MODEL CANNOT EXECUTE IT, not just the
    register file it touches.  `movq %gs:0x28, %rax` is a `mov` the model has;
    what it lacks is the SEGMENT BASE — and a table that files that under
    "GPR/other" prices a vector gap that is not there and hides a P2 item that
    is.  The three additions the Captain ordered into P2 (a segment base in
    `Ea`, a LOCK vocabulary, and the `movabs` mov form) are therefore each a
    NAMED ROW here, so the roster can be priced off this table directly."""
    if kind == "lock":
        return LOCK_BUCKET
    if kind == "segment":
        return "segment base %fs:/%gs: (P2 addition 1)"
    if mn == "movabsq" or mn == "movabs":
        return "mov imm64 / movabs (P2 addition 3)"
    if re.search(r"%zmm|%k[0-7]\b", ops):
        return "AVX-512 (zmm/k)"
    if "%ymm" in ops:
        return "AVX2/AVX (ymm)"
    if "%xmm" in ops:
        return "VEX-128 (v… xmm)" if mn.startswith("v") else "SSE-legacy (xmm)"
    if re.search(r"%mm[0-7]\b", ops):
        return "MMX (mm)"
    if "%st" in ops:
        return "x87 (st)"
    silent = silent_operand_bucket(mn)
    if silent is not None:
        return silent
    base = mn[:-1] if (mn[:-1] in GPR_EXT and mn[-1] in "bwlq") else mn
    return GPR_EXT.get(base, "GPR/other (unclassified)")


# ── which of those buckets the model's STATE can represent at all ──────────
# ⭐⭐ THE SECOND HALF OF D98, AND THE HALF THAT POINTS THE OTHER WAY.  Whether
# the model covers an instruction is decided by THREE things and only the first
# was ever coupled to the model: the roster name (`to_roster`, fixed above), the
# REGISTER FILE the operands name, and the PREFIX.  The old rule was one line —
# `kind != "plain"` is not covered — and it was written when the model had no
# vector registers, no segment base and no LOCK vocabulary.  All three have
# since landed, and the rule did not move.
#
# ⛔ IT IS A TOTAL PARTITION AND `form_in_scope` REFUSES ON A BUCKET IT DOES NOT
# KNOW.  An allow-list would send every unclassified bucket to COVERED (an
# over-claim) and a deny-list would send it to NOT COVERED (an under-claim);
# both are a default, and a default is how this document came to say +0.0 after
# a batch that moved it ([[feedback-a-declared-list-inherits-its-default]]).  A
# new bucket added to `isa_bucket` STOPS THE CENSUS until someone rules on it.
#
# ⚠️ THE GPR EXTENSION BUCKETS ARE DERIVED FROM `GPR_EXT`, not restated: they
# name a REASON, not a register file, so whether the model has `popcnt` or
# `endbr64` is decided where every other mnemonic's is — by `r in model`.
EXT_SCOPE = {v: True for v in GPR_EXT.values()}
EXT_SCOPE.update({
    # ⛔ operand-free AVX state instructions are NOT a GPR form; they are in
    # `GPR_EXT` only because there are no operands to read a width off.
    "AVX (state)":                            False,
    # ⛔ D259 ruled this False because MXCSR was ABSENT from `Cpu` (D2), so its load/store
    # could not be held.  ⭐ B0 (D266, D267) put MXCSR in `Cpu`, so the state exists and the
    # load/store is IN SCOPE and NOT COVERED — a batch of its own, never implied by B0.
    "SSE (MXCSR state)":                      True,
    # register files this model does not have
    "AVX-512 (zmm/k)":                        False,
    "AVX2/AVX (ymm)":                         False,
    "VEX-128 (v… xmm)":                       False,
    "MMX (mm)":                               False,
    "x87 (st)":                               False,
    # ⭐ the one vector register file it DOES have (P2 batches 4-9)
    "SSE-legacy (xmm)":                       True,
    # ⭐ P2 addition 1 LANDED (batch 1): the FS/GS base is a field on `Ea`, so a
    # segment override is a prefix on rows already claimed — 76,591 instructions
    # of this corpus, the commonest of them the stack-protector load.
    "segment base %fs:/%gs: (P2 addition 1)": True,
    # ⭐ P2 addition 3 LANDED (batch 3): see the `movabsq` entry in EXACT.
    "mov imm64 / movabs (P2 addition 3)":     True,
    # ⛔ P2 addition 2 LANDED (batch 2) AND THIS STAYS FALSE, DELIBERATELY.  The
    # model's LOCK coverage is PER FORM — `Op.lockIllegal` over the SDM's
    # nineteen-mnemonic list — and this tool has no model-derived route to that
    # predicate: `docs/COVERAGE.md` publishes mnemonics, not the list.  Copying
    # the nineteen names here would be a fourth hand-maintained list, of exactly
    # the kind D98 is about, and claiming a locked form by MNEMONIC would
    # over-claim `lock movq %rax,(%rbx)` — #UD on silicon, and the form a reader
    # most expects to be lockable.  So it is refused, at a MEASURED cost of
    # 9,945 instructions (0.07% of this corpus), and the refusal names the
    # cheaper build: export `Op.lockIllegal` into a generated artifact and this
    # line becomes derivable ([[feedback-a-gate-that-refuses-names-a-cheaper-build]]).
    # ⭐ D367 BUILT THAT: `x86lean-diff coverage` derives the lockable mnemonics from `Op.lockable` over the
    # vectors, and `_decide` credits a locked form whose roster name is on that line. The ruling below stays
    # False, so a locked form the model does not derive as lockable is still refused.
    "LOCK prefix (P2 addition 2)":            False,
    "GPR/other (unclassified)":               True,
})
# the buckets whose operands name an XMM register — the input to `to_roster`'s
# one operand-dependent rule.  ⚠️ `VEX-128` is xmm too, and is here for the same
# reason: `vmovq %xmm0,%rax` must resolve its spelling the same way even though
# `EXT_SCOPE` then refuses it for the ENCODING.
XMM_EXT = frozenset({"SSE-legacy (xmm)", "VEX-128 (v… xmm)"})
VEX128 = "VEX-128 (v… xmm)"
# ⭐ D344 (V6): the VEX.256 bucket, where a VEX-table mnemonic is credited in the same VEX class.
YMM = "AVX2/AVX (ymm)"

def form_in_scope(ext):
    """⛔ REFUSES rather than defaulting. See EXT_SCOPE."""
    if ext not in EXT_SCOPE:
        print(f"⛔ `{ext}` is an ISA bucket no one has ruled on. A census that "
              f"guesses whether a register file is in scope reports a coverage "
              f"number for a model nobody described. Add it to EXT_SCOPE.")
        sys.exit(2)
    return EXT_SCOPE[ext]


# ── the symbol map: build-id -> debug file -> sorted (addr, end, name) ─────
BUILD_ID_NOTE = ".note.gnu.build-id"
SYMTAB_RE = re.compile(
    r"^([0-9a-f]{8,16})\s.*\sF\s+\S+\s+([0-9a-f]{8,16})\s+(\S.*?)\s*$")

def build_id(path):
    """The GNU build-id of an ELF, read through objdump so this tool keeps its
    one external dependency and does not grow an ELF parser."""
    try:
        out = subprocess.run(["objdump", "-s", "-j", BUILD_ID_NOTE, path],
                             capture_output=True, text=True).stdout
    except OSError:
        return None
    hexes = []
    for line in out.splitlines():
        m = re.match(r"^\s*[0-9a-f]+\s((?:[0-9a-f]{2,8}\s){1,4})", line)
        if m:
            hexes.append(m.group(1).replace(" ", ""))
    blob = "".join(hexes)
    # namesz(4) descsz(4) type(4) "GNU\0"(4) = 16 bytes of header
    if len(blob) < 32 + 40:
        return None
    return blob[32:32 + 40]

def symbols(path):
    """FUNC symbols from a file's `.symtab`, as sorted (addr, end, name).

    ⚠️ A NASM SYMBOL HAS SIZE 0 — nasm emits no `.size` directive, so every
    hand-written entry point in this corpus reports size 0 while every C
    function reports a real one.  The end of a function is therefore
    `min(addr+size, next addr)` when the size is known and the next symbol's
    address when it is not; anything past a sized function's end and before the
    next symbol is UNATTRIBUTED and printed as such."""
    try:
        out = subprocess.run(["objdump", "-t", path],
                             capture_output=True, text=True).stdout
    except OSError:
        return []
    syms = []
    for line in out.splitlines():
        m = SYMTAB_RE.match(line)
        if m:
            a, sz, nm = int(m.group(1), 16), int(m.group(2), 16), m.group(3)
            if a:
                syms.append((a, sz, nm))
    syms.sort()
    out2 = []
    for i, (a, sz, nm) in enumerate(syms):
        nxt = syms[i + 1][0] if i + 1 < len(syms) else a + max(sz, 1)
        end = min(a + sz, nxt) if sz else nxt
        out2.append((a, end, nm))
    return out2

def debug_index(debug_dir):
    """build-id -> debug file, over a tree of unpacked `-dbgsym` packages."""
    idx = {}
    if not debug_dir:
        return idx
    for r, _, fs in os.walk(debug_dir):
        for f in fs:
            if f.endswith(".debug"):
                p = os.path.join(r, f)
                # the dbgsym layout names the file BY the build-id, and the
                # note is read back as a cross-check rather than trusted.
                bid = (os.path.basename(os.path.dirname(p)) +
                       f[:-len(".debug")])
                idx[bid] = p
    return idx


import bisect

# ⛔⛔ THE WIDTH A MNEMONIC DOES NOT CARRY (D257, the `cvtsi2s*` key fix).  objdump
# prints a REGISTER-source `cvtsi2sd`/`cvtsi2ss` with NO operand-size suffix
# whatever the source width, and the MEMORY-source forms WITH one:
#     cvtsi2sd %eax,%xmm0      int32  source   (f2 0f 2a c0)
#     cvtsi2sd %rax,%xmm0      int64  source   (f2 48 0f 2a c0)  <- the SAME spelling
#     cvtsi2sdl (%rbx),%xmm0   int32  source
#     cvtsi2sdq (%rbx),%xmm0   int64  source
# Keyed by the printed mnemonic, 2,603 register-source instructions had a key no
# other tool joins on, and one key held both an EXACT conversion (int32 ->
# binary64) and an INEXACT one (int64 -> binary64).  The rule that decides a
# conversion's semantics is (source WIDTH, target format), never the source's
# SHAPE, so the register form is keyed by clang's suffixed spelling — the spelling
# `oracle_availability` already probes it under — and pools with the memory form
# of the same width.
# ⚠️ ONLY THE KEY MOVES.  `is_packed` and `isa_bucket` still read the PRINTED
# mnemonic, so function-origin attribution cannot change through this rule.
# ⛔ FAILS CLOSED: a source this does not recognise keeps the bare, unjoined name.
WIDTH_KEYED = ("cvtsi2sd", "cvtsi2ss")
_GPR32_RE = re.compile(r"%(?:e(?:ax|bx|cx|dx|si|di|bp|sp)|r(?:[89]|1[0-5])d)")
_GPR64_RE = re.compile(r"%(?:r(?:ax|bx|cx|dx|si|di|bp|sp)|r(?:[89]|1[0-5]))")

def width_key(mn, ops):
    """The census key for one instruction line: the printed mnemonic, except a
    bare `cvtsi2sd`/`cvtsi2ss` takes `l`/`q` from its REGISTER source."""
    if mn not in WIDTH_KEYED:
        return mn
    src = ops.split(",", 1)[0].strip()
    if _GPR32_RE.fullmatch(src):
        return mn + "l"
    if _GPR64_RE.fullmatch(src):
        return mn + "q"
    return mn

# the closed domain the staleness stamp hashes this rule over (see `model_stamp`)
_WIDTH_PROBE_SRCS = ("%eax", "%r8d", "%r15d", "%esp", "%rax", "%r8", "%r15",
                     "%rsp", "%ax", "%al", "(%rbx)", "0x8(%rsp,%rcx,4)", "%xmm1")

def is_mem_form(ops):
    """⭐ STATUS 7c — True when an instruction's operands carry an ADDRESSING MODE: a parenthesised base/index
    (`(%rbx)`, `0x8(%rip)`) or a segment-relative address (`%fs:0x28`). That is the operand SHAPE `m` in this
    repository's coverage rows. It says nothing about whether memory is touched (`lea` names an address and reads
    none); it classifies the FORM, which is what a credited figure claims."""
    return "(" in ops or bool(SEGMENT_RE.search(ops))


def _classify(lines, syms=None, fn_sink=None, mem_sink=None):
    """objdump lines -> Counter keyed by (mnemonic, kind, origin, ext).

    ⚠️ SPLIT OUT OF `disassemble` SO IT CAN BE DRIVEN ON SYNTHETIC INPUT.  The
    three rules that moved this census most — padding runs, the `%fs:`/`%gs:`
    narrowing, and LOCK attribution — are all LINE-level, and a rule that can
    only be exercised by disassembling a 63 MB kernel does not get exercised.

    ⚠️ ORIGIN IS A CELL OF THE CONFUSION MATRIX, not a verdict: `AA` is both
    routes saying hand-written, `CC` both saying compiler, `AC` and `CA` the two
    disagreements, `U` an address no function symbol covers, and `-` a column
    with no symbol map at all.  Nothing collapses them here; `report` does the
    collapsing where a reader can see the cells it collapsed.

    ⭐ STATUS 7c (the helm, 10-19 21:09, O88: claims match what is modelled): `mem_sink`, when given, receives
    EXACTLY the keys `c` does, for the instructions whose operands carry an ADDRESSING MODE (`is_mem_form`) and
    no others. `report` runs the same `_split` over it, so every credited figure can print its register/memory
    split under the one rule that produced the figure, never a second one."""
    c = collections.Counter()
    run = 0
    pending_lock = False
    starts = [a for a, _, _ in syms] if syms else []
    # the current function's buffer: (mn, kind, ext) rows plus a packed tally
    buf, n_packed, cur = [], 0, None

    def flush_padding(run):
        if run >= 2:
            c[("int3", "padding", "-", "-")] += run
        elif run == 1:
            c[("int3", "plain", cell(), bucket_of("int3", "", "plain"))] += 1

    def cell():
        if syms is None:
            return "-"
        if cur is None:
            return "U"
        return name_route(cur[2]) + body_route(len(buf), n_packed)

    def bucket_of(mn, ops, kind):
        return isa_bucket(mn, ops, kind)

    def flush_fn():
        nonlocal buf, n_packed
        if buf:
            k = cell()
            for mn, kind, ext, mem in buf:
                c[(mn, kind, k, ext)] += 1
                if mem and mem_sink is not None:
                    mem_sink[(mn, kind, k, ext)] += 1
            # ⚠️ THE RESIDUE IS KEPT BY NAME, not just counted.  A disagreement
            # cell that cannot be read is a number nobody can check.
            if fn_sink is not None and cur is not None:
                fn_sink.setdefault(k, collections.Counter())[cur[2]] += len(buf)
        buf, n_packed = [], 0

    def locate(addr):
        if not starts:
            return None
        i = bisect.bisect_right(starts, addr) - 1
        if i < 0:
            return None
        a, e, nm = syms[i]
        return syms[i] if a <= addr < e else None

    for line in lines:
        mm = INSN_RE.match(line)
        if not mm:
            continue
        addr, mn, ops = int(mm.group(1), 16), mm.group(2), mm.group(3)
        if mn == "int3":
            run += 1
            continue
        flush_padding(run); run = 0
        if mn == "lock" and not ops.strip():
            pending_lock = True
            continue
        if syms is not None:
            here = locate(addr)
            if here is not cur:
                flush_fn()
                cur = here
        # ⚠️ `nop` keeps its CS prefix and is still a NOP; the exclusion is
        # about a segment-relative ADDRESS, which a multi-byte nop's operand
        # is not.
        seg = SEGMENT_RE.search(ops) and to_roster(mn) != "nop"
        kind = ("lock" if pending_lock else
                "vector" if VECTOR_RE.search(ops) else
                "segment" if seg else "plain")
        pending_lock = False
        if syms is None:
            # ⚠️ THROUGH `cell()`, NOT PAST IT.  This branch used to write the
            # `-` literal itself, which made `cell()`'s own `syms is None` case
            # reachable ONLY by a lone `int3` — so the rule had two statements
            # and the arm that tested it could only see one of them.  The red
            # probe found it: mutating `cell()` to return "CC" left the selftest
            # GREEN.  ⇒ 🔑 A RULE WRITTEN TWICE IS A RULE ONE ARM CAN ONLY
            # HALF-TEST, and the half nobody exercises is the half that moves.
            key = (width_key(mn, ops), kind, cell(), isa_bucket(mn, ops, kind))
            c[key] += 1
            if mem_sink is not None and is_mem_form(ops):
                mem_sink[key] += 1
        else:
            buf.append((width_key(mn, ops), kind, isa_bucket(mn, ops, kind), is_mem_form(ops)))
            if is_packed(mn, ops):
                n_packed += 1
    flush_padding(run)
    flush_fn()
    return c


def classify_lines(lines):
    """The (mnemonic, kind) PROJECTION of `_classify`, kept because the
    line-level rules are what the proven arms drive and they are orthogonal to
    attribution.  ⚠️ It is a projection, not a second implementation: there is
    one loop, and these arms test it too."""
    c = collections.Counter()
    for (mn, kind, _o, _e), k in _classify(lines).items():
        c[(mn, kind)] += k
    return c


def disassemble(path, syms=None, fn_sink=None, mem_sink=None):
    """⚠️ STREAMED, not captured.  vmlinux is 63 MB of ELF and disassembles to
    well over a gigabyte of text; `capture_output` would hold all of it in
    memory at once for a job whose whole output is a counter."""
    with subprocess.Popen(["objdump", "-d", "--no-show-raw-insn", path],
                          stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                          text=True, bufsize=1 << 20) as pr:
        c = _classify(pr.stdout, syms, fn_sink, mem_sink)
        rc = pr.wait()
    return c if rc == 0 else None


def is_elf_x86_64(p):
    try:
        h = open(p, "rb").read(20)
    except OSError:
        return False
    return h[:4] == b"\x7fELF" and h[4] == 2 and h[18:20] == b"\x3e\x00"

def elf_targets(paths):
    """The ELF x86-64 files to disassemble, ONE ENTRY PER BINARY.

    ⛔⛔ A SYMLINK IS NOT A SECOND BINARY, AND COUNTING IT AS ONE DOUBLES A
    COLUMN IN A WAY THAT LOOKS LIKE DATA.  Debian ships `libdav1d.so.7`
    alongside `libdav1d.so.7.0.0`, `libavcodec.so.61` alongside
    `libavcodec.so.61.19.101`, and `os.walk` lists both — the link resolves, the
    ELF check passes, and every count in the column comes out exactly twice.
    ⚠️ IT WAS FOUND BY THE SHAPE OF THE NUMBERS, NOT BY A GATE: a smoke run of
    the dav1d column read 74,034 · 36,578 · 27,536 · 23,124 — thirty ranked rows
    and every one of them even, against a column of ONE binary.  The
    percentages were all correct, because a doubled numerator over a doubled
    denominator is the same ratio ([[feedback-two-defects-that-cancel]]), so
    nothing in the published shape of the document could have shown it."""
    seen, out = set(), []
    for p in sorted(paths):
        if os.path.islink(p) or not is_elf_x86_64(p):
            continue
        try:
            key = os.stat(p).st_ino
        except OSError:
            continue
        if key in seen:          # a hard link is not a second binary either
            continue
        seen.add(key)
        out.append(p)
    return out


def census(paths, dbg=None, mem_sink=None):
    """⚠️ RETURNS THE SYMBOL COVERAGE TOO, because "how many of this column's
    binaries had a symbol map" is the condition under which every attribution
    number below it is true, and a column measured with no symbols reports the
    default silently."""
    total = collections.Counter()
    fns = {}
    n = n_sym = 0
    for p in elf_targets(paths):
        syms = None
        if dbg is not None:
            bid = build_id(p)
            d = dbg.get(bid) if bid else None
            syms = symbols(d) if d else symbols(p)
            if not syms:
                syms = None
        mem = collections.Counter()
        c = disassemble(p, syms, fns, mem)
        if c is None:
            continue
        total += c
        if mem_sink is not None:
            mem_sink.update(mem)    # only for a file whose counts were kept, as `total` is
        n += 1
        n_sym += 1 if syms else 0
    return total, n, n_sym, fns

# ⭐⭐ THE STALENESS STAMP (P1 seal, D69).
#
# `docs/COVERAGE.md` is GENERATED and CI fails if it is stale, because the
# generator can be re-run on any machine.  This document cannot: it needs a
# corpus of downloaded binaries, so CI can gate the INSTRUMENT (the 45 mapping
# arms) and not the READING.  That leaves a published document whose headline —
# "the model covers 84 mnemonics", and every percentage under it — is a claim
# about a model that can change underneath it, with nothing to notice.
#
# ⇒ 🔑 A FIGURE NOT RE-COMPUTED AT THE MOMENT OF WRITING IS A FIGURE OF AN
# EARLIER TREE.  So the document STAMPS the exact model it was generated
# against, and `--check` — which needs no corpus and does run in CI — recomputes
# that identity and refuses if it has moved.  The census does not become correct
# again; it becomes LOUD.
#
# ⚠️ The identity is a hash of the SORTED MNEMONIC LIST, not of the file: the
# census depends on precisely that set and on nothing else in the coverage
# table, so a reworded row must not fail this gate and a NEW MNEMONIC must.
# ⭐⭐ AND THE STAMP HASHED ONLY ONE OF THE TWO COUPLED ARTIFACTS (D98).  The
# paragraph above is true and was not enough.  A census percentage is a function
# of TWO inputs — the model, and the MAPPING that decides which of a binary's
# instructions the model covers — and this stamp hashed the first.  So when the
# model gained `movdqa`, `paddd`, `pxor` and twenty more, the stamp moved, the
# gate went red, the document was regenerated on its word, and every percentage
# came back BIT-IDENTICAL: the mapping had not grown with the roster and could
# not see the new rows.
#
# ⇒ 🔑 AN ANTI-STALENESS GATE OVER TWO COUPLED ARTIFACTS REPORTS ONLY ABOUT THE
# ONE IT HASHES — AND A FORCED REGENERATION CAN THEN MAKE A STALE NUMBER LOOK
# FRESHLY COMPUTED, which is worse than no stamp at all, because the
# regeneration reads as diligence.
#
# So the stamp carries a SECOND sha over the MAPPING'S BEHAVIOUR: every decision
# `_decide` makes over a domain that needs no corpus — every mnemonic any table
# here names, crossed with every ISA bucket `EXT_SCOPE` rules on.  ⚠️ BEHAVIOUR,
# not source text: a reworded comment must not fail this gate and a changed
# ANSWER must ([[feedback-a-staleness-stamp-hashes-only-one-half]]).  The domain
# is closed under the tables, so a new mapping rule cannot hide outside it — any
# rule that starts claiming a mnemonic must name that mnemonic somewhere here.
STAMP_RE = re.compile(r"<!-- census-model: mnemonics=(\d+) sha=([0-9a-f]{16}) "
                      r"rules=([0-9a-f]{16}) -->")
FORMS_STAMP_RE = re.compile(r"<!-- census-forms: vectors=(\d+) probes=(\d+) sha=([0-9a-f]+) -->")

def _rule_domain(model):
    """Every mnemonic this file's mapping tables can possibly rewrite, plus the
    model's own names.  ⛔ NOT read from the census's output: a gate whose
    domain came from the document it checks could only agree with it."""
    # ⛔ D344: `vex_of(model)` too. `names_of` excludes the VEX table, so until D344 no VEX-table mnemonic was in the
    # domain and the stamp could not see a rule that moved one: the VEX.256 rule (ymm → the VEX class) left
    # `rules=` byte-identical, and V5's document read CLEAN against V6's mapping.
    d = set(names_of(model)) | set(vex_of(model)) | set(EXACT) | set(SUFFIXED) | set(STRING) | set(REPS) \
        | set(GPR_EXT)
    for base in list(SUFFIXED) + list(STRING):
        d |= {base + c for c in "bwlq"}
    for pre in ("j", "set", "cmov"):
        d |= {pre + c for c in CC}
    d |= {f"mov{a}{b}{c}" for a in "sz" for b in "bwl" for c in "wlq"}
    d |= set(WIDTH_KEYED) | {b + c for b in WIDTH_KEYED for c in "lq"}
    return d

def model_stamp(model):
    import hashlib
    # ⚖️ D337: the identity is the implemented set AND its silicon split — moving
    # a mnemonic between (a) and (b) moves every figure, so it must move the stamp
    h = hashlib.sha256((" ".join(sorted(names_of(model))) + " | silicon: "
                        + " ".join(sorted(silicon_of(model)))
                        + (" | vex: " + " ".join(sorted(vex_of(model))) if vex_of(model) else "")
                        + (" | lock: " + " ".join(sorted(lockable_of(model))) if lockable_of(model) else "")
                        ).encode()).hexdigest()[:16]
    rows = []
    for m in sorted(_rule_domain(model)):
        for ext in sorted(EXT_SCOPE):
            r, cov, cls = _decide(m, ext, model)
            rows.append(f"{m}\t{ext}\t{r}\t{int(cov)}\t{cls}")
    # ⛔ D257: a rule that renames the KEY before `_decide` ever sees it is part of
    # the mapping, and a stamp that hashed only `_decide` could not see it move —
    # D98's blindness, one function earlier.  Its behaviour over a closed domain
    # goes into the same hash.
    for m in WIDTH_KEYED:
        for src in _WIDTH_PROBE_SRCS:
            rows.append(f"KEY\t{m}\t{src}\t{width_key(m, src + ',%xmm0')}")
    # ⛔ D259: and so does `isa_bucket`, which also runs before `_decide` and
    # hands it the bucket.  A bucket rule that moved an instruction between
    # register files left this stamp unmoved, so the census read as fresh.
    for m in sorted(_rule_domain(model) | _SILENT_DOMAIN | _SCALAR_CONV_DOMAIN):
        for ops in _BUCKET_PROBE_OPS:
            rows.append(f"BUCKET\t{m}\t{ops}\t{isa_bucket(m, ops)}")
            # ⛔ D260: and `is_packed`, which decides every ORIGIN cell the same
            # document publishes; a packed-rule change left the stamp unmoved too
            rows.append(f"PACKED\t{m}\t{ops}\t{int(is_packed(m, ops))}")
    rh = hashlib.sha256("\n".join(rows).encode()).hexdigest()[:16]
    return len(names_of(model)), h, rh

def check_stale(out_path):
    model = model_mnemonics()
    n, h, rh = model_stamp(model)
    try:
        text = open(os.path.join(root, out_path), encoding="utf-8").read()
    except OSError:
        print(f"⛔ {out_path} does not exist. Generate it with "
              f"`demand_census.py --corpus <dir>`.")
        return 2
    m = STAMP_RE.search(text)
    if not m:
        print(f"⛔ {out_path} carries no `census-model` stamp, so nothing can "
              f"tell which model its percentages are about. Regenerate it.")
        return 2
    sn, sh, srh = int(m.group(1)), m.group(2), m.group(3)
    # ⛔ WHICH HALF MOVED IS PART OF THE MESSAGE.  D98 was a red that said "the
    # model moved" about a document whose numbers could not move; a reader who
    # cannot tell the halves apart regenerates and believes the result.
    if (sn, sh) != (n, h) or srh != rh:
        which = ("the MODEL and the MAPPING have both moved"
                 if (sn, sh) != (n, h) and srh != rh else
                 "the MODEL has moved" if (sn, sh) != (n, h) else
                 "the MAPPING has moved (the model is unchanged)")
        print(f"⛔ THE CENSUS IS STALE — {which}. {out_path} was generated "
              f"against a model of {sn} mnemonics (sha {sh}, rules {srh}); it "
              f"is now {n} (sha {h}, rules {rh}). Every coverage percentage in "
              f"that document is against the older pair.\n"
              f"   Regenerate: demand_census.py --corpus <dir>  "
              f"(the recipe is in the document).")
        return 1
    # ⭐ D352: the modelled figure reads the model's FORMS, which the mnemonic stamp above cannot see — a new
    # memory-form vector moves no mnemonic. Its INPUTS are hashed (text only, so this runs on any runner).
    fm = FORMS_STAMP_RE.search(text)
    fv, fp, fd = forms_digest(root)
    if not fm:
        print(f"⛔ {out_path} carries no `census-forms` stamp, so nothing can tell which of the model's forms its "
              f"modelled figures are about (D352). Regenerate it.")
        return 1
    if (int(fm.group(1)), int(fm.group(2)), fm.group(3)) != (fv, fp, fd):
        print(f"⛔ THE CENSUS IS STALE — the model's FORMS have moved (D352): generated against {fm.group(1)} vectors "
              f"+ {fm.group(2)} probe forms (sha {fm.group(3)}); now {fv} + {fp} (sha {fd}). Every \"of which the model "
              f"executes a memory form\" figure is against the older forms.\n"
              f"   Regenerate: demand_census.py --corpus <dir>.")
        return 1
    print(f"demand-census staleness gate: CLEAN — the document was generated "
          f"against this exact model ({n} mnemonics, sha {h}) AND this exact "
          f"mapping (rules {rh}).")
    return 0

CELL_LABEL = {
    "AA": "both routes say HAND-WRITTEN",
    "CC": "both routes say compiler-emitted",
    "AC": "ISA-suffixed name, but the body is not packed SIMD",
    "CA": "packed-SIMD body, but no ISA suffix in the name",
    "U":  "no function symbol covers this address",
    "-":  "this column has no symbol map",
}

def _decide(m, ext, model):
    """⛔⛔ THE ONE PLACE the covered/not-covered decision is made — (roster,
    covered, class) for a single (mnemonic, ISA-bucket) pair.

    ⚠️ IT IS A FUNCTION BECAUSE IT USED NOT TO BE.  `_split`'s docstring has
    claimed since D66 that it is "the one place", and `ext_table` re-implemented
    the same three-conjunct test forty lines below it — a duplicate born in
    agreement, which diverges on the next ordinary edit and would have diverged
    on THIS one, silently leaving the P2 candidate list computed by the old rule
    while the headline moved ([[feedback-duplicate-born-in-agreement]]).  The
    conservation arm in `--selftest` fails if any second implementation appears:
    covered + the ext buckets must equal the column total, exactly."""
    r = to_roster(m, ext, model)
    if r is None:
        return None, False, "unmapped"
    # ⭐ D367: a LOCK-prefixed form is covered when the model DERIVES its mnemonic as lockable (and runs it
    # differentially); the bucket's own ruling stays False, so every other locked form is still refused.
    if ext == LOCK_BUCKET and r in lockable_of(model) and r in model:
        return r, True, "mapped"
    if not form_in_scope(ext):
        # ⭐ D342 (a): a VEX.128 instruction is outside (a)'s scope (the model's VEX forms are not in the
        # published figures), but one whose mnemonic is a VEX-table row or a siliconTable row is credited
        # in that row's OWN labelled class rather than filed as unrepresentable.
        if ext == VEX128 and r in vex_of(model):
            return r, False, "vex"
        # ⭐ D344 (V6): the same class at VEX.256 — credited by mnemonic within the bucket, as VEX.128 is.
        if ext == YMM and r in vex_of(model):
            return r, False, "vex"
        if ext == VEX128 and r in silicon_of(model):
            return r, False, "silicon-vex"
        # ⭐ D345 (V7): a silicon row the model implements at VEX.256 too, in the same labelled class.
        if ext == YMM and r in silicon256_of(model):
            return r, False, "silicon-vex"
        return r, False, "outscope"
    # ⚖️ D337: (b) is NOT covered — it is its own class, counted beside (a)
    if r in silicon_of(model):
        return r, False, "silicon"
    return r, (r in model), "mapped"

def _split(counts, model):
    """(mapped, unmapped, outscope, padding, counts-without-padding), bucketed
    by `_decide` so the whole-column figures and the per-cell figures cannot
    drift apart."""
    mapped = collections.Counter()
    unmapped = collections.Counter()
    outscope = collections.Counter()
    padding = sum(k for key, k in counts.items() if key[1] == "padding")
    rest = {key: k for key, k in counts.items() if key[1] != "padding"}
    for (m, kind, _o, ext), k in rest.items():
        r, _cov, cls = _decide(m, ext, model)
        if cls == "unmapped":
            unmapped[m] += k
        elif cls == "outscope":
            # ⛔ KEYED BY THE MNEMONIC objdump PRINTED, not by the roster name
            # it maps to.  `movq %xmm0, %rax` maps to the roster's `mov`, and
            # writing it `mov (vector operand)` DESTROYS the only word that
            # could be joined against another source: the P2 roster looks these
            # up in K's tree, where the rule is called `movq`, and the folded
            # spelling put 28,019 instructions in "K has no rule for this"
            # while putting `movq` in "K has a rule nobody executes" — the same
            # instructions counted as two opposite residues at once.
            outscope[f"{m} ({kind} operand)"] += k
        else:
            mapped[r] += k
    return mapped, unmapped, outscope, padding, rest

def _covered(counts, model):
    mapped, unmapped, outscope, _pad, rest = _split(counts, model)
    tot = sum(rest.values())
    cov = sum(k for r, k in mapped.items() if r in model)
    return tot, cov

def attribution(name, counts, model, fns, n, n_sym, fh):
    """⛔ PRINTED EVEN WHEN IT IS EMPTY.  A column with no symbol map does not
    silently read as compiler output; it says so, and its cells are `-`."""
    rest = {key: k for key, k in counts.items() if key[1] != "padding"}
    per_cell = collections.Counter()
    per_cell_cov = collections.Counter()
    for (_m, _k, o, _e), k in rest.items():
        per_cell[o] += k
    tot = sum(per_cell.values()) or 1
    fh.write(f"\n#### Hand-written vs compiler-emitted — the confusion matrix\n\n")
    fh.write(f"Symbol maps were found for **{n_sym} of {n}** objects in this column. ")
    if not n_sym:
        fh.write("⛔ **No symbol map: this column is NOT attributed**, and every "
                 "instruction below sits in the `-` cell rather than being "
                 "counted as compiler output.\n\n")
    else:
        fh.write("Rows are the two routes; a cell is a count of INSTRUCTIONS.\n\n")
    fh.write("| cell | what it means | instructions | share | covered by the model |\n")
    fh.write("|---|---|---|---|---|\n")
    for cellk in ("AA", "CA", "AC", "CC", "U", "-"):
        v = per_cell.get(cellk, 0)
        if not v:
            continue
        sub = {key: k for key, k in rest.items() if key[2] == cellk}
        st, sc = _covered(sub, model)
        per_cell_cov[cellk] = sc
        fh.write(f"| `{cellk}` | {CELL_LABEL[cellk]} | {v:,} | "
                 f"{100.0*v/tot:.2f}% | {100.0*sc/st:.1f}% |\n")
    A_name = per_cell.get("AA", 0) + per_cell.get("AC", 0)
    A_body = per_cell.get("AA", 0) + per_cell.get("CA", 0)
    if n_sym:
        fh.write(f"\n- **Hand-written by the NAME route: {A_name:,} "
                 f"({100.0*A_name/tot:.1f}%).** By the BODY route: {A_body:,} "
                 f"({100.0*A_body/tot:.1f}%). The two routes disagree on "
                 f"{per_cell.get('AC',0)+per_cell.get('CA',0):,} instructions "
                 f"({100.0*(per_cell.get('AC',0)+per_cell.get('CA',0))/tot:.1f}%), "
                 f"and that disagreement is the honest width of this split.\n")
        for cellk in ("CA", "AC"):
            top = fns.get(cellk)
            if top:
                names = ", ".join(f"`{nm}`" for nm, _ in top.most_common(6))
                fh.write(f"- The `{cellk}` cell's largest functions: {names}\n")
    return dict(cells={k: v for k, v in per_cell.items()},
                cells_covered={k: v for k, v in per_cell_cov.items()},
                name_route_asm=A_name, body_route_asm=A_body, total=tot)

def ext_table(name, counts, model, fh):
    """⛔ THE UNCOVERED WORK, BUCKETED BY ISA EXTENSION — the number P2 has to
    price.  The vector buckets are read off the operands; only the GPR bucket
    consults a table, and that table's default is PRINTED."""
    mapped, unmapped, outscope, _pad, rest = _split(counts, model)
    tot = sum(rest.values()) or 1
    buckets = collections.Counter()
    covered_buckets = collections.Counter()
    detail, by_mn = {}, {}
    for (m, _kind, _o, ext), k in rest.items():
        # ⛔ THROUGH `_decide`, NOT PAST IT — this loop used to carry its own
        # copy of the three-conjunct test.
        _r, covered, _cls = _decide(m, ext, model)
        if covered:
            # ⭐ RECORDED, NOT DISCARDED.  A bucket that leaves this table
            # because the model GAINED it reads identically to a bucket that was
            # never there — zero occurrences either way — and the tool that
            # prices P2's remaining work cannot tell "delivered" from "no
            # demand" ([[feedback-unobserved-regions-report-agreement]]).
            covered_buckets[ext] += k
            continue
        buckets[ext] += k
        detail.setdefault(ext, collections.Counter())[m] += k
        # ⭐⭐ AND THE SAME RESIDUE KEYED THE OTHER WAY ROUND.  `miss_all` keys a
        # vector residue as `movq (vector operand)`, which ERASES the register
        # file — so the tool that prices P2 sees one number for a mnemonic and
        # cannot tell MMX demand from XMM demand.  It priced `movq` at rank 9 on
        # 11,109 instructions that are **100% `%mm`**, which no XMM or GPR form
        # in K's tree would close.  The mnemonic and the bucket are both facts
        # this loop already has; only the JOIN was lossy.
        # ⛔ D337: KEYED AS `miss_all` KEYS IT — the roster name for a mapped,
        # in-scope instruction (`andnl` -> `andn`), the printed mnemonic
        # otherwise.  Until D337 no mapped instruction was ever uncovered, so the
        # two keyings agreed by accident; the first silicon GPR rows split them
        # and p2_roster's shared-denominator check refused (`rorx`: 398 by
        # mnemonic, 0 by bucket).
        key = _r if (_r is not None and form_in_scope(ext)) else m
        by_mn.setdefault(key, collections.Counter())[ext] += k
    fh.write("\n#### What is NOT covered, bucketed by ISA extension\n\n")
    fh.write("| bucket | occurrences | share of column | the mnemonics in it |\n")
    fh.write("|---|---|---|---|\n")
    for ext, k in buckets.most_common():
        top = ", ".join(f"`{m}`" for m, _ in detail[ext].most_common(6))
        fh.write(f"| {ext} | {k:,} | {100.0*k/tot:.2f}% | {top} |\n")
    return ({e: k for e, k in buckets.items()},
            {e: k for e, k in covered_buckets.items()},
            {m: dict(c) for m, c in by_mn.items()})

def shape_split(mem, model):
    """⭐ STATUS 7c — (differential, silicon, VEX) MEMORY-FORM counts, by the SAME `_split` and the same three set
    tests `report` uses for the credited figures, over the memory-form tally `_classify` kept beside them."""
    mapped, _u, _o, _p, _r = _split(mem, model)
    sil_set, vex_set = silicon_of(model), vex_of(model)
    return (sum(k for r, k in mapped.items() if r in model),
            sum(k for r, k in mapped.items() if r in sil_set),
            sum(k for r, k in mapped.items() if r in vex_set and r not in sil_set))


def _shape(credited, mem_n):
    """The split printed beside a credited figure: register-form, memory-form."""
    return f" (register-form {credited - mem_n:,} · memory-form {mem_n:,})"


# ── ⭐ D352 (STATUS 7d): the MODELLED part of each memory-form figure ─────────
# The model's forms are classified by the SAME `_classify` and keyed by the SAME
# `to_roster`, so demand and model meet under one rule, never a second one.  The
# population is what the model EXECUTES: every differential vector's bytes, and
# the instruction under test in every `hwprobe/*_ops.S` (the line after an
# `AT(...)` label, or after `LOAD` in `sse_ops.S`, the oldest probe).  A form the
# AST can express and no row runs is not counted, so the figure can only
# under-count.  ⚠️ NOT the `_ops.S` files whole: their PRE/POST loads
# (`vmovdqu`, `movq`, …) would read as modelled forms.

def forms_inputs(root_dir):
    """(vector rows [(id, mnemonic, bytes)], probe lines [(file, line)]) — the
    model side's INPUTS, as text.  Pure parsing: runs on any box, so the staleness
    stamp below can be checked where no x86 assembler exists."""
    import glob
    src = open(os.path.join(root_dir, "Tests", "Vectors.lean"), encoding="utf-8").read()
    vecs = []
    for part in re.split(r'\{\s*id := "', src)[1:]:
        rec = part.split('id := "')[0]
        vid = part.split('"', 1)[0]
        mm = re.search(r'mnemonic := "([^"]+)"', rec)
        bb = re.search(r'bytes := "([0-9a-fA-F]+)"', rec)
        if mm and bb:
            vecs.append((vid, mm.group(1), bb.group(1).lower()))
    probes = []
    for f in sorted(glob.glob(os.path.join(root_dir, "hwprobe", "*_ops.S"))):
        lines = open(f, encoding="utf-8").read().split("\n")
        for i, line in enumerate(lines):
            t = line.strip()
            if t.startswith("AT(") or t == "LOAD":
                j = i + 1
                while j < len(lines) and not lines[j].strip():
                    j += 1
                ins = lines[j].split("/*")[0].strip() if j < len(lines) else ""
                probes.append((os.path.basename(f), ins))
    return vecs, probes


def forms_digest(root_dir):
    import hashlib
    vecs, probes = forms_inputs(root_dir)
    blob = "\n".join(f"V\t{v}\t{m}\t{b}" for v, m, b in vecs) + "\n" + \
           "\n".join(f"P\t{f}\t{l}" for f, l in probes)
    return len(vecs), len(probes), hashlib.sha256(blob.encode()).hexdigest()[:16]


# objdump's spellings of a PREFIX in the mnemonic column; a vector whose disassembly is one of these is
# exempted from the mnemonic check, by name, and counted where the run reports
FORMS_PREFIX_SPELLINGS = frozenset({"rep", "repne", "addr32", "data16", "lock"})


def forms_from_lines(lines, model):
    """objdump lines of the model's own forms -> ({(roster, bucket)} with a
    register form, {(roster, bucket)} with a memory form).  `_classify` and
    `to_roster`, nothing else, so a rule change moves both sides at once."""
    mem = collections.Counter()
    c = _classify(lines, None, None, mem)
    reg, msk = set(), set()
    for key, k in c.items():
        m, kind, _o, ext = key
        if kind == "padding":
            continue
        r = to_roster(m, ext, model)
        if r is None:
            continue
        if mem[key] > 0:
            msk.add((r, ext))
        if k - mem[key] > 0:
            reg.add((r, ext))
    return reg, msk


def model_forms(root_dir, model, tmp):
    """Assemble the model's forms into one x86-64 object, disassemble it with the
    census's own objdump command, and classify it.  Returns (reg, mem, note) or
    (None, None, why) — a REFUSAL, never an empty set read as 'nothing modelled'."""
    vecs, probes = forms_inputs(root_dir)
    if not vecs or not probes:
        return None, None, f"the model side parsed EMPTY (vectors {len(vecs)}, probe lines {len(probes)})"
    if any(not l for _f, l in probes):
        return None, None, "a probe label is followed by no instruction"
    asm = [".text"]
    for i, (_v, _m, b) in enumerate(vecs):
        asm.append(f".globl _v{i}\n_v{i}:\n  .byte " + ",".join("0x" + b[k:k+2] for k in range(0, len(b), 2)))
    for i, (_f, l) in enumerate(probes):
        asm.append(f".globl _p{i}\n_p{i}:\n  {l}")
    S, O = os.path.join(tmp, "forms.S"), os.path.join(tmp, "forms.o")
    open(S, "w", encoding="utf-8").write("\n".join(asm) + "\n")
    r = subprocess.run(["clang", "-target", "x86_64-apple-macos11", "-c", S, "-o", O],
                       capture_output=True, text=True)
    if r.returncode != 0:
        return None, None, f"the assembler refused the model's forms (rc {r.returncode}): {r.stderr[:300]}"
    d = subprocess.run(["objdump", "-d", "--no-show-raw-insn", O], capture_output=True, text=True)
    lines = d.stdout.split("\n")
    # one instruction per symbol, or the population is not what it claims to be
    per, cur, bad = collections.Counter(), None, []
    for ln in lines:
        mm = re.match(r'^[0-9a-f]+ <(_[vp]\d+)>:', ln)
        if mm:
            cur = mm.group(1)
        elif cur and re.match(r'^\s+[0-9a-f]+:\s', ln) and ln.split(":", 1)[1].strip() != "lock":
            # a LOCK prefix is printed on its own line; `_classify` attributes it to the next one
            per[cur] += 1
    want = len(vecs) + len(probes)
    bad = [k for k, n in per.items() if n != 1]
    if len(per) != want or bad:
        return None, None, (f"the disassembly does not have one instruction per form: {len(per)} symbols of "
                            f"{want}, {len(bad)} with a count other than 1 (e.g. {bad[:5]})")
    # each vector's declared mnemonic must be what its bytes disassemble to, under `to_roster` — except where
    # objdump prints a PREFIX as the mnemonic (`repe` as `rep`, a 32-bit-address `loop` as `addr32`), which is
    # exempted BY NAME and counted in the note, never silently
    syms, cur = {}, None
    for ln in lines:
        mm = re.match(r'^[0-9a-f]+ <(_[vp]\d+)>:', ln)
        if mm:
            cur = mm.group(1); syms[cur] = []
        elif cur:
            syms[cur].append(ln)
    exempt, wrong = collections.Counter(), []
    for i, (vid, mn, _b) in enumerate(vecs):
        keys = _classify(syms[f"_v{i}"], None, None, collections.Counter())
        if any(to_roster(k[0], k[3], model) == mn for k in keys):
            continue
        objm = {k[0] for k in keys}
        if objm and objm <= FORMS_PREFIX_SPELLINGS:
            exempt[mn] += 1
        else:
            wrong.append((vid, mn, sorted(objm)))
    if wrong:
        return None, None, (f"{len(wrong)} vector(s) whose bytes disassemble to another mnemonic: {wrong[:5]}")
    reg, msk = forms_from_lines(lines, model)
    ex = ", ".join(f"{m} {k}" for m, k in sorted(exempt.items())) or "none"
    return reg, msk, (f"{len(vecs)} vectors + {len(probes)} probe forms; {sum(exempt.values())} vector(s) whose "
                      f"disassembly names a prefix, exempted from the mnemonic check by name ({ex})")


def modelled_mem(mem, model, msk):
    """(differential, silicon, VEX) memory-form demand for which the model EXECUTES
    a memory form at the same (roster name, bucket) — the same keys and the same
    `_decide` classes as `shape_split`, filtered by `msk`."""
    sil_set, vex_set = silicon_of(model), vex_of(model)
    cov = sil = vex = 0
    for (m, kind, _o, ext), k in mem.items():
        if kind == "padding":
            continue
        r, _c, cls = _decide(m, ext, model)
        if cls in ("unmapped", "outscope") or (r, ext) not in msk:
            continue
        if r in sil_set:
            sil += k
        elif r in vex_set:
            vex += k
        elif r in model:
            cov += k
    return cov, sil, vex


def _shape_modelled(credited, mem_n, mod_n):
    return (f" (register-form {credited - mem_n:,} · memory-form {mem_n:,}, of which the model "
            f"executes a memory form for {mod_n:,})")


def report(name, counts, model, fh, fns=None, n=0, n_sym=0, mem=None, msk=None):
    mapped, unmapped, outscope, padding, rest = _split(counts, model)
    counts = rest
    tot = sum(counts.values())
    covered = sum(k for r, k in mapped.items() if r in model)
    # ⚖️ D337: (b) is carved out of "mapped to a name the model does not
    # differentially cover" and printed on its own line — never added to (a)
    sil_set = silicon_of(model)
    silicon = sum(k for r, k in mapped.items() if r in sil_set)
    # ⭐ D342 (a): the VEX table's line, carved out the same way and never added to (a)
    vex_set = vex_of(model)
    vexn = sum(k for r, k in mapped.items() if r in vex_set and r not in sil_set)
    out_of  = sum(k for r, k in mapped.items() if r not in model) - silicon - vexn
    unk     = sum(unmapped.values())
    oos     = sum(outscope.values())
    # ⭐ STATUS 7c: the operand-shape split of each credited figure, or nothing when no tally was kept
    cov_m, sil_m, vex_m = shape_split(mem, model) if mem is not None else (None, None, None)
    # ⭐ D352 (STATUS 7d): the modelled part of each memory-form figure, when the model's forms were read
    cov_x, sil_x, vex_x = modelled_mem(mem, model, msk) if (mem is not None and msk is not None) else (None, None, None)
    _sp = (lambda cred, m: "" if m is None else _shape(cred, m))
    def sp(cred, m, x=None):
        return _sp(cred, m) if (m is None or x is None) else _shape_modelled(cred, m, x)
    fh.write(f"\n### {name}\n\n")
    fh.write(f"- **{tot:,} instructions** over "
             f"{len(set(m for m, _k, _o, _e in counts))} "
             f"distinct objdump mnemonics.\n")
    if padding:
        fh.write(f"- ⛔ **{padding:,} `int3` in runs of two or more were counted as "
                 f"PADDING and excluded** from the line above and from every "
                 f"percentage below. Before this exclusion they were "
                 f"{100.0*padding/(tot+padding):.1f}% of this column.\n")
    fh.write(f"- **Covered by the model (differentially tested mnemonics): "
             f"{covered:,} ({100.0*covered/tot:.1f}%).**{sp(covered, cov_m, cov_x)}\n")
    if sil_set:
        fh.write(f"- ⚙ **Implemented, {SILICON_LABEL}: {silicon:,} "
                 f"({100.0*silicon/tot:.2f}%)**{sp(silicon, sil_m, sil_x)} — counted as NOT covered above, "
                 f"printed beside the differential figure and never summed into it "
                 f"(D337).\n")
    if vex_set:
        fh.write(f"- ⚙ **{VEX_LABEL}: {vexn:,} ({100.0*vexn/tot:.2f}%)**{sp(vexn, vex_m, vex_x)} — VEX.128 and VEX.256 instructions whose "
                 f"mnemonic is a VEX-table row, credited by mnemonic within the bucket (memory forms included, "
                 f"modelled or not: the 'of which' figure is the modelled part, D352); counted as NOT covered above, printed beside it and "
                 f"never summed into it (D342, D344).\n")
    if mem is not None:
        fh.write("- ⚠️ **The shape split beside each credited figure is MEASURED, not modelled** (STATUS 7c): a "
                 "mnemonic is credited within its bucket WHATEVER its operand form, so a memory-form count beside a "
                 "figure is credited whether or not the model has that form. `is_mem_form` = an addressing mode in the "
                 "operands.\n")
    if msk is not None:
        fh.write("- ⭐ **D352 (STATUS 7d): \"of which the model executes a memory form for\" is the MODELLED part** — "
                 "memory-form demand whose (roster name, bucket) the model runs a memory form of, in a differential "
                 "vector or a processor probe, classified by the same `_classify`. One memory form stands for every "
                 "addressing mode at that (name, bucket); a form the AST has and no row runs is not counted, so it "
                 "can only under-count.\n")
    fh.write(f"- Mapped to a roster name the model does not have: {out_of:,} "
             f"({100.0*out_of/tot:.1f}%).\n")
    fh.write(f"- Mapped to a roster name the model HAS, but in a form its state "
             f"cannot represent — an MMX, `%ymm`, `%zmm`, `%k` or x87 register, "
             f"a VEX encoding, or a `lock` prefix on a form the model does not "
             f"list as lockable (`Lockable:` in docs/COVERAGE.md): {oos:,} ({100.0*oos/tot:.2f}%) — "
             f"counted as NOT covered.\n")
    fh.write(f"- Not mapped at all, and therefore counted as NOT covered: "
             f"{unk:,} ({100.0*unk/tot:.1f}%).\n\n")
    fh.write("| rank | mnemonic | occurrences | share | in the model? |\n")
    fh.write("|---|---|---|---|---|\n")
    merged = collections.Counter()
    for r, k in mapped.items():
        merged[r] += k
    for m, k in unmapped.items():
        merged["`" + m + "`  *(unmapped)*"] += k
    for m, k in outscope.items():
        merged[m] += k
    for i, (m, k) in enumerate(merged.most_common(30), 1):
        plain = m.strip("`").split("`")[0]
        # ⛔ D344: an UNMAPPED key names a spelling no roster row took (e.g. `vpaddd` at zmm), so it is never in
        # the model whatever its bare name matches. Until D344 such a row printed "⚙ VEX table only": V5's dav1d
        # table showed `vpaddd` 4,078 (ymm 2,975 + zmm 1,103, all unmapped) under that label.
        yes = ("—" if m.endswith("*(unmapped)*")
               else "✅" if plain in model else "⚙ silicon only" if plain in sil_set
               else "⚙ VEX table only" if plain in vex_set else "—")
        fh.write(f"| {i} | `{plain}` | {k:,} | {100.0*k/tot:.2f}% | {yes} |\n")
    fh.write(f"\n**The ranked list of mnemonics the model does NOT cover** "
             f"(the P2 roster candidates, by demand):\n\n")
    fh.write("| rank | mnemonic | occurrences | share | referee |\n|---|---|---|---|---|\n")
    miss = collections.Counter()
    for r, k in mapped.items():
        if r not in model:
            miss[r] += k
    for m, k in unmapped.items():
        miss[m] += k
    for m, k in outscope.items():
        miss[m] += k
    for i, (m, k) in enumerate(miss.most_common(25), 1):
        ref = ("⚙ silicon (hwprobe), implemented" if m in sil_set
               else "⚙ VEX table (differential, D341), implemented" if m in vex_set else "—")
        fh.write(f"| {i} | `{m}` | {k:,} | {100.0*k/tot:.2f}% | {ref} |\n")
    att = attribution(name, counts, model, fns or {}, n, n_sym, fh)
    ext, ext_covered, miss_by_ext = ext_table(name, counts, model, fh)
    # ⚠️ THE FULL uncovered map rides in the JSON, not just the top 40.  The P2
    # roster is priced by JOINING K's SIMD forms against this demand, and a
    # truncated list would price the tail at zero — which is the direction that
    # makes a roster look cheaper than it is.
    return dict(total=tot, covered=covered, pct=100.0*covered/tot,
                silicon=silicon, silicon_pct=100.0*silicon/tot,
                silicon_all={r: k for r, k in mapped.items() if r in sil_set},
                vex=vexn, vex_pct=100.0*vexn/tot,
                vex_all={r: k for r, k in mapped.items() if r in vex_set and r not in sil_set},
                miss=miss.most_common(40), miss_all=dict(miss),
                attribution=att, ext=ext, ext_covered=ext_covered,
                miss_by_ext=miss_by_ext,
                # ⭐ STATUS 7c: the memory-form part of each credited figure (None when no tally was kept)
                covered_mem=cov_m, silicon_mem=sil_m, vex_mem=vex_m,
                # ⭐ D352 (STATUS 7d): the modelled part of each memory-form figure (None when not read)
                covered_mem_modelled=cov_x, silicon_mem_modelled=sil_x, vex_mem_modelled=vex_x)

def differential_reference(model):
    """The reference model for `check_no_pooling`: every implemented mnemonic
    minus `siliconTable` READ FRESH FROM THE TREE, as a plain set.  ⛔ Never the
    `Model` the report used: a model that pooled would then be its own referee.
    ⭐ D367: it carries the lockable line (read fresh, like the silicon list), because a LOCK credit is class
    (a), differential, and a reference without it would read every credited locked form as pooled silicon."""
    return Model(frozenset(names_of(model)) - silicon_mnemonics(), lockable=lockable_mnemonics())


def check_no_pooling(counts, ref, reported):
    """⚖️ D337 — None when the reported differential figure is the figure a
    model WITHOUT `siliconTable` produces, in total, in every attribution cell
    and in every covered bucket; else the first difference.  The reference model
    is a PLAIN set of the differential mnemonics, so its mapping cannot even name
    a silicon mnemonic: if (a) moved when the silicon rows were loaded,
    something pooled them."""
    # a PLAIN set (no `.names`, no `.silicon`), or a silicon-free `Model` carrying only D367's lockable line
    ref = ref if isinstance(ref, Model) and not silicon_of(ref) else frozenset(ref)
    tot, cov = _covered(counts, ref)
    if cov != reported["covered"] or tot != reported["total"]:
        return (f"covered {reported['covered']:,} of {reported['total']:,} with the "
                f"silicon rows loaded, {cov:,} of {tot:,} without them")
    rest = {key: k for key, k in counts.items() if key[1] != "padding"}
    for cell, got in (reported.get("attribution", {}).get("cells_covered") or {}).items():
        sub = {key: k for key, k in rest.items() if key[2] == cell}
        _t, want = _covered(sub, ref)
        if want != got:
            return f"attribution cell `{cell}`: {got:,} with the silicon rows, {want:,} without"
    for ext, got in (reported.get("ext_covered") or {}).items():
        want = sum(k for (m, _kd, _o, e), k in rest.items()
                   if e == ext and _decide(m, e, ref)[1])
        if want != got:
            return f"bucket `{ext}`: {got:,} covered with the silicon rows, {want:,} without"
    return None


def selftest():
    """⛔ THE MAPPING IS WHERE A CENSUS INFLATES ITSELF, so it is driven on the
    cases that would inflate it."""
    arms = [
        # the trap this tool exists to avoid: a width-changing move must NOT
        # become the string move.
        ("movsbl", "movsx"), ("movswq", "movsx"), ("movzbl", "movzx"),
        ("movzwl", "movzx"), ("movslq", "movsx"),
        # …while the real string move still maps.
        ("movsb", "movs"), ("movsq", "movs"), ("movs", "movs"),
        ("stosq", "stos"), ("scasb", "scas"),
        # families
        ("je", "jcc"), ("jne", "jcc"), ("jg", "jcc"),
        ("sete", "setcc"), ("cmovne", "cmovcc"),
        # ⚠️ `jmp` is NOT a jcc and must not be swallowed by the `j` prefix rule
        ("jmp", "jmp"), ("jmpq", "jmp"),
        # ordinary suffixes
        ("movq", "mov"), ("addl", "add"), ("cmpb", "cmp"), ("shrq", "shr"),
        ("retq", "retq"), ("nopw", "nop"), ("cltq", "cltq"),
        # ⛔ things this tool must REFUSE to claim
        ("vmovdqa", None), ("xorps", None), ("wrmsr", None), ("swapgs", None),
        ("syscall", None), ("cpuid", None), ("iretq", None), ("lock", None),
        ("cmpxchg16b", None), ("endbr64", None),
        # ⚠️ `pxor` USED TO BE ON THAT LIST and is not any more: with no model
        # passed it is still None (the rewrite tables do not name it), and the
        # model-aware arms below are where its answer now lives.  It sat here
        # as a REFUSAL for the twenty-two batches in which the model had it.
        ("pxor", None),
    ]
    bad = []
    for m, want in arms:
        got = to_roster(m)
        ok = got == want
        print(("  ✔ " if ok else "  ⛔ ") + f"{m:12s} -> {got}" +
              ("" if ok else f"   EXPECTED {want}"))
        if not ok:
            bad.append(m)
    # ⭐⭐ THE MODEL-AWARE MAPPING AND THE SCOPE PARTITION (D98).  Every arm above
    # runs `to_roster` with NO model, which is the half that was never wrong.
    _M = model_mnemonics()
    map_arms = [
        # the identity rule: a mnemonic the model names maps to itself
        ("movdqa", None,                 "movdqa"),
        ("pxor",   "SSE-legacy (xmm)",   "pxor"),
        ("punpcklqdq", "SSE-legacy (xmm)", "punpcklqdq"),
        # ⭐ THE ONE COLLISION, RESOLVED BY THE OPERANDS AND NOT BY A GUESS
        ("movq",   "SSE-legacy (xmm)",   "movq"),
        ("movq",   "GPR/other (unclassified)", "mov"),
        ("movd",   "SSE-legacy (xmm)",   "movd"),
        # ⭐ the form P2 batch 3 landed and nothing mapped
        ("movabsq", "mov imm64 / movabs (P2 addition 3)", "mov"),
        # ⛔ a VEX spelling the model does not name is still not a roster name
        ("vpshufd", "VEX-128 (v… xmm)",  None),
        # ⭐ D344 (V6): a VEX-table spelling at ymm maps to itself; a ymm spelling of no VEX-table row does not
        ("vpaddd",  "AVX2/AVX (ymm)",    "vpaddd"),
        ("vpermq",  "AVX2/AVX (ymm)",    None),
        # ⭐ D345 (V7): a silicon row the model implements at VEX.256 maps to itself at ymm; a silicon row that is
        # VEX.128 only (`vaesenc`) maps by name but is NOT the silicon class there (the class arm below)
        ("vshufps", "AVX2/AVX (ymm)",    "vshufps"),
        ("vpmovmskb", "AVX2/AVX (ymm)",  "vpmovmskb"),
        # ⭐ D342 (a): a VEX-128 spelling that IS a VEX-table row maps to itself (and `_decide` files it
        # in the VEX class, never covered); since D344 the same spelling at ymm maps to itself too
        ("vmovdqa", "VEX-128 (v… xmm)",  "vmovdqa"),
        ("vmovdqa", "AVX2/AVX (ymm)",    "vmovdqa"),
        # ⛔ and the rewrite rules still win over the identity rule
        ("movsbl",  None,                "movsx"),
        ("nopw",    None,                "nop"),
    ]
    for m, ext, want in map_arms:
        got = to_roster(m, ext, _M)
        ok = got == want
        print(("  ✔ " if ok else "  ⛔ ") +
              f"map[{ext}] {m:10s} -> {got}" + ("" if ok else f"   EXPECTED {want}"))
        if not ok:
            bad.append("map:" + m)
    # ⛔⛔ THE OVER-CLAIM ARMS.  D98's repair widens what counts as covered, and
    # widening is the direction nobody audits: an under-claim looks like modesty
    # ([[feedback-under-claims-are-unpoliced]]).  Every register file and prefix
    # the model does NOT have gets an arm here, each on a mnemonic the model DOES
    # have — because that is the only shape in which the over-claim can occur.
    scope_arms = [
        ("paddw",   "SSE-legacy (xmm)",                       True),
        ("paddw",   "MMX (mm)",                               False),
        ("paddd",   "AVX2/AVX (ymm)",                         False),
        ("movdqa",  "AVX-512 (zmm/k)",                        False),
        ("movq",    "VEX-128 (v… xmm)",                       False),
        ("fstp",    "x87 (st)",                               False),
        ("vzeroupper", "AVX (state)",                         False),
        # ⭐ the two P2 additions that LANDED and are therefore in scope
        ("movq",    "segment base %fs:/%gs: (P2 addition 1)", True),
        ("movabsq", "mov imm64 / movabs (P2 addition 3)",     True),
        # ⭐ D367: the LOCK bucket's ruling stays False, but a mnemonic the model DERIVES as lockable is
        # credited — and a form `lockable` refuses is still refused, which is the over-claim this arm exists for.
        ("addq",    "LOCK prefix (P2 addition 2)",            True),
        ("movq",    "LOCK prefix (P2 addition 2)",            False),
        ("cmpq",    "LOCK prefix (P2 addition 2)",            False),
        # a form the model does not have is refused by `r in model`, not by the
        # partition — the partition says its FORM is representable.  ⭐ D347 (V8a)
        # MODELLED `endbr64`, so this arm moved to `endbr32` (same bucket, still
        # absent), and `endbr64` now asserts the other direction: landed ⇒ covered.
        ("endbr32", "CET-IBT",                                False),
        ("endbr64", "CET-IBT",                                True),
        ("popcntq", "POPCNT",                                 True),
    ]
    for m, ext, want in scope_arms:
        _r, got, _c = _decide(m, ext, _M)
        ok = got == want
        print(("  ✔ " if ok else "  ⛔ ") +
              f"scope {m:11s} in {ext:38s} -> covered={got}" +
              ("" if ok else f"   EXPECTED {want}"))
        if not ok:
            bad.append("scope:" + m + "/" + ext)
    # ⛔ AND THE PARTITION IS TOTAL: an ISA bucket nobody has ruled on must STOP
    # the census, not fall to either answer.  Driven in-process by catching the
    # exit, because a default here is invisible by construction.
    try:
        form_in_scope("Doubleplus-SIMD (nonexistent)")
        ok = False
    except SystemExit:
        ok = True
    print(("  ✔ " if ok else "  ⛔ ") +
          "an ISA bucket with no scope ruling REFUSES, it does not default")
    bad += [] if ok else ["scope-default"]
    # ⛔ every bucket `isa_bucket` can actually return has a ruling
    for ext in set(GPR_EXT.values()) | {
            "GPR/other (unclassified)", "AVX-512 (zmm/k)", "AVX2/AVX (ymm)",
            "VEX-128 (v… xmm)", "SSE-legacy (xmm)", "MMX (mm)", "x87 (st)",
            "LOCK prefix (P2 addition 2)",
            "segment base %fs:/%gs: (P2 addition 1)",
            "mov imm64 / movabs (P2 addition 3)"}:
        if ext not in EXT_SCOPE:
            print(f"  ⛔ `{ext}` is returnable by isa_bucket and unruled")
            bad.append("unruled:" + ext)
    # ⭐⭐ CONSERVATION: covered + the ext buckets == the column total, EXACTLY.
    # This is what makes a second implementation of the covered/not-covered test
    # observable: `ext_table` carried one for twenty-two batches and agreed with
    # `_split` the whole time, which is precisely why nobody looked at it.
    synth = collections.Counter()
    for key, k in [(("movdqa", "vector", "CC", "SSE-legacy (xmm)"), 100),
                   (("paddw",  "vector", "CC", "MMX (mm)"),          40),
                   (("vpaddd", "vector", "AA", "AVX2/AVX (ymm)"),    25),
                   (("movq",   "segment","CC", "segment base %fs:/%gs: (P2 addition 1)"), 7),
                   (("addq",   "lock",   "CC", "LOCK prefix (P2 addition 2)"), 3),
                   (("int3",   "padding","-",  "-"),                 11),
                   (("movq",   "plain",  "CC", "GPR/other (unclassified)"), 60)]:
        synth[key] += k
    _mp, _um, _os, _pad, _rest = _split(synth, _M)
    c_tot = sum(_rest.values())
    c_cov = sum(k for r, k in _mp.items() if r in _M)
    buckets, cov_buckets, by_ext = ext_table("conservation", synth, _M,
                                             io.StringIO())
    ok = (c_cov + sum(buckets.values()) == c_tot and c_tot == 235
          and c_cov == 170 and sum(cov_buckets.values()) == c_cov
          # ⛔ the per-mnemonic keying is the SAME residue, not a second count
          and sum(sum(v.values()) for v in by_ext.values())
              == sum(buckets.values())
          and by_ext.get("paddw", {}).get("MMX (mm)") == 40)
    print(("  ✔ " if ok else "  ⛔ ") +
          f"conservation: covered {c_cov} + uncovered {sum(buckets.values())} "
          f"== total {c_tot} (padding {_pad} excluded)" +
          ("" if ok else "   EXPECTED 170 + 65 == 235 (D367: the 3 `lock addq` are credited)"))
    bad += [] if ok else ["conservation"]

    # ── ⚖️ D337: the silicon class, the mapping it needed, and NO POOLING ──────
    d337 = 0
    def arm(ok, label, tag):
        print(("  ✔ " if ok else "  ⛔ ") + label)
        if not ok:
            bad.append("d337:" + tag)
    # the l/q-suffixed GPR spellings objdump prints, which nothing used to map
    for m, want in (("andnl", "andn"), ("bzhiq", "bzhi"), ("rorxq", "rorx"),
                    ("blsmskl", "blsmsk"), ("blsrq", "blsr"), ("bextrl", "bextr"),
                    ("pdepq", "pdep"), ("pextl", "pext"), ("mulxq", "mulx"),
                    ("movntiq", "movnti"), ("adcxq", "adcx"), ("adoxl", "adox"),
                    # ⛔ and the vector extract that SHARES a prefix must not follow it
                    ("pextrw", None), ("pextrd", None)):
        got = to_roster(m)
        arm(got == want, f"map {m:8s} -> {got}" + ("" if got == want else f"   EXPECTED {want}"),
            "map:" + m)
        d337 += 1
    # the split is read from the tree, and agrees with primitive_census's reader
    _sil = silicon_mnemonics()
    try:
        import primitive_census as _PC
        _pc = frozenset(_PC.silicon_mnemonics())
    except Exception as e:                     # noqa: BLE001 — an arm, not a crash
        _pc = f"unreadable: {e}"
    arm(_pc == _sil, f"siliconTable read here ({len(_sil)}) == primitive_census's reader", "reader")
    arm({"mulx", "pmaddwd", "andn"} <= _sil and not ({"paddd", "adcx", "mov"} & _sil),
        "siliconTable holds mulx/pmaddwd/andn and no differential row (paddd, adcx, mov)", "content")
    arm(_M.silicon == _sil and not (_M & _sil) and set(_M) | _sil == set(_M.names),
        f"Model: {len(_M)} differential + {len(_sil)} silicon == {len(_M.names)} implemented, disjoint",
        "model-split")
    d337 += 3
    # three classes, one decision each
    for m, ext, want in (("paddd",   "SSE-legacy (xmm)", (True,  "mapped")),
                         ("pmaddwd", "SSE-legacy (xmm)", (False, "silicon")),
                         ("pmaddwd", "MMX (mm)",         (False, "outscope")),
                         ("andnl",   "BMI1",             (False, "silicon")),
                         ("adcxq",   "ADX",              (True,  "mapped")),
                         ("pmulld",  "SSE-legacy (xmm)", (False, "unmapped")),
                         # D342 (a): a VEX-table mnemonic at VEX-128 is its own class; a VEX siliconTable
                         # mnemonic is silicon; a VEX spelling of neither is still out of scope
                         ("vpxor",   "VEX-128 (v… xmm)", (False, "vex")),
                         ("vaesenc", "VEX-128 (v… xmm)", (False, "silicon-vex")),
                         # ⚠️ D345 moved `vmulps` from this arm's "unmapped" example into the silicon class; the
                         # unmapped example is now `vdivps`, which no table names
                         ("vmulps",  "VEX-128 (v… xmm)", (False, "silicon-vex")),
                         ("vdivps",  "VEX-128 (v… xmm)", (False, "unmapped")),
                         # D344: a VEX-table mnemonic at ymm is the same VEX class; a ymm spelling of none is not
                         ("vpxor",   "AVX2/AVX (ymm)",   (False, "vex")),
                         ("vpermq",  "AVX2/AVX (ymm)",   (False, "unmapped")),
                         # D345: a silicon row modelled at VEX.256 is the silicon class at ymm; a VEX.128-only one
                         # stays "a name the model has, in a form it cannot represent"
                         ("vmulps",  "AVX2/AVX (ymm)",   (False, "silicon-vex")),
                         ("vaesenc", "AVX2/AVX (ymm)",   (False, "outscope"))):
        _r, cov, cls = _decide(m, ext, _M)
        arm((cov, cls) == want, f"class {m:8s} in {ext:18s} -> covered={cov} {cls}"
            + ("" if (cov, cls) == want else f"   EXPECTED {want}"), "class:" + m)
        d337 += 1
    # ⭐ STATUS 7c — the operand-shape split, derived from synthetic objdump lines by the one loop and the one rule:
    # two silicon-VEX ymm forms (one register, one memory), three differential `mov`s (register, base+disp, and a
    # `%fs:` address with no parenthesis), and a `lea` (an addressing mode that reads no memory: SHAPE m, by design)
    _lines = ["  1000:\tvpmaddwd\t%ymm1, %ymm2, %ymm0", "  1004:\tvpmaddwd\t0x20(%rbx), %ymm2, %ymm0",
              "  1009:\tmovl\t%ecx, %eax", "  100b:\tmovl\t0x8(%rbx), %eax", "  100e:\tmovq\t%fs:0x28, %rax",
              "  1017:\tleaq\t0x10(%rip), %rax"]
    _mem = collections.Counter()
    _cnt = _classify(_lines, None, None, _mem)
    _cm, _sm, _vm = shape_split(_mem, _M)
    _rep = report("fixture", _cnt, _M, io.StringIO(), {}, 1, 1, _mem)
    arm(all(_mem[k] <= _cnt[k] for k in _mem) and set(_mem) <= set(_cnt),
        "7c: the memory-form tally is a SUB-counter of the main one, key by key", "7c:sub")
    arm(_sm == 1 and _rep["silicon"] == 2 and _rep["silicon_mem"] == 1,
        f"7c: silicon vpmaddwd at ymm credited 2, of which memory-form 1 (got {_rep['silicon']} / {_sm})", "7c:silicon")
    arm(_rep["covered_mem"] == _cm and _cm == 3,
        f"7c: differential memory-form = 3 (0x8(%rbx), %fs:0x28, lea's 0x10(%rip)); got {_cm}", "7c:diff")
    arm(is_mem_form("%fs:0x28, %rax") and not is_mem_form("%ecx, %eax") and is_mem_form("0x10(%rip), %rax"),
        "7c: is_mem_form reads a segment address and a base/disp as memory-form, two registers as not", "7c:rule")
    # red arm: a rule that never sees memory-form must change the reading, or the arms above prove nothing
    _orig = is_mem_form
    try:
        globals()["is_mem_form"] = lambda ops: False
        _mem2 = collections.Counter()
        _classify(_lines, None, None, _mem2)
        arm(shape_split(_mem2, _M) != (_cm, _sm, _vm),
            "7c red arm: a blind is_mem_form changes the split (the arms above can fail)", "7c:red")
    finally:
        globals()["is_mem_form"] = _orig
    d337 += 5          # the five 7c arms above
    # ⭐ D352 (STATUS 7d) — the MODELLED part, from synthetic lines for BOTH sides through the one `_classify`.
    # The model "executes" a register vpmaddwd at ymm, `movl 0x8(%rbx)` and `leaq 0x10(%rip)`: so of the fixture's
    # differential memory-form demand (3: base+disp, %fs:, rip-relative lea) it models 2 — the `%fs:` one is in
    # ANOTHER BUCKET (segment base), and the same mnemonic in another bucket must not count — and of the silicon
    # memory-form demand (1) it models 0, because it has vpmaddwd's REGISTER form only.
    _mlines = ["  2000:\tvpmaddwd\t%ymm1, %ymm2, %ymm0", "  2004:\tmovl\t0x8(%rbx), %eax",
               "  2007:\tleaq\t0x10(%rip), %rax"]
    _freg, _fmem = forms_from_lines(_mlines, _M)
    _x = modelled_mem(_mem, _M, _fmem)
    arm(_x == (2, 0, 0), f"7d: modelled memory-form (diff, silicon, vex) = (2, 0, 0); got {_x}", "7d:modelled")
    arm(any(r == "vpmaddwd" for r, _e in _freg) and not any(r == "vpmaddwd" for r, _e in _fmem),
        "7d: a register-only form is in the register set and NOT the memory set", "7d:sides")
    _buf = io.StringIO()
    _rep2 = report("fixture", _cnt, _M, _buf, {}, 1, 1, _mem, _fmem)
    arm(_rep2["covered_mem_modelled"] == 2 and _rep2["silicon_mem_modelled"] == 0
        and "of which the model executes a memory form for 2)" in _buf.getvalue()
        and _rep["covered_mem_modelled"] is None,
        "7d: report prints the modelled part when forms are given, and None (7c's text) when not", "7d:report")
    # red arms, both directions: no forms models nothing; every demand form modelled equals the memory-form figure
    _all = {(_decide(m, e, _M)[0], e) for (m, _k, _o, e) in _mem}
    arm(modelled_mem(_mem, _M, set()) == (0, 0, 0) and modelled_mem(_mem, _M, _all) == (_cm, _sm, _vm),
        "7d red arms: an empty model reads 0; a model with every demanded form reads the 7c memory-form figure", "7d:red")
    # the staleness half: the stamp hashes the model side's INPUTS, and a planted vector must move it
    import tempfile
    with tempfile.TemporaryDirectory(prefix="x86lean-census-stale-") as _td:
        os.makedirs(os.path.join(_td, "Tests")); os.makedirs(os.path.join(_td, "hwprobe"))
        _vf = os.path.join(_td, "Tests", "Vectors.lean")
        open(_vf, "w", encoding="utf-8").write('[ { id := "a", mnemonic := "mov", asm := "movl %ecx, %eax", bytes := "89c8" }\n')
        open(os.path.join(_td, "hwprobe", "x_ops.S"), "w", encoding="utf-8").write(
            "FN(x)\n  PRE\nAT(x_at)\n  vpxor (%rbx), %xmm1, %xmm3\n  POST\nSYM(p):\n  LOAD\n  mulsd %xmm1, %xmm0 /* f2 */\n")
        _d1 = forms_digest(_td)
        _vi, _pi = forms_inputs(_td)
        open(_vf, "a", encoding="utf-8").write(', { id := "b", mnemonic := "mov", asm := "movl 0x8(%rbx), %eax", bytes := "8b4308" }\n')
        _d2 = forms_digest(_td)
    arm(_d1[:2] == (1, 2) and _d2[:2] == (2, 2) and _d1[2] != _d2[2]
        and [l for _f, l in _pi] == ["vpxor (%rbx), %xmm1, %xmm3", "mulsd %xmm1, %xmm0"],
        f"7d: the forms stamp reads both probe conventions (AT, LOAD) and moves on a planted vector ({_d1} -> {_d2})",
        "7d:stamp")
    arm({"rep", "addr32", "lock"} <= FORMS_PREFIX_SPELLINGS and "mov" not in FORMS_PREFIX_SPELLINGS,
        "7d: the prefix exemption names prefixes only", "7d:prefix")
    d337 += 6          # the six 7d arms above
    # ⛔⛔ THE NO-POOLING ARM, with its plants.  One fixture: 50 differential, 30 +
    # 5 silicon-refereed, 4 out of scope, 2 unmapped.
    fx = collections.Counter({("paddd",   "vector", "CC", "SSE-legacy (xmm)"): 50,
                              ("pmaddwd", "vector", "AA", "SSE-legacy (xmm)"): 30,
                              ("andnl",   "plain",  "CC", "BMI1"):             5,
                              ("paddw",   "vector", "AA", "MMX (mm)"):         4,
                              ("pmulld",  "vector", "AA", "SSE-legacy (xmm)"): 2})
    ref = differential_reference(_M)
    with contextlib.redirect_stdout(io.StringIO()):
        honest = report("fixture", fx, _M, io.StringIO(), {}, 1, 1)
        # PLANT 1: a classifier that POOLS — a model whose covered set includes
        # the silicon rows (the census as it stood from D335 to D337)
        pooled = report("fixture", fx, Model(_M.names, ()), io.StringIO(), {}, 1, 1)
    why_h = check_no_pooling(fx, ref, honest)
    arm(why_h is None and honest["covered"] == 50 and honest["silicon"] == 35
        and honest["total"] == 91 and sum(honest["miss_all"].values()) == 41,
        f"honest: covered 50, silicon 35 beside it, not-covered 41 of 91 — no-pooling passes ({why_h})",
        "honest")
    why_p = check_no_pooling(fx, ref, pooled)
    arm(why_p is not None and pooled["covered"] == 85,
        f"PLANT pooling classifier (covered {pooled['covered']}) is REFUSED: {why_p}", "plant-pool")
    # the two keyings of the residue agree (p2_roster joins them on a shared denominator)
    _strip = collections.Counter()
    for _k, _v in honest["miss_all"].items():
        _strip[re.sub(r" \((vector|segment|lock) operand\)$", "", _k)] += _v
    _byx = {_k: sum(_v.values()) for _k, _v in honest["miss_by_ext"].items()}
    arm(dict(_strip) == _byx and _byx.get("andn") == 5,
        f"miss_all and miss_by_ext key the residue alike (andnl -> andn): {_byx}", "keying")
    d337 += 1
    # PLANT 2: the honest classification, with (b) SUMMED into the headline
    summed = dict(honest, covered=honest["covered"] + honest["silicon"])
    why_s = check_no_pooling(fx, ref, summed)
    arm(why_s is not None, f"PLANT (a)+(b) summed into one figure is REFUSED: {why_s}", "plant-sum")
    # PLANT 3: a reference that is the pooled model's own set must NOT be what
    # `differential_reference` returns — it reads siliconTable from the tree
    arm(not (differential_reference(Model(_M.names, ())) & _sil),
        "the reference reads siliconTable from the tree, never the model under test", "plant-ref")
    # and the stamp sees a mnemonic move between (a) and (b) with the set unchanged
    _sa, _sb = model_stamp(_M), model_stamp(Model(_M.names, ()))
    arm(_sa[0] == _sb[0] and _sa[1] != _sb[1],
        "the stamp's model half moves when the silicon split moves and the implemented set does not",
        "stamp-split")
    d337 += 5
    # ⭐ THE STAMP'S SECOND HALF MOVES WHEN THE MAPPING DOES AND THE MODEL DOES NOT
    _n0, _h0, _r0 = model_stamp(_M)
    _saved = EXT_SCOPE["MMX (mm)"]
    EXT_SCOPE["MMX (mm)"] = True
    _n1, _h1, _r1 = model_stamp(_M)
    EXT_SCOPE["MMX (mm)"] = _saved
    _n2, _h2, _r2 = model_stamp(_M)
    ok = (_h0 == _h1) and (_r0 != _r1) and (_r0 == _r2)
    print(("  ✔ " if ok else "  ⛔ ") +
          "the stamp's `rules` half moves when the MAPPING moves and the model "
          "does not — the exact blindness D98 was" +
          ("" if ok else f"   model {_h0}/{_h1}  rules {_r0}/{_r1}/{_r2}"))
    bad += [] if ok else ["stamp-rules-half"]
    # ⛔ D344: the `rules` half must see a rule that moves a VEX-table mnemonic. Its domain once held none, so the
    # VEX.256 rule left the stamp byte-identical. The arm asks the precondition directly (every VEX-table mnemonic is
    # in the domain); `census_redprobe.py` drives the mutation that removes them and sees this arm fail.
    ok = bool(vex_of(_M)) and vex_of(_M) <= _rule_domain(_M)
    print(("  ✔ " if ok else "  ⛔ ") + "every VEX-table mnemonic is in the stamp's rule domain (D344)")
    bad += [] if ok else ["stamp-vex-domain"]

    # ── the LINE-LEVEL rules, each driven on the shape that moved the number ──
    def L(*rows):
        return [f"  ffffffff81000{i:03x}:      \t{r}" for i, r in enumerate(rows)]
    line_arms = [
        ("a run of int3 is PADDING, not code",
         L("int3", "int3", "int3", "movq %rax, %rbx"),
         {("int3", "padding"): 3, ("movq", "plain"): 1}),
        ("a LONE int3 is a real breakpoint and is counted",
         L("movq %rax, %rbx", "int3", "movq %rax, %rbx"),
         {("int3", "plain"): 1, ("movq", "plain"): 2}),
        ("a lock line marks the NEXT instruction and is not itself counted",
         L("lock", "incl 0x34(%rcx)"),
         {("incl", "lock"): 1}),
        ("%gs: is a real override",
         L("movq %gs:0x28, %rax"), {("movq", "segment"): 1}),
        ("%cs: on a multi-byte nop is NOT",
         L("nopw %cs:0x0(%rax,%rax,1)"), {("nopw", "plain"): 1}),
        ("%es: on a string op is NOT",
         L("rep stos %al, %es:(%rdi)"), {("rep", "plain"): 1}),
        ("a vector register is out of scope",
         L("movq %xmm0, %rax"), {("movq", "vector"): 1}),
    ]
    for name, lines, want in line_arms:
        got = dict(classify_lines(lines))
        ok = got == want
        print(("  ✔ " if ok else "  ⛔ ") + name +
              ("" if ok else f"\n      got {got}\n      want {want}"))
        if not ok:
            bad.append(name)

    # ══ THE ASSEMBLY COLUMN CLASS, every rule driven in BOTH directions ══
    # ⛔ THE ARM THAT WOULD HAVE CAUGHT THE MMX OVER-CLAIM.  Before `%mm[0-7]`
    # entered VECTOR_RE this line classified as `plain` and `movq` -> `mov`
    # counted as COVERED.
    mmx_arms = [
        ("an MMX register is out of scope, like any other vector register",
         L("movq %mm0, %mm3"), {("movq", "vector"): 1}),
        ("...and a GPR `movq` beside it is still plain",
         L("movq %rax, %rbx"), {("movq", "plain"): 1}),
    ]
    for name, lines, want in mmx_arms:
        got = dict(classify_lines(lines))
        ok = got == want
        print(("  ✔ " if ok else "  ⛔ ") + name +
              ("" if ok else f"\n      got {got}\n      want {want}"))
        if not ok:
            bad.append(name)

    name_arms = [
        ("dav1d_ipred_dc_8bpc_avx2", "A"), ("dav1d_inv_txfm_add_16x4_avx512icl", "A"),
        ("ff_h264_idct_add_8_ssse3", "A"), ("x264_pixel_sad_16x16_mmxext", "A"),
        ("__memcpy_avx_unaligned_erms", "A"), ("vpx_sad16x16_sse2", "A"),
        # ...and the C side, including a name that merely CONTAINS a token
        ("cdef_find_dir_c", "C"), ("generate_grain_y_c", "C"),
        ("blessed_helper", "C"), ("assert_failed", "C"), ("process_stream", "C"),
    ]
    for nm, want in name_arms:
        got = name_route(nm)
        ok = got == want
        print(("  ✔ " if ok else "  ⛔ ") + f"name route {nm:36s} -> {got}" +
              ("" if ok else f"   EXPECTED {want}"))
        if not ok:
            bad.append("name:" + nm)

    packed_arms = [
        # ⛔ scalar floating point in a vector register is NOT packed SIMD, and
        # calling it packed would make every math-heavy C function read as asm.
        (("addsd", "%xmm1, %xmm0"), False), (("mulss", "%xmm1, %xmm0"), False),
        (("cvtsi2sd", "%rax, %xmm0"), False), (("movsd", "%xmm1, %xmm0"), False),
        (("movq", "%xmm0, %rax"), False), (("movd", "%eax, %xmm0"), False),
        (("movq", "%rax, %rbx"), False),
        # ...and the packed forms, at each width
        (("paddw", "%xmm1, %xmm0"), True), (("pshufb", "%xmm1, %xmm0"), True),
        (("vpaddd", "%ymm2, %ymm1, %ymm0"), True),
        (("vpmulhrsw", "%zmm2, %zmm1, %zmm0"), True),
        (("movq", "%mm0, %mm3"), True), (("movaps", "%xmm1, %xmm0"), True),
        # ⭐ D260: every SUFFIXED scalar conversion is scalar too — `(ss|sd)$` saw
        # only the bare `cvtsi2sd`, which is the one spelling the arm above tests
        (("cvtsi2sdl", "(%rbx), %xmm0"), False), (("cvtsi2ssq", "0x8(%rsp), %xmm1"), False),
        (("cvttsd2si", "%xmm0, %eax"), False), (("cvttss2si", "%xmm1, %rax"), False),
        (("cvtsd2si", "%xmm0, %eax"), False), (("cvtss2si", "%xmm0, %rax"), False),
        (("vcvttsd2si", "%xmm0, %eax"), False),
        (("vcvtsi2sdl", "(%rbx), %xmm1, %xmm0"), False),
        # ...and a PACKED conversion is still packed: the rule is by meaning
        (("cvtdq2ps", "%xmm1, %xmm0"), True), (("cvttps2dq", "%xmm1, %xmm0"), True),
        (("cvtpi2ps", "%mm0, %xmm0"), True), (("vcvtps2pd", "%xmm1, %ymm0"), True),
    ]
    for (mn, ops), want in packed_arms:
        got = is_packed(mn, ops)
        ok = got == want
        print(("  ✔ " if ok else "  ⛔ ") + f"packed? {mn:10s} {ops:24s} -> {got}" +
              ("" if ok else f"   EXPECTED {want}"))
        if not ok:
            bad.append("packed:" + mn + ops)

    body_arms = [((4, 4), "C"), ((7, 7), "C"), ((8, 8), "A"),
                 ((100, 60), "A"), ((100, 50), "A"), ((100, 49), "C"),
                 ((100, 0), "C")]
    for (n_i, n_p), want in body_arms:
        got = body_route(n_i, n_p)
        ok = got == want
        print(("  ✔ " if ok else "  ⛔ ") +
              f"body route {n_p}/{n_i} packed -> {got}" +
              ("" if ok else f"   EXPECTED {want}"))
        if not ok:
            bad.append(f"body:{n_p}/{n_i}")

    ext_arms = [
        (("vpaddd", "%zmm2, %zmm1, %zmm0"), "AVX-512 (zmm/k)"),
        (("vpcmpeqb", "%zmm1, %zmm0, %k1"), "AVX-512 (zmm/k)"),
        (("vpaddd", "%ymm2, %ymm1, %ymm0"), "AVX2/AVX (ymm)"),
        (("vpaddd", "%xmm2, %xmm1, %xmm0"), "VEX-128 (v… xmm)"),
        (("paddd", "%xmm1, %xmm0"), "SSE-legacy (xmm)"),
        (("paddd", "%mm1, %mm0"), "MMX (mm)"),
        # ⛔ D259 FLIPPED THIS ARM ON PURPOSE.  Until then it expected
        # "GPR/other": an x87 load from memory names no `%st`, and the arm pinned
        # the operand rule's blind spot as the right answer.
        (("fldt", "0x10(%rsp)"), "x87 (st)"),
        (("fstp", "%st(1)"), "x87 (st)"),
        # ⭐ D259: the register file is in the MNEMONIC when the operands name none
        (("emms", ""), "MMX (mm)"),
        (("fnstsw", "%ax"), "x87 (st)"),
        (("wait", ""), "x87 (st)"),
        (("fld1", ""), "x87 (st)"),
        (("fcos", ""), "x87 (st)"),
        (("fildll", "0x8(%rsp)"), "x87 (st)"),
        (("fstpl", "-0x8(%rbp)"), "x87 (st)"),
        (("cvttsd2si", "(%rbx),%eax"), "SSE-legacy (xmm)"),
        (("cvttss2si", "0x10(%rsp),%rax"), "SSE-legacy (xmm)"),
        (("cvtss2si", "(%rbx),%eax"), "SSE-legacy (xmm)"),
        (("vcvttsd2si", "(%rbx),%eax"), "VEX-128 (v… xmm)"),
        # ...and the controls: the operand rule still decides where it can, and a
        # name that merely LOOKS like the families is not captured by them
        (("cvttsd2si", "%xmm0,%eax"), "SSE-legacy (xmm)"),
        (("cvtsi2sdl", "(%rbx),%xmm0"), "SSE-legacy (xmm)"),
        (("fldl2e", ""), "x87 (st)"),
        (("ldmxcsr", "0x4(%rsp)"), "SSE (MXCSR state)"),
        (("vstmxcsr", "(%rax)"), "SSE (MXCSR state)"),
        (("fxsave", "(%rax)"), "GPR/other (unclassified)"),
        (("frobnicates", "(%rax)"), "GPR/other (unclassified)"),
        (("fstpq", "(%rax)"), "GPR/other (unclassified)"),
        (("addl", "(%rbx),%eax"), "GPR/other (unclassified)"),
        (("popcntq", "%rax, %rbx"), "POPCNT"),
        (("endbr64", ""), "CET-IBT"),
        (("shlx", "%rax, %rbx, %rcx"), "BMI2"),
        (("vzeroupper", ""), "AVX (state)"),
        # ⛔ the DEFAULT is a named, printed bucket — never a silent "other"
        (("frobnicate", "%rax"), "GPR/other (unclassified)"),
    ]
    for (mn, ops), want in ext_arms:
        got = isa_bucket(mn, ops)
        ok = got == want
        print(("  ✔ " if ok else "  ⛔ ") + f"bucket {mn:12s} -> {got}" +
              ("" if ok else f"   EXPECTED {want}"))
        if not ok:
            bad.append("ext:" + mn)
    # ⛔ THE THREE P2 ADDITIONS ARE NAMED ROWS, NOT "GPR/other".  A `mov` the
    # model has, refused for its PREFIX, must not be priced as a vector gap.
    prefix_arms = [
        (("movq", "%gs:0x28, %rax", "segment"),
         "segment base %fs:/%gs: (P2 addition 1)"),
        (("incl", "0x34(%rcx)", "lock"), "LOCK prefix (P2 addition 2)"),
        (("movabsq", "$0x123456789, %rax", "plain"),
         "mov imm64 / movabs (P2 addition 3)"),
        # ...and a plain instruction is unaffected by the new rows
        (("paddd", "%xmm1, %xmm0", "plain"), "SSE-legacy (xmm)"),
        (("movq", "%rax, %rbx", "plain"), "GPR/other (unclassified)"),
    ]
    for (mn, ops, kind), want in prefix_arms:
        got = isa_bucket(mn, ops, kind)
        ok = got == want
        print(("  ✔ " if ok else "  ⛔ ") + f"bucket[{kind}] {mn:10s} -> {got}" +
              ("" if ok else f"   EXPECTED {want}"))
        if not ok:
            bad.append("pfx:" + mn)

    # ── attribution by ADDRESS, with the unattributed gap printed as `U` ──
    def LA(base, *rows):
        return [f"  {base+i*4:016x}:      \t{r}" for i, r in enumerate(rows)]
    syms = [(0x1000, 0x1020, "ff_idct_add_avx2"),
            (0x2000, 0x2020, "decode_frame_c")]
    lines = (LA(0x1000, *["vpaddd %ymm1, %ymm2, %ymm0"] * 8) +
             LA(0x2000, *["movq %rax, %rbx"] * 8) +
             LA(0x3000, "movq %rax, %rbx"))
    got = collections.Counter()
    for (mn, kind, o, ext), k in _classify(lines, syms).items():
        got[o] += k
    want = {"AA": 8, "CC": 8, "U": 1}
    ok = dict(got) == want
    print(("  ✔ " if ok else "  ⛔ ") +
          "attribution by address: AA / CC / and an address no symbol covers is `U`" +
          ("" if ok else f"\n      got {dict(got)}\n      want {want}"))
    bad += [] if ok else ["attr-cells"]
    # ...and with NO symbol map every instruction sits in `-`, never in `CC`
    got2 = collections.Counter()
    for (mn, kind, o, ext), k in _classify(lines, None).items():
        got2[o] += k
    ok = dict(got2) == {"-": 17}
    print(("  ✔ " if ok else "  ⛔ ") +
          "no symbol map => every instruction is `-`, NOT counted as compiler output" +
          ("" if ok else f"\n      got {dict(got2)}"))
    bad += [] if ok else ["attr-nosym"]
    # ...and the two disagreement cells are reachable, not decorative
    syms2 = [(0x1000, 0x1020, "ff_idct_add_avx2"), (0x2000, 0x2020, "dav1d_msac_decode")]
    lines2 = (LA(0x1000, *["movq %rax, %rbx"] * 8) +
              LA(0x2000, *["vpaddd %ymm1, %ymm2, %ymm0"] * 8))
    got3 = collections.Counter()
    for (mn, kind, o, ext), k in _classify(lines2, syms2).items():
        got3[o] += k
    ok = dict(got3) == {"AC": 8, "CA": 8}
    print(("  ✔ " if ok else "  ⛔ ") +
          "both DISAGREEMENT cells are reachable (AC: suffixed name, scalar body; "
          "CA: packed body, unsuffixed name)" +
          ("" if ok else f"\n      got {dict(got3)}"))
    bad += [] if ok else ["attr-disagree"]

    # ── D257: the WIDTH key, on every source shape, in both directions ──
    width_arms = [
        (("cvtsi2sd", "%eax,%xmm0"), "cvtsi2sdl"), (("cvtsi2sd", "%r8d, %xmm0"), "cvtsi2sdl"),
        (("cvtsi2sd", "%rax,%xmm0"), "cvtsi2sdq"), (("cvtsi2sd", "%r15,%xmm0"), "cvtsi2sdq"),
        (("cvtsi2ss", "%esp,%xmm1"), "cvtsi2ssl"), (("cvtsi2ss", "%rsp,%xmm1"), "cvtsi2ssq"),
        # the memory forms arrive suffixed and pass through untouched
        (("cvtsi2sdl", "(%rbx),%xmm0"), "cvtsi2sdl"),
        (("cvtsi2ssq", "0x8(%rsp,%rcx,4),%xmm0"), "cvtsi2ssq"),
        # ⛔ FAILS CLOSED: a source it does not recognise keeps the bare name
        (("cvtsi2sd", "(%rbx),%xmm0"), "cvtsi2sd"), (("cvtsi2sd", "%ax,%xmm0"), "cvtsi2sd"),
        (("cvtsi2sd", "%r1,%xmm0"), "cvtsi2sd"), (("cvtsi2sd", "%r16,%xmm0"), "cvtsi2sd"),
        # ⛔ and nothing else is renamed — not even the VEX spelling of the same family
        (("vcvtsi2sd", "%eax,%xmm1,%xmm0"), "vcvtsi2sd"), (("movq", "%rax,%rbx"), "movq"),
    ]
    for (mn, ops), want in width_arms:
        got = width_key(mn, ops)
        ok = got == want
        print(("  ✔ " if ok else "  ⛔ ") + f"width key {mn:10s} {ops:26s} -> {got}" +
              ("" if ok else f"   EXPECTED {want}"))
        if not ok:
            bad.append("width:" + mn + ops)
    # ...the key moves and the ORIGIN does not: eight int32 conversions are a scalar
    # body.  Renamed BEFORE `is_packed`, `cvtsi2sdl` fails `SCALAR_FP` and the body
    # would route `A` — this arm is the plant for that ordering.
    lines3 = LA(0x2000, *["cvtsi2sd %eax,%xmm0"] * 6, *["cvtsi2sd %rax,%xmm0"] * 2)
    got4 = collections.Counter()
    for (mn, kind, o, ext), k in _classify(lines3, [(0x2000, 0x2020, "decode_frame_c")]).items():
        got4[(mn, o)] += k
    want4 = {("cvtsi2sdl", "CC"): 6, ("cvtsi2sdq", "CC"): 2}
    ok = dict(got4) == want4
    print(("  ✔ " if ok else "  ⛔ ") +
          "a register-source conversion is keyed by WIDTH and its body still routes CC" +
          ("" if ok else f"\n      got {dict(got4)}\n      want {want4}"))
    bad += [] if ok else ["width-origin"]
    # ⭐ D260: a body of scalar float→int truncations and suffixed int→float
    # conversions is SCALAR code, and routes CC
    lines5 = LA(0x3000, *["cvttsd2si %xmm0,%eax"] * 6, *["cvtsi2sdl (%rbx),%xmm0"] * 2)
    got5 = collections.Counter()
    for (mn, kind, o, ext), k in _classify(lines5, [(0x3000, 0x3020, "scale_frame_c")]).items():
        got5[(mn, o)] += k
    want5 = {("cvttsd2si", "CC"): 6, ("cvtsi2sdl", "CC"): 2}
    ok = dict(got5) == want5
    print(("  ✔ " if ok else "  ⛔ ") +
          "a body of suffixed scalar conversions routes CC, not packed-SIMD A" +
          ("" if ok else f"\n      got {dict(got5)}\n      want {want5}"))
    bad += [] if ok else ["scalar-conv-origin"]
    # ...and the stamp SEES the rule: an identity key must move the `rules` half
    _saved_wk = globals()["width_key"]
    globals()["width_key"] = lambda mn, ops: mn
    try:
        _n3, _h3, _r3 = model_stamp(_M)
    finally:
        globals()["width_key"] = _saved_wk
    _n4, _h4, _r4 = model_stamp(_M)
    ok = (_h3 == _h0) and (_r3 != _r0) and (_r4 == _r0)
    print(("  ✔ " if ok else "  ⛔ ") +
          "the stamp's `rules` half moves when the WIDTH KEY moves (D257: a rename "
          "before `_decide` is part of the mapping)" +
          ("" if ok else f"   rules {_r0}/{_r3}/{_r4}"))
    bad += [] if ok else ["stamp-width-key"]
    # ...and it SEES THE BUCKET RULE (D259): `isa_bucket` runs before `_decide`
    # too, and an unhashed bucket change leaves a census reading as fresh.
    _saved_ib = globals()["isa_bucket"]
    globals()["isa_bucket"] = lambda mn, ops, kind="plain": (
        "GPR/other (unclassified)" if mn == "emms" else _saved_ib(mn, ops, kind))
    try:
        _n5, _h5, _r5 = model_stamp(_M)
    finally:
        globals()["isa_bucket"] = _saved_ib
    _n6, _h6, _r6 = model_stamp(_M)
    ok = (_h5 == _h0) and (_r5 != _r0) and (_r6 == _r0)
    print(("  ✔ " if ok else "  ⛔ ") +
          "the stamp's `rules` half moves when ONE BUCKET moves (D259: `isa_bucket` "
          "is part of the mapping)" +
          ("" if ok else f"   rules {_r0}/{_r5}/{_r6}"))
    bad += [] if ok else ["stamp-bucket"]
    # ...and it SEES THE PACKED RULE (D260), which decides every origin cell
    _saved_ip = globals()["is_packed"]
    globals()["is_packed"] = lambda mn, ops: (
        True if mn == "cvttsd2si" else _saved_ip(mn, ops))
    try:
        _n7, _h7, _r7 = model_stamp(_M)
    finally:
        globals()["is_packed"] = _saved_ip
    _n8, _h8, _r8 = model_stamp(_M)
    ok = (_h7 == _h0) and (_r7 != _r0) and (_r8 == _r0)
    print(("  ✔ " if ok else "  ⛔ ") +
          "the stamp's `rules` half moves when ONE PACKED VERDICT moves (D260: the "
          "origin split is in the same document)" +
          ("" if ok else f"   rules {_r0}/{_r7}/{_r8}"))
    bad += [] if ok else ["stamp-packed"]

    # ── the `objdump -t` line shapes this tool must parse ──
    sym_arms = [
        ("000000000011f2c0 l     F .text\t0000000000000417 cdef_find_dir_c",
         (0x11f2c0, 0x417, "cdef_find_dir_c")),
        # ⚠️ a nasm symbol has SIZE 0 — this is the shape the split depends on
        ("0000000000064fa0 l     F .text\t0000000000000000 dav1d_generate_grain_y_8bpc_avx2",
         (0x64fa0, 0, "dav1d_generate_grain_y_8bpc_avx2")),
        ("0000000000028000 g     F .text\t00000000000000a0 memcpy@@GLIBC_2.14",
         (0x28000, 0xa0, "memcpy@@GLIBC_2.14")),
    ]
    for line, want in sym_arms:
        m = SYMTAB_RE.match(line)
        got = (int(m.group(1), 16), int(m.group(2), 16), m.group(3)) if m else None
        ok = got == want
        print(("  ✔ " if ok else "  ⛔ ") + f"symtab line -> {got}" +
              ("" if ok else f"   EXPECTED {want}"))
        if not ok:
            bad.append("symtab")
    # a NON-function line must not be read as a symbol
    ok = SYMTAB_RE.match("0000000000200000 l    d  .data\t0000000000000000 .data") is None
    print(("  ✔ " if ok else "  ⛔ ") + "a section/data line is NOT read as a function symbol")
    bad += [] if ok else ["symtab-neg"]

    # ── a symlink is not a second binary ──
    import tempfile
    with tempfile.TemporaryDirectory(prefix="x86lean-census-") as td:
        real = os.path.join(td, "libx.so.1.2.3")
        open(real, "wb").write(b"\x7fELF\x02\x01\x01\x00" + b"\x00" * 8 +
                               b"\x03\x00\x3e\x00" + b"\x00" * 40)
        os.symlink(real, os.path.join(td, "libx.so.1"))
        paths = [os.path.join(td, f) for f in os.listdir(td)]
        got = elf_targets(paths)
        ok = got == [real]
        print(("  ✔ " if ok else "  ⛔ ") +
              "a shipped symlink (libx.so.1 -> libx.so.1.2.3) is ONE binary, not two" +
              ("" if ok else f"\n      got {got}"))
        bad += [] if ok else ["symlink"]

    # and the model set must be non-empty and must contain a form we know it has
    model = model_mnemonics()
    for must in ("mov", "add", "cmpxchg8b"):
        ok = must in model
        print(("  ✔ " if ok else "  ⛔ ") + f"model set contains `{must}`")
        if not ok:
            bad.append("model:" + must)
    # ── the staleness stamp, driven BOTH ways ───────────────────────────────
    import shutil, tempfile
    doc = os.path.join(root, "docs", "DEMAND-CENSUS.md")
    if os.path.exists(doc):
        saved = open(doc, encoding="utf-8").read()
        try:
            ok = check_stale("docs/DEMAND-CENSUS.md") == 0
            print(("  ✔ " if ok else "  ⛔ ") +
                  "the SHIPPED census matches the model it was generated against")
            bad += [] if ok else ["stamp-control"]
            # ⛔ THE PLANT IS DERIVED FROM THE SHIPPED STAMP, NEVER WRITTEN AS A
            # LITERAL.  It was a literal until D98, in the old two-field format;
            # when the stamp grew a third field the plant stopped matching
            # `STAMP_RE`, the substitution wrote nothing, and the arm that
            # proves this gate can go red was itself testing a document with no
            # stamp at all — the anti-staleness gate carrying a stale literal in
            # its own selftest ([[feedback-a-gate-is-not-exempt-from-its-own-defect]]).
            m0 = STAMP_RE.search(saved)
            def _flip(h):
                return h[:-1] + ("0" if h[-1] != "0" else "1")
            def _plant(n=None, sha=None, rules=None):
                return STAMP_RE.sub(
                    f"<!-- census-model: mnemonics={n or m0.group(1)} "
                    f"sha={sha or m0.group(2)} "
                    f"rules={rules or m0.group(3)} -->", saved)
            ok = m0 is not None
            print(("  ✔ " if ok else "  ⛔ ") +
                  "the shipped stamp PARSES, so the plants below are real edits")
            bad += [] if ok else ["stamp-parse"]
            if ok:
                for label, text, want_half in (
                        ("a census generated against a DIFFERENT MODEL is "
                         "reported STALE",
                         _plant(sha=_flip(m0.group(2))), "the MODEL has moved"),
                        # ⭐⭐ D98 ITSELF, AS AN ARM: the model is byte-identical
                        # and the MAPPING has moved.  This is the case the old
                        # stamp could not see, and seeing it is the whole repair.
                        ("a census generated against a DIFFERENT MAPPING is "
                         "reported STALE, with the model unchanged",
                         _plant(rules=_flip(m0.group(3))),
                         "the MAPPING has moved (the model is unchanged)")):
                    open(doc, "w", encoding="utf-8").write(text)
                    buf = io.StringIO()
                    with contextlib.redirect_stdout(buf):
                        r = check_stale("docs/DEMAND-CENSUS.md")
                    said = want_half in buf.getvalue()
                    good = (r == 1) and said
                    print(("  ✔ " if good else "  ⛔ ") + label +
                          ("" if good else f"   rc={r} names-the-half={said}"))
                    bad += [] if good else ["stamp-stale"]
            # and no stamp at all must refuse, not pass
            open(doc, "w", encoding="utf-8").write(STAMP_RE.sub("", saved))
            r = check_stale("docs/DEMAND-CENSUS.md")
            print(("  ✔ " if r == 2 else "  ⛔ ") +
                  "a census with NO stamp is refused, not read as fresh")
            bad += [] if r == 2 else ["stamp-missing"]
        finally:
            open(doc, "w", encoding="utf-8").write(saved)
        ok = open(doc, encoding="utf-8").read() == saved
        print(("  ✔ " if ok else "  ⛔ ") + "the document is byte-restored")
        bad += [] if ok else ["stamp-restore"]
    if bad:
        print(f"demand-census selftest: FAIL ({len(bad)} arms)")
        return 1
    n_new = (len(mmx_arms) + len(name_arms) + len(packed_arms) +
             len(body_arms) + len(ext_arms) + len(sym_arms) +
             len(prefix_arms) + 6 +
             # D98: the model-aware mapping, the scope partition, its totality,
             # conservation, the stamp's second half, and the second plant
             len(map_arms) + len(scope_arms) + 6 +
             # D257: the width key, its origin invariance, the stamp seeing it
             len(width_arms) + 2 +
             # D337: the silicon class, its mapping, and the no-pooling plants
             d337)
    print(f"demand-census selftest: PASS ({len(arms)+len(line_arms)+7+n_new} arms; "
          f"the width-changing/string-move trap in both directions, every "
          f"line-level rule that moved the number, and both routes of the "
          f"hand-written/compiler split in both directions)")
    return 0

DOC_PREAMBLE = """## The corpus, and how to rebuild it

Public Debian `amd64` binaries, downloaded and never vendored. The recipe, so
the number can be re-derived rather than believed:

```bash
# one subdir of $CORPUS per column, named as COLUMN_CLASS names it
for u in main/c/coreutils/coreutils_9.10-1_amd64.deb \\
         main/g/glibc/libc6_2.44-1_amd64.deb \\
         main/g/gcc-14/cpp-14-x86-64-linux-gnu_14.4.0-2_amd64.deb \\
         main/l/linux/linux-image-6.1.0-50-amd64-unsigned_6.1.176-1_amd64.deb \\
         main/f/ffmpeg/libavcodec61_7.1.5-0+deb13u1_amd64.deb \\
         main/f/ffmpeg/libavutil59_7.1.5-0+deb13u1_amd64.deb \\
         main/x/x264/libx264-164_0.164.3108+git31e19f9-2+b1_amd64.deb \\
         main/d/dav1d/libdav1d7_1.5.1-1_amd64.deb \\
         main/libv/libvpx/libvpx9_1.15.0-2.1+deb13u1_amd64.deb \\
         main/v/vlc/vlc-plugin-base_3.0.23-0+deb13u1_amd64.deb; do
  curl -O "https://deb.debian.org/debian/pool/$u"
done                       # then `ar x` + `tar xf data.tar.*` each one
# vmlinux is the xz payload inside vmlinuz: find the `fd 37 7a 58 5a 00` magic
# and decompress from it; the result starts with \\x7fELF.
# vlc-plugin-base is split at unpack: plugins/codec/ -> vlc-codec,
# plugins/video_chroma/ -> vlc-video_chroma (VLC delegates decoding to
# libavcodec, so its OWN hand-written SIMD is in the chroma converters).

# ⛔ AND THE SYMBOLS, WITHOUT WHICH THE ATTRIBUTION SILENTLY REPORTS ITS DEFAULT.
# The shipped .so files are STRIPPED: `.dynsym` holds only exported names and
# carries ZERO ISA-suffixed symbols in every column of this corpus.  The
# per-function split needs `.symtab`, which lives in the debug packages.
for u in d/dav1d/libdav1d7-dbgsym_1.5.1-1_amd64.deb \\
         x/x264/libx264-164-dbgsym_0.164.3108+git31e19f9-2+b1_amd64.deb \\
         libv/libvpx/libvpx9-dbgsym_1.15.0-2.1+deb13u1_amd64.deb \\
         f/ffmpeg/libavcodec61-dbgsym_7.1.5-0+deb13u1_amd64.deb \\
         f/ffmpeg/libavutil59-dbgsym_7.1.5-0+deb13u1_amd64.deb \\
         v/vlc/vlc-plugin-base-dbgsym_3.0.23-0+deb13u1_amd64.deb \\
         c/coreutils/coreutils-dbgsym_9.10-1_amd64.deb \\
         g/gcc-14/cpp-14-x86-64-linux-gnu-dbgsym_14.4.0-2_amd64.deb; do
  curl -O "https://deb.debian.org/debian-debug/pool/main/$u"
done
curl -O https://deb.debian.org/debian/pool/main/g/glibc/libc6-dbg_2.44-1_amd64.deb

scripts/demand_census.py --corpus $CORPUS --debug $DEBUG
```

⚠️ **GPL code is COUNTED, never copied.** Nothing from these binaries enters
this repository; the disassembly is read, tallied, and discarded.

⛔ **THE KERNEL IS ITS OWN COLUMN AND IS NEVER POOLED** with the user-space
ones. Its privileged instructions are outside the model's stated scope rather
than missing from it, so a pooled number would report coverage for a corpus the
model never claimed.

⛔ **AND HAND-WRITTEN ASSEMBLY IS ITS OWN COLUMN CLASS**, never pooled with
compiler output. They are two demands: a compiler emits a narrow, predictable
vocabulary, while a codec's hand-written kernels are packed SIMD in forms no
compiler produces. Averaging them reports a number for a corpus nobody writes.

## What this number is, and what it is not

It is a **STATIC** count of instruction occurrences in a disassembly: what a
binary CONTAINS, which is the right question for deciding what to model next and
the wrong one for deciding what is hot at run time.

⚠️ It is an **UPPER BOUND on form-level coverage.** This tool maps a MNEMONIC to
a roster name; the model covers FORMS. An addressing mode or operand shape the
model lacks is still counted as covered if the mnemonic matches, so the
remaining error is in the flattering direction and is not measured.

**What decides whether a form is in scope at all** is the register file its
operands name and the prefix it carries, and every bucket is ruled on
explicitly — there is no default:

| the operands name… | in scope? | why |
|---|---|---|
| GPRs only | ✅ | the model's whole P0/P1 roster |
| an `%fs:`/`%gs:` segment base | ✅ | **P2 addition 1** put the base on `Ea` |
| a 64-bit immediate (`movabsq`) | ✅ | **P2 addition 3**; `Operand.imm` was always 64-bit |
| an `%xmm` register, SSE-legacy encoding | ✅ | **P2 batches 4–9** |
| an `%mm0`–`%mm7` MMX register | ⛔ | this model has no MMX register file |
| a `%ymm`, `%zmm` or `%k` register | ⛔ | no AVX/AVX-512 state |
| a VEX-encoded `%xmm` form (`v…`) | ⛔ | a different encoding, not a different name |
| an x87 `%st` register | ⛔ | no x87 state |
| a `lock` prefix | ✅ per form | see below |

⭐ **The `lock` prefix is credited PER FORM, through a published predicate (D367).** P2
addition 2 landed a LOCK vocabulary, and `docs/COVERAGE.md` now publishes a `Lockable:`
line: every mnemonic with a vector whose form `Op.lockable` accepts. A locked instruction
is covered when its roster name is in the model AND on that line; any other locked form
is refused and counted as NOT covered. Claiming a locked instruction by MNEMONIC alone
would credit the model with `lock movq %rax,(%rbx)`, which is `#UD` on silicon and the
form a reader most expects to be lockable; the line is what prevents that.
⚠️ **The limit, declared:** a name is on the line when a vector's FORM is lockable, which
need not be a vector that carries the `lock` byte. Some credited names (`and`, `sub`,
`btr`, `xor` among them) are credited from an unlocked memory-destination vector plus
the predicate, not from a differentially run locked instruction.

⛔ **The MMX exclusion was a real over-claim.** `%[xyz]mm` does not match
`%mm0`, so until the assembly class arrived every MMX instruction whose mnemonic
maps to a roster name — `movq %mm0, %mm3` is spelled `movq` — was counted as
covered. `%mm` occurs **0 times in glibc and 0 times in cc1**, and **15,690
times in libx264**: the gap was invisible in the corpus that existed and
material in the one that did not.

⛔ **And the opposite error ran for twenty-two batches in the other direction.**
The rule that excluded vector operands was written when the model had no vector
registers, and it did not move when the model gained twenty-two SSE mnemonics,
an `%fs:`/`%gs:` base and a 64-bit immediate move: the mapping from an objdump
mnemonic to a roster name kept a hand-maintained vector half that returned
"unknown" for every one of them. Regenerating this document after those batches
changed **every percentage by +0.0**, and the ranked list below went on offering
`movdqa` — which the model HAS — as the second-largest gap to close. That half
is now DERIVED from the model rather than listed, and the staleness stamp at the
top of this file hashes the mapping's behaviour as well as the model, because a
stamp over two coupled artifacts that hashes one of them reports only about the
one it hashes.

"""

ASM_CLASS_PREAMBLE = """
Each column is split **per function** into hand-written and compiler-emitted by
**two independent routes** — the symbol NAME (an ISA token as a `_`-delimited
component: `_sse2`, `_ssse3`, `_avx2`, `_avx512icl`, `_mmxext`, `_xop`, `_fma3`)
and the function BODY (packed-SIMD density ≥ 50% over ≥ 8 instructions). The
**confusion matrix** is published rather than a single number, because each
route has a blind spot the other one sees: the name route misses a nasm function
with no ISA suffix, and the body route misses hand-written GPR-only assembly.
The disagreement cells are printed with their largest functions so they can be
read rather than believed.

⚠️ Packed SIMD is not "touches a vector register": the scalar floating-point
forms (`addsd`, `mulss`, `cvtsi2sd`) and the GPR↔xmm transfers (`movd`, `movq`)
are excluded, or every math-heavy C function would read as hand-written.
"""


CONTROL_VERDICT = """
⛔ **THE `cc1` CONTROL FIRED ON THE NAME ROUTE, AND IT NAMED ITS OWN CAUSE.**
A C++ compiler's own binary should contain no hand-written assembly, and the
body route agrees — 0.0%. The name route reads 2.5%, and the `AC` cell says why:
`ix86_expand_int_sse_cmp`, `gen_avx_haddv8sf3`, `ix86_expand_sse_movcc`,
`pass_remove_partial_avx_dependency`. These are compiler functions **about** SSE
and AVX, and `sse` and `avx` are `_`-delimited components of their names.

⇒ 🔑 **THE NAME ROUTE IS A CONVENTION, NOT A FACT.** It over-claims in a program
whose SUBJECT is the instruction set, and it under-claims wherever the
convention is not followed — `vlc-video_chroma` reads **0.0% by name and 53.1%
by body**, because VLC's chroma converters are hand-written SIMD with ordinary C
names. The two failures point in opposite directions, which is the entire reason
there are two routes and the entire reason the matrix is published instead of a
number.

⚠️ **THE THRESHOLD IS NOT WIDENED TO MAKE THIS PASS.** Deriving a control's new
allowance from the thing it is checking would leave a gate that can only agree
with its subject. The reading stands as ⛔ and the split is quoted as a RANGE —
the `AA` cell is the floor, the wider of the two routes is the ceiling.

"""

# ⛔ THE COLUMN CLASS IS DECLARED, AND AN UNDECLARED COLUMN IS AN ERROR.
# A default here would be the whole defect this class exists to fix: an
# unrecognised codec column silently pooled into "compiler output" would report
# a coverage number for a demand nobody has.
COLUMN_CLASS = {
    "cc1": "compiler", "coreutils": "compiler", "glibc": "compiler",
    "vmlinux-kernel": "kernel",
    "ffmpeg": "asm", "x264": "asm", "dav1d": "asm", "vpx": "asm",
    "vlc-codec": "asm", "vlc-video_chroma": "asm",
}
CONTROLS = {"cc1": "must read ~0% hand-written",
            "glibc": "must read substantially hand-written"}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus")
    ap.add_argument("--debug", help="tree of unpacked -dbgsym packages; symbols "
                                    "are matched to binaries by build-id")
    ap.add_argument("--kernel")
    ap.add_argument("--out", default="docs/DEMAND-CENSUS.md")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    if args.selftest:
        return selftest()
    if args.check:
        return check_stale(args.out)
    if not args.corpus:
        print("⛔ --corpus is required")
        return 2
    model = model_mnemonics()
    # ⭐ D352 (STATUS 7d): the model's executed forms, read once; a refusal stops the run (never an empty set)
    import tempfile
    with tempfile.TemporaryDirectory(prefix="x86lean-census-forms-") as _td:
        _reg, msk, _fnote = model_forms(root, model, _td)
    if msk is None:
        print(f"⛔ D352: the model's forms could not be read — {_fnote}. Nothing written.")
        return 2
    print(f"D352: model forms read — {_fnote}; {len(_reg)} (name, bucket) with a register form, "
          f"{len(msk)} with a memory form")
    dbg = debug_index(args.debug)
    groups = {}
    for g in sorted(os.listdir(args.corpus)):
        d = os.path.join(args.corpus, g)
        if not os.path.isdir(d):
            continue
        if g not in COLUMN_CLASS:
            print(f"⛔ column `{g}` has no declared class. Add it to "
                  f"COLUMN_CLASS as 'compiler', 'asm' or 'kernel' — a census "
                  f"that guesses a column's class is a census that pools.")
            return 2
        groups[g] = [os.path.join(r, f) for r, _, fs in os.walk(d) for f in fs]
    # ⛔ D337: written to a sibling `.partial` and moved into place only at the
    # end, so a run the no-pooling check refuses (exit 3) leaves the shipped
    # document untouched — a half-written census still carries a fresh stamp.
    out_final = os.path.join(root, args.out)
    out_part = out_final + ".partial"
    with open(out_part, "w", encoding="utf-8") as fh:
        fh.write("# THE DEMAND-SIDE CENSUS — what real binaries actually execute\n\n")
        fh.write("*Generated by `scripts/demand_census.py`. Do not edit.*\n\n")
        n_m, h_m, rh_m = model_stamp(model)
        fh.write(f"<!-- census-model: mnemonics={n_m} sha={h_m} "
                 f"rules={rh_m} -->\n")
        _nv, _np, _fd = forms_digest(root)
        fh.write(f"<!-- census-forms: vectors={_nv} probes={_np} sha={_fd} -->\n\n")
        fh.write(DOC_PREAMBLE)
        fh.write(f"The model implements **{len(names_of(model))} mnemonics**: "
                 f"**{len(model)} differentially tested** (refereed by ACL2 x86isa "
                 f"over the swept pre-states) and **{len(silicon_of(model))} "
                 f"{SILICON_LABEL}** (the rows of `siliconTable`). ⚖️ **Count "
                 f"mechanisms, not voices (D332, D337):** every \"covered\" figure "
                 f"below is the DIFFERENTIAL one alone, and equals what a model "
                 f"without `siliconTable` would read — the run recomputes it that "
                 f"way and refuses (exit 3) if it differs. The silicon-refereed "
                 f"demand is printed on its own line beside it and is never summed "
                 f"into it; a reader may cite the two side by side.\n\n")
        if vex_of(model):
            fh.write(f"⭐ **D342 (a): a third population, {len(vex_of(model))} VEX-table mnemonics** (VEX.128, "
                     f"differentially tested against x86isa in the VEX table of `docs/COVERAGE.md`, D341, and NOT "
                     f"in the 199-mnemonic figure). A VEX.128 instruction is outside the differential figure's scope, "
                     f"so one whose mnemonic is a VEX-table row is printed on a third labelled line, and one whose "
                     f"mnemonic is a `siliconTable` row on the silicon line; neither is summed into \"covered\".\n\n")
        fh.write(f"Every number below "
                 f"is a STATIC count of instruction occurrences in a disassembly, "
                 f"not a dynamic profile: it measures what a binary CONTAINS, which "
                 f"is the right question for deciding what to model next and the "
                 f"wrong one for deciding what is hot.\n")
        results = {}
        for klass, title in (("compiler", "COMPILER OUTPUT"),
                             ("asm", "HAND-WRITTEN ASSEMBLY (codec libraries)"),
                             ("kernel", "THE KERNEL — its own column, never pooled")):
            cols = [g for g in groups if COLUMN_CLASS[g] == klass]
            if not cols:
                continue
            fh.write(f"\n## {title}\n")
            if klass == "asm":
                fh.write(ASM_CLASS_PREAMBLE)
            for g in sorted(cols):
                mem = collections.Counter()
                counts, n, n_sym, fns = census(groups[g], dbg, mem)
                if not counts:
                    continue
                results[g] = report(f"{g} — {n} ELF x86-64 objects", counts,
                                    model, fh, fns, n, n_sym, mem, msk)
                results[g]["class"] = klass
                # ⛔ D337 NO-POOLING: checked per column, before the document is
                # finished, so a pooled figure never reaches a reader
                why = check_no_pooling(counts, differential_reference(model), results[g])
                if why:
                    print(f"⛔ D337 NO-POOLING ({g}): {why}\n   Nothing written; "
                          f"the partial output is {out_part}.")
                    return 3
            # ⛔ POOLED WITHIN A CLASS AND NEVER ACROSS ONE.
            if klass == "asm" and len(cols) > 1:
                ext_pool = collections.Counter()
                for g in cols:
                    for e, k in results.get(g, {}).get("ext", {}).items():
                        ext_pool[e] += k
                tot = sum(results[g]["total"] for g in cols if g in results)
                cov = sum(results[g]["covered"] for g in cols if g in results)
                sil_n = sum(results[g]["silicon"] for g in cols if g in results)
                vex_n = sum(results[g].get("vex", 0) for g in cols if g in results)
                fh.write(f"\n### The assembly class, pooled\n\n")
                fh.write(f"- **{tot:,} instructions**, covered by the model "
                         f"(differentially tested mnemonics) "
                         f"**{cov:,} ({100.0*cov/tot:.1f}%)**.\n")
                if silicon_of(model):
                    fh.write(f"- ⚙ **Implemented, {SILICON_LABEL}: {sil_n:,} "
                             f"({100.0*sil_n/tot:.2f}%)** — inside the not-covered "
                             f"figure below, never added to the line above (D337).\n")
                if vex_of(model):
                    fh.write(f"- ⚙ **{VEX_LABEL}: {vex_n:,} ({100.0*vex_n/tot:.2f}%)** — inside the "
                             f"not-covered figure below, never added to the line above (D342).\n")
                fh.write(f"- ⛔ Pooled ACROSS the codec columns and never with "
                         f"compiler output: the two are different demands, which "
                         f"is why this class exists.\n\n")
                unc = sum(ext_pool.values()) or 1
                fh.write(f"- **Not covered: {unc:,} instructions "
                         f"({100.0*unc/tot:.1f}% of the class)** — this is the "
                         f"P2 demand, and the table below is it, per extension.\n\n")
                fh.write("| bucket | occurrences | share of the class | "
                         "share of the UNCOVERED work |\n|---|---|---|---|\n")
                for e, k in ext_pool.most_common():
                    fh.write(f"| {e} | {k:,} | {100.0*k/tot:.2f}% | "
                             f"{100.0*k/unc:.1f}% |\n")
                results["_asm_pooled"] = dict(total=tot, covered=cov,
                                              pct=100.0*cov/tot,
                                              silicon=sil_n,
                                              silicon_pct=100.0*sil_n/tot,
                                              vex=vex_n, vex_pct=100.0*vex_n/tot,
                                              ext=dict(ext_pool))
        # ── the pre-registered controls, checked in the generated document ──
        fh.write("\n## The controls, and the one that fired\n\n")
        fh.write("Pre-registered before the corpus was downloaded, and riding in "
                 "the same run as the result they license — because a split "
                 "measured with no control is a number with no condition.\n\n")
        fh.write("| column | pre-registered | NAME route | BODY route | verdict |\n")
        fh.write("|---|---|---|---|---|\n")
        ctl = {}
        for g, want in CONTROLS.items():
            r = results.get(g)
            if not r:
                continue
            a = r["attribution"]
            nm = 100.0 * a["name_route_asm"] / (a["total"] or 1)
            bd = 100.0 * a["body_route_asm"] / (a["total"] or 1)
            ok_n = (nm < 1.0) if g == "cc1" else (nm > 5.0)
            ok_b = (bd < 1.0) if g == "cc1" else (bd > 5.0)
            v = ("✅ both routes as pre-registered" if ok_n and ok_b else
                 "⛔ the NAME route is NOT as pre-registered" if ok_b else
                 "⛔ the BODY route is NOT as pre-registered" if ok_n else
                 "⛔ NEITHER route is as pre-registered")
            ctl[g] = dict(name=nm, body=bd, ok_name=ok_n, ok_body=ok_b)
            fh.write(f"| `{g}` | {want} | {nm:.1f}% | {bd:.1f}% | {v} |\n")
        fh.write(CONTROL_VERDICT)
        results["_controls"] = ctl
        json.dump(results, open(out_final + ".json.partial", "w", encoding="utf-8"),
                  indent=1, default=str)
    os.replace(out_part, out_final)
    os.replace(out_final + ".json.partial", out_final + ".json")
    print(f"wrote {args.out}")
    for g, r in results.items():
        if g.startswith("_"):
            continue
        a = r["attribution"]
        print(f"  {g:18s} {r['total']:>12,} insns  covered {r['covered']:>10,} "
              f"{r['pct']:5.1f}%  silicon {r['silicon']:>7,}  "
              f"hand-written(name) {100.0*a['name_route_asm']/(a['total'] or 1):5.1f}%  "
              f"(body) {100.0*a['body_route_asm']/(a['total'] or 1):5.1f}%")
    return 0

# ⛔ GUARDED SO THIS FILE CAN BE IMPORTED.  `EXT_SCOPE` — which of the ISA
# buckets the model's state can represent — is read by `p2_roster.py`, and the
# alternative to importing it is a second copy of the partition in the tool that
# prices the gap: the two would agree on the day they were written and diverge
# on the next batch, which is the shape D98 itself was.
if __name__ == "__main__":
    sys.exit(main())
