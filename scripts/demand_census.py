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
import os, re, sys, json, subprocess, collections, argparse

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# ── the model's roster, read from the model, never restated ────────────────
def model_mnemonics():
    """The mnemonics `X86.rosterP0` names.  ⚠️ Read from the GENERATED coverage
    table, which CI already fails on if it is stale — not from a list here,
    which would be a copy that drifts."""
    path = os.path.join(root, "docs", "COVERAGE.md")
    text = open(path).read()
    ms = re.findall(r'^\| `([a-z0-9]+)` \|', text, re.M)
    if not ms:
        print("⛔ no mnemonics read from docs/COVERAGE.md; a census with no "
              "model to compare against is not a measurement.")
        sys.exit(2)
    return set(ms)

# ── objdump mnemonic -> roster name ────────────────────────────────────────
CC = ("o no b c nae ae nb nc e z ne nz be na a nbe s ns p pe np po l nge "
      "ge nl le ng g nle").split()
SUFFIXED = {"mov","add","sub","and","or","xor","cmp","test","shl","shr","sar",
            "lea","inc","dec","neg","not","push","pop","adc","sbb","rol","ror",
            "rcl","rcr","bt","bts","btr","btc","xchg","bswap","mul","imul",
            "div","idiv","cmpxchg","xadd","shld","shrd","popcnt","lzcnt",
            "tzcnt","bsf","bsr","blsi","movbe","sarx","shlx","shrx","nop",
            "cmpxchg8b"}
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
}

def to_roster(m):
    """objdump mnemonic -> roster name, or None if this tool will not claim it.

    ⚠️ ORDER MATTERS AND THE DANGEROUS RULE IS LAST.  `movsbl`, `movswq`,
    `movzbl` are the width-changing moves (`movsx`/`movzx`); `movsb`/`movsq` are
    the STRING move.  Stripping a trailing size letter first would turn
    `movsbl` into `movsb` and then into the string `movs` — a different
    instruction the model has, so the census would silently claim it.  The
    width-changing forms are matched BEFORE any suffix stripping."""
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
    return None

INSN_RE = re.compile(r"^\s*[0-9a-f]+:\s+([a-z][a-z0-9.]*)\s*(.*)")
# ⛔⛔ TWO WAYS A MNEMONIC-LEVEL CENSUS OVER-CLAIMS, BOTH MEASURED RATHER THAN
# FOOTNOTED.  This tool maps an objdump MNEMONIC to a roster name, but the model
# covers FORMS -- so an instruction whose mnemonic the model has can still be
# one the model cannot execute:
#   * `movq %xmm0, %rax` is spelled `movq` and moves a VECTOR register.  Measured
#     before this rule existed: 0.636% of cc1 and 0.121% of glibc, every one of
#     them `movq`.
#   * `mov %fs:0x28, %rax` -- the stack-protector load in most compiled
#     functions -- carries a SEGMENT PREFIX, and `Ea` has no segment field
#     because segmentation is out of scope by declaration.  Measured: 0.244% of
#     cc1, 2.655% of glibc, 0.802% of the kernel.
# Both now count as NOT COVERED, so the headline number is honest by
# construction instead of by a sentence underneath it.
#
# ⚠️ THEY DO NOT MAKE THE NUMBER EXACT, AND THE LIMIT IS STATED IN THE
# GENERATED DOCUMENT: an addressing mode or operand shape the model lacks is
# still counted as covered if the mnemonic matches.  What is claimed here is an
# UPPER BOUND on form-level coverage, and these two rules move it toward the
# truth rather than to it.
VECTOR_RE  = re.compile(r"%[xyz]mm|%k[0-7]\b|%st")
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

def classify_lines(lines):
    """objdump lines -> Counter keyed by (mnemonic, kind).

    ⚠️ SPLIT OUT OF `disassemble` SO IT CAN BE DRIVEN ON SYNTHETIC INPUT.  The
    three rules that moved this census most — padding runs, the `%fs:`/`%gs:`
    narrowing, and LOCK attribution — are all LINE-level, and a rule that can
    only be exercised by disassembling a 63 MB kernel does not get exercised."""
    c = collections.Counter()
    run = 0
    pending_lock = False
    def flush(run):
        if run >= 2:
            c[("int3", "padding")] += run
        elif run == 1:
            c[("int3", "plain")] += 1
    for line in lines:
        mm = INSN_RE.match(line)
        if not mm:
            continue
        mn, ops = mm.group(1), mm.group(2)
        if mn == "int3":
            run += 1
            continue
        flush(run); run = 0
        if mn == "lock" and not ops.strip():
            pending_lock = True
            continue
        # ⚠️ `nop` keeps its CS prefix and is still a NOP; the exclusion is
        # about a segment-relative ADDRESS, which a multi-byte nop's operand
        # is not.
        seg = SEGMENT_RE.search(ops) and to_roster(mn) != "nop"
        kind = ("lock" if pending_lock else
                "vector" if VECTOR_RE.search(ops) else
                "segment" if seg else "plain")
        pending_lock = False
        c[(mn, kind)] += 1
    flush(run)
    return c


def disassemble(path):
    """⚠️ STREAMED, not captured.  vmlinux is 63 MB of ELF and disassembles to
    well over a gigabyte of text; `capture_output` would hold all of it in
    memory at once for a job whose whole output is a counter."""
    with subprocess.Popen(["objdump", "-d", "--no-show-raw-insn", path],
                          stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                          text=True, bufsize=1 << 20) as pr:
        c = classify_lines(pr.stdout)
        rc = pr.wait()
    return c if rc == 0 else None


def is_elf_x86_64(p):
    try:
        h = open(p, "rb").read(20)
    except OSError:
        return False
    return h[:4] == b"\x7fELF" and h[4] == 2 and h[18:20] == b"\x3e\x00"

def census(paths):
    total = collections.Counter()
    n = 0
    for p in paths:
        if not is_elf_x86_64(p):
            continue
        c = disassemble(p)
        if c is None:
            continue
        total += c
        n += 1
    return total, n

def report(name, counts, model, fh):
    mapped = collections.Counter()
    unmapped = collections.Counter()
    outscope = collections.Counter()
    padding = sum(k for (m, kind), k in counts.items() if kind == "padding")
    counts = {kv: k for kv, k in counts.items() if kv[1] != "padding"}
    for (m, kind), k in counts.items():
        r = to_roster(m)
        if r is None:
            unmapped[m] += k
        elif kind != "plain":
            outscope[f"{r} ({kind} operand)"] += k
        else:
            mapped[r] += k
    tot = sum(counts.values())
    covered = sum(k for r, k in mapped.items() if r in model)
    out_of  = sum(k for r, k in mapped.items() if r not in model)
    unk     = sum(unmapped.values())
    oos     = sum(outscope.values())
    fh.write(f"\n### {name}\n\n")
    fh.write(f"- **{tot:,} instructions** over {len(set(m for m, _ in counts))} "
             f"distinct objdump mnemonics.\n")
    if padding:
        fh.write(f"- ⛔ **{padding:,} `int3` in runs of two or more were counted as "
                 f"PADDING and excluded** from the line above and from every "
                 f"percentage below. Before this exclusion they were "
                 f"{100.0*padding/(tot+padding):.1f}% of this column.\n")
    fh.write(f"- **Covered by the model: {covered:,} ({100.0*covered/tot:.1f}%).**\n")
    fh.write(f"- Mapped to a roster name the model does not have: {out_of:,} "
             f"({100.0*out_of/tot:.1f}%).\n")
    fh.write(f"- Mapped, but carrying a VECTOR register, an `%fs:`/`%gs:` "
             f"SEGMENT PREFIX, or a `lock` prefix — none of which this model "
             f"has: {oos:,} ({100.0*oos/tot:.2f}%) — counted as NOT covered.\n")
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
        yes = "✅" if plain in model else "—"
        fh.write(f"| {i} | `{plain}` | {k:,} | {100.0*k/tot:.2f}% | {yes} |\n")
    fh.write(f"\n**The ranked list of mnemonics the model does NOT cover** "
             f"(the P2 roster candidates, by demand):\n\n")
    fh.write("| rank | mnemonic | occurrences | share |\n|---|---|---|---|\n")
    miss = collections.Counter()
    for r, k in mapped.items():
        if r not in model:
            miss[r] += k
    for m, k in unmapped.items():
        miss[m] += k
    for m, k in outscope.items():
        miss[m] += k
    for i, (m, k) in enumerate(miss.most_common(25), 1):
        fh.write(f"| {i} | `{m}` | {k:,} | {100.0*k/tot:.2f}% |\n")
    return dict(total=tot, covered=covered, pct=100.0*covered/tot,
                miss=miss.most_common(40))

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
        ("cmpxchg16b", None), ("pxor", None), ("endbr64", None),
    ]
    bad = []
    for m, want in arms:
        got = to_roster(m)
        ok = got == want
        print(("  ✔ " if ok else "  ⛔ ") + f"{m:12s} -> {got}" +
              ("" if ok else f"   EXPECTED {want}"))
        if not ok:
            bad.append(m)
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

    # and the model set must be non-empty and must contain a form we know it has
    model = model_mnemonics()
    for must in ("mov", "add", "cmpxchg8b"):
        ok = must in model
        print(("  ✔ " if ok else "  ⛔ ") + f"model set contains `{must}`")
        if not ok:
            bad.append("model:" + must)
    if bad:
        print(f"demand-census selftest: FAIL ({len(bad)} of "
              f"{len(arms)+len(line_arms)+3} arms)")
        return 1
    print(f"demand-census selftest: PASS ({len(arms)+len(line_arms)+3} arms; "
          f"the width-changing/string-move trap in both directions, and every "
          f"line-level rule that moved the number)")
    return 0

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus")
    ap.add_argument("--kernel")
    ap.add_argument("--out", default="docs/DEMAND-CENSUS.md")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args()
    if args.selftest:
        return selftest()
    if not args.corpus:
        print("⛔ --corpus is required")
        return 2
    model = model_mnemonics()
    groups = {}
    for g in sorted(os.listdir(args.corpus)):
        d = os.path.join(args.corpus, g)
        if not os.path.isdir(d):
            continue
        paths = [os.path.join(r, f) for r, _, fs in os.walk(d) for f in fs]
        groups[g] = paths
    with open(os.path.join(root, args.out), "w") as fh:
        fh.write("# THE DEMAND-SIDE CENSUS — what real binaries actually execute\n\n")
        fh.write("*Generated by `scripts/demand_census.py`. Do not edit.*\n\n")
        fh.write("""## The corpus, and how to rebuild it

Public Debian `amd64` binaries, downloaded and never vendored. The recipe, so
the number can be re-derived rather than believed:

```bash
for u in main/c/coreutils/coreutils_9.10-1_amd64.deb \\
         main/g/glibc/libc6_2.44-1_amd64.deb \\
         main/g/gcc-14/cpp-14-x86-64-linux-gnu_14.4.0-2_amd64.deb \\
         main/l/linux/linux-image-6.1.0-50-amd64-unsigned_6.1.176-1_amd64.deb; do
  curl -O "https://deb.debian.org/debian/pool/$u"
done                       # then `ar x` + `tar xf data.tar.*` each one
# vmlinux is the xz payload inside vmlinuz: find the `fd 37 7a 58 5a 00` magic
# and decompress from it; the result starts with \\x7fELF.
scripts/demand_census.py --corpus <dir with one subdir per column>
```

⚠️ **GPL code is COUNTED, never copied.** Nothing from these binaries enters
this repository; the disassembly is read, tallied, and discarded.

⛔ **THE KERNEL IS ITS OWN COLUMN AND IS NEVER POOLED** with the three user-space
ones. Its privileged instructions are outside the model's stated scope rather
than missing from it, so a pooled number would report coverage for a corpus the
model never claimed.

## What this number is, and what it is not

It is a **STATIC** count of instruction occurrences in a disassembly: what a
compiler EMITS, which is the right question for deciding what to model next and
the wrong one for deciding what is hot at run time.

⚠️ It is an **UPPER BOUND on form-level coverage.** This tool maps a MNEMONIC to
a roster name; the model covers FORMS. Three ways a mnemonic-level count
over-claims are excluded here and measured — a vector-register operand, an
`%fs:`/`%gs:` segment prefix, and a `lock` prefix — but an addressing mode or
operand shape the model lacks is still counted as covered if the mnemonic
matches. The remaining error is in the flattering direction and is not measured.

""")
        fh.write(f"The model covers **{len(model)} mnemonics**. Every number below "
                 f"is a STATIC count of instruction occurrences in a disassembly, "
                 f"not a dynamic profile: it measures what a compiler EMITS, which "
                 f"is the right question for deciding what to model next and the "
                 f"wrong one for deciding what is hot.\n")
        results = {}
        for g, paths in groups.items():
            counts, n = census(paths)
            if not counts:
                continue
            results[g] = report(f"{g} — {n} ELF x86-64 objects", counts, model, fh)
        json.dump(results, open(os.path.join(root, args.out + ".json"), "w"),
                  indent=1, default=str)
    print(f"wrote {args.out}")
    for g, r in results.items():
        print(f"  {g:12s} {r['total']:>12,} instructions   covered {r['pct']:.1f}%")
    return 0

sys.exit(main())
