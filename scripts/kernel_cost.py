#!/usr/bin/env python3
"""KERNEL-COST MEASUREMENT AND CEILING (plan v1 §3.3, §3.7).

⚠️ WHAT THIS MEASURES, PRECISELY.  Lean's profiler reports `type checking`
separately from `elaboration` and `tactic execution`.  `type checking` is the
KERNEL: the time the trusted checker spends replaying what the elaborator
produced.  It is the number plan v1 §3.7 asks to be measured and capped, because
it is the one that explodes when a proof leans on defeq across a
composite-routine boundary — and it is NOT the number that dominates the build,
so a wall-clock ceiling would not notice the blow-up until it was enormous.

The §3.3 MEASUREMENT the plan asks for is the per-module kernel time on the
twenty forms.  It measures the cost of the three-axiom route.  It does NOT
choose an axiom base: that was fixed by the helm's ruling (TRUSTBASE.md), and
the measurement is reported, not obeyed.

CEILINGS live in `scripts/kernel_ceilings.txt`.  A module over its ceiling, or
with no ceiling registered, FAILS — that is the "fail on a registered ceiling"
of §3.7.  Raising a ceiling is a decision to record in docs/DECISIONS.md.

Usage:  kernel_cost.py [--register]   (--register rewrites the ceiling file)
"""
import os, re, subprocess, sys, glob, json

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(root)
CEIL_FILE = "scripts/kernel_ceilings.txt"
# Headroom over the measured baseline.  Generous enough that ordinary noise on a
# loaded machine does not fail a build, tight enough that a real regression does.
HEADROOM = 3.0
FLOOR_MS = 50   # below this, timing noise dominates and a ratio is meaningless

def modules():
    fs = sorted(glob.glob("X86/*.lean")) + ["X86.lean", "X86Native.lean"] \
         + sorted(glob.glob("Tests/*.lean")) + ["Tests.lean"]
    return [f for f in fs if os.path.exists(f)]

def mod_name(f):
    return f[:-5].replace("/", ".")

def kernel_ms(f):
    r = subprocess.run(
        ["lake", "env", "lean", "-D", "profiler=true", "-D", "profiler.threshold=100000", f],
        capture_output=True, text=True)
    if r.returncode != 0:
        print(f"⛔ {f} did not compile:\n{r.stdout}\n{r.stderr}")
        sys.exit(2)
    # ⚠️ The profiler writes to STDERR, not stdout.  The first draft of this
    # script searched stdout only, measured 0.0ms for every module, and printed
    # "kernel-cost gate: CLEAN" — a gate that cannot see its subject reports a
    # pass. Both streams are searched now, and a module that yields NO reading
    # is an error rather than a zero.
    blob = r.stdout + "\n" + r.stderr
    m = re.search(r'^\s*type checking\s+([\d.]+)(ms|s)\s*$', blob, re.M)
    if not m:
        # A pure re-export module (X86.lean is nothing but `import` lines)
        # type-checks nothing, so the profiler prints its cumulative block with
        # no `type checking` entry.  That is a real zero.  A run with NO
        # cumulative block at all is a failed measurement and must not be
        # silently read as zero — the distinction is the whole difference
        # between "nothing to check" and "we did not look".
        if "cumulative profiling times" in blob:
            return 0.0
        print(f"⛔ {f}: the profiler produced no cumulative block at all. "
              f"A missing reading is not a zero.")
        sys.exit(2)
    v = float(m.group(1))
    return v * 1000 if m.group(2) == "s" else v

# ⭐ THE DENOMINATOR FOR A TABLE-DRIVEN MODULE, AND WHY IT CAN BE TRUSTED.
#
# `Tests.Coverage` type-checks `decide` over the coverage TABLE: its kernel cost
# is linear in the number of rows, and the roster grows every batch by
# construction.  An absolute-millisecond ceiling on such a module is a gate that
# must be RAISED EVERY BATCH — and a gate relaxed on schedule is not a gate, it
# is a chore that trains its owner to raise it.  Batches 3 and 14 both raised
# this one; batch 10 recorded 2.4x headroom as "room to do this properly rather
# than under pressure", and by batch 14 the headroom was 1.09x.  So the ceiling
# for such a module is registered PER ROW and multiplied by the live row count.
#
# ⚠️ The row count is not counted by this script.  It is read from the LITERAL
# in `theorem roster_size_is_N : rosterSize = N := by decide` — and that literal
# is kernel-pinned to the table by `table_row_count : tableP0.length =
# rosterSize`, so the denominator this gate divides by is a number Lean PROVES
# is the table's length, not a number this script counted and could get wrong.
# A missing or unparseable literal is an ERROR, never a default: a denominator
# guessed at is a ceiling that means nothing.
PER_ROW_TAG = "@perRow"

def roster_size():
    src = open("Tests/Coverage.lean").read()
    ms = re.findall(r'rosterSize\s*=\s*(\d+)\s*:=\s*by\s+decide', src)
    if len(ms) != 1:
        print(f"⛔ could not read a unique kernel-pinned `rosterSize = N` from "
              f"Tests/Coverage.lean (found {len(ms)}). A per-row ceiling "
              f"without a trustworthy denominator is not a gate.")
        sys.exit(2)
    return int(ms[0])


# ⭐⭐ P1 BATCH 20 — THE DENOMINATOR BATCH 17 SAID COULD BE PINNED, PINNED.
# `vectorCount` is proved equal to `vectors.length` in Tests/Coverage.lean, so
# this is a number Lean checks and not a number this script counted.  The same
# refusal as `roster_size`: a missing literal is an ERROR, never a default.
def vector_count():
    src = open("Tests/Coverage.lean").read()
    ms = re.findall(r'vectorCount\s*=\s*(\d+)\s*:=\s*by\s+decide', src)
    if len(ms) != 1:
        print(f"⛔ could not read a unique kernel-pinned `vectorCount = N` from "
              f"Tests/Coverage.lean (found {len(ms)}). A per-declaration ceiling "
              f"without a trustworthy denominator is not a gate.")
        sys.exit(2)
    return int(ms[0])


# ⭐⭐⭐ PER-DECLARATION KERNEL TIME — THE MEASUREMENT BATCH 17 RECORDED AS
# BLOCKED, AND THE BLOCK WAS ONE SENTENCE TOO WIDE.
#
# Batch 17 wrote: "A vector count could be pinned the same way; an ASSERTION
# count cannot be, because it is a property of the file's text and not of any
# term in it."  Both halves are TRUE.  What was not noticed for three batches is
# what they rule out: they block gating the module's TOTAL in an
# (assertions x vectors) unit.  They say nothing about gating EACH
# DECLARATION — and a per-declaration gate needs no assertion count at all,
# because dividing by the number of declarations is the only thing the assertion
# count was ever for.
#
# ⇒ 🔑 A BLOCKED REPAIR BLOCKS A DESIGN, NOT A GOAL.
#
# The mechanism: `lean --json -D profiler.threshold=N` emits one
# `type checking took X` message PER DECLARATION, carrying `fileName` and
# `pos.line`, so a failure names the declaration instead of the module.  Plain
# (non-JSON) output carries the same timings with NO position, which is why the
# first attempt at this looked impossible too.
def per_declaration(f, threshold_ms=100):
    """[(line, name, ms)] for one module, kernel time attributed by source line."""
    r = subprocess.run(
        ["lake", "env", "lean", "--json", "-D", "profiler=true",
         "-D", f"profiler.threshold={threshold_ms}", f],
        capture_output=True, text=True)
    if r.returncode != 0:
        print(f"⛔ {f} did not compile under the per-declaration profiler:\n{r.stderr}")
        sys.exit(2)
    src = open(f).read().splitlines()
    # A declaration's header is the nearest `theorem`/`def`/`example` at or
    # before the message's line — the message sits on the declaration's own line
    # for a term-mode proof and on its tactic block for others.
    def name_at(line):
        for k in range(line, 0, -1):
            m = re.match(r'\s*(?:private\s+)?(theorem|def|example|lemma)\s+(\S+)',
                         src[k - 1])
            if m:
                return m.group(2)
        return "?"
    out, seen = [], 0
    for ln in r.stdout.splitlines():
        if not ln.startswith("{"):
            continue
        try:
            m = json.loads(ln)
        except json.JSONDecodeError:
            continue
        g = re.match(r'type checking took ([\d.]+)(ms|s)', m.get("data", ""))
        if not g:
            continue
        seen += 1
        v = float(g.group(1)) * (1000 if g.group(2) == "s" else 1)
        out.append((m["pos"]["line"], name_at(m["pos"]["line"]), v))
    if not out:
        print(f"⛔ {f}: the per-declaration profiler produced no `type checking` "
              f"message at all. A gate that cannot see its subject reports a pass.")
        sys.exit(2)
    return sorted(out, key=lambda t: -t[2])

# ⭐⭐ P1 BATCH 17 — THE GROWTH LAW, MEASURED AND REPORTED RATHER THAN
# REDISCOVERED, AND THE LOAD AVERAGE BESIDE IT.
#
# The per-row ceiling was introduced by batch 14 precisely so that a gate would
# not need raising every batch (D38).  It has not needed raising since — and the
# DENSITY it gates has climbed every batch anyway: 266 -> 339 -> 363 ms/row
# across batches 14 to 16, so the headroom went 1.77x -> 1.39x -> 1.30x.
#
# ⛔ AND THE SERIES CANNOT BE EXTENDED HONESTLY, BECAUSE NONE OF THOSE READINGS
# RECORDS WHETHER THE MACHINE WAS IDLE.  This file's own comment knows that it
# matters — it records "measured on an IDLE machine (81.8 / 81.4 across two
# runs)" for `Tests.Nonvacuity`, and notes that a reading taken during the
# selftest was ~15% high — and the line beside it, the per-row figure handed
# from batch to batch, records nothing.  ⇒ A MEASUREMENT WHOSE CONDITIONS ARE
# NOT RECORDED CANNOT BE COMPARED WITH A LATER ONE; the discipline was written
# down once and not applied to the number that is actually tracked.  So this
# script now prints the one-minute LOAD AVERAGE beside every figure it reports,
# and a head reading a batch record can tell whether the trend is real.
#
# ⛔ SO THE ROW IS NOT THE UNIT EITHER.  `Tests.Coverage`'s cost is linear in
# (ASSERTIONS x VECTORS), and neither factor is the roster size: a batch adds
# theorems and vectors faster than it adds mnemonics.  Batch 16 -> 17 moves
# +2.6% in the flat unit (688.6 -> 706.6 ns) and +8.9% per row (362.7 -> 394.9).
# ⚠️ ONE PAIR IS NOT A SERIES, and it is offered as one pair: batch 17's reading
# records its load (two runs at 2.20 and 4.08, both 31 200 ms) and batch 16's
# records none, so this is the FIRST comparison in the repository that could be
# checked at all.
#
# ⚠️ AND THE SOUND REPAIR IS BLOCKED, WHICH IS WHY THIS PRINTS AND DOES NOT
# GATE.  The per-row ceiling can be trusted because its denominator is
# KERNEL-PINNED — `roster_size_is_N` is proved equal to the table's length, so
# it is a number Lean checks rather than a number this script counted.  A vector
# count could be pinned the same way; an ASSERTION count cannot be, because it
# is a property of the file's text and not of any term in it.  Registering a
# ceiling in a unit whose denominator this script greps for would trade a proven
# denominator for a guessed one — the exact thing the note above says makes a
# ceiling mean nothing.
#
# So the figure is REPORTED on every run, in the unit that is actually flat, so
# that the growth law is observed each batch instead of being reconstructed from
# git by whoever finally hits the ceiling.
#
# ⛔⛔ P1 BATCH 20 MEASURED THAT UNIT AND IT IS NOT FLAT.  "Linear in
# (assertions x vectors)" was inferred from two whole-module totals, and a total
# cannot tell a linear module from a super-linear one.  Profiled PER
# DECLARATION at 700 and again at 775 vectors -- the same code, minutes apart --
# three declarations grow FASTER than their input:
#
#     vectors_cover_the_roster   x1.645        (vectors x1.107)
#     every_row_has_a_vector     x1.324
#     every_vector_has_a_row     x1.321
#
# and the reason is in the source rather than in the timings: `vectorMnemonics`
# is `(vectors.map Vec.mnemonic).eraseDups`, and `List.eraseDups` is QUADRATIC.
# The two theorems above then run `contains` over its result once per row.
#
# ⭐⭐ P1 BATCH 21 PRICED THAT REPAIR BEFORE TAKING IT, AND IT WAS THE SMALLER
# OF THE TWO.  The dedup is real -- `vectorMnemonics.length = 83` costs 935 ms
# against a 69 ms control forcing the same 775 projections with no dedup -- but
# it is 2.8 s of a 37 900 ms module (7%).  What was never measured is that the
# kernel's reduction cache SPANS A DECLARATION AND NOT TWO, so the three
# mem-dest sweeps were paid three times over: 10 600 + 9 720 + 5 250 = 25 570 ms
# apart, 11 200 ms in one declaration.  Stating each group's claims in ONE
# reduction (`memDestSweep`, `vectorCoverage`) and DERIVING the original
# theorems from it, statements byte-for-byte unchanged, took the module
# 37 900 -> 22 400 ms.  ⇒ 🔑 A COST MODEL THAT ONLY KNOWS ABOUT THE ARTIFACT
# CANNOT SEE THE COST OF ASKING TWICE.  See D63.
#
# ⚠️ AND THE TWO DECLARATIONS THAT DOMINATE THE MODULE ARE BARELY VECTOR-DRIVEN
# AT ALL -- `mem_dest_rewrite_changed_exactly_the_three_operand_rows` x1.050 and
# `mem_dest_claims_are_backed` x1.077, most of even that being the SHAPES prose
# this batch lengthened rather than the vectors it added.  Together they are 53%
# of the module.
#
# ⇒ A PER-VECTOR DENOMINATOR WOULD HAVE GONE SLACK EXACTLY WHERE THE COST IS,
# and slack is the direction nobody polices.  The gate that was going to replace
# the per-row ceiling is therefore NOT INSTALLED: its own second source refused
# it (D62).  What IS installed is the measurement that refused it, printed on
# every run, because the next design needs this table and not another two
# batches of whole-module totals.
def coverage_growth_denominator():
    """(assertions, vectors) for Tests.Coverage — REPORTED, never gated."""
    thms = len(re.findall(r'^theorem\s', open("Tests/Coverage.lean").read(), re.M))
    vecs = len(re.findall(r'\{\s*id\s*:=\s*"', open("Tests/Vectors.lean").read()))
    return thms, vecs

def read_ceilings():
    """Returns {module: (kind, value)} where kind is "abs" or "perRow"."""
    d = {}
    if os.path.exists(CEIL_FILE):
        for line in open(CEIL_FILE):
            line = line.split("#")[0].strip()
            if line:
                parts = line.split()
                if len(parts) == 3 and parts[1] == PER_ROW_TAG:
                    d[parts[0]] = ("perRow", float(parts[2]))
                elif len(parts) == 2:
                    d[parts[0]] = ("abs", float(parts[1]))
                else:
                    print(f"⛔ unparseable ceiling line: {line!r}")
                    sys.exit(2)
    return d

def main():
    register = "--register" in sys.argv
    subprocess.run(["lake", "build", "X86", "Tests", "X86Native"],
                   capture_output=True, text=True)
    ceil = read_ceilings()
    nrows = roster_size()
    nvecs = vector_count()
    rows, total, fail = [], 0.0, False
    for f in modules():
        n = mod_name(f)
        ms = kernel_ms(f)
        total += ms
        rows.append((n, ms))
    if register:
        with open(CEIL_FILE, "w") as fh:
            fh.write("# Registered KERNEL (type-checking) ceilings, milliseconds.\n")
            fh.write("# Generated by scripts/kernel_cost.py --register on the P0 baseline.\n")
            fh.write(f"# Ceiling = max(measured x {HEADROOM}, {FLOOR_MS}ms): below the floor,\n")
            fh.write("# timing noise dominates and a ratio would fail on a loaded machine.\n")
            for n, ms in rows:
                prev = ceil.get(n)
                if prev and prev[0] == "perRow":
                    fh.write(f"{n} {PER_ROW_TAG} "
                             f"{max(ms * HEADROOM / nrows, FLOOR_MS / nrows):.1f}\n")
                else:
                    fh.write(f"{n} {max(ms * HEADROOM, FLOOR_MS):.0f}\n")
        print(f"registered {len(rows)} ceilings → {CEIL_FILE}")
        ceil = read_ceilings()

    try:
        la1, la5, _ = os.getloadavg()
        load = f"{la1:.2f} (1 min) / {la5:.2f} (5 min)"
    except OSError:
        load = "unavailable"
    # ⚠️ WHAT THIS LINE SAYS IS MEASURED, NOT INHERITED.  A first version quoted
    # scripts/kernel_ceilings.txt's "~15% high under load" — and batch 17 then
    # measured it: ordinary background load moves `Tests.Coverage` by NOTHING
    # (31 200 / 31 200 / 31 000 / 31 300 ms at one-minute loads of 2.20 / 4.08 / 3.42 / 3.88),
    # while CONTENTION WITH THE 56-ARM SELFTEST — a CPU-saturating Lean-and-ACL2
    # mix — moved it 4%-8% (32 500 and 33 600).  So the rule is not "load", it is
    # "contention for the same resource", and printing the inherited figure would
    # have been this repository's own D47 in the line added to prevent it.
    print(f"⚠️ LOAD AVERAGE DURING THIS MEASUREMENT: {load}. Measured effect on "
          f"Tests.Coverage: ordinary background load, none (four runs within "
          f"1% at loads 2.2-4.1); contention with the full selftest, 4%-8%. "
          f"A figure quoted without this line cannot be compared with another.")
    print(f"coverage-table rows (kernel-pinned rosterSize): {nrows}")
    print(f"{'MODULE':<24}{'KERNEL(ms)':>12}{'CEILING(ms)':>13}   VERDICT")
    for n, ms in rows:
        e = ceil.get(n)
        if e is None:
            v, fail = "UNREGISTERED ⛔", True
            cs = "-"
        else:
            kind, val = e
            c = val * nrows if kind == "perRow" else val
            if ms > c:
                v, fail = "OVER CEILING ⛔", True
            else:
                v = "ok" if kind == "abs" else f"ok ({val:.1f}/row x {nrows})"
            cs = f"{c:.0f}"
        print(f"{n:<24}{ms:>12.1f}{cs:>13}   {v}")
    print("---")
    cov = dict(rows).get("Tests.Coverage")
    if cov:
        thms, vecs = coverage_growth_denominator()
        if thms and vecs:
            print(f"Tests.Coverage growth law (REPORTED, not gated): {cov:.0f}ms "
                  f"= {cov/nrows:.1f} ms/row over {nrows} rows, "
                  f"{cov/nvecs:.2f} ms/vector over {nvecs} kernel-pinned vectors "
                  f"({thms} assertions)")
            print("  ⚠️  NEITHER unit is flat, and after batch 21 ONE "
                  "declaration (memDestSweep) is ~half the module while being "
                  "barely vector-driven. See D62 and D63 and the per-declaration "
                  "table below; do not gate on a whole-module density.")
            for line, name, ms in per_declaration("Tests/Coverage.lean")[:8]:
                print(f"    {ms:9.0f} ms  {name}  (Tests/Coverage.lean:{line})")
    print(f"total kernel time across the development: {total:.1f}ms")
    if fail:
        print("⛔ kernel-cost gate FAILED (over ceiling, or unregistered).")
        return 1
    print("kernel-cost gate: CLEAN")
    return 0

sys.exit(main())
