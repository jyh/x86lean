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
# ⭐⭐ P2 BATCH 1 (D75) — THE CEILINGS PATH IS A SEAM, AND IT IS A SEAM BECAUSE A
# COMMIT SHIPPED A PLANTED DEFECT.  `--selftest` used to mutate this file IN THE
# TREE and restore it afterwards; `afcde4a` was staged inside that window and
# pushed `@decl vectorCoverageXX` — the exact string the third arm plants — to
# both remotes.  ⇒ A PROBE THAT EDITS THE TREE MAKES `git add -A` A RACE, and
# the window is invisible: this script's output says nothing about the tree, and
# the planted line is one character from a legitimate one.  With the seam the
# probe writes only under TMPDIR and the repository is never touched, which is
# the same move the P1 seal made for `scripts/sharing_redprobe.sh` (a467a22).
CEIL_FILE = os.environ.get("X86LEAN_CEIL_FILE", "scripts/kernel_ceilings.txt")
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
DECL_TAG    = "@decl"     # ⭐ an ABSOLUTE ceiling on one named declaration
TAIL_TAG    = "@tail"     # ⭐ an ABSOLUTE ceiling on everything else in the module

# ⭐⭐ THE PER-DECLARATION GATE (P1 seal, D68) — THE UNIT PROBLEM, ENDED.
#
# The helm, 13:37: *"a number measured in the wrong unit and applied with care is
# still the wrong number."*  `Tests.Coverage` was gated PER ROW, and D62 had
# already proved the row is not the unit: after D63 one declaration is half the
# module and is barely row- or vector-driven.  Every refinement since batch 14
# went into the MARGIN (x1.6, worst-of-N, loads recorded) and none into the
# DENOMINATOR.
#
# ⇒ An ABSOLUTE millisecond ceiling on a NAMED DECLARATION has no denominator, so
# it cannot be in the wrong unit.  D62 designed exactly this and recorded it as
# blocked; D63 removed the reason it looked hard.
#
# ⛔ AND THE MEASUREMENT REFUSED THE NAIVE VERSION OF IT, which was to gate every
# declaration.  Four profiles on a quiet machine (one-minute loads 3.25-5.37):
#
#     memDestSweep                       11 800 · 12 100 · 11 900 · 11 900   2.5%
#     pre_states_have_a_returnable_frame  1 800 ·  1 800 ·  1 690 ·  1 820   7.7%
#     vectorCoverage                      1 440 ·  1 410 ·  1 410 ·  1 450   2.8%
#     ---------------------------------------------------------------- gateable
#     table_mnemonics_subset_roster          708 ·   513 ·     …             38%
#     bitcnt_encodable_forms_…               912 ·   809 ·   844 ·    919    13%
#     (and the COUNT of attributed declarations moved 26 / 27 / 28 between runs)
#
# ⇒ 🔑 **A PER-DECLARATION CEILING IS SOUND ONLY FOR DECLARATIONS BIG ENOUGH TO
# MEASURE.**  Below about a second the run-to-run noise is larger than any
# sensible margin, and a gate there would need relaxing on somebody's schedule —
# which is the chore D62 warned about, one layer down.
#
# So: the three declarations above a second are gated INDIVIDUALLY, and
# everything else is gated as ONE ABSOLUTE TAIL (module total minus the gated
# declarations).  Neither number divides by anything.
# ⚠️ A gated declaration MISSING from the profile is an ERROR, never a pass: a
# declaration that has been renamed or deleted takes its ceiling with it, and a
# gate that cannot find its subject reports a pass.

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
# ⛔ AND THE TECHNIQUE IS NOT GENERAL, WHICH WAS MEASURED RATHER THAN LEFT TO BE
# OVER-APPLIED.  NINETEEN theorems here reduce `preStates 1 8` -- more sharing by
# count than the six that were merged -- and merging four of them saves 7%
# (786 -> 733 ms, back to back).  ⇒ 🔑 SHARING PAYS WHERE THE SHARED SUBJECT'S
# REDUCTION IS EXPENSIVE, NOT WHERE THE SUBJECT IS MERELY SHARED.  A dedup or a
# character sweep costs seconds; 86 records built from simple constructors do
# not, and the per-state PREDICATE, which is where those theorems' time goes,
# is different in each and cannot be shared at all.  D63 §5.
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
    """Returns ({module: (kind, value)}, {module: {decl: ms}}, {module: tail_ms})."""
    d, decls, tails = {}, {}, {}
    if os.path.exists(CEIL_FILE):
        for line in open(CEIL_FILE):
            line = line.split("#")[0].strip()
            if not line:
                continue
            parts = line.split()
            if len(parts) == 4 and parts[1] == DECL_TAG:
                decls.setdefault(parts[0], {})[parts[2]] = float(parts[3])
            elif len(parts) == 3 and parts[1] == TAIL_TAG:
                tails[parts[0]] = float(parts[2])
            elif len(parts) == 3 and parts[1] == PER_ROW_TAG:
                d[parts[0]] = ("perRow", float(parts[2]))
            elif len(parts) == 2:
                d[parts[0]] = ("abs", float(parts[1]))
            else:
                print(f"⛔ unparseable ceiling line: {line!r}")
                sys.exit(2)
    return d, decls, tails

def selftest():
    """⛔ DRIVE THE PER-DECLARATION GATE RED, EACH FAILURE MODE ALONE.

    A ceiling gate is the easiest kind to have and not have: it passes when the
    numbers are fine, and it also passes when it has stopped looking. This one
    has FOUR ways to stop looking and each is planted separately, in the CEILING
    FILE rather than in the model — a probe that edits its subject can leave it
    edited."""
    import shutil, tempfile
    saved = open(CEIL_FILE).read()
    probe_dir = tempfile.mkdtemp(prefix="x86lean-ceilprobe-")
    probe_ceil = os.path.join(probe_dir, "kernel_ceilings.txt")
    arms = [
        ("a declaration OVER its ceiling",
         lambda t: re.sub(r"(@decl memDestSweep )\S+", r"\g<1>100", t),
         "OVER"),
        ("the TAIL over its ceiling",
         lambda t: re.sub(r"(@tail )\S+", r"\g<1>100", t), "OVER"),
        # ⛔ the arm that matters most: a gated declaration that is renamed or
        # deleted takes its ceiling with it, and a gate that cannot find its
        # subject must not report a pass.
        ("a gated declaration that is NOT in the profile",
         lambda t: t.replace("@decl vectorCoverage ", "@decl vectorCoverageXX "),
         "NOT FOUND"),
        # ⛔ and the way this design could be used to become ungated: gate a few
        # declarations, omit the tail, and the rest of the module is free.
        ("declarations gated with NO tail ceiling",
         lambda t: re.sub(r"^.*@tail.*$", "", t, flags=re.M), "no @tail"),
    ]
    bad = []
    try:
        for name, mutate, expect in arms:
            # ⛔ THE MUTATION GOES TO A TEMP FILE AND THE CHILD IS POINTED AT IT.
            # Nothing under the repository is written; see D75 and the note on
            # CEIL_FILE for the commit that paid for this line.
            open(probe_ceil, "w").write(mutate(saved))
            r = subprocess.run([sys.executable, os.path.abspath(__file__)],
                               capture_output=True, text=True,
                               env=dict(os.environ, X86LEAN_CEIL_FILE=probe_ceil))
            out = r.stdout + r.stderr
            ok = r.returncode != 0 and expect in out
            print(("  ✔ " if ok else "  ⛔ ") + name +
                  ("" if ok else f"   (rc={r.returncode}, expected {expect!r})"))
            if not ok:
                bad.append(name)
    finally:
        shutil.rmtree(probe_dir, ignore_errors=True)
    # ⭐ THE POSITIVE CONTROL: four reds prove the gate can fail; only this proves
    # it can pass.
    #
    # ⚠️ ITS BYTE CHECK IS NOW TRIVIALLY TRUE, AND IS KEPT ON PURPOSE.  With the
    # seam the probe cannot write the shipped file, so "byte-restored" is no
    # longer a fact about a restore — it is the REGRESSION GUARD if the seam is
    # ever removed and the mutations come back into the tree.  Stated rather
    # than left to read as a live check (D75).
    r = subprocess.run([sys.executable, os.path.abspath(__file__)],
                       capture_output=True, text=True)
    ok = r.returncode == 0 and open(CEIL_FILE).read() == saved
    print(("  ✔ " if ok else "  ⛔ ") +
          "control: the shipped ceilings PASS, and the tree file is UNTOUCHED")
    # ⛔⛔ AND WHEN IT FAILS, PRINT WHY.  This arm used to DISCARD `r.stdout`, so a
    # CI log said only "a control failed" and never named the declaration that
    # was over its ceiling — the reading a developer actually needs, and the one
    # that cannot be recovered from a remote runner afterwards.  It cost two
    # diagnosis cycles (D94) before it was worth fixing: both times the answer
    # was only obtainable by re-running the whole gate locally, on a DIFFERENT
    # machine from the one that failed, which for a TIMING gate is precisely the
    # measurement that cannot be transferred.
    #
    # ⇒ 🔑 A GATE THAT REFUSES MUST SAY WHAT IT SAW.  A refusal with no reading
    # attached turns every remote failure into a local re-run, and for anything
    # machine-dependent the local re-run answers a different question.
    if not ok:
        if r.returncode == 0:
            print("     (the ceiling file was MODIFIED by the probe — a restore failed)")
        print("     ── the failing run's own output ──")
        for line in (r.stdout + r.stderr).splitlines():
            print("     " + line)
    if not ok:
        bad.append("control")
    if bad:
        print(f"kernel-cost selftest: FAIL ({len(bad)} of {len(arms)+1} arms)")
        return 1
    print(f"kernel-cost selftest: PASS ({len(arms)+1} arms — every way this gate "
          f"could stop looking, driven separately, plus the control)")
    return 0


def main():
    if "--selftest" in sys.argv:
        return selftest()
    register = "--register" in sys.argv
    subprocess.run(["lake", "build", "X86", "Tests", "X86Native"],
                   capture_output=True, text=True)
    ceil, decl_ceils, tail_ceils = read_ceilings()
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
        ceil, decl_ceils, tail_ceils = read_ceilings()

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
        if e is None and n in decl_ceils:
            # ⚠️ NOT unregistered: gated PER DECLARATION below, which is a
            # stronger statement than a module total and is why the module total
            # has no ceiling of its own. The tail ceiling covers the remainder,
            # and the block below REFUSES if a module gates declarations without
            # one — so this branch cannot become a way to be ungated.
            v, cs = "gated per declaration ↓", "-"
        elif e is None:
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
    # ⭐⭐ THE PER-DECLARATION GATE.  No denominator anywhere in it.
    for mod, want in sorted(decl_ceils.items()):
        f = [x for x in modules() if mod_name(x) == mod]
        if not f:
            print(f"⛔ {mod} has per-declaration ceilings but no source file.")
            fail = True
            continue
        got = {name: ms for _l, name, ms in per_declaration(f[0])}
        total = dict(rows).get(mod)
        print(f"--- {mod}: per-declaration ceilings (ABSOLUTE ms, no denominator)")
        named = 0.0
        for name, c in sorted(want.items(), key=lambda kv: -kv[1]):
            ms = got.get(name)
            if ms is None:
                # ⛔ A MISSING READING IS NOT A ZERO.  A renamed or deleted
                # declaration takes its ceiling with it, and this gate must not
                # go quiet when its subject leaves.
                print(f"  ⛔ {name:44s} NOT FOUND in the profile — renamed, "
                      f"deleted, or now below the profiler threshold")
                fail = True
                continue
            named += ms
            v = "OVER ⛔" if ms > c else "ok"
            if ms > c:
                fail = True
            print(f"  {name:44s}{ms:>9.0f}{c:>9.0f}   {v}")
        tc = tail_ceils.get(mod)
        if tc is not None and total is not None:
            tail = total - named
            v = "OVER ⛔" if tail > tc else "ok"
            if tail > tc:
                fail = True
            print(f"  {'(everything else in the module)':44s}{tail:>9.0f}"
                  f"{tc:>9.0f}   {v}")
        elif tc is None:
            print(f"  ⛔ {mod} gates declarations but has no {TAIL_TAG} ceiling, "
                  f"so the rest of the module is ungated.")
            fail = True

    print("---")
    cov = dict(rows).get("Tests.Coverage")
    if cov:
        thms, vecs = coverage_growth_denominator()
        if thms and vecs:
            print(f"Tests.Coverage growth law (REPORTED, not gated): {cov:.0f}ms "
                  f"= {cov/nrows:.1f} ms/row over {nrows} rows, "
                  f"{cov/nvecs:.2f} ms/vector over {nvecs} kernel-pinned vectors "
                  f"({thms} assertions)")
            # ⛔ THIS SENTENCE USED TO NAME `memDestSweep` AS "~half the module"
            # AS A LITERAL, and P2 batch 11 took it from 18 500 to 4 400 ms —
            # 23% — while the sentence went on saying half.  A gate's own OUTPUT
            # is prose too, and prose in a tool nobody re-reads is exactly the
            # ungated claim this repository keeps paying for (D65, D94, D102).
            # ⇒ The share and the name are DERIVED from the profile now, so the
            # warning cannot describe a distribution the tool is not seeing.
            decls = per_declaration("Tests/Coverage.lean")
            top_ms, top_name = (decls[0][2], decls[0][1]) if decls else (0.0, "?")
            print(f"  ⚠️  NEITHER unit is flat: the largest single declaration "
                  f"({top_name}) is {100.0*top_ms/cov:.0f}% of the module on its "
                  f"own. See D62, D63 and D103 and the per-declaration table "
                  f"below; do not gate on a whole-module density.")
            for line, name, ms in decls[:8]:
                print(f"    {ms:9.0f} ms  {name}  (Tests/Coverage.lean:{line})")
    print(f"total kernel time across the development: {total:.1f}ms")
    if fail:
        print("⛔ kernel-cost gate FAILED (over ceiling, or unregistered).")
        return 1
    print("kernel-cost gate: CLEAN")
    return 0

sys.exit(main())
