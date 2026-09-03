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
import os, re, subprocess, sys, glob

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
    print(f"total kernel time across the development: {total:.1f}ms")
    if fail:
        print("⛔ kernel-cost gate FAILED (over ceiling, or unregistered).")
        return 1
    print("kernel-cost gate: CLEAN")
    return 0

sys.exit(main())
