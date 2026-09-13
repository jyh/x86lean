#!/usr/bin/env python3
"""DOES A Δku GATE SEE THE ms GATE'S OWN RED-FIRST PLANT?  (seal:
docs/seals/2026-09-13-armA-constructor-plant.md)

`kernel_delta.py`'s arm 2 plants N constructors on `PrefetchHint` in
`X86/Syntax.lean` (plus N match arms) and requires the ms gate to go red. This
applies the SAME plant (imported, not retyped) in a detached worktree at HEAD and
reads `X86.Syntax` two ways: ku by `deterministic_cost.measure` (wrapped plus
unattributed), and kernel ms as the sum of `type checking` over one profiler pass
per repeat.

  ku_constructor_plant.py [--sizes 0,0,128,512] [--repeats 5] [--out F.json]

⛔ Kernel ms is one box, one session: a RATIO within the run, never an absolute.
"""
# ⛔ REFUSE AN UNKNOWN FLAG BEFORE ANY WORK HAPPENS — see portable.strict_flags.
if __name__ == "__main__":
    import os as _os, sys as _sys
    _sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
    from portable import strict_flags as _strict_flags
    _strict_flags(__file__)

import json
import os
import re
import shutil
import statistics
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import deterministic_cost as dc  # noqa: E402
from kernel_delta import plant_constructors  # noqa: E402  the gate's own plant

TC = re.compile(r"type checking took ([\d.]+)(ms|s)")


def arg(name, default):
    for i, a in enumerate(sys.argv):
        if a == name and i + 1 < len(sys.argv):
            return sys.argv[i + 1]
    return default


def module_ms(wt):
    r = subprocess.run(["lake", "env", "lean", "-D", "profiler=true", "-D", "profiler.threshold=0",
                        "--json", "X86/Syntax.lean"], cwd=wt, capture_output=True, text=True)
    tot, seen = 0.0, False
    errs = []
    for ln in r.stdout.splitlines():
        try:
            m = json.loads(ln)
        except json.JSONDecodeError:
            continue
        if m.get("severity") == "error":
            errs.append(m.get("data", "")[:200])
        for g in TC.finditer(m.get("data", "")):
            seen = True
            tot += float(g.group(1)) * (1000 if g.group(2) == "s" else 1)
    if r.returncode != 0 or errs or not seen:
        raise SystemExit(f"⛔ profiling X86/Syntax.lean failed (rc {r.returncode}, "
                         f"type-checking lines seen: {seen}):\n" + "\n".join(errs[:3]) + r.stderr[-800:])
    return tot


def main():
    sizes = [int(x) for x in arg("--sizes", "0,0,128,512").split(",")]
    repeats = int(arg("--repeats", "5"))
    out = arg("--out", None)
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True,
                          text=True).stdout.strip()
    res = {"head": head, "origin": dc.machine_id(),
           "load_start": os.getloadavg(), "repeats": repeats, "rows": []}
    print(f"HEAD {head[:9]}  load1 {res['load_start'][0]:.2f}  repeats {repeats}")
    for n in sizes:
        root = tempfile.mkdtemp(prefix="x86lean-kuctor-")
        wt = os.path.join(root, "wt")
        try:
            subprocess.run(["git", "worktree", "add", "--detach", wt, head], cwd=ROOT,
                           check=True, capture_output=True)
            if n:
                plant_constructors(n)(wt)
            reading, why = dc.measure(wt, "X86.Syntax")
            if reading is None:
                raise SystemExit(f"⛔ no ku reading at N={n}: {why}")
            ku = sum(reading["ku"].values()) + reading["orphans"]["orphan_kernel_unfoldings"]
            ms = [module_ms(wt) for _ in range(repeats)]
            row = {"n": n, "ku_total": ku, "ku_wrapped": sum(reading["ku"].values()),
                   "ku_unattributed": reading["orphans"]["orphan_kernel_unfoldings"],
                   "ms": ms, "ms_median": statistics.median(ms)}
            res["rows"].append(row)
            print(f"  N={n:<4} ku {ku:>8} (wrapped {row['ku_wrapped']}, unattributed "
                  f"{row['ku_unattributed']})  type checking median {row['ms_median']:.1f} ms  "
                  f"range {min(ms):.1f}-{max(ms):.1f}")
        finally:
            subprocess.run(["git", "worktree", "remove", "--force", wt], cwd=ROOT,
                           capture_output=True)
            shutil.rmtree(root, ignore_errors=True)
    res["load_end"] = os.getloadavg()
    print(f"load1 at end {res['load_end'][0]:.2f}")
    if out:
        with open(out, "w", encoding="utf-8") as fh:
            json.dump(res, fh, indent=1)
    return 0


if __name__ == "__main__":
    sys.exit(main())
