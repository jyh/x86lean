#!/usr/bin/env python3
"""WHAT FRACTION OF EACH MODULE'S KERNEL TIME CAN THE UNFOLDING COUNTER SEE?  (D229)

D228 measured the kernel `unfolded declarations` counter (ku) BLIND to literal
`Nat` arithmetic and to no-unfolding terms, and within ~2x of time on the kinds
that unfold. Until this census ku had been read on ONE module, `Tests.Coverage`,
the one chosen because it is the unfolding kind. This reads every module the
merge gate budgets, at the current tree, two ways:

  ku   `deterministic_cost.measure` — wrapped declarations PLUS the unattributed
       remainder, which is where `inductive`, `structure` and `deriving` land
  ms   one `lean -D profiler=true` pass: every `type checking took` line, summed,
       and CLASSIFIED BY THE SOURCE LINE AT THAT MESSAGE'S OWN POSITION (never by
       the nearest declaration above it — that rule put 140 ms of `inductive` and
       `deriving` time on a `def` with ku 0, measured 2026-09-13)

and prints ms per 1k ku per module beside D228's unfolding band.

  ku_module_census.py [--modules A,B,...] [--out F.json]

⛔ ms is one box, one session, one pass: read the RATIO and the SHARES, never the
absolute. ⛔ ku and ms are read on the same tree, which must be clean of `.lean`
changes (refused otherwise: a census of a tree nobody committed describes nothing).
"""
import json
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import deterministic_cost as dc  # noqa: E402

BAND = (1.652, 3.411)   # D228 run 4: K4 and K5, ms per 1k ku on the unfolding kinds
TC = re.compile(r"type checking took ([\d.]+)(ms|s)")
DEFAULT = ["X86.Basic", "X86.Syntax", "X86.Theorems", "X86.Program", "Tests.Anchors",
           "Tests.Program", "Tests.Nonvacuity", "Tests.VectorRuns", "X86Native", "Tests.Coverage"]


def classify(src_line):
    s = src_line.strip()
    if re.match(r"(private |protected )*(inductive|structure|class)\b", s):
        return "inductive/structure"
    if s.startswith("deriving") or " deriving " in s:
        return "deriving"
    if re.match(r"(@\[[^\]]*\]\s*)?(private |protected |partial |noncomputable )*"
                r"(theorem|lemma|example)\b", s):
        return "theorem"
    if re.match(r"(@\[[^\]]*\]\s*)?(private |protected |partial |noncomputable )*"
                r"(def|abbrev|instance)\b", s):
        return "def"
    return "other"


def unwrapped_ku(module, header_only=False):
    """ku with the diagnostics options and NO wrapper — the reading the instrument must reproduce.
    `header_only` elaborates the instrument's own header alone, which is what it costs."""
    path = module.replace(".", "/") + ".lean"
    src = [] if header_only else open(os.path.join(ROOT, path), encoding="utf-8").read().split("\n")
    imps = [i for i, l in enumerate(src) if l.startswith("import ")]
    at = max(imps) + 1 if imps else 0
    body = dc.HB_HEADER if header_only else "import Lean\nset_option diagnostics true\nset_option diagnostics.threshold 1\n"
    tmp = os.path.join(tempfile.gettempdir(), f"x86lean-census-{module}-{os.getpid()}.lean")
    with open(tmp, "w", encoding="utf-8") as fh:
        fh.write("\n".join(src[:at] + [body] + src[at:]))
    try:
        r = subprocess.run(["lake", "env", "lean", "--json", tmp], cwd=ROOT, capture_output=True, text=True)
    finally:
        os.remove(tmp)
    k, errs = 0, []
    for ln in r.stdout.splitlines():
        try:
            m = json.loads(ln)
        except json.JSONDecodeError:
            continue
        if m.get("severity") == "error":
            errs.append(m.get("data", "")[:200])
        if "[diag]" in m.get("data", ""):
            k += dc._diag_counts(m["data"])[0]
    if r.returncode != 0 or errs:
        raise SystemExit(f"⛔ the unwrapped reading of {module} failed (rc {r.returncode}):\n"
                         + "\n".join(errs[:3]) + r.stderr[-600:])
    return k


def profile(module):
    path = module.replace(".", "/") + ".lean"
    src = open(os.path.join(ROOT, path), encoding="utf-8").read().split("\n")
    r = subprocess.run(["lake", "env", "lean", "-D", "profiler=true", "-D", "profiler.threshold=0",
                        "--json", path], cwd=ROOT, capture_output=True, text=True)
    kinds, total, errs = {}, 0.0, []
    for ln in r.stdout.splitlines():
        try:
            m = json.loads(ln)
        except json.JSONDecodeError:
            continue
        if m.get("severity") == "error":
            errs.append(m.get("data", "")[:200])
        for g in TC.finditer(m.get("data", "")):
            v = float(g.group(1)) * (1000 if g.group(2) == "s" else 1)
            k = classify(src[m["pos"]["line"] - 1])
            kinds[k] = kinds.get(k, 0.0) + v
            total += v
    if r.returncode != 0 or errs or total == 0:
        raise SystemExit(f"⛔ profiling {path} failed (rc {r.returncode}, total {total}):\n"
                         + "\n".join(errs[:3]) + r.stderr[-600:])
    return total, kinds


def main():
    mods = DEFAULT
    out = None
    for i, a in enumerate(sys.argv):
        if a == "--modules":
            mods = sys.argv[i + 1].split(",")
        if a == "--out":
            out = sys.argv[i + 1]
    dirty = subprocess.run(["git", "status", "--porcelain", "--", "*.lean"], cwd=ROOT,
                           capture_output=True, text=True).stdout.strip()
    if dirty:
        raise SystemExit(f"⛔ .lean changes in the tree; refusing:\n{dirty}")
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True,
                          text=True).stdout.strip()
    res = {"head": head, "origin": dc.machine_id(), "load_start": os.getloadavg(),
           "band": BAND, "modules": {}}
    print(f"HEAD {head[:9]}  load1 {res['load_start'][0]:.2f}  band {BAND[0]}-{BAND[1]} ms/1k ku (D228)")
    print(f"{'module':18} {'ms':>8} {'ku':>9} {'ms/1k ku':>9}  {'x band top':>10}  shares of ms")
    # ⛔ CONSERVATION, DERIVED (D229): the wrapped total must equal the unwrapped total plus what
    # the header alone costs. X86.Basic failed this by -4,437 before the name-collision repair,
    # and nothing downstream of a summed map could have noticed.
    hdr = unwrapped_ku("X86.Basic", header_only=True)
    res["header_ku"] = hdr
    print(f"the instrument's header alone costs {hdr} ku")
    for mod in mods:
        reading, why = dc.measure(ROOT, mod)
        if reading is None:
            raise SystemExit(f"⛔ no ku reading for {mod}: {why}")
        ku = sum(reading["ku"].values()) + reading["orphans"]["orphan_kernel_unfoldings"]
        raw = unwrapped_ku(mod)
        if ku != raw + hdr:
            raise SystemExit(f"⛔ {mod}: wrapped ku {ku} != unwrapped {raw} + header {hdr} "
                             f"(off by {ku - raw - hdr:+d}) — the instrument does not conserve here")
        ms, kinds = profile(mod)
        ratio = None if raw == 0 else 1000.0 * ms / raw   # the MODULE's ku, without the header
        res["modules"][mod] = {"ms": ms, "ku": ku, "ku_unwrapped": raw, "ku_unattributed":
                               reading["orphans"]["orphan_kernel_unfoldings"],
                               "ms_per_1k_ku": ratio, "ms_by_kind": kinds}
        shares = " · ".join(f"{k} {100 * v / ms:.0f}%" for k, v in
                            sorted(kinds.items(), key=lambda x: -x[1]) if v / ms >= 0.05)
        rt = "BLIND" if ratio is None else f"{ratio:9.2f}"
        over = "" if ratio is None else f"{ratio / BAND[1]:9.1f}x"
        print(f"{mod:18} {ms:8.1f} {ku:9d} {rt:>9}  {over:>10}  {shares}")
    res["load_end"] = os.getloadavg()
    print(f"load1 at end {res['load_end'][0]:.2f}")
    if out:
        with open(out, "w", encoding="utf-8") as fh:
            json.dump(res, fh, indent=1)
    return 0


if __name__ == "__main__":
    sys.exit(main())
