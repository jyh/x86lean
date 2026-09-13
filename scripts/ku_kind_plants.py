#!/usr/bin/env python3
"""DOES THE KERNEL UNFOLDING COUNTER SEE EVERY KIND OF KERNEL WORK?  (seal:
docs/seals/2026-09-13-armA-accuracy-by-kind.md)

ARM A gates `Δku`, the kernel's `unfolded declarations` counter, instead of
kernel milliseconds.  Its zero band (D189) makes it DECIDABLE.  This asks
whether it is ACCURATE: every earlier reading held the KIND of kernel work
fixed, so a kind the counter cannot see would pass a Δku gate with an exact,
confident zero at any size.

Five plant kinds, one declaration per generated file, each at three sizes.
Each file is elaborated in two SEPARATE passes so neither instrument perturbs
the other: one with `diagnostics` (ku), and `--repeats` with `profiler`
(kernel `type checking` ms, median and range reported).

  ku_kind_plants.py [--repeats 5] [--out F.json]
  ku_kind_plants.py --selftest

⛔ Kernel ms here is one box, one session: use it for RATIOS within a run,
never as an absolute.
"""
import json
import os
import platform
import re
import statistics
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
from deterministic_cost import _diag_counts  # noqa: E402  the [kernel]-only parser

MOD = 1000000007


def k1(n):
    return f"theorem plant : (List.replicate {n} 1).foldr (· + ·) 0 = {n} := by decide"


def k2(n):
    return f"theorem plant : 3 ^ {n} % {MOD} = {pow(3, n, MOD)} := by decide"


def k3(n):
    ty = " ∧ ".join(["True"] * n)
    tm = "trivial"
    for _ in range(n - 1):
        tm = f"And.intro trivial ({tm})"
    return f"theorem plant : {ty} :=\n  {tm}"


def k4(n):
    cs = []
    for i in range(n):
        a = (0x9E3779B97F4A7C15 * (i + 1)) % 2**64
        b = (0xC2B2AE3D27D4EB4F * (i + 7)) % 2**64
        cs.append(f"(({a}#64) + ({b}#64) = ({(a + b) % 2**64}#64))")
    return "theorem plant : " + " ∧ ".join(cs) + " := by decide"


def k5(n):
    s = "a" * n
    return f'theorem plant : "{s}" ++ "b" = "{s}b" := by decide'


KINDS = {
    "K1 list-decide": (k1, [400, 800, 1600]),
    "K2 gmp-literal": (k2, [1000000, 4000000, 16000000]),  # kept under 2^24 (believed, not verified, to bound the kernel's literal Nat.pow)
    "K3 inference": (k3, [250, 500, 1000]),
    "K4 bitvec-decide": (k4, [12, 25, 50]),  # 100 conjuncts: `Decidable` synthesis fails (measured 2026-09-13)
    "K5 string-decide": (k5, [200, 400, 800]),
}

# ⛔ `exponentiation.threshold` (default 256): WITHOUT it K2 is refused at elaboration with
#   `maximum recursion depth has been reached` (measured 2026-09-13 at 80,000 / 1,000,000 /
#   4,000,000); WITH it all three elaborate at ku 10. It changes what the elaborator agrees to do,
#   not the kind of work the kernel is given.
DIAG = "set_option diagnostics true\nset_option diagnostics.threshold 1\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option exponentiation.threshold 20000000\n"
PROF = "set_option profiler true\nset_option profiler.threshold 0\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option exponentiation.threshold 20000000\n"
TC = re.compile(r"type checking took ([\d.]+)(ms|s)")


def elaborate(body, header, tmpdir, tag):
    path = os.path.join(tmpdir, f"{tag}.lean")
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(header + body + "\n")
    r = subprocess.run(["lean", "--json", path], cwd=ROOT,
                       capture_output=True, text=True)
    msgs, errs = [], []
    for ln in r.stdout.splitlines():
        try:
            m = json.loads(ln)
        except json.JSONDecodeError:
            continue
        (errs if m.get("severity") == "error" else msgs).append(m.get("data", ""))
    if r.returncode != 0 or errs:
        # ⛔ say what it saw: a refusal that discards the child's output is a re-run elsewhere
        raise SystemExit(f"⛔ plant {tag} did not elaborate (rc {r.returncode}):\n"
                         + "\n".join(e[:400] for e in errs[:3]) + r.stderr[-800:])
    return msgs


def read_ku(body, tmpdir, tag):
    k = 0
    seen = False
    for d in elaborate(body, DIAG, tmpdir, tag + "-ku"):
        if "[diag]" in d:
            seen = True
            k += _diag_counts(d)[0]
    return k, seen


def read_ms(body, tmpdir, tag):
    for d in elaborate(body, PROF, tmpdir, tag + "-ms"):
        for g in TC.finditer(d):
            v = float(g.group(1))
            return v * 1000 if g.group(2) == "s" else v
    raise SystemExit(f"⛔ plant {tag}: the profiler printed no `type checking` line — "
                     "a missing reading is not a zero")


def run(repeats, out):
    load = os.getloadavg()
    print(f"CONDITIONS load1 {load[0]:.2f} load5 {load[1]:.2f} repeats {repeats}")
    lean = subprocess.run(["lean", "--version"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(["git", "status", "--porcelain", "--", "scripts/ku_kind_plants.py"],
                           cwd=ROOT, capture_output=True, text=True).stdout.strip()
    origin = {"lean": lean, "repo_head": head, "tool_uncommitted": bool(dirty),
              "platform": sys.platform, "machine": platform.machine(), "cpus": os.cpu_count()}
    print(f"ORIGIN {json.dumps(origin)}")
    res = {"origin": origin, "conditions": {"load_start": load, "repeats": repeats}, "kinds": {}}
    with tempfile.TemporaryDirectory(prefix="x86lean-kuplant-") as tmp:
        c1, _ = read_ku(k1(400), tmp, "control-a")
        c2, _ = read_ku(k1(400), tmp, "control-b")
        print(f"A1 CONTROL  same file twice: ku {c1} and {c2}  Δ {c2 - c1}")
        res["control"] = [c1, c2]
        for kind, (gen, sizes) in KINDS.items():
            rows = []
            for n in sizes:
                body = gen(n)
                tag = kind.split()[0] + f"-{n}"
                ku, seen = read_ku(body, tmp, tag)
                ms = [read_ms(body, tmp, tag) for _ in range(repeats)]
                med = statistics.median(ms)
                rows.append({"n": n, "ku": ku, "diag_seen": seen, "ms": ms, "ms_median": med})
                print(f"  {kind:18} n={n:<7} ku {ku:>9}  ms median {med:9.1f}  "
                      f"range {min(ms):.1f}-{max(ms):.1f}{'' if seen else '  (no [diag] message)'}")
            a, b = rows[-2], rows[-1]
            dku, dms = b["ku"] - a["ku"], b["ms_median"] - a["ms_median"]
            ratio = None if dku <= 10 else 1000.0 * dms / dku
            rise = rows[-1]["ms_median"] / rows[0]["ms_median"] if rows[0]["ms_median"] > 0 else None
            res["kinds"][kind] = {"rows": rows, "marginal_dku": dku, "marginal_dms": dms,
                                  "ms_per_1k_ku": ratio, "ms_rise_small_to_large": rise,
                                  "ku_span": rows[-1]["ku"] - rows[0]["ku"]}
            rtxt = "BLIND (Δku<=10)" if ratio is None else f"{ratio:.3f}"
            print(f"  {kind:18} marginal Δku {dku}  Δms {dms:.1f}  ms/1k ku {rtxt}  "
                  f"ms rise {'n/a' if rise is None else f'{rise:.2f}x'}")
    res["conditions"]["load_end"] = os.getloadavg()
    print(f"CONDITIONS load1 at end {res['conditions']['load_end'][0]:.2f}")
    if out:
        with open(out, "w", encoding="utf-8") as fh:
            json.dump(res, fh, indent=1)
    return res


def selftest():
    """The generators must produce what the seal says, and the ku parser must read
    ONLY the [kernel] section. Pure; no Lean."""
    fails = []
    if "3 ^ 5 %" not in k2(5) or str(pow(3, 5, MOD)) not in k2(5):
        fails.append("K2 does not state 3^n mod p with its value")
    if k3(3).count("True") != 3 or k3(3).count("And.intro") != 2:
        fails.append("K3 conjunct/term counts wrong")
    if k4(2).count("#64") != 6:
        fails.append("K4 does not carry 3 BitVec literals per conjunct")
    msg = ("[diag] Diagnostics\n  [reduction] unfolded declarations (max: 9, num: 1):\n"
           "    Nat.rec ↦ 9\n  [kernel] unfolded declarations (max: 5, num: 2):\n"
           "    List.foldr ↦ 5\n    List.replicate ↦ 4\n")
    if _diag_counts(msg)[0] != 9:
        fails.append(f"kernel parse read {_diag_counts(msg)[0]}, want 9 (the reduction 9 must not count)")
    print("SELFTEST", "FAIL" if fails else "PASS", *fails, sep="\n  " if fails else " ")
    return 1 if fails else 0


def main():
    if "--selftest" in sys.argv:
        return selftest()
    rep = 5
    out = None
    for i, a in enumerate(sys.argv):
        if a == "--repeats":
            rep = int(sys.argv[i + 1])
        if a == "--out":
            out = sys.argv[i + 1]
    run(rep, out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
