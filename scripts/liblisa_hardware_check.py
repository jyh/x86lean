#!/usr/bin/env python3
"""Read the rules behind `Main.lean knownDivergences` off libLISA's processor-synthesized semantics.

WHY (D221).  Every declared divergence says x86isa is wrong and names K and the SDM as the authorities that
agree with x86lean. libLISA judges K incorrect on 18-28 instruction variants per machine (D220), so the
arbiter is fallible, and neither of the two authorities is a processor. libLISA's semantics were
synthesized by executing instructions on five CPUs. A dataflow's `inputs` are the state that bit flips on
the CPU showed the output to depend on, so a byte absent from every output's inputs is a byte the
processor was observed NOT to read.

⛔ THE ENCODINGS ARE NOT OURS, AND THE VERDICT IS ABOUT A PROXY.  libLISA's population holds no encoding
that starts with a 66, F2 or F3 prefix (0 of 117,229 bitpatterns on the Xeon), so the legacy-SSE bytes
x86lean tests (`660ff1c1`, `660f6ec1`, ...) are absent. What it has is the VEX.128 form of the same
instruction, which the SDM gives the same count rule and the same low-half result. A PASS here is a
processor reading of the RULE on that form; it is not a reading of the legacy encoding.

THE RULES DECIDED, per CPU file:
  D108 (8 packed shifts)  the xmm0 result reads count-source xmm1 bytes 0..7 and no others
  D93  (movd, movq)       xmm0 above the moved width is written from NO input, as the constant ZERO
CONTROLS: imul must resolve; vpxor must read xmm1 bytes 8..15 (an upper-half read IS visible when it
exists); the legacy-66 pxor must be absent (the census); five plants must each turn a PASS into a FAIL.

Inputs: the JSONL that `liblisa-semantics-tool server <cpu>.json` prints for `--queries` on stdin (the
tool panics on the trailing EOF, after answering; the line count below is the gate, not its exit code).
Recipe: docs/LIBLISA-HARDWARE-CHECK-2026-09-12.md.

Exit 0 clean; 1 on a finding; 2 when it cannot find its subject (a line-count mismatch, or a
knownDivergences entry with no proxy here).
"""
import argparse, copy, json, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# knownDivergences vec -> (proxy name, VEX.128 bytes: op xmm0 with xmm1 / a GPR, rule)
PROXY = {
    "psllw_x": ("vpsllw", "c5f9f1c1", "count"), "pslld_x": ("vpslld", "c5f9f2c1", "count"),
    "psllq_x": ("vpsllq", "c5f9f3c1", "count"), "psrlw_x": ("vpsrlw", "c5f9d1c1", "count"),
    "psrld_x": ("vpsrld", "c5f9d2c1", "count"), "psrlq_x": ("vpsrlq", "c5f9d3c1", "count"),
    "psraw_x": ("vpsraw", "c5f9e1c1", "count"), "psrad_x": ("vpsrad", "c5f9e2c1", "count"),
    "movd_to_x": ("vmovd", "c5f96ec1", "clear4"), "movq_to_x": ("vmovq", "c4e1f96ec1", "clear8"),
}
CONTROLS = [("ctl_imul", "0fafc3"), ("ctl_vpxor", "c5f9efc1"), ("ctl_legacy66_pxor", "660fefc1")]


def queries():
    return CONTROLS + [(v, PROXY[v][1]) for v in sorted(PROXY)]


def declared_vecs(root=ROOT):
    src = open(os.path.join(root, "Main.lean")).read()
    m = re.search(r"def knownDivergences : List KnownDivergence :=(.*?)\n\ndef ", src, re.S)
    if not m:
        return None
    return set(re.findall(r'vec := "([^"]+)"', m.group(1)))


def reg_bytes(loc, want):
    r = loc.get("Dest", loc).get("Reg") if isinstance(loc, dict) else None
    if not r:
        return set()
    name = r["reg"]
    tag = ("xmm%d" % name["Xmm"]["Reg"]) if "Xmm" in name else name.get("GpReg", "").lower()
    return set(range(r["size"]["start_byte"], r["size"]["end_byte"] + 1)) if tag == want else set()


def consts_of(expr):
    if isinstance(expr, dict):
        return [expr["Const"]["data"]] if "Const" in expr else [c for v in expr.values() for c in consts_of(v)]
    return [c for v in expr for c in consts_of(v)] if isinstance(expr, list) else []


def xmm0_outputs(rec):
    return [w for w in rec["write_targets"] if reg_bytes(w["write_target"], "xmm0")]


def read_of(outs, src):
    return set().union(set(), *(reg_bytes(i, src) for w in outs for i in w["inputs"]))


def written(outs):
    return set().union(set(), *(reg_bytes(w["write_target"], "xmm0") for w in outs))


def verdict(name, rec):
    if name == "ctl_legacy66_pxor":
        return ("PASS", "absent from the population") if rec is None else ("FAIL", "a legacy-66 encoding matched")
    if rec is None:
        return ("FAIL", "null: unmatched OR a failed synthesis -- UNMEASURED, never agreement")
    outs = xmm0_outputs(rec)
    if name == "ctl_imul":
        return ("PASS", "%d write targets" % len(rec["write_targets"]))
    if name == "ctl_vpxor":
        up = read_of(outs, "xmm1") & set(range(8, 16))
        return ("PASS" if up == set(range(8, 16)) else "FAIL", "xmm1 bytes 8..15 read: %s" % sorted(up))
    rule = PROXY[name][2]
    if rule == "count":
        rd = read_of(outs, "xmm1")
        ok = rd == set(range(8)) and set(range(16)) <= written(outs)
        return ("PASS" if ok else "FAIL", "count-source xmm1 bytes read %s" % sorted(rd))
    lo = int(rule[len("clear"):])
    upper = [w for w in outs if set(range(lo, 16)) >= reg_bytes(w["write_target"], "xmm0")]
    n_in = sum(len(w["inputs"]) for w in upper)
    consts = [c for w in upper for c in consts_of(w["computation"])]
    zero = bool(consts) and all(set(c.lower().removeprefix("#x")) <= {"0"} for c in consts)
    low_gpr = read_of([w for w in outs if max(reg_bytes(w["write_target"], "xmm0")) < lo], "rcx")
    ok = written(upper) == set(range(lo, 16)) and n_in == 0 and zero and low_gpr == set(range(lo))
    return ("PASS" if ok else "FAIL",
            "xmm0[%d..15]: %d inputs, constant zero=%s; rcx bytes into xmm0[0..%d]: %s"
            % (lo, n_in, zero, lo - 1, sorted(low_gpr)))


def plants(recs):
    """Each plant must turn a PASS into a FAIL; returns how many did NOT."""
    missed = 0
    r = copy.deepcopy(recs["psllw_x"])
    for w in xmm0_outputs(r):
        w["inputs"].append({"Dest": {"Reg": {"reg": {"Xmm": {"Reg": 1}}, "size": {"start_byte": 8, "end_byte": 15}}}})
    missed += verdict("psllw_x", r)[0] != "FAIL"
    r = copy.deepcopy(recs["movd_to_x"])
    for w in xmm0_outputs(r):
        if min(reg_bytes(w["write_target"], "xmm0")) >= 4:
            w["inputs"].append({"Dest": {"Reg": {"reg": {"Xmm": {"Reg": 0}}, "size": {"start_byte": 4, "end_byte": 4}}}})
    missed += verdict("movd_to_x", r)[0] != "FAIL"
    r = copy.deepcopy(recs["ctl_vpxor"])
    for w in xmm0_outputs(r):
        w["inputs"] = [i for i in w["inputs"] if not (reg_bytes(i, "xmm1") & set(range(8, 16)))]
    missed += verdict("ctl_vpxor", r)[0] != "FAIL"
    missed += verdict("psrad_x", None)[0] != "FAIL"
    # a replace over the whole record hits RIP's increment constant first; plant IN an upper byte
    r = copy.deepcopy(recs["movq_to_x"])
    for w in xmm0_outputs(r):
        if min(reg_bytes(w["write_target"], "xmm0")) == 9:
            w["computation"] = json.loads(json.dumps(w["computation"]).replace("#x0", "#x1", 1))
    missed += verdict("movq_to_x", r)[0] != "FAIL"
    return missed


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--queries", action="store_true", help="print the instruction bytes to feed the server, in order")
    ap.add_argument("results", nargs="*", help="one <cpu>.check.jsonl per machine")
    args = ap.parse_args(argv)
    if args.queries:
        print("\n".join(h for _, h in queries()))
        return 0
    decl = declared_vecs()
    if decl is None or decl != set(PROXY):
        print("REFUSED: knownDivergences vecs %s != proxied vecs %s" % (sorted(decl or []), sorted(PROXY)))
        return 2
    if not args.results:
        ap.print_usage()
        return 2
    rc = 0
    for path in args.results:
        lines = [l for l in open(path).read().splitlines() if l.strip()]
        if len(lines) != len(queries()):
            print("%s: REFUSED -- %d result lines for %d queries" % (path, len(lines), len(queries())))
            return 2
        recs = {n: json.loads(l) for (n, _), l in zip(queries(), lines)}
        print("== %s" % os.path.basename(path))
        for n, h in queries():
            v, why = verdict(n, recs[n])
            label = n if n.startswith("ctl") else "%s (%s)" % (n, PROXY[n][0])
            print("  %-4s %-22s %-11s %s" % (v, label, h, why))
            rc |= v == "FAIL"
        missed = plants(recs)
        print("  plants: %s" % ("5 of 5 caught" if not missed else "%d of 5 NOT caught" % missed))
        rc |= missed != 0
    return int(rc)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
