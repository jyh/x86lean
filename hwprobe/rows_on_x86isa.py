"""hwprobe/rows_on_x86isa.py — hwprobe's rows on ACL2 x86isa, the column the referee is compared with (D266).

From the repository root, after `scripts/setup_oracle.sh` and an `x86lean-diff emit-acl2 run/cases.lsp`
(one emitted case is the template):
    python3 hwprobe/rows_on_x86isa.py gen          # run/hwprobe_cases.lsp and run/hwprobe_drive.lsp
    vendor/acl2/saved_acl2 < run/hwprobe_drive.lsp > run/hwprobe_acl2.out
    python3 hwprobe/rows_on_x86isa.py score        # one line per row; the last line is the count
The population is mk_rows.build()'s, minus CVTSS2SD and CVTSD2SS at a zero source: x86isa's guard violation there
(RTL::SSE-POST-COMP requires a non-zero value) aborts every case after it (D258; D272 for the narrowing direction).
They are excluded and printed. A control case runs LAST, so a run that died early
cannot read as complete.
"""
import re, os, sys
import mk_rows as M

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "scripts"))
import portable as P  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
RUN = os.path.join(ROOT, "run")
BYTES = dict(M.OPS, **M.POPS)
EXCLUDED = {"cvtss2sd_negzero", "cvtsd2ss_zero", "cvtsd2ss_negzero"}
# Paths are relative to the repository root, where the ACL2 image is run from.
DRIVE = """(include-book "projects/x86isa/tools/execution/init-state" :dir :system :ttags :all)
(include-book "projects/x86isa/machine/x86" :dir :system :ttags :all)
(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 99000 state)
(ld "scripts/x86isa_driver.lisp")
(ld "hwprobe/run_case_mx.lisp")
(ld "run/hwprobe_cases.lsp")
(in-package "X86ISA")
(x86l-run-all-mx *x86lean-cases* x86 state)
"""


def rows():
    M.ROWS.clear()
    M.build()
    return [r for r in M.ROWS if r[0] not in EXCLUDED]


def prows():
    """B5: the packed rows. %xmm0 and %xmm1 are loaded with all 128 bits of A and B, and all 128 of %xmm0 are scored."""
    M.PROWS.clear()
    M.build_packed()
    return list(M.PROWS)


def gen():
    src = open(os.path.join(RUN, "cases.lsp"), encoding="utf-8").read()
    rec = re.search(r'  \(:id "minsd_x1_x0/0".*?(?=\n  \(:id )', src, re.S).group(0)

    def mk(cid, bs, x0, x1, mx):
        bs = bytes.fromhex(bs)
        r = rec.replace('"minsd_x1_x0/0"', '"%s"' % cid)
        r = re.sub(r':len \d+', ':len %d' % len(bs), r, count=1)
        r = re.sub(r':bytes \([^)]*\)', ':bytes (' + ' '.join('#x%02x' % b for b in bs) + ')', r, count=1)
        r = re.sub(r'\(#x000000000040000[0-9a-f] \. #x[0-9a-f]{2}\) ?', '', r)
        r = r.replace(':mem (', ':mem (' + ' '.join('(#x%016x . #x%02x)' % (0x400000 + i, b)
                                                    for i, b in enumerate(bs)) + ' ', 1)
        r = re.sub(r'\(0 \. #x[0-9a-f]{32}\)', '(0 . #x%032x)' % x0, r, count=1)
        r = re.sub(r'\(1 \. #x[0-9a-f]{32}\)', '(1 . #x%032x)' % x1, r, count=1)
        # the hardware probe loads `a` from %rdi, and cvtsi2sd reads %edi: the GPR must carry it too
        r = re.sub(r'\(7 \. #x[0-9a-f]{16}\)', '(7 . #x%016x)' % (x0 & ((1 << 64) - 1)), r, count=1)
        r = re.sub(r':mxcsr #x[0-9a-f]+\s*', '', r)   # the emitter writes one since B0; ours must be the only one
        return r.replace(':rflags', ':mxcsr #x%08x :rflags' % mx, 1)

    out = [mk(n, BYTES[fn], a, b, mx) for (n, fn, mx, a, b, want, mask, fl) in rows()]
    out += [mk(n, BYTES[fn], A, B, mx) for (n, fn, mx, A, B, want, fl) in prows()]
    out.append(mk("CONTROL_last", "f20f59c1", 0x3FF8000000000000, 0x4000000000000000, 0x1F80))
    with open(os.path.join(RUN, "hwprobe_cases.lsp"), "w", encoding="utf-8") as fh:
        fh.write('(in-package "X86ISA")\n(defconst *x86lean-cases*\n \'(\n' + "\n".join(out) + "\n ))\n")
    with open(os.path.join(RUN, "hwprobe_drive.lsp"), "w", encoding="utf-8") as fh:
        fh.write(DRIVE)
    print("cases", len(out), "excluded", sorted(EXCLUDED))


def score():
    post = {}
    cur = None
    for line in open(os.path.join(RUN, "hwprobe_acl2.out"), encoding="utf-8"):
        if line.startswith("CASE "):
            cur = re.match(r'CASE id=(\S+)', line).group(1)
        elif line.startswith("POST ") and cur:
            kv = dict(t.split("=", 1) for t in line[5:].split() if "=" in t)
            post[cur] = kv
            cur = None
    bad = 0
    for (n, fn, mx, a, b, want, mask, fl) in rows():
        kv = post[n]
        if fn in ("p_comisd", "p_ucomisd", "p_comiss", "p_ucomiss"):
            got = sum(int(kv[k]) << bit for k, bit in (("cf", 0), ("pf", 2), ("af", 4), ("zf", 6), ("sf", 7), ("of", 11)))
        elif fn in ("p_cvtss2sd", "p_cvtsd2ss", "p_cvtsi2ss", "p_cvtsi2ssq", "p_cvtsi2sdq"):
            got = int(kv["xmm1"], 16) & ((1 << 64) - 1)
        elif fn == "p_cvttsd2si":
            got = int(kv["rax"], 16)
        else:
            got = int(kv["xmm0"], 16) & ((1 << 64) - 1)
        got &= mask
        gmx = int(kv["mxcsr"], 16)
        ok = got == want and gmx == (mx | fl) and kv.get("refused") == "0"
        bad += not ok
        print("%s %-28s x86isa %016x want %016x  mxcsr %04x want %04x" %
              ("ok  " if ok else "DIFF", n, got, want, gmx, mx | fl))
    for (n, fn, mx, A, B, want, fl) in prows():
        kv = post[n]
        got = int(kv["xmm0"], 16)
        gmx = int(kv["mxcsr"], 16)
        ok = got == want and gmx == (mx | fl) and kv.get("refused") == "0"
        bad += not ok
        print("%s %-28s x86isa %032x want %032x  mxcsr %04x want %04x" %
              ("ok  " if ok else "DIFF", n, got, want, gmx, mx | fl))
    c = post.get("CONTROL_last", {})
    print("rows", len(rows()) + len(prows()), "disagreements", bad, "control xmm0", c.get("xmm0"), "mxcsr", c.get("mxcsr"))


if __name__ == "__main__":
    # ⛔ THIS READ `gen() if sys.argv[1] == "gen" else score()`, so EVERY argument that was not
    # exactly `gen` — a typo, `--help`, a probe of the interface — fell through to `score()` and
    # printed the whole 485-row comparison. Measured: `--definitely-not-a-real-flag-xyz` exits 0
    # after 486 lines. That is `portable.strict_flags`'s own docstring case, in the file the
    # flag-strictness gate does not scan, because its population is `scripts/*.py`.
    P.strict_flags(__file__)
    mode = sys.argv[1] if len(sys.argv) > 1 else None
    if mode == "gen":
        gen()
    elif mode == "score":
        score()
    else:
        raise SystemExit("⛔ rows_on_x86isa: expected `gen` or `score`, got %r. REFUSING rather "
                         "than falling through to score(), which prints a 485-row comparison and "
                         "exits 0 — a green about a subject nobody asked for." % (mode,))
