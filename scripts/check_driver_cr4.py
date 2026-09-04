#!/usr/bin/env python3
"""⭐⭐⭐ P2 — DOES THE **DIFFERENTIAL PATH** ENABLE SSE?  Measured through
`x86l-run-case`, which is the only call site a differential run ever uses.

⛔ WHY THIS FILE EXISTS, AND WHY THE GATE THAT LOOKED LIKE IT ALREADY EXISTED
   DID NOT COVER IT.

`scripts/oracle_availability.py --p2` has carried a CR4 gate since the P2 roster
run, with both arms (CR4=0 and CR4=0x600), a form that must execute only in the
second, an MMX form that must execute in both, and a refuse-always control.  It
is a good gate and it is GREEN.  It is also blind to the defect this file was
written for: `measure_cr4()` builds its OWN `init-x86-state-64` call, so what it
measured was the ORACLE's capability, on a call site no differential run touches.
The call site that feeds the comparator — `x86l-run-case` in
`scripts/x86isa_driver.lisp` — passed `nil` for `ctrs` from P0 until this batch.

  ⇒ 🔑 A CAPABILITY MEASURED ON A BYPASS PATH SAYS NOTHING ABOUT THE PATH THAT
  SHIPS.  Both call sites reach the same oracle and only one of them was
  configured; the probe answered "x86isa can do SSE", which is true, and was
  read as "the differential can do SSE", which was false.

⚠️ AND IT WOULD HAVE FAILED SILENTLY IN THE WORST DIRECTION.  With `ctrs` = nil
every SSE form raises #UD, so the oracle's post-state is a REFUSAL.  Nothing on
the Lean side writes XMM yet, so once vector semantics land the first run would
have compared a Lean model that computed a result against an oracle that
declined to run at all — and `refused=` is a field the comparator reads, so this
one would have been loud.  The quiet version is the one to fear: a form the
oracle refuses for a reason the harness attributes to the MODEL.

## WHAT THIS GATE DOES

Two arms over the SAME real pre-states, in one invocation:

  * ARM ON  — the driver EXACTLY AS SHIPPED.  The SSE forms must EXECUTE.
  * ARM OFF — the driver with `*x86l-ctrs*` rewritten to `nil`, which is
    byte-for-byte the pre-batch driver.  The SSE forms must REFUSE.

⚠️ THE OFF ARM IS THE POINT.  An ON arm alone cannot tell "CR4 is set" from "this
oracle never needed CR4 in the first place" — a probe must CREATE the condition
it claims to detect, and the plant is DERIVED FROM THE SHIPPED FILE rather than
written here, so this gate cannot go stale against a driver it no longer matches
([[feedback-a-gate-is-not-exempt-from-its-own-defect]]).  If the defconst is not
found, the probe REFUSES rather than reporting agreement.

⚠️ AND TWO CONTROLS RIDE IN BOTH ARMS, because "everything refuses" is what a
broken harness looks like and is indistinguishable from a true OFF reading
without them:
  * CONTROL:mov  — a scalar store that must EXECUTE in both arms.  It is what
    makes the OFF arm a reading about SSE rather than about a dead run.
  * CONTROL:movnti — must REFUSE in both arms, so an ON arm in which the
    discriminator has stopped discriminating cannot pass as success
    ([[feedback-a-refusing-form-needs-a-refuse-always-control]]).

LANE.  Personal lane; ACL2 x86isa is BSD-3 and is CONSULTED BY EXECUTION.

Usage:  check_driver_cr4.py [--selftest]
"""
import os, re, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import oracle_availability as OA

DRIVER = "scripts/x86isa_driver.lisp"

# ⛔ THE PLANT'S SUBJECT, quoted from the shipped driver.  If this string is not
# in the file the probe cannot build its OFF arm and MUST NOT run: a plant that
# silently fails to apply gives an OFF arm identical to the ON arm, and two
# identical arms agree to the case ([[feedback-two-arms-that-agree-to-the-case]]).
CTRS_DEFCONST = "(defconst *x86l-ctrs* (list (cons #.*cr4* #x600)))"

# ⚠️ A BOUNDED NUMBER OF REAL PRE-STATES, and the bound is stated rather than
# hidden: CR4.OSFXSR is a decode-time check that does not vary with the GPRs or
# the flags, so this question is answered by a handful of the differential's own
# pre-states and asking it over all 86 twice would buy nothing and cost minutes
# ([[feedback-make-the-probe-cheap]]).  They are the REAL emitted pre-states, not
# a fresh set written here.
N_PRE = 6

# (label, asm, bytes, expect OFF, expect ON)
FORMS = [
    ("movdqa",  "movdqa (%rbx), %xmm0", "660f6f03", "refuses",  "executes"),
    ("paddd",   "paddd %xmm1, %xmm0",   "660ffec1", "refuses",  "executes"),
    ("movdqu",  "movdqu (%rbx), %xmm0", "f30f6f03", "refuses",  "executes"),
    ("pxor",    "pxor %xmm1, %xmm0",    "660fefc1", "refuses",  "executes"),
    ("CONTROL:mov",    "movl %ecx, (%rbx)",    "890b",   "executes", "executes"),
    ("CONTROL:movnti", "movntil %ecx, (%rbx)", "0fc30b", "refuses",  "refuses"),
]


def die(msg):
    print("⛔ " + msg)
    sys.exit(2)


def build_cases(pres, path):
    body = []
    for label, _asm, hx, _e0, _e1 in FORMS:
        tag = OA.tag_of(label)
        for i, c in enumerate(pres):
            body.append(OA.rewrite(c, i, tag, hx))
    open(path, "w").write('(in-package "X86ISA")\n(defconst *x86lean-cases*\n \'(\n'
                          + "".join(body) + "))\n")
    return len(body)


def run(cases_path, driver_path, out_path):
    acl2 = os.environ.get("ACL2", os.path.join(ROOT, "vendor/acl2/saved_acl2"))
    if not os.access(acl2, os.X_OK):
        die(f"no ACL2 image at {acl2} — run scripts/setup_oracle.sh")
    drive = out_path + ".lsp"
    open(drive, "w").write(
        '(include-book "projects/x86isa/tools/execution/init-state" :dir :system :ttags :all)\n'
        '(include-book "projects/x86isa/machine/x86" :dir :system :ttags :all)\n'
        "(set-fmt-hard-right-margin 100000 state)\n(set-fmt-soft-right-margin 99000 state)\n"
        f'(ld "{driver_path}")\n(ld "{cases_path}")\n(in-package "X86ISA")\n'
        "(x86l-run-all *x86lean-cases* x86 state)\n")
    with open(out_path, "w") as fh:
        subprocess.run([acl2], stdin=open(drive), stdout=fh, stderr=subprocess.STDOUT)
    res, cur = {}, None
    for line in open(out_path):
        m = re.match(r"^CASE id=(\S+) len=", line)
        if m:
            cur = m.group(1).rsplit("/", 1)[0]
            continue
        if line.startswith("POST ") and cur:
            e, r = res.get(cur, (0, 0))
            if re.search(r"refused=1", line):
                r += 1
            else:
                e += 1
            res[cur] = (e, r)
            cur = None
    return res


def verdict(res, n, tag):
    """(reading, why) per form — a MISSING reading is never read as a refusal."""
    out = {}
    for label, _asm, _hx, _e0, _e1 in FORMS:
        t = OA.tag_of(label)
        e, r = res.get(t, (0, 0))
        if e + r != n:
            out[label] = (None, "produced %d records of %d expected in arm %s — "
                                "a missing reading is not a refusal" % (e + r, n, tag))
        elif r == n:
            out[label] = ("refuses", "")
        elif e == n:
            out[label] = ("executes", "")
        else:
            out[label] = ("MIXED", "%d executed, %d refused of %d in arm %s"
                          % (e, r, n, tag))
    return out


def measure():
    base = open(DRIVER).read()
    if CTRS_DEFCONST not in base:
        die(f"{DRIVER} no longer contains the CR4 defconst this probe plants on:\n"
            f"    {CTRS_DEFCONST}\n"
            "  Without it the OFF arm would be identical to the ON arm and the gate "
            "would report agreement about a condition it never created.")
    pres = OA.pre_states()[:N_PRE]
    if not pres:
        die("no pre-states recovered — a probe with no subject is not a measurement.")
    tmp = tempfile.mkdtemp(prefix="x86lean-cr4-")
    cases = os.path.join(tmp, "cases.lsp")
    n = build_cases(pres, cases)
    print(f"── {len(FORMS)} forms x {len(pres)} real pre-states = {n} cases, "
          f"through `x86l-run-case`, twice ──")

    drv_on = os.path.join(tmp, "driver_on.lisp")
    drv_off = os.path.join(tmp, "driver_off.lisp")
    open(drv_on, "w").write(base)
    open(drv_off, "w").write(base.replace(
        CTRS_DEFCONST, "(defconst *x86l-ctrs* nil)", 1))

    on = verdict(run(cases, drv_on, os.path.join(tmp, "on.out")), len(pres), "ON")
    off = verdict(run(cases, drv_off, os.path.join(tmp, "off.out")), len(pres), "OFF")
    return on, off, len(pres)


def report(on, off, forms=None, quiet=False):
    forms = FORMS if forms is None else forms
    bad, rows = [], []
    for label, asm, _hx, e0, e1 in forms:
        g0, why0 = off[label]
        g1, why1 = on[label]
        if g0 is None or g1 is None:
            bad.append((label, why0 or why1))
            continue
        if (g0, g1) != (e0, e1):
            bad.append((label, "declared (OFF %s, ON %s), MEASURED (OFF %s, ON %s)%s"
                        % (e0, e1, g0, g1, ("  [" + (why0 or why1) + "]") if (why0 or why1) else "")))
        rows.append((label, asm, g0, g1, (g0, g1) == (e0, e1)))
    if not quiet:
        print(f"\n  {'form':18s} {'asm':24s} {'CR4=nil':>10s} {'CR4=0x600':>11s}")
        for label, asm, g0, g1, ok in rows:
            print(f"  {'✔' if ok else '⛔'} {label:16s} {asm:24s} {g0:>10s} {g1:>11s}")
    return bad


def main():
    on, off, n = measure()
    bad = report(on, off)
    if "--selftest" in sys.argv:
        # ⭐ RED FIRST.  The shipped table must be green before a plant means
        # anything, and then EVERY declaration is flipped one arm at a time and
        # must be reported.  A gate seen only green has not been seen at all.
        if bad:
            print("\n⛔ selftest cannot run: the SHIPPED table already disagrees.")
            for lab, why in bad:
                print(f"    {lab}: {why}")
            return 1
        arms = 0
        # ⚠️ THE PLANT GOES THROUGH `report()` ITSELF, not through a comparison
        # written here.  A first draft of this arm asked whether the MEASURED
        # value differed from the INVERTED declaration — which, once the shipped
        # table is green, is true by construction for every form and reports PASS
        # without ever calling the code that does the reporting.  A red arm that
        # cannot fail is a green light wired to nothing
        # ([[feedback-a-claim-the-vectors-cannot-distinguish]]).
        for which, idx in (("OFF", 3), ("ON", 4)):
            planted = []
            for f in FORMS:
                lab, asm, hx, e0, e1 = f
                if idx == 3:
                    planted.append((lab, asm, hx,
                                    "executes" if e0 == "refuses" else "refuses", e1))
                else:
                    planted.append((lab, asm, hx, e0,
                                    "executes" if e1 == "refuses" else "refuses"))
            got = report(on, off, planted, quiet=True)
            if len(got) != len(FORMS):
                print(f"\n⛔ selftest arm FAILED — inverting every {which} declaration "
                      f"was reported by {len(got)} of {len(FORMS)} forms. A wrong "
                      f"{which} claim would go unreported.")
                return 1
            arms += 1
            print(f"  ✔ red arm: an inverted {which} declaration is reported by all "
                  f"{len(FORMS)} forms")
        # ⚠️ AND THE PLANT MUST REACH THE DRIVER, NOT ONLY THE TABLE.  Flipping a
        # declaration tests the comparison; it does not test that this probe can
        # still BUILD its OFF arm.  If the defconst were renamed, `measure()`
        # refuses outright — so that path is asserted here rather than assumed.
        base_txt = open(DRIVER).read()
        if base_txt.replace(CTRS_DEFCONST, "(defconst *x86l-ctrs* nil)", 1) == base_txt:
            print("\n⛔ selftest arm FAILED — the OFF-arm plant did not change the "
                  "driver text, so both arms would have run the same file.")
            return 1
        arms += 1
        print("  ✔ red arm: the OFF-arm plant demonstrably rewrites the shipped driver")
        # ⚠️ and an EMPTY run must be reported by every form, not read as agreement
        empty = verdict({}, n, "EMPTY")
        if any(v[0] is not None for v in empty.values()):
            print("\n⛔ selftest arm FAILED — a run that produced NO records was not "
                  "reported as a failure by every form.")
            return 1
        print(f"  ✔ red arm: an EMPTY run is reported by all {len(FORMS)} forms, "
              f"not read as agreement")
        print(f"\ndriver-CR4 selftest: PASS ({arms + 1} red arms)")
        return 0
    if bad:
        print("\n⛔ driver-CR4 gate: FAIL")
        for lab, why in bad:
            print(f"    {lab}: {why}")
        return 1
    print("\ndriver-CR4 gate: CLEAN — through `x86l-run-case` itself, SSE forms "
          "execute with the shipped driver and REFUSE when its `*x86l-ctrs*` is "
          "planted back to `nil`; the scalar control executed in both arms and "
          "the refuse-always control refused in both.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
