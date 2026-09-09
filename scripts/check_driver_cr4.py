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
import collections, os, re, subprocess, sys, tempfile

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

# ⛔⛔ THE VOCABULARY IS THREE-VALUED (QUEUE 0b(6), 2026-09-09).  It was
# `refuses | executes` with `executes` as the RESIDUAL, which is D170's defect
# verbatim, sitting in the gate that CERTIFIES every differential run at
# CR4=0x600.  It was unpoliced BY LUCK — the six rows below contained none of the
# three known stalling forms — and 0b(6) recorded it as LATENT for that reason.
# ⇒ 🔑 A DEFECT ABSENT ONLY BECAUSE THE INPUT SET HAPPENS TO EXCLUDE IT IS NOT
# FIXED, AND THE NEXT ROW ADDED TO THAT LIST IS WHAT DECIDES.  So the repair adds
# the row as well as the state: a third value nothing exercises is a branch no
# input reaches, and a branch no input reaches is not a gate
# ([[feedback-an-implied-assertion-is-not-a-second-gate]]).
#
# (label, asm, bytes, expect OFF, expect ON)   values: refuses | executes | stalls
FORMS = [
    ("movdqa",  "movdqa (%rbx), %xmm0", "660f6f03", "refuses",  "executes"),
    ("paddd",   "paddd %xmm1, %xmm0",   "660ffec1", "refuses",  "executes"),
    ("movdqu",  "movdqu (%rbx), %xmm0", "f30f6f03", "refuses",  "executes"),
    ("pxor",    "pxor %xmm1, %xmm0",    "660fefc1", "refuses",  "executes"),
    # ⭐ THE STALL CONTROL.  x86isa leaves RIP unadvanced with the refusal flag
    # CLEAR for this form — D170 measured it 88/88 through `measure`, the same
    # driver and the same `x86l-run-case` call site.  Its OFF reading was a
    # SEALED PREDICTION here (refuses, on the OSFXSR #UD gate), scored below.
    # It earns its place the way CONTROL:movnti does: without it the `stalls`
    # branch is never taken and could be deleted without a single arm going red.
    ("STALL:movmskps", "movmskps %xmm1, %eax", "0f50c1", "refuses", "stalls"),
    ("CONTROL:mov",    "movl %ecx, (%rbx)",    "890b",   "executes", "executes"),
    ("CONTROL:movnti", "movntil %ecx, (%rbx)", "0fc30b", "refuses",  "refuses"),
]

VALUES = ("refuses", "executes", "stalls")

# ⛔⛔ AND THE PARSE IS STRICT, BECAUSE THE RESIDUAL WAS THE BUG.  Both fields are
# REQUIRED.  A `POST` line that carries neither — the driver emits exactly one,
# `POST init-error`, when `init-x86-state-64` fails — was scored `executes` by
# the shipped parser here AND by `oracle_availability.measure`, MEASURED with a
# plant on 2026-09-09: 6 of 6 records, in both, read as successful execution.
# ⇒ 🔑 A CLASSIFIER'S RESIDUAL IS ITS REAL DEFAULT, AND MAKING IT THREE-VALUED
# MOVED THE RESIDUAL WITHOUT REMOVING IT.  A total failure to build the machine
# is the strongest possible NON-reading and it was the strongest possible
# positive reading ([[feedback-a-classifiers-value-set-is-a-claim]]).
# ⚠️ `rip` is pinned to SIXTEEN LOWERCASE HEX DIGITS on purpose.  The driver
# prints it through `x86l-hex(...,16)`, but D177 nearly shipped a sibling parser
# whose producer used ACL2's ambient print-base of 10, where `int("4194304",16)`
# silently misses ENTRY_RIP and scores a stall as an execution.  Under this
# pattern a base-10 rip does not match, so the gate REFUSES instead of agreeing
# ([[feedback-a-parser-is-correct-only-where-its-producer-is]]).
RE_REFUSED = re.compile(r"\brefused=([01])\b")
RE_RIP = re.compile(r"\brip=([0-9a-f]{16})\b")

Counts = collections.namedtuple("Counts", "executes refuses stalls unparsed")
# ⚠️ A NAMEDTUPLE, NOT A TUPLE.  Growing the previous 2-tuple by one field is
# exactly the edit that silently changed a meaning in `p2_roster` on 09/08 and
# published a STALLS count of 1 where the answer was 3.  Every consumer here
# reads by NAME ([[feedback-a-positional-index-bets-the-record-wont-grow]]).
ZERO = Counts(0, 0, 0, 0)


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


def parse(text):
    """{tag: Counts} over a driver transcript.  ⛔ PURE STRING WORK AND SEPARATE
    FROM `run()` ON PURPOSE: the defect this function was rewritten for is a
    PARSING defect, so its red arms must be able to fire without ACL2.  An arm
    behind a 20-second oracle run is a discipline; an arm that runs in
    microseconds is a gate ([[feedback-make-the-probe-cheap]])."""
    res, cur = {}, None
    for line in text.splitlines():
        m = re.match(r"^CASE id=(\S+) len=", line)
        if m:
            cur = m.group(1).rsplit("/", 1)[0]
            continue
        if line.startswith("POST ") and cur:
            c = res.get(cur, ZERO)
            ref, rip = RE_REFUSED.search(line), RE_RIP.search(line)
            if ref is None or rip is None:
                # ⛔ NOT `executes`.  See the RE_REFUSED comment: this is the
                # branch the whole repair exists for.
                c = c._replace(unparsed=c.unparsed + 1)
            elif ref.group(1) == "1":
                c = c._replace(refuses=c.refuses + 1)
            elif int(rip.group(1), 16) == OA.ENTRY_RIP:
                # ⚠️ A STALL IS `rip UNCHANGED`, not `rip != entry + len` — a form
                # whose meaning is to move RIP elsewhere (a jump, a taken branch,
                # or a `rep` signalling another iteration by NOT advancing, D46)
                # would be misread by the stricter test.  No such form is in
                # `FORMS` today; one added later must be read against this line.
                c = c._replace(stalls=c.stalls + 1)
            else:
                c = c._replace(executes=c.executes + 1)
            res[cur] = c
            cur = None
    return res


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
    return parse(open(out_path).read())


def verdict(res, n, tag, forms=None):
    """(reading, why) per form — a MISSING reading is never read as a refusal,
    and an UNPARSEABLE one is never read as an execution."""
    out = {}
    for label, _asm, _hx, _e0, _e1 in (FORMS if forms is None else forms):
        t = OA.tag_of(label)
        c = res.get(t, ZERO)
        total = c.executes + c.refuses + c.stalls + c.unparsed
        if total != n:
            out[label] = (None, "produced %d records of %d expected in arm %s — "
                                "a missing reading is not a refusal" % (total, n, tag))
        elif c.unparsed:
            # ⛔ REFUSE, LOUDLY, AND NAME THE COUNT.  A gate that discards what it
            # saw turns a diagnosable failure into a re-run somewhere else
            # ([[feedback-a-gate-that-refuses-must-say-what-it-saw]]).
            out[label] = (None, "%d of %d POST records in arm %s carry no parseable "
                                "`refused=` / 16-hex-digit `rip=` pair (the driver's "
                                "`POST init-error` is one such line). NOT scored as "
                                "an execution." % (c.unparsed, n, tag))
        elif c.refuses == n:
            out[label] = ("refuses", "")
        elif c.executes == n:
            out[label] = ("executes", "")
        elif c.stalls == n:
            out[label] = ("stalls", "")
        else:
            out[label] = ("MIXED", "%d executed, %d refused, %d stalled of %d in arm %s"
                          % (c.executes, c.refuses, c.stalls, n, tag))
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


def parser_arms():
    """⭐ THE ARMS FOR THE DEFECT 0b(6) NAMED, AND THEY NEED NO ORACLE.

    Every one of these plants a condition and requires this file's own `parse`
    to report it.  Two of the four are POSITIVE CONTROLS in the same run: without
    them "everything is unparseable" and "everything is a stall" both look like
    success ([[feedback-a-probe-must-create-its-condition]],
    [[feedback-a-plant-probes-control-comes-first]]).

    Returns (ok, n_arms, failures)."""
    fails, arms = [], 0

    # ⛔ THE PLANT'S SUBJECT IS DERIVED FROM THE SHIPPED DRIVER, NEVER TYPED HERE,
    # for the same reason CTRS_DEFCONST is: a plant that quietly stops matching
    # its subject gives an arm that passes about nothing.
    m = re.search(r'"CASE id=~s0 len=~x1~%(POST [^~"]*)~%"', open(DRIVER).read())
    if not m:
        return False, 0, [("init-error plant",
                           "could not derive the failure-POST literal from %s — the "
                           "driver's emission changed and this arm cannot build its "
                           "subject. REFUSING rather than reporting agreement." % DRIVER)]
    init_err = m.group(1)

    def transcript(post_line, k=3):
        return "".join("CASE id=probe/%d len=3\n%s\n" % (i, post_line) for i in range(k))

    GOOD = "POST rax=0000000000000000 rip=%016x cf=0 refused=0"

    # ARM 1 (POSITIVE CONTROL, FIRST): a well-formed advanced rip is `executes`.
    #   Without this the three arms below cannot be told from a dead parser.
    c = parse(transcript(GOOD % (OA.ENTRY_RIP + 3))).get("probe", ZERO)
    arms += 1
    if c != Counts(executes=3, refuses=0, stalls=0, unparsed=0):
        fails.append(("control: an advanced rip must read `executes`", repr(c)))

    # ARM 2 (POSITIVE CONTROL): rip UNCHANGED with the refusal flag clear is a
    #   STALL.  This is the branch the repair added; without an input that
    #   reaches it, it could be deleted and no arm would go red.
    c = parse(transcript(GOOD % OA.ENTRY_RIP)).get("probe", ZERO)
    arms += 1
    if c != Counts(executes=0, refuses=0, stalls=3, unparsed=0):
        fails.append(("control: rip == ENTRY_RIP with refused=0 must read `stalls`", repr(c)))

    # ARM 3 ⭐ THE DEFECT ITSELF: the driver's own init-failure line.
    c = parse(transcript(init_err)).get("probe", ZERO)
    arms += 1
    if c != Counts(executes=0, refuses=0, stalls=0, unparsed=3):
        fails.append((
            "the driver's %r must be UNPARSEABLE, never `executes`" % init_err,
            "%r — this is the shipped defect: a total failure to build the machine "
            "scored as successful execution, in the gate that certifies every "
            "differential run at CR4=0x600" % (c,)))

    # ARM 4 ⭐ THE D177 NEAR-MISS, MADE PERMANENT: a base-10 rip.  If a future
    #   producer prints rip in ACL2's ambient print-base, `int("4194304",16)`
    #   misses ENTRY_RIP and a STALL is scored as an EXECUTION.  Under the strict
    #   16-hex-digit pattern that line is unparseable and the gate refuses.
    c = parse(transcript("POST rax=0 rip=%d cf=0 refused=0" % OA.ENTRY_RIP)).get("probe", ZERO)
    arms += 1
    if c != Counts(executes=0, refuses=0, stalls=0, unparsed=3):
        fails.append((
            "a BASE-10 rip must be UNPARSEABLE, never `executes`",
            "%r — D177's near-miss: int('4194304',16) = 68174084 misses ENTRY_RIP, "
            "falls to the residual, and scores a stall as an execution "
            "([[feedback-a-parser-is-correct-only-where-its-producer-is]])" % (c,)))

    # ⛔⛔ ARMS 6 AND 7 EXIST BECAUSE THE RED PROBE FOUND ARMS 1-5 BLIND TO A REAL
    #   LOOSENING.  Planting `if rip is None:` in place of `if ref is None or rip
    #   is None:` — dropping the `refused=` requirement entirely, so the rip alone
    #   decides every record — fired NO ARM AT ALL.  None of the transcripts above
    #   carries the one shape that would catch it: a well-formed rip with the
    #   refusal field ABSENT.  `x86l-post` prints both fields today, so the
    #   condition is unreachable from the CURRENT producer — which is precisely
    #   the "unpoliced by luck" that 0b(6) exists to remove, one level down.
    #   ⇒ 🔑 AN UNCAUGHT PLANT IS A FINDING ABOUT THE ARMS UNTIL PROVED OTHERWISE
    #   ([[feedback-probe-silence-has-two-causes]]).  Both halves of the AND are
    #   now armed separately, because a conjunction tested only as a whole is one
    #   arm wearing two names.
    c = parse(transcript("POST rax=0 rip=%016x cf=0" % OA.ENTRY_RIP)).get("probe", ZERO)
    arms += 1
    if c != Counts(executes=0, refuses=0, stalls=0, unparsed=3):
        fails.append(("a POST line with a good rip but NO `refused=` must be UNPARSEABLE",
                      "%r — the rip alone must never decide a record" % (c,)))

    c = parse(transcript("POST rax=0 cf=0 refused=0")).get("probe", ZERO)
    arms += 1
    if c != Counts(executes=0, refuses=0, stalls=0, unparsed=3):
        fails.append(("a POST line with `refused=0` but NO `rip=` must be UNPARSEABLE",
                      "%r — without a rip the stall test cannot run, and a record "
                      "the stall test could not read is not an execution" % (c,)))

    # ARM 8: and `verdict` must turn an unparsed count into a REFUSAL, not a
    #   reading — the counter being right is not the same as the caller using it.
    #   ⚠️ THIS ARM DOES NOT GO THROUGH `parse`, so no plant in the parser can
    #   reach it; it needs its own, and the red probe carries one.
    v = verdict({OA.tag_of(l): Counts(0, 0, 0, 3) for l, *_ in FORMS}, 3, "PLANT")
    arms += 1
    if any(r is not None for r, _why in v.values()):
        fails.append(("verdict() must report an all-unparsed arm for EVERY form",
                      repr({k: v[k][0] for k in v})))
    return (not fails), arms, fails


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
        # ⚠️ ROTATE, DO NOT "INVERT".  The vocabulary is three-valued now, and a
        # two-valued flip (`refuses` <-> `executes`) leaves a `stalls` row mapped
        # to a value it never had — which still differs, so the arm passes, but
        # it passes without ever planting a wrong STALL claim.  Rotation
        # guarantees the planted value differs from the true one for EVERY row
        # including the stall control ([[feedback-a-control-can-share-the-blind-spot]]).
        rot = {VALUES[i]: VALUES[(i + 1) % len(VALUES)] for i in range(len(VALUES))}
        for which, idx in (("OFF", 3), ("ON", 4)):
            planted = []
            for f in FORMS:
                lab, asm, hx, e0, e1 = f
                if idx == 3:
                    planted.append((lab, asm, hx, rot[e0], e1))
                else:
                    planted.append((lab, asm, hx, e0, rot[e1]))
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
        arms += 1
        ok, n_p, fails = parser_arms()
        if not ok:
            print("\n⛔ selftest FAILED in the PARSER arms:")
            for lab, why in fails:
                print(f"    {lab}\n      {why}")
            return 1
        print(f"  ✔ {n_p} parser arms (2 positive controls first, then the "
              f"`POST init-error` and base-10-rip plants, then verdict's refusal)")
        arms += n_p
        print(f"\ndriver-CR4 selftest: PASS ({arms} red arms)")
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
