#!/usr/bin/env python3
"""⭐⭐ P1 BATCH 21 — THE UNAVAILABLE LIST, MEASURED INSTEAD OF DECLARED.

`claimed_forms.py --remaining` partitions the unclaimed roster rows into three
buckets: rows with no encoding (DERIVED), rows the oracle cannot execute, and
AVAILABLE WORK.  Until this batch the second bucket was a HARD-CODED SET OF NINE
MNEMONICS written down at batch 18, and D61 recorded what that costs:

  ⇒ 🔑 A DECLARED LIST INHERITS THE DIRECTION OF ITS DEFAULT.  This one defaults
  to *available*, so every gap in it INVENTS work.  `movnti` was measured
  UNAVAILABLE at batch 20 (82/82 refused, with an identical-shape control that
  executed 82/82 in the same run) — and the finding was written into D61 and
  into docs/COVERAGE.md and into NEITHER GATE.  Three batches of prose said the
  list had been corrected while `--remaining` went on printing `movnti` under
  AVAILABLE WORK.  ⇒ 🔑 A CITATION IS AN UNGATED CLAIM.

So the list is now MEASURED, by executing one form per mnemonic on the oracle
over the real pre-states, and the measurement is GATED IN BOTH DIRECTIONS:

  * a mnemonic declared UNAVAILABLE that starts executing is a FINDING — the
    oracle has gained it and the roster's residue is stale;
  * a mnemonic declared AVAILABLE that refuses is a FINDING — the direction that
    invents work, which is the one nobody polices.

⚠️ EVERY RUN CARRIES A POSITIVE CONTROL, `movl %ecx,(%rbx)`, which must execute
at every pre-state.  A run in which everything refuses is what a broken harness
looks like, and without the control it is indistinguishable from a true reading.
The control is the identical SHAPE and ADDRESS as `movnti`, so its success
places the refusal on the OPCODE rather than on the memory access (D61's first
route, re-run rather than cited).

⚠️ ONE FORM PER MNEMONIC, NOT ONE PER ROW.  x86isa implements an instruction or
it does not; the register and memory shapes of an unimplemented mnemonic are the
same missing semantic function.  The forms below are the `l`-width shapes and
the count of ROWS each mnemonic stands for is `claimed_forms.py`'s business, not
this file's.

LANE.  Personal lane; ACL2 x86isa is BSD-3 and is CONSULTED BY EXECUTION.

Usage:  oracle_availability.py [--check] [--selftest]
"""
import collections, os, re, subprocess, sys, tempfile

# ⭐⭐⭐ THE BUCKET RULE IS THE CENSUS'S, IMPORTED — NOT A SECOND ONE THAT AGREES
# WITH IT (D143). `demand_census.isa_bucket` is the TOTAL rule that produced the
# demand side of the join; computing the probe side with a different function is
# two rules for one partition, and the gate that was supposed to notice checks
# the VOCABULARY (is every probe bucket a census bucket) and not the RULE, so it
# passes whenever both names exist. Measured before the change: the two agreed on
# 256 of 256 rows both classified, and disagreed on none — which is exactly why a
# duplicate born in agreement survives to diverge on the next ordinary append.
# ⛔ The import is safe in this direction only: `demand_census` imports nothing
# local and guards its own `main`, while `p2_roster` imports both.
# [[feedback-duplicate-born-in-agreement]] [[feedback-a-join-on-a-lossy-key]]
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import demand_census as _DC

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(root)
ACL2 = os.environ.get("ACL2", os.path.join(root, "vendor", "acl2", "saved_acl2"))

# ⭐ THE TABLE.  `expect` is what this repository claims about the oracle, and
# the run below is what the oracle says.  The bytes are clang's, not mine
# (`clang -target x86_64-unknown-linux-gnu`), and the asm is beside them so a
# reader can re-assemble any line.
# ⭐ The address every probe case enters at, and where its bytes are placed.  ONE
# name, because the stall test in `measure` compares against it and a second
# literal would drift from the one `rewrite` uses.
ENTRY_RIP = 0x400000

FORMS = [
    # (mnemonic,   asm,                       bytes,                expect)
    # ⚠️ `expect` is now THREE-VALUED: refuses · executes · stalls (D170).
    ("andn",    "andnl %ecx, %edx, %eax",   "c4e268f2c1",         "refuses"),
    ("bextr",   "bextrl %ecx, %edx, %eax",  "c4e270f7c2",         "refuses"),
    ("blsmsk",  "blsmskl %ecx, %eax",       "c4e278f3d1",         "refuses"),
    ("blsr",    "blsrl %ecx, %eax",         "c4e278f3c9",         "refuses"),
    ("bzhi",    "bzhil %ecx, %edx, %eax",   "c4e270f5c2",         "refuses"),
    ("mulx",    "mulxl %ecx, %edx, %eax",   "c4e26bf6c1",         "refuses"),
    ("pdep",    "pdepl %ecx, %edx, %eax",   "c4e26bf5c1",         "refuses"),
    ("pext",    "pextl %ecx, %edx, %eax",   "c4e26af5c1",         "refuses"),
    ("rorx",    "rorxl $3, %ecx, %eax",     "c4e37bf0c103",       "refuses"),
    # ⛔ D61's row, and the reason this file exists.
    ("movnti",  "movntil %ecx, (%rbx)",     "0fc30b",             "refuses"),
    # ⛔⛔ P2 BATCH 37 (D170) — MOVMSKPS IS NOT AVAILABLE WORK, and it is the
    # first entry here that had to be MEASURED because a sibling suggested
    # otherwise.  `pmovmskb` is the same constructor at the same operand shape
    # and executes 88/88; `unpcklps` is also a NO-PREFIX SSE form and executes
    # 88/88 — both in the SAME differential run.  So the refusal is a fact about
    # this MNEMONIC, not about its prefix class, its feature bit or its shape.
    # ⚠️ AND IT IS SILENT: x86isa leaves RIP unadvanced with its `refused` flag
    # CLEAR — the only form in the table that does — so the differential filed
    # 464 field mismatches as `spec`, i.e. as this model being wrong about a rule
    # the oracle never evaluated.
    ("movmskps", "movmskps %xmm1, %eax",     "0f50c1",             "stalls"),
    # ⭐ THE POSITIVE CONTROL — identical shape and address to `movnti`.
    ("CONTROL:mov", "movl %ecx, (%rbx)",    "890b",               "executes"),
    # ⭐ AND A SECOND CONTROL AT THIS BATCH'S OWN FORM, so a run that has stopped
    # seeing memory-operand instructions cannot pass.
    ("CONTROL:cmpxchg8b", "cmpxchg8b (%rbx)", "0fc70b",           "executes"),
    # ⭐⭐ THE DECLINED ROWS, RECORDED AS **EXECUTES** — and that is the point.
    #
    # `claimed_forms.py --remaining` puts these in a bucket called "DECLINED by a
    # recorded decision", which is only honest if the decline is a DECISION and
    # not an oracle limitation wearing a decision's name.  Measured: all six
    # execute at every pre-state, so **oracle support is not what is stopping
    # them**, and a later reader cannot quietly re-derive "declined" as
    # "unsupported".
    #
    # D23 — the bit-string `m,r` shape of the bit-test group: `step`'s `.bit`
    # case takes the offset MODULO the operand width, which is right for a
    # register destination and wrong here, where the offset is signed and the
    # effective address moves with it.  ⚠️ Closing D23 is real work in the
    # PRE-STATES, not in `step`: with RBX at 0x2000 and ECX sweeping the
    # adversarial list, the effective address leaves the watched window, and an
    # unobserved region reports agreement.
    #
    # ⛔⛔ D25's ROW LEFT THIS LIST IN P2 BATCH 23, AND ITS DEPARTURE IS THE
    # ENTRY WORTH READING.  `xchg` at a memory operand was declined because its
    # implicit LOCK is an atomicity claim a model with no LOCK vocabulary could
    # neither make nor break — and this comment used to end *"oracle support is
    # not an argument to un-decline it."*  It still is not: what un-declined it
    # was the VOCABULARY (`Ea.lock`, D77), not the measurement in this table.
    # The row is gone from here because it is CLAIMED now, and a probe that went
    # on labelling a claimed row `DECLINED:` would be publishing a decision the
    # repository no longer holds.
    #
    # ⚠️ The count in this comment used to be SIX and is now FOUR; it is written
    # as "the declined rows" rather than a number, because a number in a comment
    # beside a list is the thing that goes stale while the list is right (D74).
    # `claimed_forms.DECLINED` is the table, and `claimed_forms --check` is what
    # holds it to the claimed set.
    ("DECLINED:bt m,r",   "btl %ecx,(%rbx)",   "0fa30b",          "executes"),
    ("DECLINED:bts m,r",  "btsl %ecx,(%rbx)",  "0fab0b",          "executes"),
    ("DECLINED:btr m,r",  "btrl %ecx,(%rbx)",  "0fb30b",          "executes"),
    ("DECLINED:btc m,r",  "btcl %ecx,(%rbx)",  "0fbb0b",          "executes"),
    # ⭐ AND `xchg` STAYS IN THE RUN AS AN UNLABELLED FORM, because a row that
    # left the residue is exactly the row whose oracle support somebody will
    # want to re-check — and because dropping it entirely would shrink the
    # probe's subject silently.
    ("CLAIMED:xchg m,r",  "xchgl %ecx,(%rbx)", "870b",            "executes"),
]

CASES = "run/cases.lsp"

def pre_states():
    """The real pre-states, taken from the emitted differential cases.  ⚠️ NOT a
    fresh set written here: a probe on states the differential does not use
    would answer a question nobody asked."""
    # ⛔⛔ P2 ITEM 2: ALWAYS RE-EMIT.  This read `if not os.path.exists(CASES)`,
    # so the probe used whatever `run/cases.lsp` happened to be on disk — an
    # artifact of a PREVIOUS run, in a possibly older record format, describing
    # pre-states the current model does not emit.  A gate that reuses a stale
    # input reports about a subject nobody chose, and says nothing about which.
    # Re-emitting costs a couple of seconds against a six-second gate.
    subprocess.run(["lake", "env", ".lake/build/bin/x86lean-diff",
                    "emit-acl2", CASES], check=True, capture_output=True)
    lines = open(CASES).read().splitlines(True)
    cases, cur = [], None
    for l in lines:
        if l.lstrip().startswith("(:id "):
            if cur: cases.append(cur)
            cur = [l]
        elif cur is not None:
            cur.append(l)
    if cur: cases.append(cur)
    cases[-1][-1] = cases[-1][-1].rstrip()[:-1] + "\n"     # drop the defconst's close
    first = re.search(r'\(:id "([^/]+)/', cases[0][0]).group(1)
    sel = [c for c in cases if re.match(r'\(:id "%s/\d+"' % re.escape(first), c[0].lstrip())]
    if not sel:
        print("⛔ no pre-states recovered from %s. A probe with no subject is not "
              "a measurement." % CASES)
        sys.exit(2)
    return sel

def rewrite(case, i, tag, hexbytes):
    b = [f"#x{hexbytes[k:k+2]}" for k in range(0, len(hexbytes), 2)]
    c = list(case)
    c[0] = re.sub(r'\(:id "[^"]*"', '(:id "%s/%d"' % (tag, i), c[0], count=1)
    c[0] = re.sub(r':len \d+', ':len %d' % len(b), c[0], count=1)
    c[1] = ":bytes (%s)\n" % " ".join(b)
    # the instruction bytes live at RIP in the :mem alist; replace exactly the
    # ones this case had and append the rest.
    def repl(m):
        return " ".join("(#x%016x . %s)" % (ENTRY_RIP + k, b[k]) for k in range(len(b)))
    # ⛔⛔ P2 ITEM 2: THE `:mem` LINE IS FOUND BY CONTENT, NOT BY INDEX.  This
    # said `c[4]`, and `c[4]` was the `:mem` line until P2 batch 1 inserted a
    # `:fsbase`/`:gsbase` line into the record — after which `c[4]` is `:rflags`
    # and every rewrite silently placed no bytes at all.
    # ⇒ 🔑 A POSITIONAL INDEX INTO A RECORD IS A BET THAT THE RECORD WILL NOT
    # GROW, and this repository has now lost that bet twice: P2 batch 1's own
    # oracle run read twelve results off their POSITION because the labels were
    # not emitting.  Same defect, one layer up, six hours apart.
    mem_i = next((k for k, l in enumerate(c) if l.lstrip().startswith(":mem ")), None)
    if mem_i is None:
        print("⛔ no `:mem` line in the case record for %s — the emitted format "
              "changed and this rewrite cannot find its subject." % tag)
        sys.exit(2)
    c[mem_i] = re.sub(r'\(#x0000000000400000 \. #x[0-9a-f]{2}\)(?: \(#x00000000004000[0-9a-f]{2} \. #x[0-9a-f]{2}\))*',
                      repl, c[mem_i], count=1)
    if "#x%016x" % (ENTRY_RIP + len(b) - 1) not in c[mem_i]:
        print("⛔ could not place %d instruction bytes at RIP for %s" % (len(b), tag))
        sys.exit(2)
    return "".join(c)

def tag_of(mn):
    """⚠️ THE CASE ID CANNOT CARRY A SPACE.  The record format is
    `CASE id=<tag>/<n> len=<n>`, read by splitting on whitespace, so a mnemonic
    like `DECLINED:bt m,r` would emit an id the reader truncates and every one of
    its records would go missing.  It did, on the first run — and the gate
    REFUSED rather than reading the silence as a refusal, which is the whole
    reason that branch says "a missing reading is not a refusal"."""
    return re.sub(r"[^A-Za-z0-9]", "_", mn)

def measure(forms):
    """{mnemonic: (executed, refused)} — by EXECUTING, never by reading a catalogue."""
    sel = pre_states()
    body = []
    for mn, _asm, hexbytes, _exp in forms:
        tag = tag_of(mn)
        for i, c in enumerate(sel):
            body.append(rewrite(c, i, tag, hexbytes))
    tmp = tempfile.mkdtemp(prefix="x86lean-avail-")
    cases = os.path.join(tmp, "cases.lsp")
    open(cases, "w").write('(in-package "X86ISA")\n(defconst *x86lean-cases*\n \'(\n'
                           + "".join(body) + "))\n")
    drive = os.path.join(tmp, "drive.lsp")
    open(drive, "w").write(
        '(include-book "projects/x86isa/tools/execution/init-state" :dir :system :ttags :all)\n'
        '(include-book "projects/x86isa/machine/x86" :dir :system :ttags :all)\n'
        "(set-fmt-hard-right-margin 100000 state)\n(set-fmt-soft-right-margin 99000 state)\n"
        '(ld "scripts/x86isa_driver.lisp")\n(ld "%s")\n(in-package "X86ISA")\n'
        "(x86l-run-all *x86lean-cases* x86 state)\n" % cases)
    out = os.path.join(tmp, "out.txt")
    with open(out, "w") as fh:
        subprocess.run([ACL2], stdin=open(drive), stdout=fh, stderr=subprocess.STDOUT)
    res, cur = {}, None
    for l in open(out):
        if l.startswith("CASE "):
            cur = re.search(r"id=(\S+)", l).group(1).rsplit("/", 1)[0]
        elif l.startswith("POST ") and cur:
            e, r, st = res.get(cur, (0, 0, 0))
            # ⛔⛔ P2 BATCH 37 (D170) — THREE-VALUED, AND IT USED TO BE TWO.
            # This read `if refused=1 then refused else EXECUTED`, so `executed`
            # was a RESIDUAL and not a measurement: a case that neither refused
            # nor ran was scored as available.  `movmskps` is the first form to
            # occupy that third state — x86isa leaves RIP unadvanced with the
            # refusal flag CLEAR — and this gate reported it `executes 88/88`
            # while the differential produced 464 field mismatches for it.
            # ⇒ 🔑 A TWO-VALUED CLASSIFIER OVER A THREE-VALUED WORLD SCORES THE
            # UNSEEN STATE AS WHICHEVER VALUE IS THE RESIDUAL, and here the
            # residual was SUCCESS — in the one gate whose stated purpose is to
            # stop unavailable work from being invented.
            # ⚠️ A STALL IS `rip UNCHANGED`, not `rip != entry + len`: a form
            # whose meaning is to move RIP elsewhere (a jump, a taken branch, or
            # a `rep` signalling another iteration by NOT advancing — D46) would
            # be misread by the stricter test.  No such form is in `FORMS` today;
            # one added later must be read against this comment.
            rip = re.search(r"rip=([0-9a-f]+)", l)
            if re.search(r"refused=1", l): r += 1
            elif rip and int(rip.group(1), 16) == ENTRY_RIP: st += 1
            else: e += 1
            res[cur] = (e, r, st)
            cur = None
    return res, len(sel)

def report(forms, res, n, quiet=False):
    bad = []
    for mn, asm, _b, exp in forms:
        tag = tag_of(mn)
        e, r, st = res.get(tag, (0, 0, 0))
        if e + r + st != n:
            bad.append((mn, "produced %d records, expected %d — a missing reading "
                            "is not a refusal" % (e + r + st, n)))
            continue
        got = ("refuses" if r == n else "executes" if e == n
               else "stalls" if st == n else "MIXED")
        if got != exp:
            bad.append((mn, "declared %s, MEASURED %s (executed %d, refused %d, "
                            "stalled %d of %d)" % (exp, got, e, r, st, n)))
        if not quiet:
            mark = "✔" if got == exp else "⛔"
            print(f"  {mark} {mn:22s} {asm:26s} {got:9s} "
                  f"({e} executed, {r} refused, {st} stalled)")
    return bad


# ══════════════════════════════════════════════════════════════════════════
# ⭐⭐ P2's ORACLE-AVAILABILITY RUN (the Captain's 09/03 P2 word).
#
# The P2 roster prices its wave from K's tree, which is a CATALOGUE reading, and
# every batch in it is priced "runnable pending an oracle-availability run".
# This is that run, against the ORACLE — ACL2 x86isa, the differential partner,
# which is a different artifact from the coverage target list.
#
# ⛔⛔ THE FIRST READING WAS A FINDING ABOUT THE PRE-STATES, NOT ABOUT THE ORACLE,
# AND IT POINTED THE WRONG WAY BY 86% OF THE GAP.  Twenty of twenty vector forms
# refused — `movdqa`, `paddd`, every `v`-form — with both controls behaving.  Had
# that gone to the Captain it would have said P2's first three batches have no
# oracle at all, which would have killed the phase.  The oracle's own fault
# record said otherwise: `#UD Encountered!`, and `(ctri 4 x86)` read **0**.
# CR4.OSFXSR was never set, because P0 and P1 only ever needed scalar integer
# instructions, so x86isa raised #UD on SSE exactly as hardware would.
#
# ⇒ 🔑 A REFUSAL IS A FINDING ABOUT THE STATE UNTIL PROVED OTHERWISE, and the
# proof is an ARM THAT CHANGES THE STATE — not a reading of the model's source.
# So the discrimination lives in this gate rather than in a sentence about it:
# every form runs under BOTH CR4 settings, and both readings are declared.
#
# ⚠️ AND A REFUSE-ALWAYS CONTROL RIDES IN THE CR4-ON ARM.  Without `movnti`,
# "I set a bit and everything started executing" is indistinguishable from a
# discriminator that has stopped discriminating
# ([[feedback-a-refusing-form-needs-a-refuse-always-control]]).
#
# ⚠️⚠️ AND "EXECUTES" IS NOT "DIFFERENTIABLE".  x86isa running a form without a
# fault says the ORACLE can be asked.  It does not say the harness can SEE the
# answer: `x86l-post` reports 16 GPRs, RIP, the flags and two memory windows,
# and `X86/State.lean` has no vector register file at all (absent at P0 on
# purpose).  A P2 differential run today would execute every vector form on both
# sides and OBSERVE none of their results — which does not report "unknown", it
# positively reports agreement ([[feedback-unobserved-regions-report-agreement]]).
# THAT is P2's harness cost, and this run does not reduce it by one line.
CR4_OFF = "nil"
CR4_ON  = "'((4 . #x600))"          # OSFXSR | OSXMMEXCPT — what an OS sets

# ⭐⭐ P2 BATCH 19 — THE OPERANDS, WHICH USED TO BE ZERO AND WERE NEVER CHOSEN.
#
# `init-x86-state-64` takes no XMM argument, so until this batch EVERY verdict in
# the table below was a reading taken at xmm0 = xmm1 = 0 — one point of the value
# space, and the single most special value IEEE-754 has.  Nothing declared that;
# it was the default of a function that has no parameter for it, which is the
# quietest kind of frozen dimension ([[feedback-defects-hide-where-nothing-varies]]).
#
# ⛔ AND THE FROZEN POINT CAN INVERT A VERDICT.  `cvtss2sd` at a zero source does
# not execute and does not refuse: it violates an ACL2 guard —
#     (RTL::SSE-POST-COMP U MXCSR F), guard (AND (REAL/RATIONALP U) (NOT (= U 0)) …)
#     violated by (RTL::SSE-POST-COMP 0 8064 '(NIL 53 11))
# — and a guard violation produces NO READING, which is a THIRD verdict this
# table's two-valued model has no slot for.  At any non-zero source the same form
# executes and returns the right answer.  Read at zero it looks unavailable; it is
# available.  ⇒ 🔑 A PROBE THAT NEVER VARIES A DIMENSION REPORTS THE DEFAULT OF
# THAT DIMENSION, AND THE DEFAULT LOOKS LIKE AN ANSWER.
#
# ⚠️ WHY THESE BYTES AND NOT A RANDOM PATTERN.  The same 128 bits must be an
# ORDINARY value under every reading this table takes, because the question is
# "can the oracle run this form", not "can it run this value":
#     low 32  0x40404040 = 3.0078f      — a normal single
#     low 64  0x4040404040404040 ≈ 32.5 — a normal double
#     as packed bytes/words/dwords      — ordinary non-zero integers
# A random pattern would have been a NaN or a denormal under some reading and
# would have turned a availability probe into a value probe.
#
# ⛔ THE ZERO READING IS NOT DISCARDED — it is the SELFTEST's positive control
# (`--selftest`, the `cvtss2sd` arm).  It must still crash, or the xmm write below
# silently did nothing and every "executes" in this table is once again a reading
# at zero wearing a non-zero label ([[feedback-a-probe-must-create-its-condition]]).
XMM0_NZ = 0x40404040404040404040404040404040
XMM1_NZ = 0x40204020402040204020402040204020

# (label, asm, bytes, expect at CR4=0, expect at CR4=0x600)
#
# ⚠️ THE CR4=0 COLUMN FOR THE SSE ROWS IS A PREDICTION, NOT A SECOND READING.
# Those forms were measured only at CR4=0x600; "refuses with SSE disabled" is
# what the hardware rule says must happen, so it is DECLARED here and the gate
# measures it on every run.  A prediction a gate tests immediately is worth
# having; a prediction written into prose is not.
P2_FORMS = [
    # ── batch 1, SSE-legacy (xmm): 67.3% of the measured gap ──
    ("movdqa",     "movdqa (%rbx), %xmm0",        "660f6f03",     "refuses", "executes"),
    ("paddd",      "paddd %xmm1, %xmm0",          "660ffec1",     "refuses", "executes"),
    ("movdqu",     "movdqu (%rbx), %xmm0",        "f30f6f03",     "refuses", "executes"),
    ("movaps",     "movaps (%rbx), %xmm0",        "0f2803",       "refuses", "executes"),
    ("pxor",       "pxor %xmm1, %xmm0",           "660fefc1",     "refuses", "executes"),
    ("pshufd",     "pshufd $0x1b, %xmm1, %xmm0",  "660f70c11b",   "refuses", "executes"),
    ("paddw",      "paddw %xmm1, %xmm0",          "660ffdc1",     "refuses", "executes"),
    ("movd",       "movd %ecx, %xmm0",            "660f6ec1",     "refuses", "executes"),
    ("movss",      "movss (%rbx), %xmm0",         "f30f1003",     "refuses", "executes"),
    ("punpcklwd",  "punpcklwd %xmm1, %xmm0",      "660f61c1",     "refuses", "executes"),
    ("por",        "por %xmm1, %xmm0",            "660febc1",     "refuses", "executes"),
    ("movups",     "movups (%rbx), %xmm0",        "0f1003",       "refuses", "executes"),
    ("psrad",      "psrad $0x3, %xmm0",           "660f72e003",   "refuses", "executes"),
    ("psubw",      "psubw %xmm1, %xmm0",          "660ff9c1",     "refuses", "executes"),
    ("punpcklbw",  "punpcklbw %xmm1, %xmm0",      "660f60c1",     "refuses", "executes"),
    ("punpckhwd",  "punpckhwd %xmm1, %xmm0",      "660f69c1",     "refuses", "executes"),
    ("movsd",      "movsd (%rbx), %xmm0",         "f20f1003",     "refuses", "executes"),
    ("pand",       "pand %xmm1, %xmm0",           "660fdbc1",     "refuses", "executes"),
    ("punpckldq",  "punpckldq %xmm1, %xmm0",      "660f62c1",     "refuses", "executes"),
    ("psllw",      "psllw $0x2, %xmm0",           "660f71f002",   "refuses", "executes"),
    ("packuswb",   "packuswb %xmm1, %xmm0",       "660f67c1",     "refuses", "executes"),
    ("movq_xmm",   "movq %xmm0, %rax",            "66480f7ec0",   "refuses", "executes"),
    # ⛔⛔ AND THE ONES THE ORACLE DOES NOT HAVE, WHICH IS WHY A BATCH CANNOT BE
    # PRICED FROM A SAMPLE OF ITS OWN MEMBERS.  `pmaddwd` refuses with SSE fully
    # enabled, in the same run in which `movdqa` beside it executes: seven forms
    # had been probed and all seven executed; the eighth did not.
    # ⚠️ THE COUNT AND THE RANK ARE DELIBERATELY NOT WRITTEN HERE.  This comment
    # said "THE NINE" and "rank 4 ... 2.31% of the whole gap" from `00dd9ea` until
    # D127.  All three drifted (49, rank 1, 5.15%) and two were already false in
    # the commit that introduced them — the table beside them said REFUSES 11 and
    # ranked `pmaddwd` 5th on the day they were typed.  The live figures are
    # DERIVED into `docs/P2-ROSTER.md` from `b["joined"]` and `rf_names`; read
    # them there, where a regeneration cannot leave them behind.
    # ⇒ 🔑 a byte-for-byte derivation gate proves `file == script`, never
    #   `script == true`, so a hand-written figure is invisible to it forever —
    #   and a figure in a COMMENT is invisible to every gate there is.
    ("pmaddwd",    "pmaddwd %xmm1, %xmm0",        "660ff5c1",     "refuses", "refuses"),
    ("psubusw",    "psubusw %xmm1, %xmm0",        "660fd9c1",     "refuses", "refuses"),
    ("psadbw",     "psadbw %xmm1, %xmm0",         "660ff6c1",     "refuses", "refuses"),
    ("pmullw",     "pmullw %xmm1, %xmm0",         "660fd5c1",     "refuses", "refuses"),
    ("pmaxsw",     "pmaxsw %xmm1, %xmm0",         "660feec1",     "refuses", "refuses"),
    ("pminsw",     "pminsw %xmm1, %xmm0",         "660feac1",     "refuses", "refuses"),
    ("pshufb",     "pshufb %xmm1, %xmm0",         "660f3800c1",   "refuses", "refuses"),
    ("pmulhrsw",   "pmulhrsw %xmm1, %xmm0",       "660f380bc1",   "refuses", "refuses"),
    ("palignr",    "palignr $0x4, %xmm1, %xmm0",  "660f3a0fc104", "refuses", "refuses"),
    # ⛔⛔⛔ P2 BATCH 16 — EIGHTEEN MORE, AND THE ROSTER WAS RANKING EVERY ONE OF
    # THEM AS AVAILABLE WORK.  The P2 roster's oracle column reads `⚠️ not
    # measured` for any row this table does not name, and D65's law is that a
    # declared list inherits the direction of its DEFAULT — this one defaults to
    # AVAILABLE, so an unmeasured row does not read "unknown", it reads "go build
    # it".  Thirteen non-VEX rows carried that mark; one ACL2 run moved eighteen
    # mnemonics out of the residue.
    #
    # ⚠️ WHAT MAKES THIS WORSE THAN A GAP: the batch that found it went looking
    # for the PACK group — `packssdw`, rank 15, 5,613 instructions, `⚠️ not
    # measured` — and would have written a batch's semantics against an oracle
    # that cannot execute it.  `packuswb` beside it DOES execute, so a group
    # sampled at one member would have passed
    # ([[feedback-a-batch-cannot-be-sampled]], the law that made `pmaddwd` a
    # surprise at rank 1, paid a second time at rank 15).
    #
    # ⭐ BOTH CONTROLS RODE IN THE SAME RUN AND BOTH BEHAVED: `packuswb` and
    # `paddd` executed at all 88 pre-states, `pmaddwd` refused at all 88.
    #
    # THE WHOLE SATURATING ADD/SUBTRACT FAMILY, named as a family rather than as
    # eight rows: x86isa has no saturating packed arithmetic at all.
    ("paddsb",     "paddsb %xmm1, %xmm0",         "660fecc1",     "refuses", "refuses"),
    ("paddsw",     "paddsw %xmm1, %xmm0",         "660fedc1",     "refuses", "refuses"),
    ("paddusb",    "paddusb %xmm1, %xmm0",        "660fdcc1",     "refuses", "refuses"),
    ("paddusw",    "paddusw %xmm1, %xmm0",        "660fddc1",     "refuses", "refuses"),
    ("psubsb",     "psubsb %xmm1, %xmm0",         "660fe8c1",     "refuses", "refuses"),
    ("psubsw",     "psubsw %xmm1, %xmm0",         "660fe9c1",     "refuses", "refuses"),
    ("psubusb",    "psubusb %xmm1, %xmm0",        "660fd8c1",     "refuses", "refuses"),
    # the averages, the unsigned min/max pair, and four multiplies
    ("pavgb",      "pavgb %xmm1, %xmm0",          "660fe0c1",     "refuses", "refuses"),
    ("pavgw",      "pavgw %xmm1, %xmm0",          "660fe3c1",     "refuses", "refuses"),
    ("pmaxub",     "pmaxub %xmm1, %xmm0",         "660fdec1",     "refuses", "refuses"),
    ("pminub",     "pminub %xmm1, %xmm0",         "660fdac1",     "refuses", "refuses"),
    ("pmulhw",     "pmulhw %xmm1, %xmm0",         "660fe5c1",     "refuses", "refuses"),
    ("pmuludq",    "pmuludq %xmm1, %xmm0",        "660ff4c1",     "refuses", "refuses"),
    ("pmaddubsw",  "pmaddubsw %xmm1, %xmm0",      "660f3804c1",   "refuses", "refuses"),
    # ⛔ AND THE TWO SIGNED PACKS — `packuswb`'s own siblings.  `packssdw` is
    # roster rank 15 at 5,613 and CANNOT BE BUILT; `packsswb` is not in the
    # ranked table at all.  The UNSIGNED one executes and is declared above.
    ("packssdw",   "packssdw %xmm1, %xmm0",       "660f6bc1",     "refuses", "refuses"),
    ("packsswb",   "packsswb %xmm1, %xmm0",       "660f63c1",     "refuses", "refuses"),
    # ⭐⭐ AND THE SEVEN THAT DO EXECUTE — declared so the roster stops calling
    # them UNMEASURED and a later head can pick a batch from a MEASUREMENT.  The
    # six packed COMPARES are the next buildable group in the whole residue.
    ("pcmpeqb",    "pcmpeqb %xmm1, %xmm0",        "660f74c1",     "refuses", "executes"),
    ("pcmpeqw",    "pcmpeqw %xmm1, %xmm0",        "660f75c1",     "refuses", "executes"),
    ("pcmpeqd",    "pcmpeqd %xmm1, %xmm0",        "660f76c1",     "refuses", "executes"),
    ("pcmpgtb",    "pcmpgtb %xmm1, %xmm0",        "660f64c1",     "refuses", "executes"),
    ("pcmpgtw",    "pcmpgtw %xmm1, %xmm0",        "660f65c1",     "refuses", "executes"),
    ("pcmpgtd",    "pcmpgtd %xmm1, %xmm0",        "660f66c1",     "refuses", "executes"),
    ("pmovmskb",   "pmovmskb %xmm1, %eax",        "660fd7c1",     "refuses", "executes"),
    # ── P2 BATCH 11's CANDIDATES: the packed SHIFT group and the permute.
    #    ⛔ PROBED PER FORM, NOT PER GROUP.  `psllw` and `psrad` at an immediate
    #    were already measured executing, and seven of their siblings had never
    #    been asked — which is exactly the sample that made `pmaddwd` a surprise
    #    at rank 1 ([[feedback-a-batch-cannot-be-sampled]]).  Both COUNT SHAPES
    #    are probed, because `psrad $imm` and `psrad %xmm` are different opcodes
    #    (`66 0f 72 /4 ib` against `66 0f e2 /r`) and an oracle may have one.
    ("psrlw_i",    "psrlw $0x2, %xmm0",           "660f71d002",   "refuses", "executes"),
    ("psraw_i",    "psraw $0x2, %xmm0",           "660f71e002",   "refuses", "executes"),
    ("psrld_i",    "psrld $0x2, %xmm0",           "660f72d002",   "refuses", "executes"),
    ("pslld_i",    "pslld $0x2, %xmm0",           "660f72f002",   "refuses", "executes"),
    ("psrlq_i",    "psrlq $0x2, %xmm0",           "660f73d002",   "refuses", "executes"),
    ("psllq_i",    "psllq $0x2, %xmm0",           "660f73f002",   "refuses", "executes"),
    ("psrldq_i",   "psrldq $0x2, %xmm0",          "660f73d802",   "refuses", "executes"),
    ("pslldq_i",   "pslldq $0x2, %xmm0",          "660f73f802",   "refuses", "executes"),
    ("psrad_x",    "psrad %xmm1, %xmm0",          "660fe2c1",     "refuses", "executes"),
    ("psrlw_x",    "psrlw %xmm1, %xmm0",          "660fd1c1",     "refuses", "executes"),
    # ── ⭐⭐ batch 19, SCALAR SSE FLOATING POINT: 26,757 instructions, 6.4% of the
    #    whole P2 gap, and NEVER ASKED ABOUT until this batch.  Batch 18's bank
    #    closed with "everything larger either refuses or is VEX".  The first half
    #    of that sentence was scoped to the PROBED set and was true; the second
    #    half was a claim about the WHOLE residue and was false — these six are
    #    neither refusing nor VEX, they were simply never in the table.  ⇒ 🔑 A
    #    CATEGORY WITH NO SLOT IN THE SENTENCE READS AS ABSENT, and a bank's
    #    closing "next" line is the sentence nobody re-derives.
    #
    #    ⚠️ ALL SIX EXECUTE, and the arithmetic is RIGHT, not merely non-faulting:
    #    measured 2.0*3.0 = 6.0 (0x40C00000), 2.0+3.0 = 5.0 (0x40A00000),
    #    cvtss2sd 3.0f -> 3.0 (0x4008000000000000).  A form that faults is easy to
    #    tell from one that runs; a form that RUNS WRONG is not, so the values were
    #    checked against IEEE-754 by hand rather than assumed from a clean exit.
    #
    #    ⛔ "EXECUTES" HERE IS NOT "BUILDABLE THIS WEEK".  `X86/State.lean` has no
    #    MXCSR (absent on purpose, D2) and Lean's own `Float` is an opaque extern
    #    type the kernel cannot reduce, so these six need a soft-float IEEE-754
    #    layer over `BitVec` plus a new state field — and a state field costs every
    #    record proof ([[feedback-a-state-field-costs-every-record-proof]]).  That
    #    is a DESIGN BLOCK, priced in D118, not the next vector batch.
    ("mulss",      "mulss %xmm1, %xmm0",          "f30f59c1",     "refuses", "executes"),
    ("mulsd",      "mulsd %xmm1, %xmm0",          "f20f59c1",     "refuses", "executes"),
    ("addss",      "addss %xmm1, %xmm0",          "f30f58c1",     "refuses", "executes"),
    ("addsd",      "addsd %xmm1, %xmm0",          "f20f58c1",     "refuses", "executes"),
    ("movhps",     "movhps (%rbx), %xmm0",        "0f1603",       "refuses", "executes"),
    # ⛔ THE ROW THAT COULD NOT BE WRITTEN BEFORE THE PROBE WAS REPAIRED.  At the
    # old zero operands this form produces NO READING (an ACL2 guard violation,
    # not a refusal), so declaring it `executes` would have FAILED the gate for a
    # reason that had nothing to do with the oracle's support for it.  The
    # measurement forced the instrument, rather than the instrument bounding the
    # measurement ([[feedback-a-gate-that-refuses-names-a-cheaper-build]]).
    ("cvtss2sd",   "cvtss2sd %xmm1, %xmm0",       "f30f5ac1",     "refuses", "executes"),
    # ── batch 2, AVX2/AVX (ymm): 11.8% ──
    ("vmovdqa_y",  "vmovdqa (%rbx), %ymm0",       "c5fd6f03",     "refuses", "executes"),
    ("vpaddd_y",   "vpaddd %ymm1, %ymm2, %ymm0",  "c5edfec1",     "refuses", "executes"),
    # ── batch 3, VEX-128: 6.8% ──
    ("vpxor_x",    "vpxor %xmm1, %xmm2, %xmm0",   "c5e9efc1",     "refuses", "executes"),
    # ── batch 4, MMX: 4.7%.  ⭐ MMX predates SSE and needs no CR4 bit — which is
    #    itself the control that says the CR4 arm is changing the right thing. ──
    ("movq_mmx",   "movq %mm1, %mm0",             "0f6fc1",       "executes", "executes"),
    ("paddw_mmx",  "paddw %mm1, %mm0",            "0ffdc1",       "executes", "executes"),
    # ── batch 5, AVX-512: 3.7%.  ⛔ REFUSES IN BOTH ARMS — the one batch this
    #    oracle cannot answer at all, and the only one that needs another. ──
    ("vmovdqa32",  "vmovdqa32 (%rbx), %zmm0",     "62f17d486f03", "refuses", "refuses"),
    ("vpaddw_z",   "vpaddw %zmm1, %zmm2, %zmm0",  "62f16d48fdc1", "refuses", "refuses"),
    # ── batch 6, CET-IBT: 1.8% ──
    ("endbr64",    "endbr64",                     "f30f1efa",     "executes", "executes"),
    # ── the three additions, in the Captain's order: ALL THREE ALREADY EXECUTE ──
    ("ADD1:mov %gs:", "movq %gs:0x28, %rax",      "65488b042528000000", "executes", "executes"),
    ("ADD2:lock incl", "lock incl (%rbx)",        "f0ff03",       "executes", "executes"),
    ("ADD3:movabsq", "movabsq $0x123456789abc, %rax",
                                    "48b8bc9a785634120000", "executes", "executes"),
    # ── ⭐⭐ batch 21, THE CENSUS OF THE UNPROBED REMAINDER.  The 19:21 ruling
    #    makes arm C ripen "when the measured buildable list is EMPTY — post the
    #    census that proves it".  D118's lesson is that an ASSERTED-empty queue is
    #    exactly the thing that turns out to be wrong, so the remainder was
    #    MEASURED before anything was declared about it.
    #
    #    ⛔⛔ AND VEX IS SPLIT, WHICH NO PRIOR SENTENCE HERE ALLOWED FOR.  Batch
    #    18's bank read "everything larger either refuses or is VEX", treating VEX
    #    as a single class blocked only by OUR decoding vocabulary.  It is not one
    #    class: `vmovaps`/`vpsubw`/`vmovdqu` at ymm EXECUTE, while `vpmaddwd`,
    #    `vpsrad`, `vpshufb`, `vpbroadcastd`, `vaddps`, `vmulps` and `vshufps`
    #    REFUSE.  So the VEX residue is blocked by BOTH causes at once, in
    #    different places, and a plan that priced only the vocabulary would have
    #    been wrong about which rows it bought.
    #
    #    ⭐ AND TWO ROWS ARE BUILDABLE TODAY: `prefetchnta` and `prefetcht0` (466
    #    instructions) EXECUTE and are architecturally NO-OPS — they change no
    #    state this model observes.  ⚠️ That claim is the one to distrust
    #    ([[feedback-the-burden-is-on-the-departure]]): a "no-op" is only a no-op
    #    where the write is invisible, so it is written here as a MEASUREMENT of
    #    the oracle and NOT yet as a semantics.
    ("vmovaps",    "vmovaps (%rbx), %ymm0",       "c5fc2803",     "refuses", "executes"),
    ("vpsubw",     "vpsubw %ymm1, %ymm2, %ymm0",  "c5edf9c1",     "refuses", "executes"),
    ("vmovdqu",    "vmovdqu (%rbx), %ymm0",       "c5fe6f03",     "refuses", "executes"),
    ("vpmaddwd",   "vpmaddwd %ymm1, %ymm2, %ymm0", "c5edf5c1",    "refuses", "refuses"),
    ("vpsrad",     "vpsrad $3, %ymm1, %ymm0",     "c5fd72e103",   "refuses", "refuses"),
    ("vpshufb",    "vpshufb %ymm1, %ymm2, %ymm0", "c4e26d00c1",   "refuses", "refuses"),
    ("vpbroadcastd", "vpbroadcastd %xmm1, %ymm0", "c4e27d58c1",   "refuses", "refuses"),
    ("vaddps",     "vaddps %ymm1, %ymm2, %ymm0",  "c5ec58c1",     "refuses", "refuses"),
    ("vmulps",     "vmulps %ymm1, %ymm2, %ymm0",  "c5ec59c1",     "refuses", "refuses"),
    ("vshufps",    "vshufps $27, %ymm1, %ymm2, %ymm0", "c5ecc6c11b", "refuses", "refuses"),
    # ⚠️ The two integer->float converts JOIN THE SOFT-FLOAT COMMISSION (D118 §5):
    # they execute on the oracle and are blocked by this model's lack of MXCSR and
    # of a kernel-reducible float, not by the oracle.  23,085 becomes 25,688.
    ("cvtsi2sd",   "cvtsi2sdl %ecx, %xmm0",       "f20f2ac1",     "refuses", "executes"),
    ("cvtsi2ss",   "cvtsi2ssl %ecx, %xmm0",       "f30f2ac1",     "refuses", "executes"),
    ("prefetchnta", "prefetchnta (%rbx)",         "0f1803",       "executes", "executes"),
    ("prefetcht0", "prefetcht0 (%rbx)",           "0f180b",       "executes", "executes"),
    # ── ⭐⭐ batch 24, THE VEX-128 BUCKET — and the reason a mnemonic already in
    #    this table could still read `not measured`.
    #
    #    ⛔⛔ THE JOIN IS PER (MNEMONIC, BUCKET), AND THAT IS NOT A TECHNICALITY.
    #    Batch 21 probed `vpsubw` at **ymm** and it EXECUTES; the roster went on
    #    printing `⚠️ not measured` for `vpsubw`, because its DEMAND is dominantly
    #    VEX-128 and `dominant_bucket` correctly refuses to carry a ymm reading
    #    across to an xmm row.  The same mnemonic is two questions.
    #    ⇒ 🔑 A CENSUS IS NOT FINISHED WHEN EVERY MNEMONIC HAS BEEN NAMED; it is
    #    finished when every (mnemonic, BUCKET) the demand actually occupies has
    #    been asked.  Eleven ranked rows and 48,525 instructions were still
    #    unmeasured after batch 21 for exactly this reason.
    #
    #    ⚠️ AND THE ANSWER DIFFERS BY WIDTH, so the caution was earned:
    #    `vpsubw` executes at BOTH widths, but `vpaddw` — rank 4, 11,682
    #    instructions — is measured here at xmm where batch 21 never reached it.
    ("vpaddw",     "vpaddw %xmm1, %xmm2, %xmm0",     "c5e9fdc1",   "refuses", "executes"),
    # ⛔ RENAMED FROM `vpsubw` BY D130, AND THE RENAME IS THE REPAIR. This row
    # and the ymm row above it shared one LABEL, so `measure_cr4` printed two
    # `P2RESULT tag=vpsubw` lines and its collector kept the LAST — one
    # reading scored against two rows in two different BUCKETS. See
    # `p2_structure_check`.
    ("vpsubw_v",   "vpsubw %xmm1, %xmm2, %xmm0",     "c5e9f9c1",   "refuses", "executes"),
    ("vpmulhrsw",  "vpmulhrsw %xmm1, %xmm2, %xmm0",  "c4e2690bc1", "refuses", "refuses"),
    ("vpunpcklwd", "vpunpcklwd %xmm1, %xmm2, %xmm0", "c5e961c1",   "refuses", "refuses"),
    ("vpunpckhwd", "vpunpckhwd %xmm1, %xmm2, %xmm0", "c5e969c1",   "refuses", "refuses"),
    ("vpmaddubsw", "vpmaddubsw %xmm1, %xmm2, %xmm0", "c4e26904c1", "refuses", "refuses"),
    ("vpackssdw",  "vpackssdw %xmm1, %xmm2, %xmm0",  "c5e96bc1",   "refuses", "refuses"),
    ("vmovq",      "vmovq %xmm1, %xmm0",             "c5fa7ec1",   "refuses", "refuses"),
    ("vsubps",     "vsubps %xmm1, %xmm2, %xmm0",     "c5e85cc1",   "refuses", "refuses"),
    # ── ⭐⭐⭐ batch 25, THE UNASKED REMAINDER, RANKED BY A TOOL RATHER THAN BY EYE.
    #
    #    `p2_roster.py --unprobed` prints every (mnemonic, BUCKET) pair the census
    #    has demand for and has never asked, with the demand each would resolve.
    #    Before it existed the rule from batch 24 was applied by hand, and eleven
    #    rows sat unasked for three batches because doing it by eye is how a list
    #    of 328 pairs gets sampled instead of worked.
    #
    #    ⛔ THE TOOL ALSO REPORTS THAT THIS DOCUMENT ANSWERS THE QUESTION TWICE.
    #    Counted by NAME — is the mnemonic anywhere in this table? — 64.5% of the
    #    gap is probed. Counted by KEY — is it asked at the bucket its demand
    #    lives in, which is what each roster row actually looks up? — 52.3%. The
    #    12.1% between them is 50,646 instructions that read as measured and are
    #    not. See D124.
    #
    #    ⚠️ ENCODINGS ASSEMBLED BY clang AND READ BACK FROM THE DISASSEMBLY, never
    #    typed: a hand-written byte string is a control for a different
    #    instruction, and this repository has already paid for one (the batch-24
    #    alignment control that dropped a `66` prefix and became MMX `pand`).
    ('vpaddw_y',        'vpaddw %ymm1, %ymm2, %ymm0',           'c5edfdc1',       "refuses", "executes"),
    ('vpmulhrsw_y',     'vpmulhrsw %ymm1, %ymm2, %ymm0',        'c4e26d0bc1',     "refuses", "refuses"),
    ('vpunpcklwd_y',    'vpunpcklwd %ymm1, %ymm2, %ymm0',       'c5ed61c1',       "refuses", "refuses"),
    ('vpunpckhwd_y',    'vpunpckhwd %ymm1, %ymm2, %ymm0',       'c5ed69c1',       "refuses", "refuses"),
    ('vpmaddubsw_y',    'vpmaddubsw %ymm1, %ymm2, %ymm0',       'c4e26d04c1',     "refuses", "refuses"),
    ('vpackssdw_y',     'vpackssdw %ymm1, %ymm2, %ymm0',        'c5ed6bc1',       "refuses", "refuses"),
    ('vsubps_y',        'vsubps %ymm1, %ymm2, %ymm0',           'c5ec5cc1',       "refuses", "refuses"),
    ('vpabsw_y',        'vpabsw %ymm1, %ymm0',                  'c4e27d1dc1',     "refuses", "refuses"),
    ('vpunpcklbw_y',    'vpunpcklbw %ymm1, %ymm2, %ymm0',       'c5ed60c1',       "refuses", "refuses"),
    ('vpmulld_y',       'vpmulld %ymm1, %ymm2, %ymm0',          'c4e26d40c1',     "refuses", "refuses"),
    ('vinserti128_y',   'vinserti128 $1, %xmm1, %ymm2, %ymm0',  'c4e36d38c101',   "refuses", "refuses"),
    ('vmovd_x',         'vmovd %xmm1, %eax',                    'c5f97ec8',       "refuses", "refuses"),
    ('vpsubd_x',        'vpsubd %xmm1, %xmm2, %xmm0',           'c5e9fac1',       "refuses", "executes"),
    ('vmovhps_x',       'vmovhps %xmm1, (%rbx)',                'c5f8170b',       "refuses", "refuses"),
    ('vpand_x',         'vpand %xmm1, %xmm2, %xmm0',            'c5e9dbc1',       "refuses", "executes"),
    ('vpor_x',          'vpor %xmm1, %xmm2, %xmm0',             'c5e9ebc1',       "refuses", "executes"),
    ('pandn',           'pandn %xmm1, %xmm0',                   '660fdfc1',       "refuses", "executes"),
    ('movapd',          'movapd %xmm1, %xmm0',                  '660f28c1',       "refuses", "executes"),
    ('subss',           'subss %xmm1, %xmm0',                   'f30f5cc1',       "refuses", "executes"),
    ('subsd',           'subsd %xmm1, %xmm0',                   'f20f5cc1',       "refuses", "executes"),
    ('movntdqa',        'movntdqa (%rbx), %xmm0',               '660f382a03',     "refuses", "refuses"),
    ('movd_mmx',        'movd %mm1, %eax',                      '0f7ec8',         "executes", "executes"),
    ('psubw_mmx',       'psubw %mm1, %mm0',                     '0ff9c1',         "executes", "executes"),
    ('punpcklbw_mmx',   'punpcklbw %mm1, %mm0',                 '0f60c1',         "executes", "executes"),
    ('pxor_mmx',        'pxor %mm1, %mm0',                      '0fefc1',         "executes", "executes"),
    # ⚠️ MMX, and DECLINED BY DESIGN rather than by the oracle — this model has no
    # MMX register file.  `emms` executes and `pshufw` refuses; both are recorded
    # so neither reads as available work.
    ("emms",       "emms",                        "0f77",         "executes", "executes"),
    ("pshufw",     "pshufw $27, %mm1, %mm0",      "0f70c11b",     "refuses", "refuses"),
    # ⭐⭐ P2 BATCH 26 — THE TOP OF `p2_roster.py --unprobed`, ASKED.
    #    Twenty-three (mnemonic, bucket) pairs, ranks 1-24 of the ranked unasked
    #    list (rank 21 `vzeroupper` is SKIPPED and the reason is D128 §5: its
    #    bucket `AVX (state)` is one `probe_bucket` cannot express, so a probe
    #    for it would be dropped from `measured_availability` and the pair would
    #    stay unasked no matter how often it was asked).
    #    ⛔ EVERY `hx` BELOW CAME FROM `clang`, none was typed, and D128's gate
    #    re-derives all of them on both disassemblers at every CI run.
    #    ⚠️ ASKED PER PAIR, NEVER PER GROUP ([[feedback-a-batch-cannot-be-sampled]]):
    #    the VEX-128 and ymm spellings of the same mnemonic are different keys and
    #    are probed separately, because that is exactly the sampling that made
    #    `pmaddwd` a surprise at rank 1.
    #    ⛔⛔ AND IT HAPPENED AGAIN, IN THIS BATCH, ON THE PREDICTION. Eighteen of
    #    the twenty-three verdicts were predicted correctly before the run; FIVE
    #    were wrong and ALL FIVE in the same direction (predicted `executes`,
    #    measured `refuses`). Four of them are the VEX-128 unpacks — and their
    #    SSE-legacy siblings `punpckldq`/`punpcklwd`/`punpcklbw`/`punpckhwd` all
    #    EXECUTE, three of them declared a few dozen lines above this comment.
    #    ⇒ 🔑 THE SAME OPERATION HAS DIFFERENT ORACLE SUPPORT AT DIFFERENT
    #      ENCODINGS, which is the whole reason the census key is (mnemonic,
    #      BUCKET) and not a mnemonic. A verdict inferred from a sibling in
    #      another bucket is not evidence about this one.
    ("vpackuswb",   "vpackuswb %ymm1, %ymm2, %ymm0",   "c5ed67c1",     "refuses", "refuses"),
    ("pmulhuw",     "pmulhuw %xmm1, %xmm0",            "660fe4c1",     "refuses", "refuses"),
    ("vpaddsw",     "vpaddsw %ymm1, %ymm2, %ymm0",     "c5ededc1",     "refuses", "refuses"),
    ("shufps",      "shufps $0x1b, %xmm1, %xmm0",      "0fc6c11b",     "refuses", "executes"),
    ("vpunpckldq",  "vpunpckldq %xmm1, %xmm2, %xmm0",  "c5e962c1",     "refuses", "refuses"),
    ("vpsraw",      "vpsraw $0x2, %ymm1, %ymm0",       "c5fd71e102",   "refuses", "refuses"),
    ("vpunpcklqdq", "vpunpcklqdq %xmm1, %xmm2, %xmm0", "c5e96cc1",     "refuses", "refuses"),
    ("vextracti128","vextracti128 $0x1, %ymm1, %xmm0", "c4e37d39c801", "refuses", "refuses"),
    ("vpmaxsw",     "vpmaxsw %ymm1, %ymm2, %ymm0",     "c5edeec1",     "refuses", "refuses"),
    ("vpunpckhqdq", "vpunpckhqdq %xmm1, %xmm2, %xmm0", "c5e96dc1",     "refuses", "refuses"),
    ("vxorps",      "vxorps %ymm1, %ymm2, %ymm0",      "c5ec57c1",     "refuses", "executes"),
    ("vpminsw",     "vpminsw %ymm1, %ymm2, %ymm0",     "c5edeac1",     "refuses", "refuses"),
    ("vpunpckhdq",  "vpunpckhdq %xmm1, %xmm2, %xmm0",  "c5e96ac1",     "refuses", "refuses"),
    ("movhlps",     "movhlps %xmm1, %xmm0",            "0f12c1",       "refuses", "executes"),
    ("vpermq",      "vpermq $0x1b, %ymm1, %ymm0",      "c4e3fd00c11b", "refuses", "refuses"),
    ("vpsubusb",    "vpsubusb %xmm1, %xmm2, %xmm0",    "c5e9d8c1",     "refuses", "refuses"),
    ("pabsw",       "pabsw %xmm1, %xmm0",              "660f381dc1",   "refuses", "refuses"),
    ("cvtsd2ss",    "cvtsd2ss %xmm1, %xmm0",           "f20f5ac1",     "refuses", "executes"),
    ("divsd",       "divsd %xmm1, %xmm0",              "f20f5ec1",     "refuses", "executes"),
    ("vpunpckhbw",  "vpunpckhbw %ymm1, %ymm2, %ymm0",  "c5ed68c1",     "refuses", "refuses"),
    ("pinsrw",      "pinsrw $0x3, %ecx, %xmm0",        "660fc4c103",   "refuses", "refuses"),
    ("packuswb_mmx","packuswb %mm1, %mm0",             "0f67c1",       "executes", "executes"),
    ("comisd",      "comisd %xmm1, %xmm0",             "660f2fc1",     "refuses", "executes"),
    # ══════════════════════════════════════════════════════════════════
    # P2 BATCH 27 — ranks 2-24 of `p2_roster.py --unprobed`, 23 pairs.
    # Rank 1 `vzeroupper` / `AVX (state)` is SKIPPED, again and deliberately:
    # `probe_bucket` reads the bucket off the OPERANDS and that bucket has none,
    # so a probe for it runs, has its verdict DISCARDED, and leaves the pair
    # exactly as unasked as before (D128 §5).  Named here so the next head does
    # not spend a probe rediscovering it.
    # ⛔ EVERY `hx` BELOW CAME FROM `clang`, none was typed; D128's gate
    # re-derives all of them on BOTH disassemblers at every CI run.
    #
    # ⭐⭐ THE PREDICTION ROUTE CHANGED THIS BATCH, BECAUSE b26's ROUTE FAILED.
    # b26 predicted from SIBLING BASE RATES and got five wrong, all in the same
    # direction, four of them by inferring a VEX-128 verdict from an SSE-legacy
    # sibling.  So b27's declarations were read off x86isa's own instruction
    # listing instead, `machine/inst-listing.lisp`, at THE ENTRY WHOSE ENCODING
    # MATCHES THE BYTES CLANG PRODUCED (VEX/EVEX class, vector length, prefix,
    # opcode, /reg).  A `'NIL` semantic-function slot ⇒ declare refuses.
    # ⛔⛔ CORRECTED BY D132: THIS PARAGRAPH ORIGINALLY CALLED THE LISTING "A
    # SECOND SOURCE" AND IT IS NOT ONE.  `machine/dispatch-creator.lisp` includes
    # `inst-listing` and builds the opcode dispatch FROM it, so the slot read
    # here is the datum that DECIDES the running machine's behaviour.  The
    # listing and the machine are ONE source read two ways.  ⇒ the 23 of 23 below
    # is not a model of the oracle proving itself; it is this reading proving
    # FAITHFUL.  A miss would have been the finding.  See
    # `scripts/p2_oracle_support.py`, which generalises the read and scores it on
    # all 168 measured pairs.
    # ⚠️ The CR4=0 column is predicted too, and independently: MMX needs neither
    # OSFXSR nor OSXMMEXCPT, so the four MMX forms are predicted to execute in
    # BOTH arms (as the shipped `packuswb_mmx` row does), and every SSE/AVX form
    # to refuse at CR4=0.  A miss in that column is its own finding.
    #
    # ⭐⭐ THE RESULT: 23 OF 23, IN BOTH COLUMNS (46 of 46 cells), against b26's
    # 18 of 23 on the base-rate route.  ⛔ AND A GREEN THAT EASY IS A SUSPECT —
    # the pricing below is what it bought, and chasing it is what found D132's
    # correction above.  Three naive rules scored on the same 23, on the
    # published CR4=0x600 column:
    #     "always refuses"                    17 / 23
    #     "always executes"                    6 / 23
    #     "refuse iff VEX/EVEX (v-prefixed)"  20 / 23   <- the best baseline
    #     THE CATALOGUE ROUTE                 23 / 23
    # It beats the best baseline on exactly three rows, and they are the three
    # that discriminate: `pmuldq` and `movntdq` are legacy SSE forms the baseline
    # calls executes and the oracle REFUSES (no semantic function), and
    # `vpcmpeqw` is a VEX.256 form the baseline calls refuses and the oracle
    # EXECUTES.  ⚠️ The probe is also demonstrably not stuck: three distinct
    # verdict patterns came back in one run — (executes, executes) x4,
    # (refuses, executes) x2, (refuses, refuses) x17.
    # ⛔ WHAT THIS DOES NOT LICENSE: the remaining 258 pairs.  A batch cannot be
    # sampled ([[feedback-a-batch-cannot-be-sampled]]) — this is 23 asked pairs
    # across 5 buckets, not a proof about the route.  The catalogue stays a
    # SCREEN that makes a prediction scorable; `measured_availability` still
    # publishes only what ACL2 executed.
    ("vpsrlw_y",       "vpsrlw $0x2, %ymm1, %ymm0",           "c5fd71d102",   "refuses", "refuses"),
    ("pmuldq",         "pmuldq %xmm1, %xmm0",                 "660f3828c1",   "refuses", "refuses"),
    ("vpshufd_y",      "vpshufd $0x1b, %ymm1, %ymm0",         "c5fd70c11b",   "refuses", "refuses"),
    ("vpbroadcastw_y", "vpbroadcastw %xmm1, %ymm0",           "c4e27d79c1",   "refuses", "refuses"),
    ("vpminsd_y",      "vpminsd %ymm1, %ymm2, %ymm0",         "c4e26d39c1",   "refuses", "refuses"),
    ("vpmaxsd_y",      "vpmaxsd %ymm1, %ymm2, %ymm0",         "c4e26d3dc1",   "refuses", "refuses"),
    ("vpmovzxbw_y",    "vpmovzxbw %xmm1, %ymm0",              "c4e27d30c1",   "refuses", "refuses"),
    ("vpblendd_y",     "vpblendd $0x5, %ymm1, %ymm2, %ymm0",  "c4e36d02c105", "refuses", "refuses"),
    ("vpsrld_y",       "vpsrld $0x2, %ymm1, %ymm0",           "c5fd72d102",   "refuses", "refuses"),
    ("vpsubsw_z",      "vpsubsw %zmm1, %zmm2, %zmm0",         "62f16d48e9c1", "refuses", "refuses"),
    ("vpsadbw_y",      "vpsadbw %ymm1, %ymm2, %ymm0",         "c5edf6c1",     "refuses", "refuses"),
    ("vpbroadcastq_y", "vpbroadcastq %xmm1, %ymm0",           "c4e27d59c1",   "refuses", "refuses"),
    ("psraw_mmx",      "psraw %mm1, %mm0",                    "0fe1c1",       "executes", "executes"),
    ("comiss",         "comiss %xmm1, %xmm0",                 "0f2fc1",       "refuses", "executes"),
    ("vpmullw_y",      "vpmullw %ymm1, %ymm2, %ymm0",         "c5edd5c1",     "refuses", "refuses"),
    ("punpcklwd_mmx",  "punpcklwd %mm1, %mm0",                "0f61c1",       "executes", "executes"),
    ("punpckhbw_mmx",  "punpckhbw %mm1, %mm0",                "0f68c1",       "executes", "executes"),
    ("movntdq",        "movntdq %xmm0, (%rbx)",               "660fe703",     "refuses", "refuses"),
    ("vperm2f128_y",   "vperm2f128 $0x1, %ymm1, %ymm2, %ymm0","c4e36d06c101", "refuses", "refuses"),
    ("vpalignr_v",     "vpalignr $0x4, %xmm1, %xmm2, %xmm0",  "c4e3690fc104", "refuses", "refuses"),
    ("vbroadcasti128_y","vbroadcasti128 (%rbx), %ymm0",       "c4e27d5a03",   "refuses", "refuses"),
    ("psllw_mmx",      "psllw %mm1, %mm0",                    "0ff1c1",       "executes", "executes"),
    ("vpcmpeqw_y",     "vpcmpeqw %ymm1, %ymm2, %ymm0",        "c5ed75c1",     "refuses", "executes"),
    # ══════════════════════════════════════════════════════════════════
    # P2 BATCH 28 — THE QUEUE REORDERED, AND THE FIRST BATCH THAT CAN FAIL.
    #
    # Not the top of `--unprobed` by demand: the top 23 of the 84 pairs
    # `scripts/p2_oracle_support.py` DERIVES as implemented, by demand. Same
    # census progress per pair, but every pair asked here is one that CAN BECOME
    # A DIFFERENTIAL VECTOR, which is what the project is for.
    #
    # ⛔⛔ AND THIS BATCH IS A REAL TEST WHERE BATCH 27 WAS NOT.  D132 established
    # that the listing GENERATES the dispatch, so asking a pair the listing calls
    # UNIMPLEMENTED can only confirm the read.  Asking one it calls IMPLEMENTED
    # is different: the machine can still refuse for reasons a static read cannot
    # see — bytes that do not decode to that entry, a feature-flag or CR4 gate,
    # or an ACL2 guard violation, which yields NO READING AT ALL rather than a
    # refusal (`cvtss2sd` at zero operands does exactly that, which is why it is
    # the operand control).  ⇒ every row here is a chance for the derived support
    # to be caught out, and a MISSING reading is a third outcome that is neither
    # verdict.
    #
    # ⚠️ SEVEN OF THESE MNEMONICS ARE ALREADY IN THIS TABLE AT SSE-legacy
    # (punpckhwd, pand, paddd, punpckldq, psrlq, por, psrlw) and are asked here
    # at MMX.  Distinct census keys, distinct labels, measured separately — the
    # thing b26 proved matters and D130 proved was silently broken.
    # ⛔ EVERY `hx` CAME FROM `clang`; none was typed.
    ("divss",           "divss %xmm1, %xmm0",                "f30f5ec1",      "refuses", "executes"),
    ("vpandn_v",        "vpandn %xmm1, %xmm2, %xmm0",        "c5e9dfc1",      "refuses", "executes"),
    ("movhpd",          "movhpd (%rbx), %xmm0",              "660f1603",      "refuses", "executes"),
    ("cvttsd2si",       "cvttsd2si %xmm1, %eax",             "f20f2cc1",      "refuses", "executes"),
    ("punpckhwd_mmx",   "punpckhwd %mm1, %mm0",              "0f69c1",        "executes", "executes"),
    ("pand_mmx",        "pand %mm1, %mm0",                   "0fdbc1",        "executes", "executes"),
    ("movddup",         "movddup %xmm1, %xmm0",              "f20f12c1",      "refuses", "executes"),
    ("paddd_mmx",       "paddd %mm1, %mm0",                  "0ffec1",        "executes", "executes"),
    ("mulps",           "mulps %xmm1, %xmm0",                "0f59c1",        "refuses", "executes"),
    ("punpckldq_mmx",   "punpckldq %mm1, %mm0",              "0f62c1",        "executes", "executes"),
    ("psrlq_mmx",       "psrlq %mm1, %mm0",                  "0fd3c1",        "executes", "executes"),
    ("vpcmpgtw_v",      "vpcmpgtw %xmm1, %xmm2, %xmm0",      "c5e965c1",      "refuses", "executes"),
    ("addps",           "addps %xmm1, %xmm0",                "0f58c1",        "refuses", "executes"),
    ("vpsubb_v",        "vpsubb %xmm1, %xmm2, %xmm0",        "c5e9f8c1",      "refuses", "executes"),
    ("por_mmx",         "por %mm1, %mm0",                    "0febc1",        "executes", "executes"),
    ("xorps",           "xorps %xmm1, %xmm0",                "0f57c1",        "refuses", "executes"),
    ("cvttss2si",       "cvttss2si %xmm1, %eax",             "f30f2cc1",      "refuses", "executes"),
    ("punpckhdq_mmx",   "punpckhdq %mm1, %mm0",              "0f6ac1",        "executes", "executes"),
    ("movlhps",         "movlhps %xmm1, %xmm0",              "0f16c1",        "refuses", "executes"),
    ("psrlw_mmx",       "psrlw %mm1, %mm0",                  "0fd1c1",        "executes", "executes"),
    ("andps",           "andps %xmm1, %xmm0",                "0f54c1",        "refuses", "executes"),
    ("vpcmpgtb_v",      "vpcmpgtb %xmm1, %xmm2, %xmm0",      "c5e964c1",      "refuses", "executes"),
    ("movlpd",          "movlpd (%rbx), %xmm0",              "660f1203",      "refuses", "executes"),
    # ══════════════════════════════════════════════════════════════════
    # P2 BATCH 29 — the next 23 pairs the derived support calls IMPLEMENTED,
    # and the FP-heaviest batch yet, which is the point.  Eleven rows are
    # floating point (sqrtss, sqrtsd, cvtss2si, cvtsd2si, minss/minsd,
    # maxss/maxsd, ucomiss/ucomisd, subps), and an ACL2 GUARD VIOLATION is the
    # one divergence class that yields NO READING AT ALL rather than a verdict.
    # ⚠️ PRICED BEFORE THE RUN, NOT EXPLAINED AFTER: at xmm0=0x4040..40 and
    # xmm1=0x4020..20 every single lane is 3.0078125 / 2.5039..., every double
    # lane 32.25 / 8.2539..., all NORMAL POSITIVE — no NaN, no denormal, no zero
    # divisor, no negative root, both conversions far inside int32.  So no guard
    # violation is expected; if one fires it is the finding, and `p2_run` reports
    # a MISSING reading separately because a missing reading is not a refusal.
    # ⚠️ psllq, psrad and pcmpgtb already sit at SSE-legacy and are asked here at
    # MMX — distinct keys, distinct labels, measured separately.
    # ⛔ EVERY `hx` CAME FROM `clang`; none was typed.
    ("vpaddb_y",       "vpaddb %ymm1, %ymm2, %ymm0",      "c5edfcc1",      "refuses", "executes"),
    ("minsd",          "minsd %xmm1, %xmm0",              "f20f5dc1",      "refuses", "executes"),
    ("maxss",          "maxss %xmm1, %xmm0",              "f30f5fc1",      "refuses", "executes"),
    ("psllq_mmx",      "psllq %mm1, %mm0",                "0ff3c1",        "executes", "executes"),
    ("psrad_mmx",      "psrad %mm1, %mm0",                "0fe2c1",        "executes", "executes"),
    ("minss",          "minss %xmm1, %xmm0",              "f30f5dc1",      "refuses", "executes"),
    ("vmovddup_v",     "vmovddup %xmm1, %xmm0",           "c5fb12c1",      "refuses", "executes"),
    ("maxsd",          "maxsd %xmm1, %xmm0",              "f20f5fc1",      "refuses", "executes"),
    ("ucomiss",        "ucomiss %xmm1, %xmm0",            "0f2ec1",        "refuses", "executes"),
    ("vpcmpeqb_y",     "vpcmpeqb %ymm1, %ymm2, %ymm0",    "c5ed74c1",      "refuses", "executes"),
    ("vpcmpeqd_y",     "vpcmpeqd %ymm1, %ymm2, %ymm0",    "c5ed76c1",      "refuses", "executes"),
    ("cvtss2si",       "cvtss2si %xmm1, %eax",            "f30f2dc1",      "refuses", "executes"),
    ("andpd",          "andpd %xmm1, %xmm0",              "660f54c1",      "refuses", "executes"),
    ("subps",          "subps %xmm1, %xmm0",              "0f5cc1",        "refuses", "executes"),
    ("ucomisd",        "ucomisd %xmm1, %xmm0",            "660f2ec1",      "refuses", "executes"),
    ("sqrtss",         "sqrtss %xmm1, %xmm0",             "f30f51c1",      "refuses", "executes"),
    ("movupd",         "movupd (%rbx), %xmm0",            "660f1003",      "refuses", "executes"),
    ("movlps",         "movlps (%rbx), %xmm0",            "0f1203",        "refuses", "executes"),
    ("psubb_mmx",      "psubb %mm1, %mm0",                "0ff8c1",        "executes", "executes"),
    ("cvtsd2si",       "cvtsd2si %xmm1, %eax",            "f20f2dc1",      "refuses", "executes"),
    ("sqrtsd",         "sqrtsd %xmm1, %xmm0",             "f20f51c1",      "refuses", "executes"),
    ("pcmpgtb_mmx",    "pcmpgtb %mm1, %mm0",              "0f64c1",        "executes", "executes"),
    ("vpcmpgtd_y",     "vpcmpgtd %ymm1, %ymm2, %ymm0",    "c5ed66c1",      "refuses", "executes"),
    # ══════════════════════════════════════════════════════════════════
    # P2 BATCH 30 — THE IMPLEMENTED REMAINDER, EXHAUSTED IN ONE BATCH.
    # Not "the next 23": ALL 38 pairs that `scripts/p2_oracle_support.py`
    # reads as IMPLEMENTED in x86isa's instruction listing, 1,317 instructions
    # of census demand.  After this batch the derived-support queue holds NO
    # implemented pair that has never been asked, and what remains unasked is
    # 158 pairs the listing says are NOT implemented plus 16 whose names it
    # does not carry.
    # ⭐ WHY ONE BATCH AND NOT TWO.  The costs that scale with BATCHES rather
    # than rows are the whole cost here: one ACL2 run (13.5 s for the table,
    # not per row), one `ci_local --job build`, one DECISIONS entry, one
    # roster regeneration, one commit.  The costs that scale with ROWS —
    # a spelling chosen, an encoding taken from clang, a verdict predicted —
    # are identical whether they are spread over one batch or two.  Splitting
    # would have bought nothing and paid the fixed cost twice
    # ([[feedback-measure-tokens-per-request]]: the unit of cost is the BATCH).
    # ⛔ AND IT DOES NOT WEAKEN THE TEST.  Each row is scored independently
    # against a declaration hashed before ACL2 ran; 38 rows that could each
    # fail is a STRICTLY STRONGER run than 23 that could, not a laxer one.
    # ⛔ EVERY `hx` CAME FROM `clang` (one assembly unit, one `objdump -d`,
    # the addresses checked CONSECUTIVE so the row/instruction zip is verified
    # rather than assumed); none was typed.
    # ⚠️ THE NINE MMX ROWS ARE DECLARED (executes, executes).  MMX does not go
    # through CR4.OSFXSR, so the CR4=0 arm is not a refusal for them — the
    # precedent is batch 29's psllq/psrad/psubb/pcmpgtb at MMX.  Ten mnemonics
    # here already sit at SSE-legacy (psrld, paddb, pcmpgtw, pslld, pcmpeqd,
    # pcmpeqb, pcmpeqw, psubd, pcmpgtd) and are asked here at MMX: DISTINCT
    # census keys, distinct labels, measured separately.
    # ⚠️ THE FP RISK, PRICED BEFORE THE RUN AND NOT EXPLAINED AFTER.  Nine rows
    # do FP ARITHMETIC (addpd, subpd, mulpd, divpd, divps, maxps, minps,
    # sqrtps, cvtpd2ps) and an ACL2 GUARD VIOLATION is the outcome that is
    # NEITHER verdict — it yields no reading at all.  At XMM0_NZ/XMM1_NZ the
    # double lanes are 32.501960784313724 and 8.125246051728084, the single
    # lanes 3.0039215087890625 and 2.5039138793945312, and EVERY result was
    # computed before the run: add 40.627207 · sub 24.376715 · mul 264.086429
    # · div 4.00012 (pd) / 1.199690 (ps) · max 3.003922 · min 2.503914 ·
    # sqrt 1.582376 · cvtpd2ps 8.125246 — all NORMAL, no NaN, no denormal, no
    # Inf, no zero divisor, no negative root, the conversion far inside float
    # range.  So none is expected; a firing is the FINDING, and `p2_run`
    # reports a MISSING reading separately because it is not a refusal.
    # ⚠️ movmskps and vmovmskps write a GPR, not a vector register (the b29
    # precedent is cvtss2si); probe_bucket reads the bucket off `%xmm`.
    # ⛔ DECLARATION SEALED BEFORE ACL2 RAN: sha256 of the 38 rows below
    # = 6e8474ff4f07771264068577b88644d49e94954752cecf2d5d1815c2609ff942,
    # 2026-09-05T20:02:18Z.
    ("psrld_mmx",       "psrld %mm1, %mm0",                  "0fd2c1",          "executes", "executes"),
    ("paddb_mmx",       "paddb %mm1, %mm0",                  "0ffcc1",          "executes", "executes"),
    ("pcmpgtw_mmx",     "pcmpgtw %mm1, %mm0",                "0f65c1",          "executes", "executes"),
    ("pslld_mmx",       "pslld %mm1, %mm0",                  "0ff2c1",          "executes", "executes"),
    ("pcmpeqd_mmx",     "pcmpeqd %mm1, %mm0",                "0f76c1",          "executes", "executes"),
    ("pcmpeqb_mmx",     "pcmpeqb %mm1, %mm0",                "0f74c1",          "executes", "executes"),
    ("pcmpeqw_mmx",     "pcmpeqw %mm1, %mm0",                "0f75c1",          "executes", "executes"),
    ("psubd_mmx",       "psubd %mm1, %mm0",                  "0ffac1",          "executes", "executes"),
    ("pcmpgtd_mmx",     "pcmpgtd %mm1, %mm0",                "0f66c1",          "executes", "executes"),
    ("shufpd",          "shufpd $0x1, %xmm1, %xmm0",         "660fc6c101",      "refuses", "executes"),
    ("xorpd",           "xorpd %xmm1, %xmm0",                "660f57c1",        "refuses", "executes"),
    ("unpcklps",        "unpcklps %xmm1, %xmm0",             "0f14c1",          "refuses", "executes"),
    ("mulpd",           "mulpd %xmm1, %xmm0",                "660f59c1",        "refuses", "executes"),
    ("addpd",           "addpd %xmm1, %xmm0",                "660f58c1",        "refuses", "executes"),
    ("andnps",          "andnps %xmm1, %xmm0",               "0f55c1",          "refuses", "executes"),
    ("movmskps",        "movmskps %xmm1, %eax",              "0f50c1",          "refuses", "executes"),
    ("andnpd",          "andnpd %xmm1, %xmm0",               "660f55c1",        "refuses", "executes"),
    ("unpcklpd",        "unpcklpd %xmm1, %xmm0",             "660f14c1",        "refuses", "executes"),
    ("orps",            "orps %xmm1, %xmm0",                 "0f56c1",          "refuses", "executes"),
    ("unpckhps",        "unpckhps %xmm1, %xmm0",             "0f15c1",          "refuses", "executes"),
    ("orpd",            "orpd %xmm1, %xmm0",                 "660f56c1",        "refuses", "executes"),
    ("subpd",           "subpd %xmm1, %xmm0",                "660f5cc1",        "refuses", "executes"),
    ("maxps",           "maxps %xmm1, %xmm0",                "0f5fc1",          "refuses", "executes"),
    ("minps",           "minps %xmm1, %xmm0",                "0f5dc1",          "refuses", "executes"),
    ("unpckhpd",        "unpckhpd %xmm1, %xmm0",             "660f15c1",        "refuses", "executes"),
    ("divps",           "divps %xmm1, %xmm0",                "0f5ec1",          "refuses", "executes"),
    ("divpd",           "divpd %xmm1, %xmm0",                "660f5ec1",        "refuses", "executes"),
    ("sqrtps",          "sqrtps %xmm1, %xmm0",               "0f51c1",          "refuses", "executes"),
    ("cvtpd2ps",        "cvtpd2ps %xmm1, %xmm0",             "660f5ac1",        "refuses", "executes"),
    ("vpaddq_v",        "vpaddq %xmm1, %xmm2, %xmm0",        "c5e9d4c1",        "refuses", "executes"),
    ("vmovupd_v",       "vmovupd %xmm1, %xmm0",              "c5f910c1",        "refuses", "executes"),
    ("vmovmskps_v",     "vmovmskps %xmm1, %eax",             "c5f850c1",        "refuses", "executes"),
    ("vandps_v",        "vandps %xmm1, %xmm2, %xmm0",        "c5e854c1",        "refuses", "executes"),
    ("vxorpd_v",        "vxorpd %xmm1, %xmm2, %xmm0",        "c5e957c1",        "refuses", "executes"),
    ("vorps_v",         "vorps %xmm1, %xmm2, %xmm0",         "c5e856c1",        "refuses", "executes"),
    ("vmovups_y",       "vmovups %ymm1, %ymm0",              "c5fc10c1",        "refuses", "executes"),
    ("vmovapd_y",       "vmovapd %ymm1, %ymm0",              "c5fd28c1",        "refuses", "executes"),
    ("vpcmpeqq_y",      "vpcmpeqq %ymm1, %ymm2, %ymm0",      "c4e26d29c1",      "refuses", "executes"),
    # ══════════════════════════════════════════════════════════════════
    # P2 BATCH 31 — THE TWO PAIRS THE CATALOGUE READER WAS HIDING (D138).
    # After batch 30 the derived-support queue reported `x86isa IMPLEMENTS 0
    # pairs`.  That was an artifact of the READER, not a fact about x86isa:
    # the census spells these with clang's operand-size suffix (`cvtsi2sdq`)
    # and the listing spells them without it (`CVTSI2SD`), so the join missed
    # and both landed in the "absent under this name" pile.  Resolved BY
    # ENCODING in `scripts/resolve_names.py` — #xF2A with :F2 / :F3, no VEX —
    # and x86isa IMPLEMENTS both.  192 instructions of census demand.
    # ⛔ NEVER BY STRIPPING THE SUFFIX.  That rule would also have to invent
    # `pextrd -> pextrd/q`, and no edit of the string `pextrd` produces
    # `pextrd/q` — the listing's name is two widths sharing one entry.  D100
    # published a phantom row on exactly that kind of key.
    # ⚠️ THE SOURCE IS A GPR, WHICH IS A DIMENSION THIS PROBE DOES NOT VARY —
    # so it was checked rather than assumed.  `measure_cr4`'s
    # `init-x86-state-64` call sets gprs `((0 . #x400000) (3 . #x2000))`, so
    # RAX = 0x400000 = 4,194,304 = 2^22: NON-ZERO and exactly representable in
    # both float and double.  Had RAX been 0 these would convert 0 -> 0.0 and
    # risk the SSE-POST-COMP guard violation that yields NO READING — the
    # `cvtss2sd`-at-zero failure the operand control exists for.  It is not
    # zero, so no guard violation is expected and a firing is the finding.
    # ⛔ BOTH `hx` FROM `clang`; the disassembler prints `cvtsi2sd`/`cvtsi2ss`,
    # which is the name difference this batch is about, visible in the bytes.
    # ⛔ DECLARATION SEALED BEFORE ACL2 RAN: sha256 of the 2 rows below
    # = a32e3399e00d67a53c15ce9d517ea40634e41d99306a800683acdcc41198326b,
    # 2026-09-05T20:33:02Z.
    ("cvtsi2sdq",      "cvtsi2sdq %rax, %xmm0",             "f2480f2ac0",      "refuses", "executes"),
    ("cvtsi2ssq",      "cvtsi2ssq %rax, %xmm0",             "f3480f2ac0",      "refuses", "executes"),
    # ══════════════════════════════════════════════════════════════════
    # P2 BATCH 33 — `vzeroupper`, RANK 1 OF THE UNASKED LIST SINCE BATCH 26 AND
    # SKIPPED THREE TIMES (D128 §5, D138 §3) because `probe_bucket` read the
    # bucket off the OPERANDS and this form has none, so a probe for it ran, had
    # its verdict DISCARDED, and left the pair exactly as unasked as before.
    # D143 delegated `probe_bucket` to the census's own rule, which buckets it
    # `AVX (state)` out of the table the census keeps for operand-free forms.
    # 1,241 instructions; the ONLY pair x86isa implements that had never been
    # asked.
    #
    # ⛔ `hx` FROM `clang`, NOT TYPED: `c5f877`, and BOTH disassemblers agree
    # (LLVM `objdump` and GNU `objdump` — D128's gate re-derives it every run).
    #
    # ⭐ AND THAT x86isa IMPLEMENTS IT WAS CHECKED AT THE OBJECT, not inherited
    # from D138's reading of the catalogue: `inst-listing.lisp:9040` names
    # `x86-vzeroupper` as the VEX.128 form's semantic function, and the function
    # is DEFINED at `machine/instructions/fp/non-arith.lisp:50`. A catalogue can
    # name a function that does not exist; this one does.
    # [[feedback-the-oracle-is-evidence-not-the-specification]]
    #
    # ⚠️⚠️ THE DECLARATION, AND IT IS "REFUSES" IN BOTH ARMS — which is NOT what
    # "x86isa implements it" would lead you to predict, and is the reason to write
    # it down before running. The listing's exception spec is
    # `(CHK-EXC :TYPE-8 (:AVX))`, and this probe's enabled arm sets
    # `CR4 = #x600` — OSFXSR | OSXMMEXCPT. **Bit 18, OSXSAVE, is not among them**,
    # so the AVX feature check cannot pass and the form should refuse at the very
    # CR4 the differential itself runs under. If that is right, the pair moves
    # from "implemented and never asked" to "implemented and not reachable under
    # this driver", which is a different fact about the same 1,241 instructions.
    # ⛔ DECLARATION SEALED BEFORE ACL2 RAN: sha256 of the row below
    # = 5dd51ed13de0175902fd23c41f60e8a9c285265fe1b998ded649e128c9818623,
    # 2026-09-05T23:50:22Z.
    #
    # ⛔⛔ AND THE DECLARATION WAS REFUTED BY THE RUN: measured `(refuses,
    # EXECUTES)`. The gate printed `vzeroupper: declared (refuses, refuses),
    # MEASURED (refuses, executes)` and went red, which is the seal doing its job
    # — a prediction written after the fact would have been right by construction.
    #
    # ⇒ 🔑 THE ORACLE'S CATALOGUE DECLARES AN EXCEPTION CHECK ITS EXECUTION DOES
    # NOT PERFORM. `inst-listing.lisp` gives this form `(CHK-EXC :TYPE-8 (:AVX))`,
    # and `x86-vzeroupper` executes with `CR4 = #x600`, in which OSXSAVE (bit 18)
    # is clear and AVX therefore cannot be enabled on real hardware. The reasoning
    # that produced the prediction was sound about the SPEC and wrong about the
    # MACHINE. [[feedback-the-oracle-is-evidence-not-the-specification]]
    #
    # ⚠️ AND THE CONSEQUENCE IS A NOTE FOR WHOEVER MODELS THIS FORM, not a note
    # about this probe: an x86lean `vzeroupper` that DOES gate on CR4.OSXSAVE will
    # DISAGREE with this oracle on a machine where AVX is off, and the
    # differential will call that disagreement the model's. It is the oracle's.
    # A differential is blind to nothing here — it is the shared-rule case in
    # reverse, where the oracle implements FEWER rules than the spec.
    # [[feedback-two-defects-that-cancel-survive-a-green-run]]
    ("vzeroupper",     "vzeroupper",              "c5f877",       "refuses",  "executes"),
    # ══════════════════════════════════════════════════════════════════
    # 2026-09-06 — `pandn` AT `MMX (mm)`, THE LAST IMPLEMENTED PAIR THE
    # AVAILABILITY CENSUS HAD NEVER ASKED.
    #
    # ⛔⛔ AND THE QUEUE ROW THAT SENT ME HERE WAS STALE IN BOTH HALVES.  Item 1
    # said *"what remains, and it needs the oracle: a probe row for `vzeroupper`
    # … after which the unasked remainder's implemented column goes from 1 pair /
    # 1,241 instructions to 0, and the availability census is finished"*.  The
    # `vzeroupper` row EXISTS, was run, and its sealed declaration was REFUTED by
    # the run (it is the row above).  And the column did not go to 0: it reads
    # **1 pair / 88** today, because `pandn` is covered at `xmm` (P2 batch 34) and
    # SURFACED at `mm`, which is a different key.
    # ⇒ 🔑 A PREDICTION ABOUT A TOTAL, WRITTEN BEFORE THE ACT, IS A PREDICTION
    # THAT THE SET WILL NOT MOVE UNDERNEATH IT — and the act that discharges one
    # row is exactly the kind of act that adds another.  Right in direction,
    # wrong in value, and it read as arithmetic.
    # [[feedback-a-census-is-per-key-not-per-name]]
    #
    # ⛔ `hx` FROM `clang`, NOT TYPED: `clang -target x86_64-unknown-linux-gnu`
    # over ONE assembly unit containing both `pandn %mm1, %mm0` and, as a
    # POSITIVE CONTROL ON MY OWN RECIPE, `pand %mm1, %mm0` — whose disassembly
    # came back `0fdbc1`, byte-identical to the `pand_mmx` row already shipped
    # here.  A recipe that reproduces a row already in the table is a recipe I
    # can quote the other row from.
    #
    # ⭐ AND THE PREDICTION RESTS ON THE OBJECT, not on the catalogue's word.
    # `inst-listing.lisp:11605` and `:11391` are IDENTICAL IN EVERY FIELD BUT THE
    # OPCODE — same `:PFX :NO-PREFIX`, same `:FEAT '(:MMX)`, same
    # `(ARG :OP1 '(P Q) :OP2 '(Q Q))`, same exception check
    # `(CHK-EXC :TYPE-22-7 (:MMX))`, and the SAME semantic function
    # `X86-PAND/PANDN/POR/PXOR-MMX`, which is DEFINED at
    # `machine/instructions/logical.lisp:53`.  `pand %mm1, %mm0` is a MEASURED
    # row here reading (executes, executes).
    # ⇒ so this predicts (executes, executes) from a measured sibling reached
    # through the same defined function, and what the probe actually tests is the
    # DISPATCH of `0F DF` with no prefix — the one thing the two entries do not
    # share.
    #
    # ⚠️ WHAT THIS PREDICTION IS WORTH, SAID BEFORE THE RUN: it is close to the
    # null model for this table — every shipped MMX row executes in both arms
    # EXCEPT `pshufw`, which refuses in both.  So a green here is weak evidence
    # about the ORACLE and is not claimed as more.  It is exactly the evidence the
    # CENSUS needs, whose question is not "is this surprising" but "has this pair
    # been ASKED".  [[feedback-score-the-null-model]]
    # ⚠️ AND MMX NEEDS NO CR4 BIT, so the two arms are expected to agree — which
    # is why the MMX rows are this file's control that the CR4 arm changes the
    # right thing, and why a DISAGREEMENT between the arms here would be a finding
    # about the driver rather than about `pandn`.
    #
    # ⛔ DECLARATION SEALED BEFORE ACL2 RAN: sha256 of the row below
    # = a8e42fdc011a58efee0b7624781e5a7cc3a2feba62096ca53748cca0efb8a542,
    # 2026-09-06T20:55:40Z.
    ("pandn_mmx",       "pandn %mm1, %mm0",                  "0fdfc1",        "executes", "executes"),
    # ⭐ THE CONTROLS, one in each direction, in BOTH arms.
    ("CONTROL:mov",    "movl %ecx, (%rbx)",       "890b",         "executes", "executes"),
    ("CONTROL:movnti", "movntil %ecx, (%rbx)",    "0fc30b",       "refuses",  "refuses"),
]


def measure_cr4(forms, ctrs):
    """One reading per form under a given CR4, taken through `init-x86-state-64`
    directly so the control-register argument is reachable.

    ⚠️ EVERY READING CARRIES ITS OWN LABEL IN THE OUTPUT LINE.  The first version
    of this probe printed unlabelled results and they were read off by POSITION,
    which is a reading no one can check and which was wrong the first time it was
    tried."""
    lines = ['(include-book "projects/x86isa/tools/execution/init-state" '
             ':dir :system :ttags :all)',
             '(include-book "projects/x86isa/machine/x86" :dir :system :ttags :all)',
             "(set-fmt-hard-right-margin 100000 state)",
             "(set-fmt-soft-right-margin 99000 state)",
             '(in-package "X86ISA")']
    for label, _asm, hx, _e0, _e1 in forms:
        mem = " ".join("(#x%016x . #x%s)" % (0x400000 + k, hx[2*k:2*k+2])
                       for k in range(len(hx) // 2))
        lines.append(
            "(b* (((mv flg x86) (init-x86-state-64 nil #x400000 "
            "'((0 . #x400000) (3 . #x2000)) %s nil nil nil nil nil #x2 '(%s) x86))"
            " (x86 (!app-view t x86))"
            # ⭐ THE OPERANDS, set AFTER init because init has no xmm argument.
            # See XMM0_NZ above for why zero was never a choice and why these
            # particular bytes are the ones that keep this an AVAILABILITY probe.
            " (x86 (!xmmi-size 16 0 #x%032x x86))"
            " (x86 (!xmmi-size 16 1 #x%032x x86))"
            " (x86 (x86-fetch-decode-execute x86)))"
            # ⛔⛔ D177 / QUEUE item 0(a) — RIP IS PRINTED **TWICE**, AND THE SECOND
            # COPY IS THE ONE THE CLASSIFIER READS.  `stalled` is computed BY ACL2
            # as a 0/1, so it means the same thing in every print-base; `rip` is the
            # raw value, kept because a gate that refuses must be able to say what it
            # saw.  They are cross-checked below and a DISAGREEMENT IS THE FINDING.
            # ⚠️ WHY NOT JUST PARSE `rip`, WHICH IS WHAT `measure` DOES.  `measure`
            # reads the DRIVER's output, and the driver prints rip through
            # `x86l-hex(...,16)` (x86isa_driver.lisp:158) — so its
            # `rip=([0-9a-f]+)` + `int(...,16)` is right THERE.  This function builds
            # a standalone drive that never loads the driver, so `~x` prints in ACL2's
            # ambient print-base, MEASURED to be 10 (`~x` of 255 came back "255", not
            # "ff").  Copying the sibling regex here would compute
            # int("4194304",16) = 68174084, miss ENTRY_RIP, fall to the residual and
            # score the stall as `executes` — D170's exact defect, re-created inside
            # the repair for D170.  [[feedback-two-readings-are-not-two-witnesses]]
            ' (prog2$ (cw "P2RESULT tag=%s flg=~x0 refused=~x1 rip=~x2 stalled=~x3~%%" flg'
            " (if (or (ms x86) (fault x86)) 1 0) (rip x86)"
            " (if (equal (rip x86) #x%06x) 1 0)) x86))"
            % (ctrs, mem, XMM0_NZ, XMM1_NZ, tag_of(label), ENTRY_RIP))
    tmp = tempfile.mkdtemp(prefix="x86lean-p2-")
    drive = os.path.join(tmp, "drive.lsp")
    open(drive, "w").write("\n".join(lines) + "\n")
    out = os.path.join(tmp, "out.txt")
    with open(out, "w") as fh:
        subprocess.run([ACL2], stdin=open(drive), stdout=fh,
                       stderr=subprocess.STDOUT)
    got = {}
    text = open(out).read()
    # ⛔ THREE-VALUED, IN D170's ORDER: refused first, then stalled, then the
    # residual.  Before D177 this line was `refuses if refused else executes` —
    # the two-valued classifier D170's own headline condemns, still live in the
    # table the availability answer is BUILT from while `FORMS` 800 lines above
    # already declared `movmskps` a stall.
    # ⭐ THE CROSS-ARM: `rip == ENTRY_RIP` (parsed here, base-dependent) and
    # `stalled` (computed in ACL2, base-independent) are two INDEPENDENT routes to
    # one fact.  They must agree.  If ACL2's print-base ever moves, the parsed
    # route silently starts answering "executes" for every stall and the computed
    # route does not — so the disagreement is what makes a base change LOUD
    # instead of turning this gate back into the thing it was built to replace.
    for m in re.finditer(r"P2RESULT tag=(\S+) flg=(\S+) refused=(\d) "
                         r"rip=(\d+) stalled=(\d)", text):
        tag, refused, rip_dec, stalled = (m.group(1), m.group(3),
                                          int(m.group(4)), m.group(5) == "1")
        if (rip_dec == ENTRY_RIP) != stalled:
            raise SystemExit(
                "⛔ measure_cr4: the two RIP routes DISAGREE for %s — parsed "
                "rip=%d (ENTRY_RIP=%d ⇒ stalled=%s) but ACL2 computed stalled=%s. "
                "The print-base almost certainly moved; a stall would now be "
                "scored as the residual `executes`. REFUSING rather than "
                "returning a table that reads fine."
                % (tag, rip_dec, ENTRY_RIP, rip_dec == ENTRY_RIP, stalled))
        got[tag] = ("refuses" if refused == "1"
                    else "stalls" if stalled
                    else "executes")
    return got


def p2_operand_control(arms=None):
    """⭐⭐ THE ARM THAT SAYS THE OPERANDS ARE REAL — P2 batch 19.

    `measure_cr4` now writes XMM0_NZ/XMM1_NZ before every reading.  If that write
    ever stopped landing — a renamed `!xmmi-size`, a reordered `b*`, an x86isa
    bump — EVERY verdict would silently go back to being a reading at zero, and
    the table would still print 77 green ticks, because the forms that agree at
    zero are exactly the ones that agree everywhere.  ⇒ 🔑 A NO-OP WRITE AND A
    CORRECT WRITE PRODUCE THE SAME TABLE; only a form whose verdict DEPENDS on the
    operand can tell them apart.

    `cvtss2sd` is that form, and it is the only one known:
        at a ZERO source     -> an ACL2 guard violation, so NO READING at all
        at a NON-ZERO source -> executes
    So this arm runs it BOTH ways in ONE run and requires the disagreement.  If
    x86isa ever repairs the guard, the zero arm starts reading and this control
    fires — which is a finding about the oracle, not a false alarm, and is the
    reason it is stated as "these two must DIFFER" rather than "zero must crash".

    ⚠️ A THIRD READING RIDES ALONG: `packuswb` at the same non-zero registers,
    whose result must be all-ones (0xff.. bytes, from saturating 0x4040/0x4020
    words).  A zeroed xmm cannot produce it, so it WITNESSES the write directly
    instead of inferring it from an absence."""
    # ⚠️ A PARAMETER so each of the three failure branches can be DRIVEN by an arm
    # rather than only read.  A control whose own failure paths are untested is a
    # gate nobody has seen run ([[feedback-probe-gates-both-ways]]).
    if arms is None:
        arms = [("CTRL:cvt_nonzero", "f30f5ac1", XMM0_NZ, XMM1_NZ),
                ("CTRL:cvt_zero",    "f30f5ac1", 0,       0),
                ("CTRL:witness",     "660f67c1", XMM0_NZ, XMM1_NZ)]
    lines = ['(include-book "projects/x86isa/tools/execution/init-state" '
             ':dir :system :ttags :all)',
             '(include-book "projects/x86isa/machine/x86" :dir :system :ttags :all)',
             "(set-fmt-hard-right-margin 100000 state)",
             "(set-fmt-soft-right-margin 99000 state)",
             '(in-package "X86ISA")']
    for label, hx, x0, x1 in arms:
        mem = " ".join("(#x%016x . #x%s)" % (0x400000 + k, hx[2*k:2*k+2])
                       for k in range(len(hx) // 2))
        lines.append(
            "(b* (((mv flg x86) (init-x86-state-64 nil #x400000 "
            "'((0 . #x400000) (3 . #x2000)) %s nil nil nil nil nil #x2 '(%s) x86))"
            " (x86 (!app-view t x86))"
            " (x86 (!xmmi-size 16 0 #x%032x x86))"
            " (x86 (!xmmi-size 16 1 #x%032x x86))"
            " (x86 (x86-fetch-decode-execute x86)))"
            ' (prog2$ (cw "CTRLRESULT tag=%s flg=~x0 refused=~x1 xmm0=~x2~%%" flg'
            " (if (or (ms x86) (fault x86)) 1 0) (xmmi-size 16 0 x86)) x86))"
            % (CR4_ON, mem, x0, x1, tag_of(label)))
    tmp = tempfile.mkdtemp(prefix="x86lean-p2ctrl-")
    drive = os.path.join(tmp, "drive.lsp")
    open(drive, "w").write("\n".join(lines) + "\n")
    out = os.path.join(tmp, "out.txt")
    with open(out, "w") as fh:
        subprocess.run([ACL2], stdin=open(drive), stdout=fh,
                       stderr=subprocess.STDOUT)
    got = {m.group(1): (m.group(3), m.group(4)) for m in re.finditer(
        r"CTRLRESULT tag=(\S+) flg=(\S+) refused=(\d) xmm0=(\S+)", open(out).read())}
    nz, zr, wt = (got.get(tag_of(a[0])) for a in arms)
    ALLONES = str((1 << 128) - 1)
    problems = []
    if nz is None:
        problems.append("cvtss2sd at NON-ZERO operands produced no reading; the "
                        "probe's own subject does not run, so nothing it says "
                        "about the other %d forms is worth reading"
                        % (len(P2_FORMS) - 1))
    if zr is not None:
        problems.append("cvtss2sd at ZERO operands now READS (%s). Either x86isa "
                        "repaired the sse-post-comp guard — a finding, and this "
                        "control must be re-pointed at whatever still varies — or "
                        "the operands are not reaching the machine" % (zr,))
    if wt is None or wt[1] != ALLONES:
        problems.append("the packuswb witness returned %s, not all-ones; a zeroed "
                        "xmm cannot produce all-ones, so the operand write did NOT "
                        "land and every verdict is a reading at zero"
                        % (wt[1] if wt else "no reading",))
    if problems:
        print("⛔ operand control: FAIL — the availability table's verdicts are "
              "NOT established at the operands it claims")
        for p in problems:
            print("    " + p)
        return 1
    # ⛔ DERIVED, NOT RESTATED.  This sentence said "the 77 verdicts" from batch
    # 19 until batch 28, by which point the table held 202 rows.  A count written
    # as a literal in a message is invisible to every gate and re-renders never
    # — the exact shape D127 paid for, and it went stale in the one place that
    # asserts the verdicts are trustworthy.  ⇒ print the number the table has.
    print("  ✔ operand control: the write LANDS (packuswb witnesses all-ones) and "
          "the verdict DEPENDS on it (cvtss2sd executes at non-zero, no reading "
          "at zero) — so the %d verdicts are readings at the declared operands"
          % len(P2_FORMS))
    return 0


def p2_structure_check(forms=None, quiet=False):
    """⛔⛔ TWO ROWS THAT SHARE A TAG SHARE A MEASUREMENT — D130.

    `measure_cr4` emits one ACL2 form per row, each printing
    `P2RESULT tag=<tag_of(label)> ...`, and collects them into a dict KEYED BY
    THAT TAG.  A dict keeps the last writer.  So two rows with the same label do
    not produce two readings that can be compared — they produce ONE reading,
    handed to BOTH rows, and `p2_run` then scores each row against it.

    ⭐ AND THIS IS WHY THE DEFECT LIVED HERE AND NOWHERE ELSE.  The other two
    measurement paths in this repository COUNT records per tag and compare the
    count to the number of pre-states: `measure` stores `res[tag] = (e, r)` and
    `report` refuses on `e + r != n`; `check_driver_cr4.verdict` does the same.
    A tag collision there shows up immediately as "2n records, expected n".
    `measure_cr4` is the one path that collapses a tag to a SINGLE verdict by
    assignment (`got[tag] = ...`), so a second record does not add to a count —
    it overwrites, leaving no trace of the first.  ⇒ the collision is undetectable
    exactly where the collector stopped counting.

    ⇒ 🔑 THE EXISTING GUARD LOOKS FOR A MISSING READING, WHICH IS THE OTHER
    DIRECTION.  `g0 is None` catches a row that got nothing; nothing at all
    caught a row that got SOMEBODY ELSE'S.  And the shared reading is not even
    detectably odd, because both rows print a ✔ against it — identical verdicts
    in identical fields, which is what confirmation looks like
    ([[feedback-two-arms-that-agree-to-the-case]]).

    THE LIVE CASE, and why it mattered.  `vpsubw` was the label of BOTH
    `vpsubw %ymm1, %ymm2, %ymm0` (AVX2/AVX (ymm)) and
    `vpsubw %xmm1, %xmm2, %xmm0` (VEX-128 (v… xmm)).  Those are two DIFFERENT
    census keys, both published in the availability table, and the ymm one had
    never been measured: its verdict was the xmm row's reading wearing the ymm
    row's name.  b26 is the reason that is not a technicality — it measured four
    VEX-128 unpacks that REFUSE where their SSE-legacy siblings EXECUTE, which
    is the whole reason the key is (mnemonic, BUCKET) and not a mnemonic.

    ⚠️ WHAT THIS DOES *NOT* FLAG, deliberately.  Two rows may legitimately share
    a (mnemonic, bucket) KEY — `psrad $0x3, %xmm0` (0F72 /4) and
    `psrad %xmm1, %xmm0` (0FE2) are different opcodes at one census key, and the
    census counts the key.  Those rows have DISTINCT labels, so they are measured
    independently, and `measured_availability` already REFUSES if they disagree.
    That is correct and is left alone.  It is only reported here, because a
    reader of the table cannot otherwise tell that two rows fold into one
    published verdict."""
    forms = P2_FORMS if forms is None else forms
    problems = []

    tags = collections.defaultdict(list)
    for label, asm, _hx, _e0, _e1 in forms:
        tags[tag_of(label)].append((label, asm))
    for tag, rows in sorted(tags.items()):
        if len(rows) > 1:
            problems.append(
                "tag %r is emitted by %d rows (%s) — ACL2 prints %d records under "
                "that one tag and the collector keeps the LAST, so these rows do "
                "not have %d readings between them, they have ONE"
                % (tag, len(rows), ", ".join("%s [%s]" % (l, a) for l, a in rows),
                   len(rows), len(rows)))

    keys = collections.defaultdict(list)
    for label, asm, _hx, _e0, _e1 in forms:
        # ⛔ THE SAME SUBJECT AS `measured_availability`, and by the same declared
        # list. This check is about the keys that TABLE publishes; scoping it with
        # a different rule would police a set nobody publishes and leave a fold in
        # the set that is published. (Until D143 both were scoped by `bucket is
        # not None`, which agreed only because one accident drove both.)
        if label in NOT_AN_AVAILABILITY_QUESTION:
            continue
        keys[(asm.split()[0], probe_bucket(asm))].append(label)
    folded = sorted((k, v) for k, v in keys.items() if len(v) > 1)

    if problems:
        # ⚠️ SILENT UNDER `quiet`, because the red arms below call it that way and
        # a planted failure printing its own ⛔ reads as a real one in the log.
        if not quiet:
            print("⛔ P2 structure gate: FAIL — a shared tag is a shared "
                  "measurement:")
            for why in problems:
                print("    " + why)
        return 1
    if not quiet:
        print("  ✔ P2 structure: %d rows, %d distinct tags — every row has its own "
              "reading" % (len(forms), len(tags)))
        for key, labels in folded:
            print("    ⚠️ %s at %s is published from %d rows (%s), measured "
                  "separately and required to agree" % (key[0], key[1],
                                                        len(labels), ", ".join(labels)))
    return 0


def p2_run():
    bad, rows, refuted_seen = [], [], []
    # ⭐ STRUCTURE BEFORE MEASUREMENT: pure string work, microseconds,
    # and if it fails every reading below is misattributed anyway.
    if p2_structure_check():
        return 1
    # ⭐ AND THE CROSS-TABLE GATE BESIDE IT, for the same reason: pure string work,
    # and if the two tables contradict each other every reading below is scored
    # against a declaration the other table already denies.
    if forms_vs_p2forms_check():
        return 1
    if p2_operand_control():
        return 1
    off = measure_cr4(P2_FORMS, CR4_OFF)
    on = measure_cr4(P2_FORMS, CR4_ON)
    for label, asm, _hx, e0, e1 in P2_FORMS:
        t = tag_of(label)
        g0, g1 = off.get(t), on.get(t)
        if g0 is None or g1 is None:
            bad.append((label, "a reading is MISSING, and a missing reading is "
                               "not a refusal"))
            continue
        # ⛔⛔ THE REFUTATION IS SCORED HERE, AND IT IS NOT A SUPPRESSION.
        # The sealed `e0`/`e1` stay exactly as sealed; a row this table names is
        # compared against the MEASURED pair instead, and the run prints it as
        # REFUTED rather than as a tick.  A refutation that rendered as ✔ would be
        # a green wearing a correction's name — the gate would stop being able to
        # tell "we measured this and wrote it down" from "this agrees".
        # ⚠️ AND IT STILL FAILS IF THE MEASUREMENT MOVES AGAIN: the comparison is
        # against the recorded measurement, not a wildcard, so a row that starts
        # executing tomorrow goes red here rather than being permanently excused
        # ([[feedback-a-justification-outlives-its-condition]]).
        if label in REFUTED_BY_MEASUREMENT:
            r0, r1 = (REFUTED_BY_MEASUREMENT[label].e0,
                      REFUTED_BY_MEASUREMENT[label].e1)
            if (g0, g1) != (r0, r1):
                bad.append((label, "REFUTED as (%s, %s) but MEASURED (%s, %s) — "
                                   "the recorded refutation is itself now stale"
                            % (r0, r1, g0, g1)))
            else:
                refuted_seen.append(label)
            continue
        if (g0, g1) != (e0, e1):
            bad.append((label, "declared (%s, %s), MEASURED (%s, %s)"
                        % (e0, e1, g0, g1)))
        rows.append((label, asm, e0, e1, g0, g1))
    print("P2 oracle availability — ACL2 x86isa, one reading per form per CR4 arm\n")
    print(f"  {'form':18s} {'asm':32s} {'CR4=0':>10s} {'CR4=0x600':>11s}")
    for label, asm, e0, e1, g0, g1 in rows:
        # ⚖ IS ITS OWN MARK.  A refuted row does not agree with its declaration
        # and must not print the character that means "agrees"; it also is not a
        # failure.  Three states, three marks.
        mark = ("⚖" if label in REFUTED_BY_MEASUREMENT
                else "✔" if (g0, g1) == (e0, e1) else "⛔")
        print(f"  {mark} {label:16s} {asm:32s} {g0:>10s} {g1:>11s}")
    # ⛔ A REFUTATION THAT NOBODY PRINTS IS A SUPPRESSION, and one that is never
    # EXERCISED is a standing excuse nothing tests.  Both are reported.
    unseen = sorted(set(REFUTED_BY_MEASUREMENT) - set(refuted_seen))
    if unseen:
        bad.append(("REFUTATION TABLE", "these labels are recorded as refuted but "
                    "produced no scored reading this run, so their entries "
                    "excused nothing and cannot be trusted: %s" % ", ".join(unseen)))
    if refuted_seen:
        print("\n⚖ SEALED DECLARATIONS REFUTED BY MEASUREMENT (%d) — the sealed "
              "rows are UNCHANGED; the refutation is recorded beside them:"
              % len(refuted_seen))
        for lb in refuted_seen:
            r0, r1, why = REFUTED_BY_MEASUREMENT[lb]  # namedtuple unpack
            d0, d1 = next((a, b) for l, _a, _h, a, b in P2_FORMS if l == lb)
            print(f"    {lb}: sealed ({d0}, {d1})  MEASURED ({r0}, {r1})")
            print(f"        {why}")
    if bad:
        print("\n⛔ P2 oracle-availability gate: FAIL")
        for mn, why in bad:
            print(f"    {mn}: {why}")
        return 1
    # ⛔ THE SENTENCE COUNTS THE REFUTATIONS INSTEAD OF CLAIMING THEY DO NOT
    # EXIST.  It read "every declaration matches the oracle's own behaviour under
    # BOTH CR4 settings" — which the three rows printed directly above it
    # contradict.  A summary line is read far more often than the table it
    # summarises, so an over-claim there is the one that travels
    # ([[feedback-ungated-prose-overclaims]], [[feedback-a-citation-is-an-ungated-claim]]).
    print("\nP2 oracle-availability gate: CLEAN — %d of %d declarations match the "
          "oracle's own behaviour under BOTH CR4 settings and %d are REFUTED and "
          "recorded above (sealed rows unchanged); the always-executes control "
          "executed in both arms, and the always-refuses control refused in both."
          % (len(rows) - len(refuted_seen), len(rows), len(refuted_seen)))
    return 0

# ⭐⭐⭐ THE COLUMN THAT RUNS AND THE COLUMN THAT NAMES IT (D128).
#
# Every row of `P2_FORMS` carries an `asm` string and an `hx` string, and they
# are used for DIFFERENT things by different code:
#   * `hx`  is written into ACL2's memory and IS THE INSTRUCTION THAT EXECUTES
#           (`measure_cr4`, the `(#x... . #x..)` pairs).
#   * `asm` is never assembled by anything — but `measured_availability()` keys
#           the whole availability table by `asm.split()[0]`, deliberately,
#           because a probe LABEL is a tag and the assembler's own text is not.
# ⇒ 🔑 THE KEY COMES FROM THE COLUMN THAT DOES NOT RUN, AND THE MEASUREMENT COMES
#   FROM THE COLUMN THAT DOES. Nothing tied them together, so one mistyped hex
#   byte would have published a verdict about `pmaddwd` that was measured on
#   whatever those bytes actually decode to — a phantom row of D100's exact
#   family, arriving through the one column no reader checks because it is
#   unreadable by eye.
#
# ⛔ AND THE PARSER IS THE HARD PART, NOT THE COMPARISON. The byte column is
# delimited differently by the two disassemblers this project meets, and neither
# delimiter is a space:
#     LLVM   `   0: 48 b8 .. 00 00<TAB>movabsq<TAB>$0x...`
#     GNU    `   0:<TAB>48 b8 .. 34 <TAB>movabs $0x...`   and WRAPPED AT SEVEN
#            `   7:<TAB>12 00 00 `                          bytes per line
# The first parser written here matched `([0-9a-f]{2} )+` and so depended on the
# PADDING objdump adds after short instructions. It dropped the last byte of the
# widest form in the table (`movabsq`, 10 bytes) — and of that form only, so 132
# of 133 rows agreed and the one disagreement read as a defect in the TABLE.
# D89 learned this on the other side (GNU wraps at seven where LLVM does not)
# and could not test it: the dev box had one disassembler. It now has both, so
# this gate runs against BOTH and requires them to agree.
# ([[feedback-a-column-parser-is-tested-by-its-widest-datum]])

_BYTES_ONLY = re.compile(r"(?:\s*[0-9a-f]{2})+\s*\Z")
_ADDR = re.compile(r"^\s*[0-9a-f]+:")
GNU_OBJDUMP = "/opt/homebrew/opt/binutils/bin/objdump"


def bytes_of(disasm):
    """The instruction bytes in an `objdump -d` listing, for BOTH tools.

    Drop the address, split the remainder on TABS, and take the leading run of
    fields that are nothing but hex byte pairs. Trailing padding is ignored
    rather than relied on."""
    out = []
    for ln in disasm.splitlines():
        if not _ADDR.match(ln):
            continue
        for field in _ADDR.sub("", ln, count=1).split("\t"):
            if field.strip() == "":
                continue
            if _BYTES_ONLY.fullmatch(field):
                out.append(re.sub(r"\s+", "", field))
            else:
                break
    return "".join(out)


def encode_forms(asms, objdump="objdump"):
    """{asm: hex} — one .s per form, so a form the assembler refuses is NAMED
    rather than silently shifting its neighbours' bytes."""
    out = {}
    with tempfile.TemporaryDirectory() as td:
        for i, a in enumerate(asms):
            src = os.path.join(td, "f%d.s" % i); obj = os.path.join(td, "f%d.o" % i)
            open(src, "w").write("    .text\n    %s\n" % a)
            r = subprocess.run(["clang", "-target", "x86_64-unknown-linux-gnu",
                                "-c", src, "-o", obj],
                               capture_output=True, text=True)
            if r.returncode != 0:
                tail = (r.stderr.strip().splitlines() or ["?"])[-1]
                out[a] = "ASSEMBLER REFUSED: " + tail
                continue
            d = subprocess.run([objdump, "-d", "--section=.text", obj],
                               capture_output=True, text=True).stdout
            out[a] = bytes_of(d)
    return out


def _disagreements(forms, objdump):
    enc = encode_forms([a for _l, a, _h, _e0, _e1 in forms], objdump=objdump)
    return [(l, h, enc[a]) for l, a, h, _e0, _e1 in forms if enc[a] != h]


def encoding_check():
    """The `hx` every row EXECUTES is the assembly of the `asm` that NAMES it —
    on every disassembler this box has — driven red first."""
    # ══════════════════════════════════════════════════════════════════
    # ⭐ D130's STRUCTURE GATE RIDES HERE, and here on purpose: this is the
    # entry point CI runs (`--check-encodings`), because ACL2 is not on the
    # runner.  A gate that only fires under `--p2` is a gate the runner never
    # sees ([[feedback-a-gate-behind-a-failing-step-is-silent]]).
    if p2_structure_check():
        return 1
    # ⭐⭐ QUEUE 0(c) RIDES HERE TOO, and here ESPECIALLY: this is the entry point
    # CI runs, and the contradiction this gate exists to catch is invisible to
    # every ACL2-bearing path because those paths MEASURE rather than compare.
    if forms_vs_p2forms_check():
        return 1
    # ⭐ RED FIRST FOR THE CROSS-TABLE GATE, before its neighbour's arms.  Arm 1
    # plants the exact defect that was live on this tree until today — a P2 row
    # declaring `executes` for bytes `FORMS` calls `stalls`.  Arm 2 plants the
    # OPPOSITE direction, because a gate tested in one direction only is an
    # assertion about the half somebody happened to break
    # ([[feedback-probe-gates-both-ways]]).  Arm 3 removes the REFUTATION and
    # requires the gate to go red on the shipped tables — which is what makes the
    # green below evidence that the refutation is doing the work, and not that the
    # tables were trivially consistent all along.
    # ⚠️ EVERY ARM TARGETS `movmskps`, AND NOT BY PREFERENCE.  Measured: `FORMS`
    # and `P2_FORMS` share exactly ONE mnemonic and one encoding — 18 against 227
    # mnemonics, intersection `{movmskps}`.  An arm planted anywhere else does not
    # join, so it plants NOTHING and the gate is silent for a reason that has
    # nothing to do with the gate ([[feedback-a-probe-must-create-its-condition]]).
    # ⛔ MY FIRST TWO ARMS BOTH FAILED THIS WAY and the failure is kept here rather
    # than tidied away: arm 1 planted a P2 value the REFUTATION then overrode back
    # to agreement, and arm 2 planted into `xorpd`, which `FORMS` does not carry.
    # Both printed "RED ARM SILENT", which is the gate's arm-checker working.
    def _p2_with(rows, label, e1v):
        return [(l, a, h, e0, e1v) if l == label else (l, a, h, e0, e1)
                for l, a, h, e0, e1 in rows]

    def _forms_with(rows, mn, ev):
        return [(m, a, h, ev) if m == mn else (m, a, h, e) for m, a, h, e in rows]

    xt_arms = [
        ("the REFUTATION emptied — the shipped tree's OWN contradiction, which is "
         "what proves the refutation is load-bearing and not decorative",
         lambda f, p, r: (f, p, {})),
        ("FORMS flipped to `executes` for bytes the refuted P2 row calls `stalls` "
         "(the opposite direction to the live defect)",
         lambda f, p, r: (_forms_with(f, "movmskps", "executes"), p, r)),
        ("a direct P2/FORMS clash with NO override in play (`refuses` vs `stalls`)",
         lambda f, p, r: (f, _p2_with(p, "movmskps", "refuses"), {})),
    ]
    for why, plant in xt_arms:
        if not forms_vs_p2forms_check(*plant(list(FORMS), list(P2_FORMS),
                                             dict(REFUTED_BY_MEASUREMENT)),
                                      quiet=True):
            print("⛔ cross-table gate: RED ARM SILENT — %s was NOT caught, so "
                  "this gate is not watching what it claims to." % why)
            return 1
        print("  ✔ red arm caught: %s" % why)
    # ⚠️ AND THE VACUITY ARM, because the three above all pass on a gate that
    # refuses everything, and none of them can see an EMPTY domain.
    if not forms_vs_p2forms_check([], list(P2_FORMS), {}, quiet=True):
        print("⛔ cross-table gate: an EMPTY FORMS table passed — the gate can "
              "become vacuous without saying so.")
        return 1
    print("  ✔ red arm caught: an empty domain reports VACUOUS rather than green")
    if forms_vs_p2forms_check(quiet=True):
        print("⛔ cross-table gate: the SHIPPED tables fail their own check.")
        return 1
    print("  ✔ control: the shipped tables pass the same check unplanted")
    # ⭐ RED FIRST, AND THE SECOND ARM IS THE ONE THAT MATTERS.  Arm 1 plants two
    # rows with the SAME LABEL — the live `vpsubw` defect's own shape, and one a
    # reader could in principle spot.  Arm 2 plants two rows whose labels are
    # VISIBLY DIFFERENT and whose TAGS collide anyway, because `tag_of` squashes
    # every non-alphanumeric to `_`; this table already carries labels like
    # `CONTROL:mov` and `ADD1:mov %gs:`, so that collision is reachable and is
    # invisible in the source.  An arm drawn only from the visible half would be
    # silent on it ([[feedback-a-control-can-share-the-blind-spot]]).
    dup_arms = [
        ("two rows sharing a LABEL outright (the live `vpsubw` shape)",
         lambda rows: rows[:1] + [(rows[0][0],) + rows[1][1:]] + rows[2:]),
        ("two rows whose LABELS DIFFER but whose TAGS collide under `tag_of` "
         "(`X:y` and `X_y`)",
         lambda rows: [("X:y",) + rows[0][1:], ("X_y",) + rows[1][1:]] + rows[2:]),
    ]
    for why, plant in dup_arms:
        if not p2_structure_check(plant(list(P2_FORMS)), quiet=True):
            print("⛔ P2 structure gate: RED ARM SILENT — %s was NOT caught, so "
                  "this gate is not watching what it claims to." % why)
            return 1
        print("  ✔ red arm caught: %s" % why)
    # ⚠️ AND THE CONTROL, because a gate that refuses everything also passes both
    # arms above ([[feedback-a-probe-must-create-its-condition]]).
    if p2_structure_check(list(P2_FORMS), quiet=True):
        print("⛔ P2 structure gate: the UNPLANTED table failed its own gate.")
        return 1
    print("  ✔ control: the shipped table passes the same check unplanted")

    tools = [("LLVM (PATH)", "objdump")]
    if os.path.exists(GNU_OBJDUMP):
        tools.append(("GNU binutils", GNU_OBJDUMP))
    else:
        print("  ⚠️ GNU objdump is not on this box; the wrapped-column format is "
              "NOT exercised here. It is exercised on the x86-64 runner.")
    for name, tool in tools:
        bad = _disagreements(P2_FORMS, tool)
        if bad:
            print("⛔ oracle-encoding gate: FAIL under %s — the `asm` column and "
                  "the `hx` that RUNS are different instructions:" % name)
            for l, h, g in bad:
                print("    %s: declared=%s  assembler=%s" % (l, h, g))
            return 1
        print("  ✔ %-14s %d forms: every `hx` is the assembly of its own `asm`"
              % (name + ":", len(P2_FORMS)))

    # ⭐ RED FIRST, AND THE THIRD ARM IS THE ONE THAT MATTERS. A control drawn
    # from the same half of the space is silent: arms 1 and 3 are ordinary short
    # forms and would BOTH have passed against the padding-dependent parser this
    # gate was born from. Arm 2 perturbs the WIDEST row, in the one dimension a
    # column parser can be frozen in.
    # ([[feedback-a-control-can-share-the-blind-spot]])
    widest = max(P2_FORMS, key=lambda r: len(r[2]))
    arms = [
        ("one byte flipped in an ordinary short form",
         lambda l, h: "660f6f04" if l == "movdqa" else h),
        ("the WIDEST row (`%s`, %d bytes) truncated by its LAST byte — the "
         "padding blind spot" % (widest[0], len(widest[2]) // 2),
         lambda l, h: h[:-2] if l == widest[0] else h),
        ("a row carrying a DIFFERENT real instruction's encoding "
         "(`pxor` given `paddd`'s bytes)",
         lambda l, h: "660ffec1" if l == "pxor" else h),
    ]
    for why, mutate in arms:
        planted = [(l, a, mutate(l, h), e0, e1) for l, a, h, e0, e1 in P2_FORMS]
        if not _disagreements(planted, "objdump"):
            print("⛔ oracle-encoding gate: RED ARM SILENT — %s was NOT caught, "
                  "so this gate is not watching what it claims to." % why)
            return 1
        print("  ✔ red arm caught: %s" % why)
    print("oracle-encoding gate: CLEAN — %d forms, %d disassembler(s), 3 red arms"
          % (len(P2_FORMS), len(tools)))
    return 0


def main():
    if "--check-encodings" in sys.argv:
        return encoding_check()
    if "--p2" in sys.argv:
        return p2_run()
    check = "--check" in sys.argv
    if "--selftest" in sys.argv:
        # ⭐ RED FIRST, BOTH DIRECTIONS.  A gate that has only ever been seen
        # green has not been seen at all — and this one has two failure
        # directions that need opposite handling, so both are driven.
        res, n = measure(FORMS)
        base = report(FORMS, res, n, quiet=True)
        if base:
            print("⛔ selftest cannot run: the SHIPPED table already disagrees:")
            for mn, why in base: print(f"    {mn}: {why}")
            return 1
        arms = 0
        for flip, direction in (("refuses", "a declared-unavailable form that starts executing"),
                                ("executes", "a declared-available form that refuses")):
            planted = [(mn, a, b, ("executes" if e == "refuses" else "refuses"))
                       if e == flip else (mn, a, b, e) for mn, a, b, e in FORMS]
            bad = report(planted, res, n, quiet=True)
            want = sum(1 for f in FORMS if f[3] == flip)
            if len(bad) != want:
                print(f"⛔ selftest arm FAILED — planting the opposite claim on all "
                      f"{want} '{flip}' forms was reported by {len(bad)} of them. "
                      f"({direction} would go unreported.)")
                return 1
            arms += 1
            print(f"  ✔ red arm: {direction} is reported ({want} forms flipped, "
                  f"{len(bad)} reported)")
        # ⚠️ and the CONTROL must not be quietly satisfiable by a dead run
        empty = report(FORMS, {}, n, quiet=True)
        if len(empty) != len(FORMS):
            print("⛔ selftest arm FAILED — a run that produced NO records was not "
                  "reported as a failure by every form.")
            return 1
        print(f"  ✔ red arm: an EMPTY run is reported by all {len(FORMS)} forms, "
              f"not read as agreement")
        print(f"oracle-availability selftest: PASS ({arms + 1} red arms over "
              f"{len(FORMS)} forms x {n} pre-states)")
        return 0
    res, n = measure(FORMS)
    print(f"oracle availability over {n} real pre-states "
          f"({len(FORMS)} forms, ACL2 x86isa):")
    bad = report(FORMS, res, n)
    if bad:
        print("⛔ oracle-availability gate FAILED:")
        for mn, why in bad: print(f"    {mn}: {why}")
        return 1
    print("oracle-availability gate: CLEAN — every declaration matches the "
          "oracle's own behaviour, and both controls executed.")
    return 0

# ══════════════════════════════════════════════════════════════════════════
# ⭐⭐ THE MEASUREMENT, MADE READABLE BY THE ROSTER — P2 batch 11.
#
# ⛔ THE P2 ROSTER RANKED `pmaddwd` FIRST AND `psubusw` THIRD WHILE THIS FILE HAD
# HELD BOTH AS REFUSED SINCE P2 BATCH 1.  The roster joins DEMAND (the census)
# against SUPPLY (K's tree) and consults no third artifact, so a form the ORACLE
# cannot execute is priced exactly like one it can — and the ranked list a fresh
# head is handed carries the omission into the next batch.  It is D100's defect
# on the other side of the join: there the demand was another instruction's, here
# the supply is one the differential cannot ask about.
#
# ⇒ 🔑 A ROSTER THAT PRICES DEMAND DOES NOT PRICE BUILDABILITY, AND THE TWO LOOK
# THE SAME IN A RANKED TABLE.
#
# ⚠️ THE MNEMONIC IS TAKEN FROM THE `asm` COLUMN'S FIRST TOKEN, NOT FROM THE
# LABEL.  The labels are probe tags — `movq_xmm`, `movq_mmx`, `paddw_mmx`,
# `ADD1:mov %gs:` — and stripping a suffix off them to recover a mnemonic is
# precisely the lossy key that made D100's phantom row.  The `asm` string is what
# an assembler accepted, so its first token IS the mnemonic, with no rule to go
# stale.
#
# ⛔ AND A MNEMONIC THIS TABLE DOES NOT NAME IS `None` — **NOT** "executes".
# A declared list inherits the direction of its default, and the default that
# invents work is the unpoliced one: an absent form must read as UNMEASURED, so
# the roster prints a question mark rather than a licence.
# ⛔⛔ AND THE KEY IS (MNEMONIC, ISA BUCKET), NOT THE MNEMONIC.  The first draft
# of this function keyed by mnemonic alone and immediately reproduced D100 in the
# opposite direction: `vpaddw` is probed here only as `vpaddw %zmm1,%zmm2,%zmm0`
# (AVX-512, which this oracle cannot execute at all), and the roster's `vpaddw`
# row is 11,682 instructions of AVX2 `%ymm` demand.  The join printed ⛔ REFUSES
# against a row whose actual encoding was never probed.
#
# ⇒ 🔑 A VERDICT MUST BE JOINED ON THE SAME KEY THE DEMAND IS COUNTED BY.  The
# census counts the gap per (mnemonic, ISA bucket) — `miss_by_ext`, D100's own
# repair — so that is the key, and the bucket NAMES ARE THE CENSUS'S, spelled the
# same way, because two vocabularies for one partition is the second source that
# goes stale.
#
# ⚠️ AND THE FAILURE WAS AN UNDER-CLAIM, WHICH IS THE DIRECTION NOBODY POLICES:
# marking a buildable row unbuildable reads as caution, not as a mistake, and it
# would have removed a rank from the next head's list with a reason that looked
# measured. It was caught by reading the OUTPUT of the fix rather than its intent.
# ⛔⛔ THE ROWS THAT ARE NOT AN AVAILABILITY QUESTION, DECLARED WITH THE REASON
# EACH ONE IS OUT (D143). Until now these fell out silently: the old
# operand-reading rule returned `None` for anything with no vector register, and
# `measured_availability` skipped it. That is a DEFAULT wearing a decision's
# clothes — the set it produced was "rows with no `%xmm`", and every member's
# exclusion inherited that accident rather than a ruling.
#
# ⚠️ THREE OF THEM ARE OUT FOR A MEASURED REASON, and the measurement is what
# stopped this file from delegating wholesale:
#   · `ADD2:lock incl (%rbx)` — `asm.split()[0]` is the PREFIX `lock`, so the key
#     would be the phantom mnemonic `("lock", …)`, which no census row can match.
#   · `ADD1:movq %gs:0x28, %rax` — the census buckets this by KIND (`segment`),
#     a datum the asm TEXT cannot carry; keyed off the text it lands in
#     `GPR/other` and joins against ordinary `movq` demand, pricing one thing
#     with another's.
#   · `ADD3:movabsq …` — its bucket is `mov imm64 / movabs (P2 addition 3)`,
#     which is NOT one of the census's MISS buckets at all, so there is no demand
#     row for it to join and `p2_roster`'s vocabulary gate would go red on it.
#
# ⚠️ THE OTHER SIX ARE OUT ONLY BECAUSE THEY WERE OUT YESTERDAY, and that is said
# rather than dressed up: `endbr64`, `prefetcht0`, `prefetchnta`, `emms` and the
# two `CONTROL:` rows all map to real census buckets under the census's own rule,
# so their verdicts ARE availability facts this table could carry. Ruling on them
# widens what `measured_availability` means and moves the roster; it is
# `docs/QUEUE.md`'s item, not a side effect of a bucket repair.
# [[feedback-a-declared-list-inherits-its-default]]
# [[feedback-a-category-is-a-hypothesis-about-its-members]]
NOT_AN_AVAILABILITY_QUESTION = {
    "ADD2:lock incl":  "the key's mnemonic would be the prefix `lock`",
    "ADD1:mov %gs:":   "the census buckets it by kind=segment, which the asm text cannot carry",
    "ADD3:movabsq":    "its bucket is not one of the census's MISS buckets",
    "CONTROL:mov":     "a harness control, not a census question — unruled, see QUEUE",
    "CONTROL:movnti":  "a harness control, not a census question — unruled, see QUEUE",
    "endbr64":         "maps to CET-IBT under the census rule — unruled, see QUEUE",
    "prefetcht0":      "maps to PREFETCH under the census rule — unruled, see QUEUE",
    "prefetchnta":     "maps to PREFETCH under the census rule — unruled, see QUEUE",
    "emms":            "maps to GPR/other under the census rule — unruled, see QUEUE",
}


def probe_bucket(asm):
    """The census ISA bucket a probe form belongs to — the CENSUS's own rule.

    ⛔ THIS IS `demand_census.isa_bucket`, CALLED, not a rule that agrees with it.
    The demand side of the join is bucketed by that function; a second function
    here would be a second definition of one partition, and the two would diverge
    on whichever table was appended to next.

    ⚠️ It is TOTAL — every form gets a bucket. Which forms are an availability
    QUESTION is a separate matter and lives in `NOT_AN_AVAILABILITY_QUESTION`,
    where each exclusion carries its reason. Conflating the two is what made the
    old `None` return a silent default."""
    toks = asm.split(None, 1)
    return _DC.isa_bucket(toks[0], toks[1] if len(toks) > 1 else "")


def forms_vs_p2forms_check(forms=None, p2forms=None, refuted=None, quiet=False):
    """⛔⛔ THE CROSS-TABLE GATE — QUEUE item 0(c), D177.

    `FORMS` and `P2_FORMS` are two tables in ONE FILE that both answer "what does
    x86isa do with these bytes", and until now nothing compared them.  D170's
    three-valued repair landed in `FORMS` (line ~95, `movmskps` -> `stalls`) and
    not in `P2_FORMS` (line ~917, the same bytes -> `executes`), and the
    availability map is built from the second.  The contradiction sat 850 lines
    apart in one file for two days and was found by reading, not by a gate.

    ⇒ 🔑 THIS IS THE GATE THAT WOULD HAVE CAUGHT IT ON THE DAY D170 LANDED, and
      it is pure string work — microseconds, no ACL2, so it runs on the CI entry
      point where the oracle is absent ([[feedback-a-gate-behind-a-failing-step-is-silent]]).

    ⚠️ THE JOIN KEY IS (mnemonic, ENCODING), NOT THE MNEMONIC ALONE, and that is a
    DEPARTURE from the QUEUE's wording ("the same mnemonic") that has to earn
    itself.  A mnemonic can legitimately hold different verdicts at different
    buckets — `pandn` executes at `xmm` and at `mm` are two separate facts, and
    `FORMS` carries one row per mnemonic.  Joining on the mnemonic alone would
    manufacture contradictions out of that, which is the lossy key this repo has
    already paid for once ([[feedback-a-join-on-a-lossy-key]]).  The BYTES are the
    exact key: the same encoding under the same CR4 must get the same verdict.

    ⛔ AND THE BLIND SPOT IS PRINTED RATHER THAN LEFT IMPLICIT.  A stricter key
    means some shared mnemonics do not join at all, and an unjoined pair is
    UNCHECKED, not agreed.  A too-narrow observation does not report "unknown" —
    it positively claims agreement about a region it never looked at
    ([[feedback-unobserved-regions-report-agreement]]), so the count of shared
    mnemonics that did NOT join is reported on every run.

    ⚠️ BOTH SIDES ARE COMPARED AT CR4_ON.  `FORMS`'s `expect` is the verdict under
    the differential's own conditions (`check_driver_cr4.py` is the gate that says
    the driver runs at CR4=0x600), which is `P2_FORMS`'s `e1` column, not `e0`."""
    forms = FORMS if forms is None else forms
    p2forms = P2_FORMS if p2forms is None else p2forms
    refuted = REFUTED_BY_MEASUREMENT if refuted is None else refuted

    p2 = {}
    for label, asm, hx, _e0, e1 in p2forms:
        v = refuted[label].e1 if label in refuted else e1
        p2.setdefault((asm.split()[0], hx.lower()), []).append((label, v))

    bad, joined = [], 0
    for mn, _asm, hx, expect in forms:
        rows = p2.get((mn, hx.lower()))
        if not rows:
            continue
        joined += 1
        for label, v in rows:
            if v != expect:
                bad.append("%s / %s [%s]: FORMS declares %r, P2_FORMS declares %r "
                           "for the SAME BYTES" % (mn, label, hx, expect, v))

    f_mn = {mn for mn, _a, _h, _e in forms}
    p_mn = {asm.split()[0] for _l, asm, _h, _e0, _e1 in p2forms}
    joined_mn = {mn for (mn, _hx) in p2 if mn in f_mn}
    unjoined = sorted((f_mn & p_mn) - joined_mn)

    # ⛔⛔ A GATE WITH AN EMPTY DOMAIN PASSES EVERYTHING, AND SILENTLY.  These two
    # tables overlap in exactly ONE encoding today (`movmskps` / `0f50c1`) — which
    # is precisely the pair that was contradictory, so the gate's whole reach is
    # its own founding case.  If a future edit drops that overlap to zero this
    # gate would go GREEN forever while checking nothing, which is the failure it
    # exists to prevent, wearing a tick ([[feedback-a-complete-count-of-a-subset]]).
    # ⚠️ Reported as a DISTINCT failure, not as a contradiction: it is a fact about
    # the gate's REACH, and a reader must not read it as two tables disagreeing.
    if joined == 0:
        bad.append("VACUOUS: FORMS and P2_FORMS share no encoding, so this gate "
                   "compared nothing. This is a finding about the gate's reach, "
                   "NOT a contradiction between the tables.")

    if not quiet:
        print(("  ✔ " if not bad else "  ⛔ ") +
              "FORMS vs P2_FORMS: %d encodings in both tables agree" % joined +
              ("" if not bad else "   %d CONTRADICTION(S)" % len(bad)))
        for b in bad:
            print("      ⛔ %s" % b)
        # ⚠️ NOT a failure — a NUMBER for the region this key cannot see.
        print("     (%d mnemonic(s) in both tables did not join on an encoding "
              "and are UNCHECKED, not agreed%s)"
              % (len(unjoined), "" if not unjoined else ": " + ", ".join(unjoined)))
    return bad


# ⛔⛔⛔ THE REFUTATION TABLE — QUEUE item 0(b), D177 (2026-09-08).
#
# `P2_FORMS`'s `e0`/`e1` are DECLARATIONS, sealed at `sha256 = 6e8474ff…`
# 2026-09-05T20:02:18Z BEFORE the runs that score them.  A seal exists to stop a
# declaration being fitted to a measurement, so when a measurement refutes one
# the honest move is to RECORD THE REFUTATION, NOT TO EDIT THE SEALED ROW.  The
# rows below are therefore left exactly as sealed and are overridden here, in the
# open, with the evidence and the date attached.
#
# ⇒ 🔑 A FUNCTION NAMED `measured_availability` THAT RETURNS A SEALED PREDICTION
#   IS A CITATION WEARING A MEASUREMENT'S NAME.  That is the actual defect item 0
#   describes; `movmskps` is one symptom of it and `vmovmskps_v` is a second that
#   nothing had looked for ([[feedback-a-citation-is-an-ungated-claim]],
#   [[feedback-naming-a-defect-is-not-finding-its-siblings]]).
#
# ⚠️ THE SEALED VALUES ARE NOT "WRONG".  Under `measure_cr4`'s pre-D177 vocabulary
# `executes` was a TRUE statement about the refusal flag and a FALSE statement
# about the world.  The defect was the classifier's VALUE SET, which is why the
# repair is (a) a third value and only then (b) this table
# ([[feedback-a-classifiers-value-set-is-a-claim]]).
# ⚠️ THE VALUE IS A NAMED RECORD, NOT A BARE TUPLE, AND THAT IS A REPAIR OF A
# DEFECT THIS TABLE ALREADY CAUSED.  It started as `(verdict, why)`; adding the
# CR4=0 arm made it `(e0, e1, why)`, and a consumer in `p2_roster.py` kept its
# positional `[0]` — which silently stopped meaning "the verdict" and started
# meaning "the CR4=0 verdict".  It did not crash: it published `refuses` for two
# refuted rows and a STALLS count of 1 where the answer is 3, which is a number a
# reader would accept.  ⇒ 🔑 A POSITIONAL INDEX IS A BET THAT THE RECORD WILL NOT
# GROW, AND THE PAYOUT IS A PLAUSIBLE WRONG NUMBER rather than an error
# ([[feedback-a-positional-index-bets-the-record-wont-grow]]).  Fields are named
# so the next arm added here cannot repeat it.
Refutation = collections.namedtuple("Refutation", "e0 e1 why")
REFUTED_BY_MEASUREMENT = {
    "movmskps": Refutation("refuses", "stalls",
        "D170 2026-09-06: 88/88 readings, RIP never advanced from ENTRY_RIP with "
        "the refusal flag CLEAR. Re-measured D177 2026-09-08 by the repaired "
        "three-valued `measure_cr4` in a run that also produced `refuses` and "
        "`executes`, so the classifier was not stuck on one value."),
    "vmovmskps_v": Refutation("refuses", "stalls",
        "D177 2026-09-08: THE SIBLING D170 NEVER RULED ON. Same movmsk shape "
        "(writes a GPR, not a vector register). Found by asking for it directly "
        "rather than by any gate."),
    "emms": Refutation("stalls", "stalls",
        "D177 2026-09-08: FOUND ONLY BY THE FULL 267-ROW SWEEP, not by the "
        "four-form probe that confirmed the other two — which is why the sweep "
        "was run. Declared (executes, executes) and stalls under BOTH CR4 arms. "
        "It sits in NOT_AN_AVAILABILITY_QUESTION, so it moves no availability "
        "answer; its DECLARATION was still false and nothing had asked."),
}


def measured_availability():
    """{(mnemonic, bucket): "executes" | "refuses" | "stalls"} — CR4-ENABLED arm.

    ⛔ THREE-VALUED SINCE D177.  It was declared two-valued here while `FORMS`
    800 lines above already carried `stalls`, and a two-valued classifier over a
    three-valued world scores the unseen state as whichever value is the
    RESIDUAL — here `executes`, i.e. AVAILABLE, in the one table whose stated
    purpose is to stop unavailable work from being invented.

    ⚠️ CR4=0x600 is the arm to read because it is the condition the differential
    itself runs under (`scripts/check_driver_cr4.py` is the gate that says so).
    The CR4=0 column measures a machine with SSE switched off, where everything
    refuses for a reason that is not about the form.

    ⚠️ THE MNEMONIC IS THE `asm` COLUMN'S FIRST TOKEN, NOT THE LABEL.  The labels
    are probe tags — `movq_xmm`, `paddw_mmx`, `ADD1:mov %gs:` — and stripping a
    suffix off one to recover a mnemonic is the lossy key that made D100's
    phantom row.  The `asm` string is what an assembler accepted, so its first
    token IS the mnemonic, with no rule to go stale.

    ⛔ REFUSES ON A CONFLICT rather than picking one: two probes at the same
    (mnemonic, bucket) with different verdicts is a finding about this table, and
    resolving it silently would bury it."""
    out, seen = {}, {}
    for label, asm, _hx, _e0, e1 in P2_FORMS:
        # ⛔ SKIPPED BY A DECLARED LABEL WITH A REASON, never by a bucket that
        # came back empty. A rule that returns nothing and a decision not to ask
        # are different facts, and only one of them can be audited.
        if label in NOT_AN_AVAILABILITY_QUESTION:
            continue
        # ⛔ THE SEALED DECLARATION IS OVERRIDDEN HERE, NOT EDITED THERE.
        if label in REFUTED_BY_MEASUREMENT:
            e1 = REFUTED_BY_MEASUREMENT[label].e1
        key = (asm.split()[0], probe_bucket(asm))
        if key in seen and seen[key][1] != e1:
            raise SystemExit(
                "⛔ oracle-availability: %r is measured %s as %r and %s as %r. "
                "One (mnemonic, bucket), two verdicts — resolve the table, do "
                "not pick." % (key, seen[key][0], seen[key][1], label, e1))
        seen[key] = (label, e1)
        out[key] = e1
    return out


# ⛔ GUARDED.  This file used to end in a bare `sys.exit(main())`, so IMPORTING
# it ran the P1 gate and took the importing process's exit with it — which is
# exactly what happened the first time the P2 probe below tried to reuse
# `measure()` rather than copy it.  A module that cannot be imported forces the
# next tool to duplicate its runner, and a duplicated runner is one that can
# disagree with itself ([[feedback-duplicate-born-in-agreement]]).
if __name__ == "__main__":
    sys.exit(main())
