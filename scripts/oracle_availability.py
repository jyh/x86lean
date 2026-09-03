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
import os, re, subprocess, sys, tempfile

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(root)
ACL2 = os.environ.get("ACL2", os.path.join(root, "vendor", "acl2", "saved_acl2"))

# ⭐ THE TABLE.  `expect` is what this repository claims about the oracle, and
# the run below is what the oracle says.  The bytes are clang's, not mine
# (`clang -target x86_64-unknown-linux-gnu`), and the asm is beside them so a
# reader can re-assemble any line.
FORMS = [
    # (mnemonic,   asm,                       bytes,                expect)
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
    # ⭐ THE POSITIVE CONTROL — identical shape and address to `movnti`.
    ("CONTROL:mov", "movl %ecx, (%rbx)",    "890b",               "executes"),
    # ⭐ AND A SECOND CONTROL AT THIS BATCH'S OWN FORM, so a run that has stopped
    # seeing memory-operand instructions cannot pass.
    ("CONTROL:cmpxchg8b", "cmpxchg8b (%rbx)", "0fc70b",           "executes"),
    # ⭐⭐ THE SIX DECLINED ROWS, RECORDED AS **EXECUTES** — and that is the point.
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
    # D25 — `xchg` at a memory operand asserts LOCK whether or not it is
    # written.  ⛔ That decline is about VOCABULARY and this row does not touch
    # it: a single-threaded model can reproduce every observation this harness
    # makes and still be wrong about the only thing that distinguishes the
    # instruction.  **Oracle support is not an argument to un-decline it.**
    ("DECLINED:bt m,r",   "btl %ecx,(%rbx)",   "0fa30b",          "executes"),
    ("DECLINED:bts m,r",  "btsl %ecx,(%rbx)",  "0fab0b",          "executes"),
    ("DECLINED:btr m,r",  "btrl %ecx,(%rbx)",  "0fb30b",          "executes"),
    ("DECLINED:btc m,r",  "btcl %ecx,(%rbx)",  "0fbb0b",          "executes"),
    ("DECLINED:xchg m,r", "xchgl %ecx,(%rbx)", "870b",            "executes"),
]

CASES = "run/cases.lsp"

def pre_states():
    """The real pre-states, taken from the emitted differential cases.  ⚠️ NOT a
    fresh set written here: a probe on states the differential does not use
    would answer a question nobody asked."""
    if not os.path.exists(CASES):
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
        return " ".join("(#x%016x . %s)" % (0x400000 + k, b[k]) for k in range(len(b)))
    c[4] = re.sub(r'\(#x0000000000400000 \. #x[0-9a-f]{2}\)(?: \(#x00000000004000[0-9a-f]{2} \. #x[0-9a-f]{2}\))*',
                  repl, c[4], count=1)
    if "#x%016x" % (0x400000 + len(b) - 1) not in c[4]:
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
            e, r = res.get(cur, (0, 0))
            if re.search(r"refused=1", l): r += 1
            else: e += 1
            res[cur] = (e, r)
            cur = None
    return res, len(sel)

def report(forms, res, n, quiet=False):
    bad = []
    for mn, asm, _b, exp in forms:
        tag = tag_of(mn)
        e, r = res.get(tag, (0, 0))
        if e + r != n:
            bad.append((mn, "produced %d records, expected %d — a missing reading "
                            "is not a refusal" % (e + r, n)))
            continue
        got = "refuses" if r == n else ("executes" if e == n else "MIXED")
        if got != exp:
            bad.append((mn, "declared %s, MEASURED %s (executed %d, refused %d of %d)"
                        % (exp, got, e, r, n)))
        if not quiet:
            mark = "✔" if got == exp else "⛔"
            print(f"  {mark} {mn:22s} {asm:26s} {got:9s} ({e} executed, {r} refused)")
    return bad

def main():
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

sys.exit(main())
