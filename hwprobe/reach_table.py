#!/usr/bin/env python3
"""hwprobe/reach_table.py — THE REACH TABLE, as a command instead of a scratch pass (D267 §2).

D267 §2 fixes the rule that selects `mk_anchors.py`'s pins:

    a row is pinned iff x86isa disagrees with it or cannot run it,
    OR no vector of the same form reaches its class over the 88 differential pre-states.

and records that the reach half was measured by "a scratch Lean pass ... and Python classed them".
⛔ A SCRATCH PASS IS RE-DERIVED BY EVERY HEAD THAT NEEDS IT, AND ITS ANSWER REACHES THE REPOSITORY
ONLY AS A HAND-DECLARED `PINNED` SET THAT CI CANNOT RE-RUN. `mk_anchors.py` says so in its own
docstring: PINNED is "DECLARED, from two measurements this generator cannot re-run in CI". This
file makes the first of those two a command, so the declaration has an origin a reader can re-run.

    python3 hwprobe/reach_table.py --gen           # writes run/reach_streams.lean
    python3 scripts/lean_route.py lean run/reach_streams.lean > run/reach_streams.out
    python3 hwprobe/reach_table.py --form b4          # the table, one line per row
    python3 hwprobe/reach_table.py --form b4 --tsv docs/REACH-B4.tsv
    python3 hwprobe/reach_table.py --selftest         # the SIBLING control (below)

## ⭐ THE CONTROL IS THE POINT, AND IT IS A KNOWN ANSWER RATHER THAN A PLANT

`--selftest` runs this file's rule against `cvtsi2sd`, whose pins LANDED at D267 and whose reach
answer is therefore known independently of this file: exactly `cvtsi2sd_one/zero` and
`cvtsi2sd_intmin/up` are unreached. The arm reds unless the rule reproduces that set exactly.
⛔ IT ALSO REDS THE OTHER WAY: a MUTANT class (value x FULL MXCSR instead of value x RC) must NOT
reproduce it — measured, the mutant scores six. Without that half the arm would pass for a rule
that is merely strict enough, and an arm that cannot fail is decoration
([[feedback-an-expectation-written-from-intent]]).

## ⚠️ WHAT THIS TOOL DOES NOT MEASURE, RIDING WITH ITS VERDICT

- **The stream map is DECLARED AND CHECKED.** `STREAMS` is written out for a reader, and
  `--selftest` ARM 3 derives the same map from the vectors' instruction CONSTRUCTORS in
  `Tests/Vectors.lean` (never their `asm` text) and reds on any disagreement, so a vector added
  to a form without a line here is caught rather than silently over-pinned. ⚠️ THE ARM EXISTS
  BECAUSE DRIVING THE SUITE RED EXPOSED ITS ABSENCE: dropping three of the sibling's four
  vectors left ARMS 1 and 2 GREEN, because `rcx` alone already reaches everything they reach.
  Two arms were exercising ONE dimension.
- **The x86isa column** comes from `rows_on_x86isa.py`'s saved reading, which is a claim about the
  shas that produced it, not about x86isa today.
- **Reach is not coverage.** A reached row is one some vector's source EQUALS at that RC; it says
  nothing about whether the differential's comparison of that case is itself sound.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import mk_rows as M                                    # noqa: E402
import portable as P                                   # noqa: E402

STREAMS_OUT = os.path.join(ROOT, "run", "reach_streams.out")

STREAMS_LEAN = os.path.join(ROOT, "run", "reach_streams.lean")

# ⛔ THE PASS IS GENERATED INTO `run/`, NOT TRACKED AS A `.lean` FILE, and that is the gate's
# doing rather than a dodge: a tracked `*.lean` outside the lake build trips `kernel_drift --gap`,
# which globs `*.lean` because any Lean source in this repo normally MOVES A KERNEL READING. This
# one cannot — `lakefile.toml`'s targets are X86 · X86Native · Tests · Main · AxiomGate and none
# of them reaches `hwprobe/` — so the honest repair is to stop being a tracked Lean source, not to
# widen an exemption. It is also exactly how `rows_on_x86isa.py` already ships its ACL2 drivers.
PASS_SRC = r"""/-
hwprobe/reach_streams.lean — the operand streams the REACH TABLE is computed from (D267 §2).

D267 §2 records the reach table as "a scratch Lean pass [that] printed the operand bits over 88
states". A SCRATCH pass is re-derived by every head that needs it, and its result reaches the
repository only as a hand-declared `PINNED` set in `mk_anchors.py` that CI cannot re-run. This
file is that pass, tracked, so the declaration has a reproducible origin.

    python3 scripts/lean_route.py lean hwprobe/reach_streams.lean > run/reach_streams.out
    python3 hwprobe/reach_table.py --form b4

⛔ NOTHING HERE IS TYPED. Every value is read out of the pre-states the differential harness
emits, through the model's own accessors, so a change to `preStates` moves this file's output.

The four memory offsets are the ones the landed integer-conversion vectors address, read from
their instruction constructors in `Tests/Vectors.lean` and not from their `asm` strings:
`(%rbx)` = 0x2000 · `-0x3(%rbx)` = 0x1ffd · `-0x1e(%rbx)` = 0x1fe2.
-/
import Tests.Vectors

open X86 X86.Tests

def reachStreams : IO Unit := do
  let ss := preStates 1 8
  -- CONTROLS, printed with the data so a consumer cannot read the table without them:
  -- RBX must be the window base, or every memory offset below addresses something else; and
  -- RCX must mirror [0x2000], which is what makes a memory operand a peer of a register one.
  let badRbx := ss.filter (fun s => s.getReg .q .rbx != (0x2000 : BitVec 64))
  let badMirror := ss.filter (fun s => s.getReg .q .rcx != s.mem.readSize .q 0x2000)
  IO.println s!"n={ss.length} rbx_not_base={badRbx.length} rcx_ne_mem2000={badMirror.length}"
  for (s, i) in ss.zipIdx do
    let rcx   : BitVec 64 := s.getReg .q .rcx
    let rdx   : BitVec 64 := s.getReg .q .rdx
    let m2000 : BitVec 64 := s.mem.readSize .q 0x2000
    let m1ffd : BitVec 64 := s.mem.readSize .q 0x1ffd
    let m1fe2 : BitVec 64 := s.mem.readSize .q 0x1fe2
    IO.println s!"{i} rcx={rcx.toNat} rdx={rdx.toNat} m2000={m2000.toNat} m1ffd={m1ffd.toNat} m1fe2={m1fe2.toNat} mxcsr={s.mxcsr.toNat}"

#eval reachStreams
"""


def gen():
    os.makedirs(os.path.dirname(STREAMS_LEAN), exist_ok=True)
    with open(STREAMS_LEAN, "w", encoding="utf-8") as fh:
        fh.write(PASS_SRC)
    print("wrote %s" % os.path.relpath(STREAMS_LEAN, ROOT))
    print("now:  python3 scripts/lean_route.py lean run/reach_streams.lean > run/reach_streams.out")


# The source each landed vector of a form reads, by its instruction constructor in Tests/Vectors.lean.
#   .vcvtsi2  wide .rcx                  -> the 64-bit register, or its low 32 at wide=false
#   .vcvtsi2m {base := .rbx, disp := d}  -> the qword at 0x2000+d, low 32 at wide=false
# width is the SOURCE width: what the instruction actually reads out of the carrier.
STREAMS = {
    "p_cvtsi2sd":  (32, ["rcx", "rdx", "m2000", "m1ffd"]),   # cvtsi2sdl: %ecx x2, %edx, (%rbx), -0x3(%rbx)
    "p_cvtsi2ss":  (32, ["rcx", "m2000"]),                   # cvtsi2ssl: %ecx, (%rbx)
    "p_cvtsi2ssq": (64, ["rcx", "m1fe2"]),                   # cvtsi2ssq: %rcx, -0x1e(%rbx)
    "p_cvtsi2sdq": (64, ["rcx", "m1fe2"]),                   # cvtsi2sdq: %rcx, -0x1e(%rbx)
}
# The memory addresses `reach_streams.lean` emits, by the displacement off RBX (= 0x2000).
MEM_EMITTED = {0x2000: "m2000", 0x1ffd: "m1ffd", 0x1fe2: "m1fe2"}
VECTORS_LEAN = os.path.join(ROOT, "Tests", "Vectors.lean")
# (dbl, wide) -> the hwprobe form. dbl picks the destination format, wide the SOURCE width.
FORM_OF = {("true", "false"): "p_cvtsi2sd", ("true", "true"): "p_cvtsi2sdq",
           ("false", "false"): "p_cvtsi2ss", ("false", "true"): "p_cvtsi2ssq"}
RE_REG = re.compile(r"\.vcvtsi2 (true|false) (true|false) \.\w+ \.(\w+)")
RE_MEM = re.compile(r"\.vcvtsi2m (true|false) (true|false) \.\w+ \{ base := some \.rbx(?:, disp := (-?(?:0x)?[0-9a-fA-F]+))? \}")


def derive_streams(path=VECTORS_LEAN):
    """The stream map READ OFF the vectors' instruction constructors, not declared.

    ⛔ THE DECLARED TABLE IS KEPT AND CHECKED AGAINST THIS, rather than replaced by it: two
    sources that must agree catch a vector added without a thought for the reach table, which a
    derivation alone would silently absorb. A displacement this pass does not emit is REFUSED,
    never skipped — an unemitted source would read as a form with fewer vectors, and the table
    would OVER-PIN while looking complete."""
    text = open(path, encoding="utf-8").read()
    out, seen = {}, 0
    for dbl, wide, reg in RE_REG.findall(text):
        out.setdefault(FORM_OF[(dbl, wide)], set()).add(reg)
        seen += 1
    for dbl, wide, disp in RE_MEM.findall(text):
        d = int(disp, 0) if disp else 0
        addr = 0x2000 + d
        if addr not in MEM_EMITTED:
            raise SystemExit("\u26d4 reach_table: a vector reads [0x%x] (disp %s) and "
                             "reach_streams.lean does not emit it. Add it to PASS_SRC, or the table "
                             "over-pins that form." % (addr, disp))
        out.setdefault(FORM_OF[(dbl, wide)], set()).add(MEM_EMITTED[addr])
        seen += 1
    if seen == 0:
        raise SystemExit("\u26d4 reach_table: parsed ZERO cvtsi2 vectors from %s — the needle is "
                         "wrong or the file moved; REFUSING an empty population." % path)
    return out, seen

FORMS = {"b4": ["p_cvtsi2ss", "p_cvtsi2ssq", "p_cvtsi2sdq"], "sibling": ["p_cvtsi2sd"]}


def load_streams(path=STREAMS_OUT):
    """The pre-states, with the Lean pass's own controls enforced rather than reported."""
    if not os.path.exists(path):
        raise SystemExit("⛔ reach_table: %s is absent. Regenerate it:\n"
                         "   python3 hwprobe/reach_table.py --gen\n"
                         "   python3 scripts/lean_route.py lean run/reach_streams.lean > %s"
                         % (path, os.path.relpath(path, ROOT)))
    head, rows = None, []
    for line in open(path, encoding="utf-8"):
        h = re.match(r"n=(\d+) rbx_not_base=(\d+) rcx_ne_mem2000=(\d+)", line)
        if h:
            head = tuple(int(x) for x in h.groups())
            continue
        m = re.match(r"(\d+) rcx=(\d+) rdx=(\d+) m2000=(\d+) m1ffd=(\d+) m1fe2=(\d+) mxcsr=(\d+)", line)
        if m:
            k = [int(x) for x in m.groups()]
            rows.append(dict(zip(("i", "rcx", "rdx", "m2000", "m1ffd", "m1fe2", "mxcsr"), k)))
    if head is None:
        raise SystemExit("⛔ reach_table: %s carries no control header — it is not this pass's output." % path)
    n, badrbx, badmirror = head
    if badrbx or badmirror:
        raise SystemExit("⛔ reach_table: the Lean pass's own controls FAILED (rbx_not_base=%d "
                         "rcx_ne_mem2000=%d). Every memory offset below addresses something else; "
                         "REFUSING rather than scoring." % (badrbx, badmirror))
    if len(rows) != n or not rows:
        raise SystemExit("⛔ reach_table: header says n=%d, parsed %d rows — REFUSING an "
                         "unexplained population." % (n, len(rows)))
    return rows


def rc_of(mx):
    return (mx >> 13) & 3


def reached(rows, fn, key):
    """The (value, RC) pairs a form's vectors present, at the form's SOURCE width."""
    width, names = STREAMS[fn]
    mask = (1 << width) - 1
    return {key(s[nm] & mask, s["mxcsr"]) for s in rows for nm in names}


def multiplicity(rows, fn, key):
    """How MANY (pre-state, stream) pairs present each class — the margin, not the fact.

    ⛔⛔ SET MEMBERSHIP ANSWERS "is it covered?" AND THROWS AWAY "by how much?", AND THE MARGIN
    IS WHERE THE RISK IS. `mk_anchors.py` says PINNED "fails safe: a later vector that reaches a
    pinned class makes the pin redundant, never wrong." That is true and it is true in ONE
    DIRECTION. The other direction is unguarded: a `preStates` edit that stops reaching a CARRIED
    class leaves a MISSING pin, which is wrong, and PINNED is DECLARED so nothing recomputes it.
    Measured at B4: 20 of the 42 carried rows are reached by EXACTLY ONE pair — and the LANDED
    sibling `cvtsi2sd` has ZERO of 14, minimum multiplicity 2. So it is a property of B4's forms,
    not of the rule: an adversarial sweep is made of BIT PATTERNS, so a 32-bit source's 0, ±1 and
    INT_MIN are hit many times over while a 64-bit form's are hit once or not at all. All 20 are
    `q` forms; not one is `cvtsi2ss`.
    ⚠️ It counts (pre-state, stream) PAIRS, so a class reached twice by the SAME state through
    two streams scores 2 and is no more robust to a `preStates` edit than a singleton. 20 is a
    LOWER bound on the fragile set."""
    width, names = STREAMS[fn]
    mask = (1 << width) - 1
    out = {}
    for s in rows:
        for nm in names:
            k = key(s[nm] & mask, s["mxcsr"])
            out[k] = out.get(k, 0) + 1
    return out


def rows_of(fn):
    M.ROWS.clear()
    M.build()
    return [r for r in M.ROWS if r[1] == fn]


def x86isa_diffs():
    """The DIFF names from rows_on_x86isa.py's saved reading, through its own scorer."""
    import contextlib
    import io
    import rows_on_x86isa as X
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        X.score()
    text = buf.getvalue()
    if "disagreements" not in text:
        raise SystemExit("⛔ reach_table: rows_on_x86isa.score() printed no count line.")
    return {m.group(1) for m in re.finditer(r"^DIFF (\S+)", text, re.M)}


KEY_RC = lambda v, mx: (v, rc_of(mx))                 # noqa: E731  — D267 §2: "value class and RC"
KEY_FULL = lambda v, mx: (v, mx)                      # noqa: E731  — the MUTANT, for the control


def classify(rows, fn, diffs, key=KEY_RC):
    seen = reached(rows, fn, key)
    mult = multiplicity(rows, fn, key)
    width = STREAMS[fn][0]
    mask = (1 << width) - 1
    out = []
    for (n, f, mx, a, b, want, m_, fl) in rows_of(fn):
        hit = key(a & mask, mx) in seen
        if n in diffs:
            why = "x86isa differs"
        elif not hit:
            why = "no vector reaches"
        else:
            why = ""
        out.append((n, rc_of(mx), a & mask, hit, why, mult.get(key(a & mask, mx), 0)))
    return out


SIBLING_REACH_PINS = {"cvtsi2sd_one/zero", "cvtsi2sd_intmin/up"}


def selftest():
    rows = load_streams()
    ok = True
    got = {n for (n, _, _, hit, _, _) in classify(rows, "p_cvtsi2sd", set()) if not hit}
    print("control   cvtsi2sd unreached under value×RC : %s" % sorted(got))
    print("          D267 §2's landed answer           : %s" % sorted(SIBLING_REACH_PINS))
    if got != SIBLING_REACH_PINS:
        print("⛔ ARM 1 FAILED — the rule does not reproduce the sibling's landed pins.")
        ok = False
    else:
        print("✅ ARM 1 — the rule reproduces a pin set derived independently of this file.")
    mut = {n for (n, _, _, hit, _, _) in classify(rows, "p_cvtsi2sd", set(), key=KEY_FULL) if not hit}
    print("mutant    value×FULL MXCSR                  : %d unreached" % len(mut))
    if mut == SIBLING_REACH_PINS:
        print("⛔ ARM 2 FAILED — the MUTANT class also reproduces it, so ARM 1 proves nothing.")
        ok = False
    else:
        print("✅ ARM 2 — the mutant does NOT reproduce it (%d ≠ %d), so ARM 1 is load-bearing."
              % (len(mut), len(SIBLING_REACH_PINS)))
    derived, seen = derive_streams()
    declared = {k: set(v[1]) for k, v in STREAMS.items()}
    print("streams   parsed %d cvtsi2 vectors from Tests/Vectors.lean" % seen)
    if derived != declared:
        print("\u26d4 ARM 3 FAILED \u2014 the declared stream map disagrees with the vectors:")
        for k in sorted(set(derived) | set(declared)):
            if derived.get(k, set()) != declared.get(k, set()):
                print("     %-14s declared %s  derived %s"
                      % (k, sorted(declared.get(k, [])), sorted(derived.get(k, []))))
        ok = False
    else:
        print("\u2705 ARM 3 \u2014 the declared stream map equals the one read off the vectors' constructors.")
    print("selftest: %s" % ("PASS" if ok else "FAIL"))
    return 0 if ok else 1


def main():
    P.strict_flags(__file__)
    args = sys.argv[1:]
    if "--gen" in args:
        gen()
        return 0
    if "--selftest" in args:
        return selftest()
    form = "b4"
    if "--form" in args:
        form = args[args.index("--form") + 1]
    if form not in FORMS:
        raise SystemExit("⛔ reach_table: --form must be one of %s" % sorted(FORMS))
    rows = load_streams()
    diffs = x86isa_diffs()
    tsv = None
    if "--tsv" in args:
        tsv = os.path.join(ROOT, args[args.index("--tsv") + 1])
    lines, pinned, total = [], 0, 0
    for fn in FORMS[form]:
        tab = classify(rows, fn, diffs)
        total += len(tab)
        for (n, rc, a, hit, why, m) in tab:
            pinned += bool(why)
            lines.append("%s\t%s\t%d\t0x%x\t%s\t%d\t%s" % (fn, n, rc, a,
                         "reached" if hit else "unreached", m, why or "carried by vectors"))
        p = sum(1 for t in tab if t[4])
        thin = sum(1 for t in tab if t[3] and not t[4] and t[5] == 1)
        print("  %-14s %3d rows · pinned %3d · carried %3d · vectors mapped %d"
              % (fn, len(tab), p, len(tab) - p, len(STREAMS[fn][1]))
              + ("  \u26a0 %d carried row(s) reached by exactly ONE pair" % thin if thin else ""))
    print()
    print("TOTAL %d rows · PINNED %d · CARRIED %d" % (total, pinned, total - pinned))
    print("population: %d pre-states, controls clean; x86isa column from the saved reading" % len(rows))
    print("⚠️  the stream map is DECLARED and CHECKED against the vectors' constructors\n"
          "    (--selftest ARM 3); a displacement reach_streams.lean does not emit is REFUSED")
    if tsv:
        with open(tsv, "w", encoding="utf-8") as fh:
            fh.write("form\trow\trc\tsource\treach\treached_by\tdisposition\n")
            fh.write("\n".join(lines) + "\n")
        print("wrote %s (%d rows)" % (os.path.relpath(tsv, ROOT), len(lines)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
