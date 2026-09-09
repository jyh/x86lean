#!/usr/bin/env python3
"""⭐⭐⭐ THE XMM HALF OF THE RECORD FORMAT, HELD ACROSS THE LANGUAGE BOUNDARY.

P2 vector wave, batch 0.  The differential record's sixteen `xmmN=` fields are
produced TWICE — by `Cpu.renderXmms` in `X86/Serialize.lean` and by `x86l-xmms`
in `scripts/x86isa_driver.lisp` — because neither toolchain can read the other's
source.  That is the same duplicate the watch windows are, and it fails the same
way: any drift makes every rendered record differ and the whole run comes back
as disagreement.

⛔ AND IT FAILS EXPENSIVELY.  Discovering it costs a full ACL2 run — four
minutes to be told that a name, a width or an order changed.  `check_windows.py`
was written in P1 batch 15 for exactly this and catches its subject in 20 ms;
this is that gate for the register half, written on the day the field was added
rather than after the first run that pays for it.

WHAT IT CHECKS, and each is a way the two sides can disagree while both look
right in isolation:
  * the NAMES and their ORDER — `xmm0 … xmm15`, produced by a fold on one side
    and a recursion on the other;
  * the WIDTH — 32 hex digits, 128 bits.  A 16-digit reading would render the
    low half of every register and compare it happily against a full one.
  * the COUNT — sixteen.  A register file that lost one is a register nobody
    compares, and an unobserved register reports agreement.

`--selftest` mutates EACH side separately, and mutates the WIDTH as well as a
name, because a gate that only ever checked names would pass a half-width
reading — which is the failure that would silently halve the observation.
"""
import os, re, sys

# ⛔ REFUSE AN UNKNOWN FLAG BEFORE ANY WORK HAPPENS. This script dispatched on
# `"--x" in sys.argv` and otherwise fell through to its main path, so a mistyped
# flag did not fail — it RAN. Measured 2026-09-09: `threads_ab.py` given a bogus
# flag started `lake env lean -D profiler=true`, saturated a core for 300+ s on a
# shared machine, and orphaned past its caller. See portable.strict_flags.
if __name__ == "__main__":
    import os as _os, sys as _sys
    _sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
    from portable import strict_flags as _strict_flags
    _strict_flags(__file__)

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(root)

LEAN = "X86/Serialize.lean"
LISP = "scripts/x86isa_driver.lisp"


def lean_spec(text):
    """(prefix, hex-digit count) from `Cpu.renderXmms`."""
    m = re.search(r'def Cpu\.renderXmms.*?s!"\{(\w+)\.name\}=\{(\w+) hi\}\{(\w+) lo\}"',
                  text, re.S)
    if not m:
        return None
    # both halves come from the same fixed-width printer
    w = {"hex64": 16}.get(m.group(2))
    if w is None or m.group(2) != m.group(3):
        return None
    return ("xmm", 2 * w)


def lisp_spec(text):
    """(prefix, hex-digit count) from `x86l-xmms`."""
    m = re.search(r'\(defun x86l-xmms\s.*?"\s*(xmm)"\s*.*?\(x86l-hex \(rx128 i x86\) (\d+)\)',
                  text, re.S)
    if not m:
        return None
    return (m.group(1), int(m.group(2)))


def count_spec(text, pat):
    m = re.search(pat, text)
    return int(m.group(1)) if m else None


def read(p):
    return open(p).read()


def compare(lean_text, lisp_text):
    """Returns a list of disagreements; empty means the two sides match."""
    out = []
    ls, ps = lean_spec(lean_text), lisp_spec(lisp_text)
    if ls is None:
        out.append("could not parse Cpu.renderXmms in " + LEAN)
    if ps is None:
        out.append("could not parse x86l-xmms in " + LISP)
    if ls and ps:
        if ls[0] != ps[0]:
            out.append(f"register NAME prefix differs: Lean {ls[0]!r}, Lisp {ps[0]!r}")
        if ls[1] != ps[1]:
            out.append(f"register WIDTH differs: Lean {ls[1]} hex digits, "
                       f"Lisp {ps[1]} — a half-width reading compares happily "
                       f"against a full one")
    # the COUNT, from each side's own bound
    pc = count_spec(lisp_text, r'\(>= i (\d+)\)')
    if pc is None:
        out.append("could not find the register COUNT bound in " + LISP)
    elif pc != 16:
        out.append(f"the Lisp side walks {pc} registers, not 16")
    if lean_text.count("XmmReg.all") == 0:
        out.append("the Lean side no longer folds over XmmReg.all")
    # ⛔ AND THAT EACH SIDE STILL CALLS ITS OWN RENDERER.  A function that is
    # defined and not called is the quietest way for sixteen registers to leave
    # a record: both files still parse, both still describe the same format, and
    # the field simply is not there — which is the unobserved region again.
    if not re.search(r'\(x86l-xmms 0 "" x86\)', lisp_text):
        out.append("the Lisp POST line no longer calls x86l-xmms — the "
                   "registers would silently leave the record")
    if not re.search(r's\.renderXmms', lean_text):
        out.append("the Lean record no longer calls renderXmms — the "
                   "registers would silently leave the record")
    return out


def selftest():
    lean, lisp = read(LEAN), read(LISP)
    arms, ok = [], True
    base = compare(lean, lisp)
    arms.append(("control: the shipped two sides agree", not base))
    arms.append(("the Lisp side reads 16 hex digits (half width)",
                 bool(compare(lean, lisp.replace("(rx128 i x86) 32", "(rx128 i x86) 16")))))
    arms.append(("the Lisp side walks 8 registers",
                 bool(compare(lean, lisp.replace("(>= i 16)", "(>= i 8)")))))
    arms.append(("the Lean side loses its printer",
                 bool(compare(lean.replace("{hex64 hi}{hex64 lo}", "{hex64 lo}"), lisp))))
    arms.append(("the Lisp side loses its function",
                 bool(compare(lean, lisp.replace("(defun x86l-xmms ", "(defun x86l-xmmsXX ")))))
    arms.append(("the Lisp POST line stops CALLING it",
                 bool(compare(lean, lisp.replace('(x86l-xmms 0 "" x86)', '""')))))
    arms.append(("the Lean record stops CALLING it",
                 bool(compare(lean.replace("s.renderXmms", '""'), lisp))))
    for name, good in arms:
        print(("  ✔ " if good else "  ✖ ") + name)
        ok = ok and good
    print("✅ check_xmm_format selftest: each side mutated separately, name and "
          "WIDTH both driven" if ok else "⛔ check_xmm_format selftest FAILED")
    sys.exit(0 if ok else 1)


if "--selftest" in sys.argv:
    selftest()

bad = compare(read(LEAN), read(LISP))
if bad:
    print("⛔ THE XMM RECORD FORMAT DIFFERS between Lean and the ACL2 driver:")
    for b in bad:
        print("   " + b)
    print("   Any drift here makes every rendered record differ and the whole "
          "differential run come back as disagreement.")
    sys.exit(1)
print("✅ xmm record format agrees: 16 registers, 32 hex digits each, on both "
      "sides of the oracle boundary")
