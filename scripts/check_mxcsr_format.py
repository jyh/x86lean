#!/usr/bin/env python3
"""⭐⭐⭐ THE MXCSR HALF OF THE RECORD FORMAT, HELD ACROSS THE LANGUAGE BOUNDARY (sub-group B0, D266).

The record's MXCSR keys are produced TWICE — by `Cpu.renderMxcsr` in `X86/Serialize.lean` and by
`x86l-mxcsr` in `scripts/x86isa_driver.lisp` — and the pre-state crosses the boundary TWICE the other
way: `acl2Case` in `Main.lean` emits `:mxcsr`, and the driver's `x86l-run-case` loads it. This is
`check_xmm_format.py`'s question for the register that joined the record in B0.

WHAT IT CHECKS, each a way the two sides can disagree while both look right in isolation:
  * the FLAG KEYS, their ORDER and their BIT: Lean's `mxcsrFlagNames` pairs each name with a bit, and
    the Lisp side prints the name at list position i from bit i. A pair whose bit is not its position
    would print the wrong bit under the right name, and a declared divergence keyed on that name
    (`mxcsr.ie`) would then excuse a different flag;
  * the COUNT: six sticky flags, bits 0–5, on both sides;
  * the CONTROL half: the same mask (`0xFFC0`, RC, the masks, DAZ, FZ) and the same hex width;
  * that each side CALLS its renderer — a renderer defined and not called leaves the keys out of the
    record, and an unobserved field reports agreement;
  * the INPUT half: the emitter writes `:mxcsr`, and the driver reads it and loads it on every case,
    with the power-up value when a case omits it. Without the load, a sticky flag raised by one case is
    the next case's pre-state (D265 §4).

`--selftest` mutates each side separately, and mutates a BIT as well as a name, because a gate that
only compared names would pass the one drift that moves a declared divergence onto another flag.
"""
import os
import re
import sys

# ⛔ REFUSE AN UNKNOWN FLAG BEFORE ANY WORK HAPPENS (see portable.strict_flags).
if __name__ == "__main__":
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from portable import strict_flags as _strict_flags
    _strict_flags(__file__)

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(root)

LEAN = "X86/Serialize.lean"
LISP = "scripts/x86isa_driver.lisp"
MAIN = "Main.lean"


def lean_flags(text):
    """[(name, bit)] from `mxcsrFlagNames`, or None."""
    m = re.search(r'def mxcsrFlagNames\s*:\s*List \(String × Nat\)\s*:=\s*\[(.*?)\]', text, re.S)
    if not m:
        return None
    return [(n, int(b)) for n, b in re.findall(r'\("(\w+)",\s*(\d+)\)', m.group(1))]


def lisp_flags(text):
    """[names] from `*x86l-mxcsr-flags*`, or None."""
    m = re.search(r'\(defconst \*x86l-mxcsr-flags\* \'\(([^)]*)\)\)', text)
    if not m:
        return None
    return re.findall(r'"(\w+)"', m.group(1))


def lean_ctl(text):
    m = re.search(r'mxcsr\.ctl=\{hexPad \(\(s\.mxcsr &&& (0x[0-9A-Fa-f]+)\)\.setWidth 64\) (\d+)\}', text)
    return (int(m.group(1), 16), int(m.group(2))) if m else None


def lisp_ctl(text):
    m = re.search(r'" mxcsr\.ctl=" \(x86l-hex \(logand v #x([0-9a-fA-F]+)\) (\d+)\)', text)
    return (int(m.group(1), 16), int(m.group(2))) if m else None


def read(p):
    return open(p, encoding="utf-8").read()


def compare(lean, lisp, main):
    out = []
    lf, pf = lean_flags(lean), lisp_flags(lisp)
    if lf is None:
        out.append("could not parse mxcsrFlagNames in " + LEAN)
    if pf is None:
        out.append("could not parse *x86l-mxcsr-flags* in " + LISP)
    if lf is not None:
        for i, (n, b) in enumerate(lf):
            if b != i:
                out.append(f"Lean prints {n!r} from bit {b} at position {i}; the Lisp side prints position i "
                           f"from bit i, so the two keys would name different bits")
        if [b for _, b in lf] != list(range(6)):
            out.append(f"Lean's flag bits are {[b for _, b in lf]}, not the six sticky bits 0..5")
    if lf is not None and pf is not None and [n for n, _ in lf] != pf:
        out.append(f"flag keys differ: Lean {[n for n, _ in lf]}, Lisp {pf}")
    pc = re.search(r'\(defun x86l-mxcsr-keys .*?\(>= i (\d+)\)', lisp, re.S)
    if not pc:
        out.append("could not find the flag COUNT bound in x86l-mxcsr-keys")
    elif int(pc.group(1)) != 6:
        out.append(f"the Lisp side prints {pc.group(1)} flags, not 6")
    if not re.search(r'\(if \(logbitp i v\) "1" "0"\)', lisp):
        out.append("the Lisp side no longer prints bit i as the i-th key")
    lc, pcx = lean_ctl(lean), lisp_ctl(lisp)
    if lc is None:
        out.append("could not parse the mxcsr.ctl field in " + LEAN)
    if pcx is None:
        out.append("could not parse the mxcsr.ctl field in " + LISP)
    if lc and pcx and lc != pcx:
        out.append(f"the control half differs: Lean mask {lc[0]:#x} width {lc[1]}, "
                   f"Lisp mask {pcx[0]:#x} width {pcx[1]}")
    if lc and lc[0] != 0xFFC0:
        out.append(f"the control mask is {lc[0]:#x}, not 0xFFC0 (bits 6..15)")
    if not re.search(r's\.renderMxcsr', lean):
        out.append("the Lean record no longer calls renderMxcsr — the keys would silently leave the record")
    if not re.search(r'\(x86l-mxcsr x86\)', lisp):
        out.append("the Lisp POST line no longer calls x86l-mxcsr — the keys would silently leave the record")
    if not re.search(r':mxcsr #x\{hexPad \(pre\.mxcsr\.setWidth 64\) 8\}', main):
        out.append("acl2Case no longer emits the pre-state's :mxcsr")
    if not re.search(r'\(mx\s+\(cadr \(assoc-keyword :mxcsr c\)\)\)', lisp):
        out.append("the driver no longer reads :mxcsr from the case")
    if not re.search(r'\(x86 \(!mxcsr \(if \(natp mx\) mx #x1f80\) x86\)\)', lisp):
        out.append("the driver no longer loads MXCSR on every case — a sticky flag would leak into the next case")
    return out


def selftest():
    lean, lisp, main = read(LEAN), read(LISP), read(MAIN)
    arms = [
        ("control: the shipped sides agree", not compare(lean, lisp, main)),
        ("Lean pairs a key with the wrong BIT",
         bool(compare(lean.replace('("de", 1), ("ze", 2)', '("de", 2), ("ze", 1)'), lisp, main))),
        ("the Lisp side swaps two NAMES",
         bool(compare(lean, lisp.replace('"ie" "de"', '"de" "ie"'), main))),
        ("the Lisp side prints five flags",
         bool(compare(lean, re.sub(r'\(>= i 6\)', '(>= i 5)', lisp), main))),
        ("the Lean control mask loses DAZ",
         bool(compare(lean.replace("&&& 0xFFC0)", "&&& 0xFF80)"), lisp, main))),
        ("the Lean record stops CALLING its renderer",
         bool(compare(lean.replace("s.renderMxcsr,", '"",'), lisp, main))),
        ("the Lisp POST line stops CALLING its renderer",
         bool(compare(lean, lisp.replace("(x86l-mxcsr x86)", '""'), main))),
        ("the emitter stops writing :mxcsr",
         bool(compare(lean, lisp, main.replace(":mxcsr #x{hexPad", ":mxcsrX #x{hexPad")))),
        ("the driver stops LOADING it",
         bool(compare(lean, lisp.replace("(x86 (!mxcsr (if (natp mx) mx #x1f80) x86))", ""), main))),
    ]
    ok = True
    for name, good in arms:
        print(("  ✔ " if good else "  ✖ ") + name)
        ok = ok and good
    print("✅ check_mxcsr_format selftest: each side mutated separately, a BIT as well as a name"
          if ok else "⛔ check_mxcsr_format selftest FAILED")
    sys.exit(0 if ok else 1)


if "--selftest" in sys.argv:
    selftest()

bad = compare(read(LEAN), read(LISP), read(MAIN))
if bad:
    print("⛔ THE MXCSR RECORD FORMAT DIFFERS between Lean and the ACL2 driver:")
    for b in bad:
        print("   " + b)
    sys.exit(1)
print("✅ mxcsr record format agrees: six flag keys at bits 0–5 and the 0xFFC0 control half on both sides; "
      "the pre-state is emitted and loaded on every case")
