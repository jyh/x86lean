#!/usr/bin/env python3
"""⭐⭐ THE MMX HALF OF THE RECORD FORMAT, HELD ACROSS THE LANGUAGE BOUNDARY (row 77 step b, D401).

The record's MMX keys are produced TWICE — by `Cpu.renderMmx` in `X86/Serialize.lean` and by
`x86l-mmxs` in `scripts/x86isa_driver.lisp` — and the pre-state crosses the other way: `acl2Case`
in `Main.lean` emits `:mmxs`, `:fptag` and `:fptop`, and the driver's `x86l-run-case` loads all three
on every case. This is `check_mxcsr_format.py`'s question for the channel that joined the record in D401.

WHAT IT CHECKS, each a way the two sides can disagree while both look right in isolation:
  * the REGISTER COUNT (8) and the per-register WIDTH (16 hex digits) on both sides — a half-width
    reading silently halves the observation;
  * the x87 alias keys: `fptag=` at 4 hex digits from the tag word, and `fptop=` at 1 from TOP;
  * that each side CALLS its renderer — a renderer defined and not called leaves the keys out of the
    record, and an unobserved field reports agreement;
  * the INPUT half: the emitter writes the three keywords, and the driver reads them and loads them on
    EVERY case with the Lean defaults when a case omits them (x86isa's tag starts at 0 and
    `init-x86-state-64` resets none of them, so a value would otherwise leak into the next case);
  * the leak check compares the field (`a.mmx == b.mmx`).

`--selftest` mutates each side separately, and mutates a WIDTH as well as a name.
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
BASIC = "X86/Basic.lean"


def read(p):
    return open(p, encoding="utf-8").read()


def compare(lean, lisp, main, basic):
    out = []
    regs = re.search(r'def Mmxs\.regs \(m : Mmxs\) : List \(BitVec 64\) :=\s*\[([^\]]*)\]', basic)
    if not regs:
        out.append("could not parse Mmxs.regs in " + BASIC)
    else:
        names = [x.strip() for x in regs.group(1).split(",")]
        want = [f"m.mm{i}" for i in range(8)]
        if names != want:
            out.append(f"Mmxs.regs is {names}, not mm0..mm7 in order")
    if not re.search(r's!"mm\{i\}=\{hex64 v\}"', lean):
        out.append("Lean no longer prints mmN= at 16 hex digits (hex64) from Mmxs.regs")
    if not re.search(r's!"fptag=\{hexPad \(s\.mmx\.fpTag\.setWidth 64\) 4\}"', lean):
        out.append("Lean no longer prints fptag= at 4 hex digits")
    if not re.search(r's!"fptop=\{hexPad \(s\.mmx\.fpTop\.setWidth 64\) 1\}"', lean):
        out.append("Lean no longer prints fptop= at 1 hex digit")
    pc = re.search(r'\(defun x86l-mmxs .*?\(>= i (\d+)\)', lisp, re.S)
    if not pc:
        out.append("could not find the register COUNT bound in x86l-mmxs")
    elif int(pc.group(1)) != 8:
        out.append(f"the Lisp side prints {pc.group(1)} MMX registers, not 8")
    if not re.search(r'" mm"\s*\(coerce \(explode-atom i 10\) \'string\) "="\s*\(x86l-hex \(mmx i x86\) 16\)', lisp):
        out.append("the Lisp side no longer prints mmN= at 16 hex digits from (mmx i x86)")
    if not re.search(r'" fptag=" \(x86l-hex \(fp-tag x86\) 4\)', lisp):
        out.append("the Lisp side no longer prints fptag= at 4 hex digits")
    if not re.search(r'" fptop=" \(x86l-hex \(fp-statusBits->top \(fp-status x86\)\) 1\)', lisp):
        out.append("the Lisp side no longer prints fptop= at 1 hex digit")
    if not re.search(r's\.renderMxcsr, s\.renderMmx,', lean):
        out.append("the Lean record no longer calls renderMmx — the keys would silently leave the record")
    if not re.search(r'\(x86l-mmxs 0 "" x86\)', lisp):
        out.append("the Lisp POST line no longer calls x86l-mmxs — the keys would silently leave the record")
    if not re.search(r'&& a\.mmx == b\.mmx', lean):
        out.append("undefinedLeakedBy no longer compares the MMX field")
    if not re.search(r':mmxs \{mmxsToLisp pre\} :fptag #x\{hexPad \(pre\.mmx\.fpTag\.setWidth 64\) 4\} '
                     r':fptop \{pre\.mmx\.fpTop\.toNat\}', main):
        out.append("acl2Case no longer emits the pre-state's :mmxs, :fptag and :fptop")
    for kw, var in (("mmxs", "mmxs"), ("fptag", "ftag"), ("fptop", "ftop")):
        if not re.search(r'\(' + var + r'\s+\(cadr \(assoc-keyword :' + kw + r' c\)\)\)', lisp):
            out.append(f"the driver no longer reads :{kw} from the case")
    if not re.search(r'\(x86 \(x86l-set-mmxs ', lisp):
        out.append("the driver no longer loads the MMX registers on every case")
    if not re.search(r'\(x86 \(!fp-tag \(if \(natp ftag\) ftag #xffff\) x86\)\)', lisp):
        out.append("the driver no longer loads the tag word on every case (default #xffff, the Lean default)")
    if not re.search(r'\(x86 \(!fp-status \(if \(and \(natp ftop\) \(< ftop 8\)\) \(ash ftop 11\) 0\) x86\)\)', lisp):
        out.append("the driver no longer loads the status word (TOP at bits 13:11) on every case")
    if not re.search(r'fpTag : BitVec 16 := 0xFFFF', basic):
        out.append("the Lean tag default is no longer 0xFFFF, the driver's default for an omitted :fptag")
    return out


def selftest():
    lean, lisp, main, basic = read(LEAN), read(LISP), read(MAIN), read(BASIC)
    arms = [
        ("control: the shipped sides agree", not compare(lean, lisp, main, basic)),
        ("Mmxs.regs swaps two registers",
         bool(compare(lean, lisp, main, basic.replace("[m.mm0, m.mm1,", "[m.mm1, m.mm0,")))),
        ("Lean prints a register at half WIDTH",
         bool(compare(lean.replace('s!"mm{i}={hex64 v}"', 's!"mm{i}={hexPad v 8}"'), lisp, main, basic))),
        ("the Lisp side prints a register at half WIDTH",
         bool(compare(lean, lisp.replace("(x86l-hex (mmx i x86) 16)", "(x86l-hex (mmx i x86) 8)"), main, basic))),
        ("the Lisp side prints seven registers",
         bool(compare(lean, re.sub(r'\(>= i 8\)', '(>= i 7)', lisp), main, basic))),
        ("the Lisp side prints the tag at 2 digits (the abridged width)",
         bool(compare(lean, lisp.replace("(x86l-hex (fp-tag x86) 4)", "(x86l-hex (fp-tag x86) 2)"), main, basic))),
        ("the Lean record stops CALLING its renderer",
         bool(compare(lean.replace("s.renderMxcsr, s.renderMmx,", "s.renderMxcsr,"), lisp, main, basic))),
        ("the Lisp POST line stops CALLING its renderer",
         bool(compare(lean, lisp.replace('(x86l-mmxs 0 "" x86)', '""'), main, basic))),
        ("the leak check stops comparing the field",
         bool(compare(lean.replace("    && a.mmx == b.mmx\n", ""), lisp, main, basic))),
        ("the emitter stops writing :fptop",
         bool(compare(lean, lisp, main.replace(":fptop {pre", ":fptopX {pre"), basic))),
        ("the driver stops LOADING the tag word",
         bool(compare(lean, lisp.replace("(x86 (!fp-tag (if (natp ftag) ftag #xffff) x86))", ""), main, basic))),
        ("the driver's tag default drifts from Lean's",
         bool(compare(lean, lisp.replace("ftag #xffff)", "ftag 0)"), main, basic))),
    ]
    ok = True
    for name, good in arms:
        print(("  ✔ " if good else "  ✖ ") + name)
        ok = ok and good
    print("✅ check_mmx_format selftest: each side mutated separately, a WIDTH as well as a name"
          if ok else "⛔ check_mmx_format selftest FAILED")
    sys.exit(0 if ok else 1)


if "--selftest" in sys.argv:
    selftest()

bad = compare(read(LEAN), read(LISP), read(MAIN), read(BASIC))
if bad:
    print("⛔ THE MMX RECORD FORMAT DIFFERS between Lean and the ACL2 driver:")
    for b in bad:
        print("   " + b)
    sys.exit(1)
print("✅ mmx record format agrees: eight mmN= keys at 16 hex digits, fptag= at 4 and fptop= at 1 on both "
      "sides; the pre-state is emitted and loaded on every case")
