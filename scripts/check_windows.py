#!/usr/bin/env python3
"""The watch windows are declared TWICE — once in Lean, once in Lisp — because
the two models are driven by different toolchains and neither can read the
other's source.  A duplicate born in agreement diverges on the next ordinary
append (docs/DECISIONS.md), and this batch's ordinary append was widening the
data window.

⚠️ HONESTLY: this drift is LOUD, not silent.  If the two disagree, every
rendered record differs and the differential run reports total disagreement.
What this gate buys is not detection — it is detecting it in 20 ms instead of
after a 4-minute ACL2 run, which is the difference between a check that gets run
before a commit and one that does not (see `make the probe cheap`).

Exits non-zero on drift.  `--selftest` proves it can FAIL, by parsing a mutated
copy of each side in turn: a comparison that has never been red is not evidence.
"""
import re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN = ROOT / "Tests" / "Vectors.lean"
LISP = ROOT / "scripts" / "x86isa_driver.lisp"


def lean_windows(text: str):
    """The `windows` definition's `{ base := 0x…, len := N }` records."""
    m = re.search(r"def windows\s*:\s*List Window\s*:=(.*?)\n\n", text, re.S)
    if not m:
        raise SystemExit("⛔ check_windows: no `def windows` in Tests/Vectors.lean")
    body = m.group(1)
    # strip comment lines so a hex address inside prose cannot be read as data
    body = "\n".join(l for l in body.splitlines() if not l.lstrip().startswith("--"))
    out = re.findall(r"base\s*:=\s*0x([0-9a-fA-F]+)\s*,\s*len\s*:=\s*(\d+)", body)
    return [(int(b, 16), int(n)) for b, n in out]


def lisp_windows(text: str):
    """⛔ THE FIRST VERSION OF THIS FUNCTION ENDED ITS CAPTURE AT THE FIRST `))`
    AND SILENTLY RETURNED ONLY THE FIRST WINDOW — the closing paren of the last
    pair was the same character as the closing paren of the list, so the last
    pair never matched.  A non-greedy regex cannot parse nested parentheses; the
    s-expression is scanned by balance instead."""
    i = text.find("*x86l-windows*")
    if i < 0:
        raise SystemExit("⛔ check_windows: no `*x86l-windows*` in the driver")
    j = text.find("'(", i)
    if j < 0:
        raise SystemExit("⛔ check_windows: `*x86l-windows*` has no quoted list")
    depth, k = 0, j + 1
    while k < len(text):
        if text[k] == "(":
            depth += 1
        elif text[k] == ")":
            depth -= 1
            if depth == 0:
                break
        k += 1
    else:
        raise SystemExit("⛔ check_windows: unbalanced `*x86l-windows*` list")
    out = re.findall(r"\(#x([0-9a-fA-F]+)\s*\.\s*(\d+)\)", text[j:k])
    return [(int(b, 16), int(n)) for b, n in out]


def compare(lean, lisp) -> bool:
    if lean == lisp:
        return True
    print("⛔ WATCH WINDOWS DIFFER between Lean and the ACL2 driver:")
    print(f"   Tests/Vectors.lean       : {[(hex(b), n) for b, n in lean]}")
    print(f"   scripts/x86isa_driver.lisp: {[(hex(b), n) for b, n in lisp]}")
    return False


def main() -> int:
    lean_src, lisp_src = LEAN.read_text(), LISP.read_text()
    lean, lisp = lean_windows(lean_src), lisp_windows(lisp_src)

    if not lean:
        print("⛔ check_windows: parsed ZERO windows from the Lean side.")
        return 1

    if "--selftest" in sys.argv:
        # ⭐ A POSITIVE CONTROL ON EACH SIDE IN TURN.  Mutating only one side at a
        # time is what says the comparison reads BOTH, rather than comparing one
        # side with itself.
        # ⛔ THE FIRST VERSION OF THIS SELFTEST MUTATED ONLY THE FIRST WINDOW,
        # AND IT PASSED WHILE `lisp_windows` WAS DROPPING THE SECOND ONE
        # ENTIRELY.  Both controls went red, both for the right-looking reason,
        # and the comparison underneath them was still reading half its subject.
        # ⇒ A positive control proves the gate reacts to the condition it
        # CREATES; it says nothing about the part of the subject the control
        # never touches.  So each side is now mutated in the LAST window as well
        # as the first, and the parse is length-checked against the other side.
        mutations = [
            ("LEAN first window",  lambda: lean_windows(lean_src.replace("len := 64", "len := 65", 1)), None),
            ("LEAN last window",   lambda: lean_windows(lean_src.replace("len := 48", "len := 47", 1)), None),
            ("LISP first window",  None, lambda: lisp_windows(lisp_src.replace("(#x1fe0 . 64)", "(#x1fe0 . 63)", 1))),
            ("LISP last window",   None, lambda: lisp_windows(lisp_src.replace("(#x7fe0 . 48)", "(#x7fe0 . 47)", 1))),
        ]
        for name, mk_lean, mk_lisp in mutations:
            l = mk_lean() if mk_lean else lean
            r = mk_lisp() if mk_lisp else lisp
            if compare(l, r):
                print(f"⛔ SELFTEST FAILED: a mutated {name} was accepted.")
                return 1
        # ⭐ AND THE DEFECT THAT SLIPPED PAST THE MUTATIONS, STATED DIRECTLY:
        # both sides must parse to the SAME NUMBER of windows, so a parser that
        # drops a trailing entry is caught even when every value it did read
        # agrees.
        if len(lean) != len(lisp):
            print(f"⛔ window COUNT differs: Lean {len(lean)}, Lisp {len(lisp)}")
            return 1
        print(f"✅ check_windows selftest: {len(mutations)} mutations, each caught; "
              f"both sides parse {len(lean)} windows.")

    if not compare(lean, lisp):
        return 1
    print(f"✅ watch windows agree: {[(hex(b), n) for b, n in lean]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
