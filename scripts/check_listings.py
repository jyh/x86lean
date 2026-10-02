#!/usr/bin/env python3
"""Check that every Lean listing printed in the paper is the source it claims to be.

WHY.  The paper shows excerpts of the semantics (the machine state, representative
instruction clauses).  A listing typed or pasted into a .tex file is a CLAIM about
the source: it stops being true the first time the source changes, and nothing would
say so.  This script makes each listing a DERIVED copy instead.  Each block is
introduced by a marker that names its file and its first and last lines by regex,
and the check regenerates the block from the working tree and fails on any byte
difference.

THE MARKER, one line, in the .tex:

    % LISTING <id> file=<path> from=<regex> to=<regex> [strip=doc] [elide=<a>..<b>|<label>]...
    \\begin{alltt}
    ...generated...
    \\end{alltt}
    % END LISTING <id>

  file=   a path relative to the repository root.
  from=   a regex; the listing starts at the FIRST source line matching it.
  to=     a regex; the listing ends at the first line AT OR AFTER the start matching it.
  strip=doc
          removes Lean doc comments (/-- ... -/ and /-! ... -/) inside the range.
          The paper's caption must say so.
  elide=a..b|label
          replaces the lines from the first match of regex a through the first match
          of regex b (after a) with one line "  -- ... <label> (N lines)", indented
          like the first elided line.  Every elision is marked and counted.
  Values may not contain spaces; write \\s in a regex for a space.
  Runs of blank lines in the result are collapsed to one, and trailing blank lines are dropped.
  Glyphs are mapped AFTER elision, so a glyph inside an elided span never needs a mapping.

WHY ANCHORS AND NOT LINE NUMBERS.  A listing should go red when ITS lines change,
not when a line is added above it.  A regex anchor that stops matching, or matches
in the wrong place, changes the generated block, and the check fails either way.

WHY THE TEX STAYS ASCII.  arXiv builds with pdflatex.  Every non-ASCII Lean glyph is
mapped to LaTeX through GLYPHS below; a glyph not in the table is an ERROR, never a
silent drop.

WHY --write IS NOT A RECORDER.  The repository's other gates refuse an --update mode,
because a gate that rewrites its expectations from what it measures always agrees.
Here the direction is the other way: the Lean source is the authority, and the .tex
block is the copy.  --write regenerates the copy from the authority; the check (no
flag) is what CI runs, and it fails whenever the copy and the authority differ.

WHAT IT ESTABLISHES.  Every block between markers equals its regenerated source.  It
does NOT establish that the prose around a listing still describes it, nor that a
listing outside any marker is current: an alltt block without a marker is invisible
to this gate.  The --selftest control counts markers, and the paper's own listings
are expected to be marked, every one.

Usage:
    python3 scripts/check_listings.py [--tex paper/x86lean-semantics.tex]
    python3 scripts/check_listings.py --write
    python3 scripts/check_listings.py --selftest
"""

import argparse
import os
import re
import shutil
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_TEX = os.path.join("paper", "x86lean-semantics.tex")

# Non-ASCII glyphs that appear in listed Lean source, and their LaTeX inside alltt.
GLYPHS = {
    "→": r"\(\to\)",
    "←": r"\(\leftarrow\)",
    "↔": r"\(\leftrightarrow\)",
    "∀": r"\(\forall\)",
    "∃": r"\(\exists\)",
    "λ": r"\(\lambda\)",
    "≤": r"\(\le\)",
    "≥": r"\(\ge\)",
    "≠": r"\(\ne\)",
    "∧": r"\(\wedge\)",
    "∨": r"\(\vee\)",
    "¬": r"\(\neg\)",
    "⟨": r"\(\langle\)",
    "⟩": r"\(\rangle\)",
    "×": r"\(\times\)",
    "ℕ": r"\(\mathbb{N}\)",
    "ℤ": r"\(\mathbb{Z}\)",
    "∘": r"\(\circ\)",
    "≫": r"\(\gg\)",
    "…": r"\ldots{}",
    "·": r"\(\cdot\)",
    "▸": r"\(\triangleright\)",
    "∈": r"\(\in\)",
    "∉": r"\(\notin\)",
    "⊕": r"\(\oplus\)",
    "↑": r"\(\uparrow\)",
    "↓": r"\(\downarrow\)",
    "₀": r"\(_0\)",
    "₁": r"\(_1\)",
    "₂": r"\(_2\)",
    "α": r"\(\alpha\)",
    "β": r"\(\beta\)",
    "σ": r"\(\sigma\)",
}

MARK_RE = re.compile(r"^% LISTING (\S+)((?: \S+=\S+)*)\s*$")
END_RE = re.compile(r"^% END LISTING (\S+)\s*$")


class ListingError(Exception):
    pass


def parse_marker(line):
    m = MARK_RE.match(line)
    if not m:
        return None
    lid = m.group(1)
    opts = {"elide": []}
    for kv in m.group(2).split():
        k, _, v = kv.partition("=")
        if k == "elide":
            rng, bar, label = v.partition("|")
            a, dots, b = rng.partition("..")
            if not (bar and dots and a and b and label):
                raise ListingError(f"listing {lid}: malformed elide={v!r} (want a..b|label)")
            opts["elide"].append((a, b, label.replace("_", " ")))
        elif k in ("file", "from", "to", "strip"):
            opts[k] = v
        else:
            raise ListingError(f"listing {lid}: unknown key {k!r}")
    for k in ("file", "from", "to"):
        if k not in opts:
            raise ListingError(f"listing {lid}: missing {k}=")
    if opts.get("strip") not in (None, "doc"):
        raise ListingError(f"listing {lid}: strip= must be 'doc'")
    return lid, opts


def first_match(lines, rx, start, lid, what):
    r = re.compile(rx)
    for i in range(start, len(lines)):
        if r.search(lines[i]):
            return i
    raise ListingError(f"listing {lid}: {what} regex {rx!r} matches no line at or after line {start + 1}")


def strip_doc(lines):
    out, depth = [], 0
    for ln in lines:
        s = ln
        if depth == 0 and re.match(r"^\s*/-[-!]", s):
            depth = 1
            s = s[s.index("/-") + 3:]
            if "-/" in s:
                depth = 0
            continue
        if depth:
            if "-/" in s:
                depth = 0
            continue
        out.append(ln)
    return out


def escape(line, lid):
    out = []
    for ch in line:
        if ch == "\\":
            out.append(r"\(\backslash\)")
        elif ch in "{}":
            out.append("\\" + ch)
        elif ord(ch) < 128:
            out.append(ch)
        elif ch in GLYPHS:
            out.append(GLYPHS[ch])
        else:
            raise ListingError(f"listing {lid}: glyph {ch!r} (U+{ord(ch):04X}) is not in GLYPHS; add its LaTeX")
    return "".join(out)


def generate(lid, opts, root):
    path = os.path.join(root, opts["file"])
    if not os.path.isfile(path):
        raise ListingError(f"listing {lid}: no such file {opts['file']}")
    src = open(path, encoding="utf-8").read().split("\n")
    a = first_match(src, opts["from"], 0, lid, "from")
    b = first_match(src, opts["to"], a, lid, "to")
    body = src[a:b + 1]
    if opts.get("strip") == "doc":
        body = strip_doc(body)
    for ea, eb, label in opts["elide"]:
        i = first_match(body, ea, 0, lid, "elide start")
        j = first_match(body, eb, i, lid, "elide end")
        indent = re.match(r"^\s*", body[i]).group(0)
        n = j - i + 1
        body = body[:i] + [f"{indent}-- ... {label} ({n} line{'s' if n != 1 else ''})"] + body[j + 1:]
    # A removed doc comment can leave blank lines on both sides of it: keep one.
    collapsed = []
    for l in body:
        if not l.strip() and collapsed and not collapsed[-1].strip():
            continue
        collapsed.append(l)
    body = collapsed
    while body and not body[-1].strip():
        body.pop()
    return ["\\begin{alltt}"] + [escape(l.rstrip(), lid) for l in body] + ["\\end{alltt}"]


def scan(tex_lines):
    """Yield (marker_index, end_index, lid, opts) for every marked block."""
    i, seen = 0, set()
    while i < len(tex_lines):
        if tex_lines[i].startswith("% LISTING "):
            parsed = parse_marker(tex_lines[i])
            if parsed is None:
                raise ListingError(f"line {i + 1}: malformed LISTING marker")
            lid, opts = parsed
            if lid in seen:
                raise ListingError(f"listing {lid}: id used twice")
            seen.add(lid)
            for j in range(i + 1, len(tex_lines)):
                m = END_RE.match(tex_lines[j])
                if m:
                    if m.group(1) != lid:
                        raise ListingError(f"listing {lid}: closed by END LISTING {m.group(1)}")
                    break
                if tex_lines[j].startswith("% LISTING "):
                    raise ListingError(f"listing {lid}: no END LISTING before the next marker")
            else:
                raise ListingError(f"listing {lid}: no END LISTING")
            yield i, j, lid, opts
            i = j
        i += 1


def run(tex_path, root, write):
    tex = open(tex_path, encoding="utf-8").read().split("\n")
    blocks = list(scan(tex))
    bad, out, last = [], [], 0
    for i, j, lid, opts in blocks:
        want = generate(lid, opts, root)
        have = tex[i + 1:j]
        if have != want:
            bad.append(lid)
        out += tex[last:i + 1] + want
        last = j
    out += tex[last:]
    if write:
        if bad:
            with open(tex_path, "w", encoding="utf-8") as f:
                f.write("\n".join(out))
        print(f"check_listings --write: {len(blocks)} listing(s); rewrote {len(bad)}: {', '.join(bad) or 'none'}")
        return 0
    if bad:
        print(f"check_listings: RED, {len(bad)} of {len(blocks)} listing(s) differ from their source: {', '.join(bad)}")
        print("  regenerate with: python3 scripts/check_listings.py --write   (then read the diff)")
        return 1
    print(f"check_listings: CLEAN, {len(blocks)} listing(s) equal their source. "
          "Not checked: prose describing a listing; any alltt block without a marker.")
    return 0


def selftest():
    d = tempfile.mkdtemp(prefix="check_listings_")
    try:
        os.makedirs(os.path.join(d, "X"))
        src = os.path.join(d, "X", "A.lean")
        tex = os.path.join(d, "p.tex")

        def put_src(s):
            open(src, "w", encoding="utf-8").write(s)

        base_src = ("def other := 1\n"
                    "/-- the record -/\n"
                    "structure R where\n"
                    "  /-- a doc\n  over two lines -/\n"
                    "  a : Nat := 0\n"
                    "  b : Nat → Nat := id\n"
                    "  c : Nat := 2\n"
                    "  d : Nat := 3\n"
                    "  e : {x : Nat // x ≤ 1}\n"
                    "def after := 2\n")
        marker = ("% LISTING r file=X/A.lean from=^structure\\sR to=^\\s+e\\s: strip=doc "
                  "elide=^\\s+c\\s:..^\\s+d\\s:|two_fields")
        base_tex = "intro\n" + marker + "\n% END LISTING r\noutro\n"

        def check(expect_rc, label, write=False):
            rc = run(tex, d, write)
            ok = (rc == expect_rc)
            print(f"  selftest {'ok ' if ok else 'BAD'} {label}: rc={rc} want {expect_rc}")
            return ok

        results = []
        # CONTROL FIRST: generate, then the check must be clean, and the block must
        # carry exactly what the rules say.
        put_src(base_src)
        open(tex, "w").write(base_tex)
        results.append(check(0, "control: --write on an empty block", write=True))
        results.append(check(0, "control: the regenerated block is clean"))
        body = open(tex).read()
        want_bits = ["structure R where", "  a : Nat := 0", r"b : Nat \(\to\) Nat",
                     "  -- ... two fields (2 lines)", r"e : \{x : Nat // x \(\le\) 1\}"]
        for w in want_bits:
            present = w in body
            print(f"  selftest {'ok ' if present else 'BAD'} control content: {w!r} present")
            results.append(present)
        absent = ("a doc" not in body) and ("def after" not in body) and ("the record" not in body)
        print(f"  selftest {'ok ' if absent else 'BAD'} control content: doc comments and out-of-range lines absent")
        results.append(absent)
        good_tex = body
        # RED: the source drifts inside the range.
        put_src(base_src.replace("a : Nat := 0", "a : Nat := 7"))
        results.append(check(1, "red: the source changed inside the range"))
        # GREEN: the source changes OUTSIDE the range.
        put_src(base_src.replace("def after := 2", "def after := 9"))
        results.append(check(0, "green: the source changed outside the range"))
        # RED: the anchor no longer matches.
        put_src(base_src.replace("structure R", "structure S"))
        try:
            run(tex, d, False)
            print("  selftest BAD red: missing anchor raised nothing")
            results.append(False)
        except ListingError as e:
            print(f"  selftest ok  red: missing anchor refused ({e})")
            results.append(True)
        # RED: a hand edit to the block.
        put_src(base_src)
        open(tex, "w").write(good_tex.replace("a : Nat := 0", "a : Nat := 0 "))
        results.append(check(1, "red: a hand-edited block"))
        # RED: an unmapped glyph.
        put_src(base_src.replace("a : Nat := 0", "a : Nat := 0 -- ☃"))
        open(tex, "w").write(good_tex)
        try:
            run(tex, d, False)
            print("  selftest BAD red: unmapped glyph raised nothing")
            results.append(False)
        except ListingError as e:
            print(f"  selftest ok  red: unmapped glyph refused ({e})")
            results.append(True)
        # GREEN: a glyph inside an ELIDED span needs no mapping (elision happens first).
        put_src(base_src.replace("  c : Nat := 2", "  c : Nat := 2 -- ☃"))
        open(tex, "w").write(good_tex)
        results.append(check(0, "green: a glyph inside an elided span"))
        # Blank runs: a doc comment between two blank lines leaves one blank line, not two.
        put_src(base_src.replace("  a : Nat := 0\n", "  a : Nat := 0\n\n  /-- gone -/\n\n"))
        rc = run(tex, d, True)
        txt = open(tex).read()
        one_blank = "  a : Nat := 0\n\n  b" in txt and "\n\n\n" not in txt.split("% LISTING")[1]
        print(f"  selftest {'ok ' if one_blank else 'BAD'} blank runs collapse to one line")
        results.append(one_blank)
        open(tex, "w").write(good_tex)
        # RED: an unclosed marker.
        put_src(base_src)
        open(tex, "w").write("intro\n" + marker + "\noutro\n")
        try:
            run(tex, d, False)
            print("  selftest BAD red: unclosed marker raised nothing")
            results.append(False)
        except ListingError as e:
            print(f"  selftest ok  red: unclosed marker refused ({e})")
            results.append(True)
        n_ok = sum(results)
        print(f"check_listings --selftest: {n_ok}/{len(results)} arms as expected")
        return 0 if n_ok == len(results) else 1
    finally:
        shutil.rmtree(d, ignore_errors=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--tex", default=DEFAULT_TEX)
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    try:
        return run(os.path.join(ROOT, a.tex), ROOT, a.write)
    except ListingError as e:
        print(f"check_listings: RED, {e}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
