#!/usr/bin/env python3
"""EVERY TEXT-MODE FILE OPEN IN A TRACKED SCRIPT NAMES ITS ENCODING (QUEUE PORT-1).

⛔ WHY. A text-mode `open()` with no `encoding=` reads and writes in the LOCALE's encoding: UTF-8 on
macOS and Linux, cp1252 on Windows. This repository's sources are full of non-ASCII, so on the second
machine a read fails. PORT-1 counted 193 such calls when it was filed on 2026-09-09 and 196 on
2026-09-14. The remedy shipped then was `PYTHONUTF8=1` plus a refusal (`portable.require_utf8_mode`),
which fixes every call at once but only in a process that sets it. PORT-1's release was "a mechanical
pass on ALL of them in one act, never partial". `--fix` is that pass, and this gate keeps it true.

WHAT IS AN OFFENDER, read from the syntax tree of every tracked `.py` and never by running it:
  * `open(...)`                 with no `encoding=` and a mode that is absent or a literal without "b"
  * `os.fdopen(...)`, `io.open(...)`   the same rule
  * `X.read_text(...)`, `X.write_text(...)`   with no `encoding=` (pathlib; the same locale default)
  * a mode that is NOT a literal          UNDECIDABLE: it may be binary at run time, where `encoding=`
                                          raises, so `--fix` refuses it and the gate reds it
  * a file that does not parse            never a silent skip

EXEMPT, AND PRINTED AS COUNTS (a tool with no concept of "not applicable" hides what it skipped):
  * a binary mode ("rb", "wb", ...), which takes no encoding
  * `subprocess` calls with `text=True` and no `encoding=`. They decode a CHILD's output in the locale's
    encoding: the same family, and a different question (what the child writes). NOT GATED, declared.
  * any other `X.open(...)` (tarfile, gzip, zipfile, webbrowser, ...): not a text file open.

⭐ `--fix` IS VERIFIED BY SYNTAX TREE, NOT BY INSPECTION. For each file it inserts `encoding="utf-8"`
before each fixable call's closing parenthesis, re-parses the result, and requires it to equal the
ORIGINAL tree with exactly that one keyword appended to exactly those calls. A file that fails this
is left untouched and named. On macOS and Linux the locale is already UTF-8, so the pass changes no
behaviour there: it makes the behaviour the same on a machine whose locale is not.

  check_encoding.py              the gate (rc 0 clean, rc 1 offenders)
  check_encoding.py --fix        the mechanical pass, then the gate
  check_encoding.py --selftest
"""
import ast
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

if __name__ == "__main__":
    sys.path.insert(0, HERE)
    from portable import strict_flags, utf8_stdio
    utf8_stdio()
    strict_flags(__file__)

KW = "encoding"
FIX_TEXT = 'encoding="utf-8"'


def _mode_node(call, pos):
    """The mode argument: positional index `pos` or the `mode=` keyword, else None."""
    for k in call.keywords:
        if k.arg == "mode":
            return k.value
    return call.args[pos] if len(call.args) > pos else None


def classify(call):
    """None (not a file open, or already explicit), or one of OFFENDER / UNDECIDABLE / EXEMPT binary /
    EXEMPT subprocess-text."""
    name = ast.unparse(call.func)
    if any(k.arg == KW for k in call.keywords):
        return None
    if any(k.arg is None for k in call.keywords) or any(isinstance(a, ast.Starred) for a in call.args):
        opener = name in ("open", "io.open", "os.fdopen")
        return "UNDECIDABLE" if opener else None
    if name in ("open", "io.open", "os.fdopen"):
        m = _mode_node(call, 1)
        if m is None:
            return "OFFENDER"
        if isinstance(m, ast.Constant) and isinstance(m.value, str):
            return "EXEMPT binary" if "b" in m.value else "OFFENDER"
        return "UNDECIDABLE"
    if isinstance(call.func, ast.Attribute) and call.func.attr in ("read_text", "write_text"):
        return "OFFENDER"
    if name.startswith("subprocess.") and any(
            k.arg in ("text", "universal_newlines") and isinstance(k.value, ast.Constant) and k.value.value is True
            for k in call.keywords):
        return "EXEMPT subprocess-text"
    return None


def scan(src, path="<src>"):
    """[(lineno, col_offset, class, text)] in source order."""
    try:
        tree = ast.parse(src, path)
    except SyntaxError as e:
        return [(e.lineno or 0, 0, "OFFENDER", f"does not parse: {e.msg}")]
    rows = []
    for n in ast.walk(tree):
        if isinstance(n, ast.Call):
            c = classify(n)
            if c:
                rows.append((n.lineno, n.col_offset, c, ast.unparse(n)[:90]))
    return sorted(rows)


def fix_source(src):
    """(new_src, n_fixed) with every OFFENDER call given `encoding="utf-8"`, VERIFIED by syntax tree.
    Raises ValueError, and changes nothing, if the rewrite is not exactly the intended tree."""
    tree = ast.parse(src)
    targets = [n for n in ast.walk(tree) if isinstance(n, ast.Call) and classify(n) == "OFFENDER"]
    if not targets:
        return src, 0
    b = src.encode("utf-8")
    starts = [0]
    for i, ch in enumerate(b):
        if ch == 0x0A:
            starts.append(i + 1)
    edits = []
    for n in targets:
        close = starts[n.end_lineno - 1] + n.end_col_offset - 1   # ast offsets are UTF-8 BYTES
        if b[close:close + 1] != b")":
            raise ValueError(f"line {n.lineno}: the call does not end in `)`")
        operands = [a for a in n.args] + [k.value for k in n.keywords]
        if not operands:                                          # `P.read_text()`
            edits.append((close, FIX_TEXT.encode("utf-8")))
            continue
        last = max(operands, key=lambda x: (x.end_lineno, x.end_col_offset))
        seg_from = starts[last.end_lineno - 1] + last.end_col_offset
        seg = b[seg_from:close].decode("utf-8")
        code = "\n".join(line.split("#", 1)[0] for line in seg.split("\n"))
        paren_line = starts[n.end_lineno - 1]
        if "," in code and n.end_lineno > last.end_lineno and not b[paren_line:close].strip():
            # a multi-line call with a trailing comma and `)` alone on its line: keep that style
            last_line = b[starts[last.end_lineno - 1]:]
            indent = last_line[:len(last_line) - len(last_line.lstrip(b" \t"))]
            edits.append((paren_line, indent + FIX_TEXT.encode("utf-8") + b",\n"))
            continue
        if "," in code:
            ins = FIX_TEXT if b[close - 1:close] in (b" ", b"\n", b"\t") else " " + FIX_TEXT
        else:
            ins = ", " + FIX_TEXT
        edits.append((close, ins.encode("utf-8")))
    for off, ins in sorted(edits, reverse=True):
        b = b[:off] + ins + b[off:]
    new = b.decode("utf-8")
    # the certificate: new tree == old tree with the keyword appended to exactly the targets
    want = ast.parse(src)
    pos = {(n.lineno, n.col_offset, n.end_lineno, n.end_col_offset) for n in targets}
    for n in ast.walk(want):
        if isinstance(n, ast.Call) and (n.lineno, n.col_offset, n.end_lineno, n.end_col_offset) in pos:
            n.keywords.append(ast.keyword(arg=KW, value=ast.Constant("utf-8")))
    try:
        got = ast.parse(new)
    except SyntaxError as e:
        raise ValueError(f"the rewrite does not parse: {e.msg} at line {e.lineno}")
    if ast.dump(got) != ast.dump(want):
        raise ValueError("the rewrite parses to a different tree than the original plus the keyword")
    return new, len(targets)


def population(root):
    r = subprocess.run(["git", "ls-files", "*.py"], cwd=root, capture_output=True, text=True, encoding="utf-8")
    if r.returncode != 0:
        raise SystemExit(f"⛔ check_encoding: `git ls-files` failed (rc {r.returncode}), so the population is "
                         f"unknown and a clean result would mean nothing:\n{r.stderr}")
    return [p for p in r.stdout.split("\n") if p]


def check(root=ROOT):
    files = population(root)
    rows = []
    for p in files:
        with open(os.path.join(root, p), encoding="utf-8") as fh:
            rows += [(p, *r) for r in scan(fh.read(), p)]
    return files, rows


def fix(root=ROOT):
    """(files changed, calls fixed, [(path, why)] refused)."""
    changed, total, refused = 0, 0, []
    for p in population(root):
        full = os.path.join(root, p)
        with open(full, encoding="utf-8") as fh:
            src = fh.read()
        try:
            new, n = fix_source(src)
        except (ValueError, SyntaxError) as e:
            refused.append((p, str(e)))
            continue
        if n:
            with open(full, "w", encoding="utf-8", newline="") as fh:
                fh.write(new)
            changed, total = changed + 1, total + n
    return changed, total, refused


def selftest():
    out = []

    def arm(name, ok):
        out.append((bool(ok), name))

    cls = lambda s: [r[2] for r in scan(s)]  # noqa: E731
    arm("control: no file open -> nothing", cls("import os\nprint(os.sep)\n") == [])
    arm("open(p) -> OFFENDER", cls("open(p)\n") == ["OFFENDER"])
    arm('open(p, "w") -> OFFENDER', cls('open(p, "w")\n') == ["OFFENDER"])
    arm('open(p, mode="a") -> OFFENDER', cls('open(p, mode="a")\n') == ["OFFENDER"])
    arm('open(p, "rb") -> EXEMPT binary', cls('open(p, "rb")\n') == ["EXEMPT binary"])
    arm('open(p, mode="wb") -> EXEMPT binary', cls('open(p, mode="wb")\n') == ["EXEMPT binary"])
    arm('open(p, "w", encoding="utf-8") -> nothing', cls('open(p, "w", encoding="utf-8")\n') == [])
    arm("open(p, m) with a variable mode -> UNDECIDABLE", cls("open(p, m)\n") == ["UNDECIDABLE"])
    arm("open(*a) -> UNDECIDABLE", cls("open(*a)\n") == ["UNDECIDABLE"])
    arm('os.fdopen(fd, "w") -> OFFENDER', cls('os.fdopen(fd, "w")\n') == ["OFFENDER"])
    arm("io.open(p) -> OFFENDER", cls("io.open(p)\n") == ["OFFENDER"])
    arm("P.read_text() -> OFFENDER", cls("P.read_text()\n") == ["OFFENDER"])
    arm('P.write_text(s, encoding="utf-8") -> nothing', cls('P.write_text(s, encoding="utf-8")\n') == [])
    arm("tarfile.open(p) -> nothing (not a text file open)", cls("tarfile.open(p)\n") == [])
    arm("subprocess.run(c, text=True) -> EXEMPT subprocess-text",
        cls("subprocess.run(c, text=True)\n") == ["EXEMPT subprocess-text"])
    arm('subprocess.run(c, text=True, encoding="utf-8") -> nothing',
        cls('subprocess.run(c, text=True, encoding="utf-8")\n') == [])
    arm("a file that does not parse -> OFFENDER, never a silent skip", cls("def (:\n") == ["OFFENDER"])
    arm("open() named in a STRING is not a call", cls('msg = "use open(p) here"\n') == [])

    # --fix, on the shapes a textual insertion gets wrong; each result must re-scan clean
    cases = {
        "plain": ('open(p)\n', 'open(p, encoding="utf-8")\n'),
        "mode": ('open(p, "w").write(x)\n', 'open(p, "w", encoding="utf-8").write(x)\n'),
        "trailing comma": ('open(\n    p,\n    "w",\n)\n', 'open(\n    p,\n    "w",\n    encoding="utf-8",\n)\n'),
        "trailing comma, indented paren": ('x = open(\n        p,\n    )\n', 'x = open(\n        p,\n        encoding="utf-8",\n    )\n'),
        "trailing comma, paren on the code line": ('open(p, "w",)\n', 'open(p, "w", encoding="utf-8")\n'),
        "comment before paren": ('open(p,\n     "r"  # c, with a comma\n     )\n',
                                 'open(p,\n     "r"  # c, with a comma\n     , encoding="utf-8")\n'),
        "parenthesised arg": ('open((p))\n', 'open((p), encoding="utf-8")\n'),
        "nested": ('open(open(q).read().strip())\n',
                   'open(open(q, encoding="utf-8").read().strip(), encoding="utf-8")\n'),
        "non-ASCII before the call": ('x = "⛔é"; open(p)\n', 'x = "⛔é"; open(p, encoding="utf-8")\n'),
        "read_text": ("P.read_text()\n", "P.read_text(encoding=\"utf-8\")\n"),
        "binary untouched": ('open(p, "rb")\n', 'open(p, "rb")\n'),
    }
    for name, (src, want) in cases.items():
        try:
            got, _ = fix_source(src)
        except ValueError as e:
            got = f"REFUSED {e}"
        arm(f"--fix {name}: exact text", got == want)
        arm(f"--fix {name}: re-scans with no OFFENDER", "OFFENDER" not in [r[2] for r in scan(got)]
            if not got.startswith("REFUSED") else False)
    try:
        fix_source("open(p, m)\n")
        arm("--fix leaves an UNDECIDABLE call alone", True)
    except ValueError:
        arm("--fix leaves an UNDECIDABLE call alone", False)
    arm("--fix of an UNDECIDABLE call changes nothing", fix_source("open(p, m)\n") == ("open(p, m)\n", 0))

    # END TO END over a throwaway git repository: population, counts, and --fix
    with tempfile.TemporaryDirectory(prefix="x86lean-checkenc-") as tmp:
        g = lambda *a: subprocess.run(["git", *a], cwd=tmp, capture_output=True, text=True, encoding="utf-8")  # noqa: E731
        g("init", "-q")
        with open(os.path.join(tmp, "bad.py"), "w", encoding="utf-8") as fh:
            fh.write('import subprocess\nopen("x", "w").write("é")\nsubprocess.run(["a"], text=True)\n')
        with open(os.path.join(tmp, "ok.py"), "w", encoding="utf-8") as fh:
            fh.write('open("x", "rb")\n')
        with open(os.path.join(tmp, "untracked.py"), "w", encoding="utf-8") as fh:
            fh.write("open('y')\n")
        g("add", "bad.py", "ok.py")
        files, rows = check(tmp)
        arm("e2e: population is the TRACKED files (2); the untracked plant is unread", len(files) == 2)
        arm("e2e: one OFFENDER, one binary and one subprocess exemption, counted",
            sorted(r[3] for r in rows) == ["EXEMPT binary", "EXEMPT subprocess-text", "OFFENDER"])
        changed, n, refused = fix(tmp)
        files, rows = check(tmp)
        arm("e2e: --fix changed 1 file, 1 call, refused none", (changed, n, refused) == (1, 1, []))
        arm("e2e: after --fix the gate is clean", not [r for r in rows if r[3] in ("OFFENDER", "UNDECIDABLE")])

    bad = [n for ok, n in out if not ok]
    for ok, n in out:
        print(f"  {'✔' if ok else '⛔'} {n}")
    print(f"check_encoding selftest: {len(out) - len(bad)}/{len(out)} arms")
    return 1 if bad else 0


def main():
    if "--selftest" in sys.argv:
        return selftest()
    if "--fix" in sys.argv:
        changed, n, refused = fix()
        print(f"check_encoding --fix: {n} call(s) given encoding=\"utf-8\" in {changed} file(s), each file "
              f"verified by syntax tree")
        for p, why in refused:
            print(f"  ⛔ REFUSED {p}: {why}")
        if refused:
            return 1
    files, rows = check()
    off = [r for r in rows if r[3] in ("OFFENDER", "UNDECIDABLE")]
    counts = {}
    for r in rows:
        counts[r[3]] = counts.get(r[3], 0) + 1
    for p, ln, _col, c, txt in off:
        print(f"  ⛔ {c:<11} {p}:{ln}  {txt}")
    print(f"check_encoding: {len(files)} tracked .py files read · {len(off)} offender(s) · exempt, not gated: "
          f"{counts.get('EXEMPT binary', 0)} binary open(s), {counts.get('EXEMPT subprocess-text', 0)} subprocess "
          f"text=True call(s) with no encoding= (a child's output, declared in the docstring)")
    if off:
        print('⛔ give each offender encoding="utf-8" (`check_encoding.py --fix` does it and verifies the tree); an '
              "UNDECIDABLE mode must be resolved by hand.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
