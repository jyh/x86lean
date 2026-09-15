#!/usr/bin/env python3
"""NO SCRIPT IN THIS REPOSITORY STARTS A LEAN ELABORATION EXCEPT THROUGH `lean_route` (desk MB).

⛔ WHY A GATE AND NOT ONLY A RULE. The fleet's never-bare-lake rule (2026-08-06, after two OOM
incidents in one morning) was law for five weeks while 19 call sites in 14 scripts here called `lake` directly,
because the rule lived in files a script author does not read while writing a subprocess call.
The rule is now in CLAUDE.md; THIS is where the next author meets it — as a red naming the line.

WHAT IS AN OFFENDER, read from the SOURCE and never by running it (a census that invokes is not
read-only — `check_flag_strictness.py` records the incident):
  Python, from the syntax tree:
    * a list/tuple literal opening "lake", "build"           — `lake build …`
    * a list/tuple literal opening "lake", "env", "lean"     — `lake env lean FILE …`
    * a string (plain or f-string) opening `lake build` / `lake env lean`   — shell=True forms
    * a string naming `.elan/bin/lake`                         — the binary by path
  Shell, per code line (a line whose first non-blank character is `#` is a comment):
    * `lake build` or `lake env lean` in command position (line start, or after `exec`, `;`, `&&`,
      `||`, `|`, `(`, `{`, `then`, `do`, `$(`)

EXEMPT, AND PRINTED AS EXEMPT (a tool with no concept of "not applicable" hides what it skipped):
  * `lake env lean --version`         — elaborates nothing
  * `lake env <path to a binary> …`   — compiled code, not an elaboration; peaks measured
                                        2026-09-14 at 0.35 GB (axioms) and 1.19 GB (diff emit)
  * `scripts/lean_route.py`           — the door itself
  * `scripts/check_lean_route.py`     — this gate: its selftest fixtures ARE the offending shapes
  * `.github/workflows/*.yml`         — a CI runner has no wrapper and one job; not scanned

⚠️ WHAT THIS GATE DOES NOT CLAIM: a command assembled at run time from pieces that are not
literals (`[LAKE] + sub`) is invisible to it. Nothing here does that today; the population it
reads is every tracked `.py` and `.sh` in the repository, and the count is printed.
"""
import ast
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
DOOR = "scripts/lean_route.py"
# the door, and this gate (whose selftest fixtures are the offending shapes, as strings)
BY_NAME = (DOOR, "scripts/check_lean_route.py")

if __name__ == "__main__":
    sys.path.insert(0, HERE)
    from portable import strict_flags, utf8_stdio
    utf8_stdio()
    strict_flags(__file__)

_SH_CMD = re.compile(r"(?:^|[;&|({]|\$\(|\bexec\s|\bthen\s|\bdo\s)\s*lake\s+(build\b|env\s+(\S+))")
_STR_CMD = re.compile(r"^\s*lake\s+(build\b|env\s+(\S+))")


def _classify_env(target, rest=""):
    if target == "lean":
        return "EXEMPT version probe" if rest.strip().startswith("--version") else "OFFENDER"
    return "EXEMPT binary"


def scan_python(src, path):
    """[(line, class, text)] for one Python source."""
    out = []
    try:
        tree = ast.parse(src, filename=path)
    except SyntaxError as e:
        return [(e.lineno or 0, "OFFENDER", f"unparseable, so unscanned: {e.msg}")]
    for node in ast.walk(tree):
        if isinstance(node, (ast.List, ast.Tuple)):
            lits = []
            for el in node.elts:
                if isinstance(el, ast.Constant) and isinstance(el.value, str):
                    lits.append(el.value)
                else:
                    break
            if lits[:1] == ["lake"] and len(lits) >= 2:
                if lits[1] == "build":
                    out.append((node.lineno, "OFFENDER", " ".join(lits)))
                elif lits[1] == "env" and len(lits) >= 3:
                    cls = _classify_env(lits[2], " ".join(lits[3:]))
                    out.append((node.lineno, cls, " ".join(lits)))
        elif isinstance(node, ast.JoinedStr):
            head = node.values[0] if node.values else None
            if isinstance(head, ast.Constant) and isinstance(head.value, str):
                m = _STR_CMD.match(head.value)
                if m:
                    cls = "OFFENDER" if m.group(1) == "build" else _classify_env(
                        m.group(2), head.value[m.end():])
                    out.append((node.lineno, cls, head.value.strip()[:80]))
        elif isinstance(node, ast.Constant) and isinstance(node.value, str):
            m = _STR_CMD.match(node.value)
            if m:
                cls = "OFFENDER" if m.group(1) == "build" else _classify_env(
                    m.group(2), node.value[m.end():])
                out.append((node.lineno, cls, node.value.strip()[:80]))
            elif ".elan/bin/lake" in node.value:
                out.append((node.lineno, "OFFENDER", node.value.strip()[:80]))
    # f-string heads are also visited as plain Constants by ast.walk: keep one row per (line, text)
    seen, uniq = set(), []
    for row in sorted(out):
        if (row[0], row[2]) not in seen:
            seen.add((row[0], row[2]))
            uniq.append(row)
    return uniq


def scan_shell(src):
    out = []
    for i, ln in enumerate(src.split("\n"), 1):
        if ln.lstrip().startswith("#"):
            continue
        for m in _SH_CMD.finditer(ln):
            cls = "OFFENDER" if m.group(1) == "build" else _classify_env(
                m.group(2), ln[m.end():])
            out.append((i, cls, ln.strip()[:100]))
    return out


def population(root=ROOT):
    r = subprocess.run(["git", "ls-files", "*.py", "*.sh"], cwd=root, capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"⛔ check_lean_route: `git ls-files` failed (rc {r.returncode}), so the "
                         f"population is unknown and a clean result would mean nothing:\n{r.stderr}")
    return [p for p in r.stdout.split("\n") if p]


def check(root=ROOT):
    files = population(root)
    rows = []
    for p in files:
        if p in BY_NAME:
            continue
        src = open(os.path.join(root, p), encoding="utf-8", errors="replace").read()
        found = scan_python(src, p) if p.endswith(".py") else scan_shell(src)
        rows += [(p, *r) for r in found]
    return files, rows


def selftest() -> int:
    out = []

    def arm(name, ok):
        out.append((bool(ok), name))

    def classes(rows):
        return [r[1] for r in rows]

    py = lambda s: classes(scan_python(s, "t.py"))  # noqa: E731
    sh = lambda s: classes(scan_shell(s))            # noqa: E731
    arm("control: a script with no lake call -> nothing", py("import os\nprint(1)\n") == [] and sh("echo hi\n") == [])
    arm("py list `lake build` -> OFFENDER", py('subprocess.run(["lake", "build", "X86"])\n') == ["OFFENDER"])
    arm("py list `lake env lean FILE` -> OFFENDER", py('r = ["lake", "env", "lean", f]\n') == ["OFFENDER"])
    arm("py list `lake env lean` with no file (threads_ab's shape) -> OFFENDER",
        py('cmd = ["lake", "env", "lean"]\n') == ["OFFENDER"])
    arm("py tuple form -> OFFENDER", py('c = ("lake", "build")\n') == ["OFFENDER"])
    arm("py shell string `lake build x` -> OFFENDER", py('run("lake build x86lean-diff")\n') == ["OFFENDER"])
    arm("py f-string `lake env lean {f}` -> OFFENDER (one row, not two)",
        py('run(f"lake env lean {f} -D a=b")\n') == ["OFFENDER"])
    arm("py `~/.elan/bin/lake` by path -> OFFENDER", py('p = os.path.expanduser("~/.elan/bin/lake")\n') == ["OFFENDER"])
    arm("py `lake env lean --version` -> EXEMPT",
        py('subprocess.run(["lake", "env", "lean", "--version"])\n') == ["EXEMPT version probe"])
    arm("py f-string `lake env .lake/build/bin/x …` -> EXEMPT binary",
        py('run(f"lake env .lake/build/bin/x86lean-diff {m}")\n') == ["EXEMPT binary"])
    arm("py prose naming `lake build` mid-string is not a command",
        py('raise SystemExit(f"⛔ `lake build` failed in {wt}")\n# lake build X\n') == [])
    arm("sh `lake build X >/dev/null` -> OFFENDER", sh("lake build X86 x86lean-axioms >/dev/null\n") == ["OFFENDER"])
    arm("sh `exec lake env lean` -> OFFENDER", sh('exec lake env lean "$F"\n') == ["OFFENDER"])
    arm("sh inside a function body -> OFFENDER", sh('run() { lake env lean "$1" 2>&1; }\n') == ["OFFENDER"])
    arm("sh `exec lake env <binary>` -> EXEMPT binary",
        sh("exec lake env .lake/build/bin/x86lean-axioms $MODS\n") == ["EXEMPT binary"])
    arm("sh comment line -> nothing", sh("# lake build X86 is what used to run here\n") == [])
    arm("sh a routed call -> nothing", sh("python3 scripts/lean_route.py build X86\n") == [])
    arm("py unparseable -> OFFENDER, never a silent skip", py("def (:\n")[:1] == ["OFFENDER"])

    # END TO END over a throwaway git repository: population, the door's exemption, and the count
    with tempfile.TemporaryDirectory(prefix="x86lean-checkroute-") as tmp:
        g = lambda *a: subprocess.run(["git", *a], cwd=tmp, capture_output=True, text=True)  # noqa: E731
        g("init", "-q")
        os.makedirs(os.path.join(tmp, "scripts"))
        open(os.path.join(tmp, DOOR), "w", encoding="utf-8").write('X = ["lake", "build"]\n')
        open(os.path.join(tmp, "scripts", "ok.sh"), "w", encoding="utf-8").write("python3 scripts/lean_route.py build X\n")
        open(os.path.join(tmp, "scripts", "bad.py"), "w", encoding="utf-8").write('import subprocess\nsubprocess.run(["lake", "build"])\n')
        open(os.path.join(tmp, "untracked.sh"), "w", encoding="utf-8").write("lake build\n")
        g("add", DOOR, "scripts/ok.sh", "scripts/bad.py")
        files, rows = check(tmp)
        arm("e2e: population is the TRACKED files (3), the untracked plant unread", len(files) == 3)
        arm("e2e: the door is exempt and the plant is named",
            [(r[0], r[2]) for r in rows] == [("scripts/bad.py", "OFFENDER")])

    bad = [n for ok, n in out if not ok]
    for ok, n in out:
        print(f"  {'✔' if ok else '⛔'} {n}")
    print(f"check_lean_route selftest: {len(out) - len(bad)}/{len(out)} arms")
    return 1 if bad else 0


def main():
    if "--selftest" in sys.argv:
        return selftest()
    files, rows = check()
    off = [r for r in rows if r[2] == "OFFENDER"]
    ex = [r for r in rows if r[2] != "OFFENDER"]
    for p, ln, cls, txt in ex:
        print(f"  ·  {cls:<22} {p}:{ln}  {txt}")
    for p, ln, cls, txt in off:
        print(f"  ⛔ {cls:<22} {p}:{ln}  {txt}")
    print(f"check_lean_route: {len(files)} tracked .py/.sh files read · exempt by name, unread: "
          f"{', '.join(p for p in BY_NAME if p in files) or '(neither is tracked)'} · {len(ex)} exempt "
          f"call(s) printed above · {len(off)} offender(s)")
    if off:
        print("⛔ route each offender through scripts/lean_route.py (the fleet lock on a shared seat, bare "
              "lake on a CI runner, and the route printed either way).")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
