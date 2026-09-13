#!/usr/bin/env python3
"""Derive the labelled tier's label counts and its cost fit from the source, so §6's figures have a rule.

WHY (D234).  The paper and `docs/P2-PROOF-INTERFACE.md` quote "2, 4, 5 and 7 labels" and "about 19 lines plus
7.5 to 8.1 per label". The line counts had a rule (`proof_lines.py`, D217); the LABEL counts never did. Counted
by the rule that gives 2, 5 and 7 — the entries of the invariant's `atTable`, one per instruction of the program —
`guarded` has THREE, and had three at the commit that recorded four. With 3, its per-label cost over a base of 19
is 10.3, outside the quoted range, and the range's "highest on the routine with the most labels" does not hold.

THE RULE.  For each sized theorem, the program and invariant are read from its `runP_code <program> (<Invariant>`
call. The label count is the number of `(0x…, ` entries in that invariant's `atTable [...]`. It is cross-checked
against the number of instructions in `def <program> : Program`, and the script REFUSES (exit 2) when the two
readings disagree or either is absent, because an empty or ambiguous count would read as a value.

THE FIT.  Ordinary least squares of lines on labels over the routines, printed with the residual of each, and the
line's value at twenty labels. Values are printed rounded as the paper quotes them; the unrounded fit is printed too.

Usage:  label_fit.py [--sha SHA] [--file Tests/Program.lean] [--field NAME] [--selftest]
        --field prints ONE value (labels:<theorem> | slope | intercept | at20 | max_residual | max_residual_theorem), for CLAIMS.tsv.
"""
import argparse, os, re, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import proof_lines  # noqa: E402  the line-count rule, reused rather than retyped

SIZED = ["prologue_preserves_caller_frame", "guarded_writes_only_in_buffer", "fill_safe", "memcpy_safe"]


def labels(text, theorem):
    """(label count, program, invariant) or raises ValueError naming what it looked for."""
    m = re.search(r"^theorem " + re.escape(theorem) + r"\b", text, re.M)
    if not m:
        raise ValueError(f"theorem {theorem} not found")
    call = re.compile(r"runP_code\s+(\w+)\s+\((\w+)").search(text, m.end())
    nxt = re.compile(r"^theorem ", re.M).search(text, m.end())
    if not call or (nxt and call.start() > nxt.start()):
        raise ValueError(f"{theorem}: no `runP_code <program> (<Invariant>` in its body")
    prog, inv = call.group(1), call.group(2)
    d = re.search(r"^def " + re.escape(inv) + r"\b.*?atTable\s*\[(.*?)\]", text, re.M | re.S)
    p = re.search(r"^def " + re.escape(prog) + r"\s*:\s*Program\s*:=\s*\{\s*code\s*:=\s*\[(.*?)\]\s*\}", text,
                  re.M | re.S)
    if not d or not p:
        raise ValueError(f"{theorem}: {'invariant ' + inv if not d else 'program ' + prog} not found")
    n_tab = len(re.findall(r"\(0x[0-9A-Fa-f]+,", d.group(1)))
    n_code = len(re.findall(r"\(0x[0-9A-Fa-f]+,", p.group(1)))
    if n_tab != n_code or n_tab == 0:
        raise ValueError(f"{theorem}: invariant {inv} has {n_tab} labels and program {prog} {n_code} instructions")
    return n_tab, prog, inv


def fit(points):
    xs, ys = [x for x, _ in points], [y for _, y in points]
    n = len(points)
    mx, my = sum(xs) / n, sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    slope = sum((x - mx) * (y - my) for x, y in points) / sxx
    return slope, my - slope * mx


def derive(text):
    rows = []
    for t in SIZED:
        k, prog, inv = labels(text, t)
        ln, _ = proof_lines.count(text, t)
        if ln is None:
            raise ValueError(f"{t}: proof_lines found no single theorem")
        rows.append((t, k, ln))
    slope, icpt = fit([(k, ln) for _, k, ln in rows])
    res = {t: ln - (icpt + slope * k) for t, k, ln in rows}
    return rows, slope, icpt, res


def read(sha, path):
    if sha:
        r = subprocess.run(["git", "show", f"{sha}:{path}"], capture_output=True, text=True)
        if r.returncode:
            raise ValueError(f"git show {sha}:{path} failed: {r.stderr.strip()}")
        return r.stdout
    return open(path, encoding="utf-8").read()


def selftest():
    bad = []

    def ok(c, w):
        print(("  v " if c else "  x ") + w)
        if not c:
            bad.append(w)

    src = ('def p : Program := { code := [\n  (0x1, ⟨a, 1⟩),\n  (0x2, ⟨b, 1⟩)] }\n'
           'def Inv (a : BitVec 64) (s : Cpu) : Prop :=\n  True ∧ atTable\n    [(0x1, A), (0x2, B)] a s\n'
           'theorem t (n : Nat) :\n    X :=\n  (runP_code p (Inv)\n    foo)\n')
    ok(labels(src, "t")[0] == 2, "control: a two-instruction program with a two-entry table counts 2")
    try:
        labels(src.replace("[(0x1, A), (0x2, B)]", "[(0x1, A), (0x2, B), (0x3, C)]"), "t")
        ok(False, "PLANT: a table that disagrees with its program REFUSES")
    except ValueError as e:
        ok("3 labels" in str(e) and "2 instructions" in str(e), "PLANT: a table that disagrees with its program REFUSES")
    try:
        labels(src, "absent")
        ok(False, "PLANT: an absent theorem REFUSES")
    except ValueError:
        ok(True, "PLANT: an absent theorem REFUSES")
    s, i = fit([(1, 3.0), (2, 5.0), (3, 7.0)])
    ok(abs(s - 2) < 1e-9 and abs(i - 1) < 1e-9, "the fit recovers y = 1 + 2x exactly")
    try:
        text = read(None, "Tests/Program.lean")
        rows, *_ = derive(text)
        ok(len(rows) == len(SIZED), "CONTROL: the real file derives a row for every sized theorem")
    except (OSError, ValueError) as e:
        ok(False, f"CONTROL: the real file derives ({e})")
    print("label_fit selftest: " + ("OK" if not bad else f"{len(bad)} FAILED"))
    return 1 if bad else 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--sha", default=None)
    ap.add_argument("--file", default="Tests/Program.lean")
    ap.add_argument("--field", default=None)
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args(argv)
    if a.selftest:
        return selftest()
    try:
        rows, slope, icpt, res = derive(read(a.sha, a.file))
    except ValueError as e:
        print(f"⛔ label_fit REFUSES: {e}", file=sys.stderr)
        return 2
    if a.field:
        by = {t: k for t, k, _ in rows}
        if a.field.startswith("labels:") and a.field[7:] in by:
            print(by[a.field[7:]])
        elif a.field == "slope":
            print(f"{slope:.1f}")
        elif a.field == "intercept":
            print(f"{icpt:.0f}")
        elif a.field == "at20":
            print(f"{icpt + 20 * slope:.0f}")
        elif a.field == "max_residual_theorem":
            print(max(res, key=lambda t: abs(res[t])))
        elif a.field == "max_residual":
            print(f"{max(abs(v) for v in res.values()):.0f}")
        else:
            print(f"⛔ unknown --field {a.field!r}", file=sys.stderr)
            return 2
        return 0
    for t, k, ln in rows:
        print(f"  {t:34s} labels {k}  lines {ln:3d}  per label over 19: {(ln - 19) / k:5.2f}  residual {res[t]:+6.2f}")
    print(f"  least squares: lines = {icpt:.2f} + {slope:.3f} x labels;  at twenty labels {icpt + 20 * slope:.1f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
