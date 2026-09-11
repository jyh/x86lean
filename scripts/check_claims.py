#!/usr/bin/env python3
"""Re-derive every published number in `docs/CLAIMS.tsv` and refuse on disagreement.

⛔⛔ WHY.  Measured 2026-09-11 (D202): all seven headline quantities in
`docs/TACAS-PRICING.md` §1 were CORRECT, and **not one stated its denominator**.
Re-deriving them with the obvious command gives 23,352 / 618 / 59 against the
published 18,824 / 616 / 55 — `lean_lines` excludes `Main.lean`'s 4,390 lines and
`design_documents` excludes `docs/seals/`.  I got three of seven wrong and began
writing up "the file is stale by 24%" before holding the method constant across
two shas, which returned identical counts and refuted staleness outright.
⇒ 🔑 ***A CORRECT NUMBER WITH AN UNSTATED DENOMINATOR FAILS REPRODUCTION EXACTLY
LIKE A WRONG ONE, AND FAILS WORSE*** — the author defends it, the reproducer
cannot see the disagreement, and both are right.

⭐ THE FORMAT IS THE FIX, AND THE GATE IS SECONDARY.  `CLAIM-2` named the
precondition: *"the first task is a format, not a gate"*, because the
denominators were PROSE and a gate over prose would have been a third copy of the
same mistake wearing a fix's clothes.  In `CLAIMS.tsv` the denominator **is** the
command, so a claim and its population cannot drift apart — there is no second
register to keep in step.  This script only runs what that file already says.

⛔ THERE IS NO `--update`, DELIBERATELY.  A gate that rewrites its expected values
from the thing it measures is not a gate, it is a recorder that always agrees.
When a number legitimately moves, a human edits the file and the diff carries the
reason.  [[feedback-widening-a-gate-needs-a-second-source]]

⚠️ IT RUNS COMMANDS FROM A DATA FILE, and that is a real property rather than an
oversight: the commands ARE the published derivations, and a reviewer must be able
to read them.  They run from the repo root, are written by this repository, and
travel in its history where any change to one is visible in a diff.

LANE.  Personal lane.  Reads this repository and runs git over it.
"""
import argparse, os, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TSV = os.path.join(ROOT, "docs", "CLAIMS.tsv")


def rows(path=TSV):
    out = []
    for ln, raw in enumerate(open(path, encoding="utf-8"), 1):
        line = raw.rstrip("\n")
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split("\t")
        if parts[0] == "id":
            continue
        if len(parts) < 4:
            out.append(("__MALFORMED__", ln, line, None))
            continue
        out.append((parts[0], parts[1], parts[2], parts[3]))
    return out


def derive(cmd, cwd=ROOT):
    r = subprocess.run(["bash", "-c", cmd], cwd=cwd, capture_output=True, text=True)
    return r.returncode, r.stdout.strip(), r.stderr.strip()


def check(path=TSV, cwd=ROOT, verbose=True):
    findings, n = [], 0
    rs = rows(path)
    if not rs:
        # ⛔ A GATE THAT FINDS NO SUBJECT MUST REFUSE. An empty manifest passing
        # silently is the "0 jobs means the file was refused" defect.
        return ["the manifest carries NO claims — a gate with no subject must refuse, not pass"], 0
    for cid, val, cmd, where in rs:
        if cid == "__MALFORMED__":
            findings.append(f"line {val}: malformed row (needs 4 tab-separated fields): {cmd[:60]!r}")
            continue
        n += 1
        rc, got, err = derive(cmd, cwd=cwd)
        if rc != 0:
            findings.append(f"{cid}: derivation FAILED rc={rc} ({err[:80]})")
        elif got == "":
            findings.append(f"{cid}: derivation printed NOTHING — an empty result is not a value")
        elif got != val:
            findings.append(f"{cid}: published {val!r} but derives {got!r}   [{where}]")
        elif verbose:
            print(f"  ok  {cid:22s} {val:>8s}   {where}")
    return findings, n


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--tsv", default=TSV)
    a = ap.parse_args(argv)
    if a.selftest:
        return selftest()
    findings, n = check(a.tsv)
    if findings:
        print(f"⛔ check_claims: FAIL — {len(findings)} finding(s) over {n} claim(s)")
        for f in findings:
            print("   " + f)
        return 1
    print(f"check_claims: CLEAN — {n} published claim(s) re-derived and matching")
    return 0


def selftest():
    """Plants in both directions, control first."""
    import tempfile
    red, arms = 0, []

    def arm(name, ok, detail=""):
        nonlocal red
        arms.append(name)
        print(("  v " if ok else "  x ") + name + ("" if ok else f"   {detail}"))
        if not ok:
            red += 1

    print("check_claims --selftest")
    base = open(TSV, encoding="utf-8").read()

    f, n = check(verbose=False)
    arm("control: the real manifest re-derives clean", not f and n == 7, f"{f} n={n}")

    def with_tsv(text):
        fh = tempfile.NamedTemporaryFile("w", suffix=".tsv", delete=False, encoding="utf-8")
        fh.write(text); fh.close()
        r = check(fh.name, verbose=False)
        os.unlink(fh.name)
        return r

    # a WRONG published value is caught
    bad = base.replace("lean_lines\t18824", "lean_lines\t99999", 1)
    f, _ = with_tsv(bad)
    arm("PLANT: a wrong published value is caught and BOTH numbers named",
        any("lean_lines" in x and "99999" in x and "18824" in x for x in f), str(f))

    # a derivation that FAILS is caught, not silently skipped
    bad = base.replace("git show HEAD:docs/DECISIONS.md | grep -c '^## D[0-9]'",
                       "git show HEAD:docs/NO-SUCH-FILE.md", 1)
    f, _ = with_tsv(bad)
    arm("PLANT: a failing derivation is a FINDING, never a skip",
        any("decisions" in x and "FAILED" in x for x in f), str(f))

    # a derivation that prints NOTHING is caught -- an empty result is the shape
    # a silently-broken pipeline produces, and it must not read as a value.
    bad = base.replace("git ls-tree -r HEAD --name-only | grep -cE '^X86/.*\\.lean$'",
                       "true", 1)
    f, _ = with_tsv(bad)
    arm("PLANT: an EMPTY derivation result is a finding, not a pass",
        any("lean_lib_modules" in x and "NOTHING" in x for x in f), str(f))

    # a malformed row is caught rather than skipped
    f, _ = with_tsv(base + "broken_row_without_tabs\n")
    arm("PLANT: a malformed row is a finding, not silently dropped",
        any("malformed" in x for x in f), str(f))

    # ⛔ AN EMPTY MANIFEST MUST REFUSE. A gate with no subject that returns 0 is
    # the "n/n over a subset" defect: complete over nothing.
    f, n0 = with_tsv("# only a comment\nid\tvalue\tcommand\tappears_in\n")
    arm("⭐ PLANT: an EMPTY manifest REFUSES (a gate with no subject must not pass)",
        bool(f) and n0 == 0, f"{f} n={n0}")

    print(f"\n  arms={len(arms)} red={red}")
    return 1 if red else 0


if __name__ == "__main__":
    sys.exit(main())
