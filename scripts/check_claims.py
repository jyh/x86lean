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

⚖️ WHAT ITS ARMS ESTABLISH (row `LB`, declared not repaired):  **REACHABILITY ONLY, and one
   structural guarantee.** The plants show a wrong value, a failing derivation, an empty
   result, a malformed row and an empty manifest are all caught. **RATE is not established**
   for the population it cannot see: a published number that is in NO row of `CLAIMS.tsv` is
   invisible to this gate at any frequency. ⇒ The guarantee is *every number IN the manifest
   re-derives*; it is NOT *every number the repository publishes is in the manifest*.
   ⇒ 🔑 ***AN INSTRUMENT'S SILENCE IS NOT A MEASUREMENT OF THE THING IT WAS SILENT
     ABOUT*** (row `LB`, 2026-09-11, three seats independently). The remedy the row
     prescribes is DECLARATION, not more arms — most such arms cannot be strengthened,
     and the cost is that a reachability arm's silence gets read as coverage.

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
        if len(parts) < 5:
            # the line TEXT goes in the `cmd` slot, because that is the slot the
            # finding message reads. (Caught by the selftest when the column count
            # changed from 4 to 5 and this tuple was not re-ordered with it.)
            out.append(("__MALFORMED__", ln, None, line, None))
            continue
        out.append((parts[0], parts[1], parts[2], parts[3], parts[4]))
    return out


def derive(cmd, sha, cwd=ROOT):
    """Run one derivation with $SHA bound to the row's pinned sha."""
    env = dict(os.environ, SHA=sha)
    r = subprocess.run(["bash", "-c", cmd], cwd=cwd, capture_output=True, text=True, env=env)
    return r.returncode, r.stdout.strip(), r.stderr.strip()


def have_commit(sha, cwd=ROOT):
    return subprocess.run(["git", "cat-file", "-e", f"{sha}^{{commit}}"],
                          cwd=cwd, capture_output=True).returncode == 0


def check(path=TSV, cwd=ROOT, verbose=True):
    findings, n = [], 0
    rs = rows(path)
    if not rs:
        # ⛔ A GATE THAT FINDS NO SUBJECT MUST REFUSE. An empty manifest passing
        # silently is the "0 jobs means the file was refused" defect.
        return ["the manifest carries NO claims — a gate with no subject must refuse, not pass"], 0
    for cid, val, sha, cmd, where in rs:
        if cid == "__MALFORMED__":
            findings.append(f"line {val}: malformed row (needs 5 tab-separated fields): {cmd[:60]!r}")
            continue
        n += 1
        # ⛔ A PINNED SHA ABSENT FROM THE CLONE IS A FINDING, NEVER A PASS. A
        # depth-1 checkout would otherwise turn every row into a silent skip --
        # the gate reporting clean because it could not look. (CI-1's trap.)
        if not have_commit(sha, cwd=cwd):
            findings.append(f"{cid}: pinned sha {sha} is NOT in this clone -- the derivation could "
                            f"not run. `fetch-depth: 0` is required; this is a REFUSAL, not a pass.")
            continue
        rc, got, err = derive(cmd, sha, cwd=cwd)
        if rc != 0:
            findings.append(f"{cid}: derivation FAILED rc={rc} ({err[:80]})")
        elif got == "":
            findings.append(f"{cid}: derivation printed NOTHING — an empty result is not a value")
        elif got != val:
            findings.append(f"{cid}: published {val!r} but derives {got!r} at {sha}   [{where}]")
        elif verbose:
            print(f"  ok  {cid:22s} {val:>8s}  @{sha}   {where}")
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
    # ⛔⛔ THIS ARM READ `n == 7` AND BROKE THE MOMENT I ADDED THE G3 CLAIMS.
    # A count literal here is a gate on a quantity THE WORK CONSUMES — the exact
    # defect D206 was written about, committed again inside the gate D206 is about,
    # by its author, the same day. Every new claim would have demanded a second
    # edit here and the only thing the red could mean is "you published a number".
    # The control's job is "the real manifest re-derives CLEAN"; the empty-manifest
    # case has its own arm below, so `n > 0` is the non-redundant guard.
    arm("control: the real manifest re-derives clean", not f and n > 0, f"{f} n={n}")

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
    bad = base.replace("""git show "$SHA":docs/DECISIONS.md | grep -c '^## D[0-9]'""",
                       'git show "$SHA":docs/NO-SUCH-FILE.md', 1)
    f, _ = with_tsv(bad)
    arm("PLANT: a failing derivation is a FINDING, never a skip",
        any("decisions" in x and "FAILED" in x for x in f), str(f))

    # a derivation that prints NOTHING is caught -- an empty result is the shape
    # a silently-broken pipeline produces, and it must not read as a value.
    bad = base.replace("""git ls-tree -r "$SHA" --name-only | grep -cE '^X86/.*\\.lean$'""",
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
    f, n0 = with_tsv("# only a comment\nid\tvalue\tsha\tcommand\tappears_in\n")
    arm("⭐ PLANT: an EMPTY manifest REFUSES (a gate with no subject must not pass)",
        bool(f) and n0 == 0, f"{f} n={n0}")

    # ⛔ THE PINNED-SHA REFUSAL, DRIVEN. A depth-1 clone would otherwise make
    # every row a silent skip, and the gate would report clean because it could
    # not look. This arm is why that reads as a REFUSAL instead.
    bad = base.replace("\t7bb57ee\t", "\t" + "0" * 40 + "\t")
    f, _ = with_tsv(bad)
    arm("⭐ PLANT: a pinned sha ABSENT from the clone REFUSES (never a silent pass)",
        bool(f) and all("NOT in this clone" in x for x in f), str(f)[:160])

    # ⛔ AND THE REGRESSION THAT CAUSED THIS REDESIGN: deriving at HEAD instead
    # of the pinned sha. `decisions` grows with ordinary work, so a HEAD-derived
    # row reds on every decision commit -- a chore, not a gate.
    bad = base.replace('git show "$SHA":docs/DECISIONS.md', "git show HEAD:docs/DECISIONS.md", 1)
    f, _ = with_tsv(bad)
    arm("⭐ PLANT: a row that derives at HEAD instead of its pinned sha is caught "
        "(this is the defect that redded the build)",
        any("decisions" in x for x in f), str(f)[:160])

    print(f"\n  arms={len(arms)} red={red}")
    return 1 if red else 0


if __name__ == "__main__":
    sys.exit(main())
