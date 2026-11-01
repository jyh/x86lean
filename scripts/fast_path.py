#!/usr/bin/env python3
"""Decide whether a PR may take the FAST PATH: merge on its required checks, without
waiting for the selftest matrix, because the matrix would test a byte-identical artifact.

⚖️ RULED BY THE HELM 2026-10-14 07:57 (on paris's census of why x86lean lands slowly),
GO WITH A CONDITION:
  (1) every input of the selftest digest is enumerated and posted;
  (2) a planted change to EACH input class moves the digest, red-first, on the real tree,
      and a change outside the list does not;
  (3) then a PR whose digest equals a green master's merges on the required checks alone;
      the matrix still runs on master after the merge, and a red there REVERTS the PR;
  (4) which PRs took the fast path is said where a reader will meet it.
(1) and (2) were driven before this file existed (D340). This file is (3) and (4).

THE DIGEST IS `selftest_skip.digest`, IMPORTED, NEVER RE-DERIVED: a second digest that
agrees with the first today is two rules for one question (D143's lesson). Its inputs:
every tracked `*.lean` (path and blob, so an add, delete or rename moves it), plus
`lakefile.toml`, `lean-toolchain`, `lake-manifest.json` and `.github/workflows/ci.yml`.
⚠️ NOT IN IT, AND DECLARED: the runner image. A green master run inherited across an
image change is a reading on the older image; the post-merge master run is the check.

WHAT IS COMPARED: the PR's MERGE REF (`refs/pull/N/merge`, the tree that would land), not
its head — a head digest can match while the merge with a moved master does not.
AGAINST: the newest master run whose every selftest shard RAN and succeeded
(`selftest_skip.last_green_selftest`, which never inherits from a run that itself skipped).

(4) THE RECORD IS THE MERGE COMMIT: `--check` prints a `FAST-PATH:` line and the exact
`gh pr merge` command that puts that line in the merge commit's body, so
`git log --grep '^FAST-PATH:' origin/master` lists every fast-path merge, with the digest
and the green run it inherited. This file does not merge anything itself.

(4′) AND THE RECORD IS NOT THE CENSUS (D378, on PR #149's measurement): the `FAST-PATH:` line is
written by whoever merges, and over 10-14 → 10-31 it was written for 3 of the 22 merges that
landed without a completed matrix at their merged head. `--census` therefore DERIVES the list
from the forge: for every merged PR, did a `pull_request` CI run AT THE MERGED HEAD complete
every `selftest (n)` shard with success BEFORE `mergedAt`? It prints its population (how many
PRs, which window) beside the list, and which of the matrix-less merges carry the record.
A matrix-less merge is a fast-path merge for D340's revert duty, whatever its body says.

Usage:  fast_path.py --check <PR>            decide one PR (reads git and the forge; writes nothing)
        fast_path.py --census [--since DATE] every merged PR's matrix state at its merge (forge; read-only)
        fast_path.py --selftest              the decision and census rules' arms, no network
"""
import argparse, json, os, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import selftest_skip as SK

REPO = "jyh/x86lean"


def decide(pr_digest, green, green_digest, required, checks):
    """The rule, pure.  Returns (go, reasons).

    pr_digest     the merge ref's digest, or None if it could not be computed
    green         (sha, run_id) of the newest green master selftest run, or None
    green_digest  that sha's digest, or None
    required      the names branch protection requires (read live, never typed here)
    checks        {name: [conclusions...]} for the PR head; a name may appear more than once
    ⛔ INVERTED DEFAULT, AS IN selftest_skip: anything unknown REFUSES. A refusal costs
    the matrix's wall time; a false GO lands an untested artifact.
    """
    why = []
    if pr_digest is None:
        why.append("the merge ref's digest could not be computed")
    if green is None:
        why.append("no master run whose every selftest shard ran and succeeded")
    if green is not None and green_digest is None:
        why.append("the green run's sha is not in this clone")
    if pr_digest and green_digest and pr_digest != green_digest:
        why.append(f"digest differs: merge ref {pr_digest} vs green master {green_digest}"
                   " (a selftest input changed; the matrix must run)")
    if not required:
        why.append("branch protection lists no required checks (read failed or empty)")
    for name in required:
        got = checks.get(name, [])
        if not got:
            why.append(f"required check `{name}` has not reported")
        elif any(c != "success" for c in got):
            why.append(f"required check `{name}` is {sorted(set(got))}, not all success")
    return (not why), why


def _gh_json(args):
    return json.loads(subprocess.run(["gh"] + args, capture_output=True, text=True,
                                     check=True).stdout)


def check(pr):
    head = _gh_json(["pr", "view", str(pr), "--repo", REPO, "--json",
                     "headRefOid,baseRefName,state"])
    if head.get("state") != "OPEN" or head.get("baseRefName") != "master":
        print(f"⛔ FAST-PATH REFUSED for #{pr}: state {head.get('state')}, base "
              f"{head.get('baseRefName')} (open PRs against master only)")
        return 1
    ref = f"refs/fast-path/pr-{pr}"
    subprocess.run(["git", "fetch", "-q", "origin", f"+refs/pull/{pr}/merge:{ref}"],
                   check=True)
    subprocess.run(["git", "fetch", "-q", "origin", "master"], check=True)
    try:
        pr_digest, n = SK.digest(ref)
    except Exception:
        pr_digest, n = None, 0
    green = SK.last_green_selftest("master", exclude_sha=None)
    green_digest = None
    if green and SK.have_commit(green[0]):
        green_digest, _ = SK.digest(green[0])
    try:
        required = _gh_json(["api", f"repos/{REPO}/branches/master/protection/"
                             "required_status_checks"]).get("contexts", [])
    except Exception:
        required = []
    rows = _gh_json(["pr", "checks", str(pr), "--repo", REPO, "--json", "name,state"])
    checks = {}
    for r in rows:
        checks.setdefault(r["name"], []).append(r["state"].lower())
    go, why = decide(pr_digest, green, green_digest, required, checks)
    print(f"merge ref {ref}: digest {pr_digest} over {n} inputs")
    print(f"green master: {green} digest {green_digest}")
    print(f"required ({len(required)}): " + ", ".join(required))
    if not go:
        print(f"⛔ FAST-PATH REFUSED for #{pr} — the matrix runs:")
        for w in why:
            print("   · " + w)
        return 1
    line = (f"FAST-PATH: merge-ref digest {pr_digest} == green master {green[0][:7]} "
            f"(selftest run {green[1]}); required checks {len(required)}/{len(required)} success; "
            f"the post-merge master run is the check, and a red there reverts this merge.")
    print("✅ FAST-PATH GO for #%s" % pr)
    print(line)
    print(f"merge with:  gh pr merge {pr} --repo {REPO} --merge "
          f"--match-head-commit {head['headRefOid']} --body '{line}'")
    return 0


def classify(merged_at, runs):
    """BEFORE | AFTER | NEVER for one merged PR. `runs` is one entry per `pull_request` CI run at
    the MERGED HEAD: a list of (shard conclusion, shard completed_at) pairs, one per `selftest (n)`
    job. A run counts only if it HAS shards and EVERY shard succeeded; its completion is its last
    shard's. BEFORE if any such run completed at or before `merged_at` (ISO-8601 UTC strings compare
    as text), AFTER if one exists and all completed later, NEVER if none exists."""
    done = [max(t for _c, t in r) for r in runs
            if r and all(c == "success" for c, _t in r)]
    if not done:
        return "NEVER"
    return "BEFORE" if min(done) <= merged_at else "AFTER"


def census(since):
    prs = _gh_json(["pr", "list", "--repo", REPO, "--state", "merged", "--limit", "500",
                    "--json", "number,headRefOid,mergedAt,mergeCommit"])
    prs = sorted((p for p in prs if p["mergedAt"] >= since), key=lambda p: p["mergedAt"])
    rec = set(subprocess.run(["git", "log", "--first-parent", "--format=%H", "--grep", "^FAST-PATH:",
                              "origin/master"], capture_output=True, text=True, check=True).stdout.split())
    rows = []
    for p in prs:
        runs = []
        page = _gh_json(["api", f"repos/{REPO}/actions/runs?head_sha={p['headRefOid']}"
                         "&event=pull_request&per_page=100"])["workflow_runs"]
        for r in page:
            if r["name"] != "CI":
                continue
            jobs = _gh_json(["api", f"repos/{REPO}/actions/runs/{r['id']}/jobs?per_page=100"])["jobs"]
            runs.append([(j["conclusion"], j["completed_at"] or "") for j in jobs
                         if j["name"].startswith("selftest (")])
        mc = (p.get("mergeCommit") or {}).get("oid", "")
        rows.append((p["number"], mc[:7], p["mergedAt"][:16], classify(p["mergedAt"], runs), mc in rec))
    less = [r for r in rows if r[3] != "BEFORE"]
    print(f"fast-path census: {len(rows)} merged PR(s) since {since}; {len(less)} without a completed "
          f"matrix at the merged head before the merge; {sum(r[4] for r in less)} of those carry FAST-PATH:")
    for n, sha, at, cls, r in less:
        print(f"  #{n:<4} {sha}  merged {at}Z  matrix {cls:<6}  {'FAST-PATH: recorded' if r else 'NOT recorded'}")
    unrec = [r for r in rows if r[4] and r[3] == "BEFORE"]
    for n, sha, at, _cls, _r in unrec:
        print(f"  #{n:<4} {sha}  merged {at}Z  matrix BEFORE  FAST-PATH: recorded (the matrix had completed anyway)")
    print("NOT READ: who merged (every merge reads one shared account); whether each merge ref's digest equalled a "
          "green master's (D340's GO); a matrix at an EARLIER head of the same PR, by design; "
          "a re-ATTEMPTED run, read at its LATEST attempt only (a run green before the merge and re-attempted "
          "after it reads AFTER: the safe direction).")
    return 0


def selftest():
    bad, ran = [], []
    def arm(name, cond):
        ran.append(name)
        print(("  ✔ " if cond else "  ⛔ ") + name)
        if not cond:
            bad.append(name)
    req = ["private-paths", "trailers"]
    ok_checks = {"private-paths": ["success", "success"], "trailers": ["success"]}
    g = ("a" * 40, 1)
    go, _ = decide("d1", g, "d1", req, ok_checks)
    arm("control: equal digests, all required success ⇒ GO", go)
    arm("a DIFFERENT digest REFUSES", not decide("d1", g, "d2", req, ok_checks)[0])
    arm("no green master run REFUSES", not decide("d1", None, None, req, ok_checks)[0])
    arm("a green run not in the clone REFUSES", not decide("d1", g, None, req, ok_checks)[0])
    arm("an uncomputable merge digest REFUSES", not decide(None, g, "d1", req, ok_checks)[0])
    arm("an EMPTY required list REFUSES (a failed read is not 'nothing required')",
        not decide("d1", g, "d1", [], ok_checks)[0])
    arm("a required check that has NOT REPORTED refuses",
        not decide("d1", g, "d1", req + ["claim"], ok_checks)[0])
    arm("ONE failing run of a twice-reported check refuses (all, not any)",
        not decide("d1", g, "d1", req, {"private-paths": ["success", "failure"],
                                         "trailers": ["success"]})[0])
    arm("a PENDING required check refuses",
        not decide("d1", g, "d1", req, {"private-paths": ["pending"], "trailers": ["success"]})[0])
    arm("a failing NON-required check does not block (the matrix is what is skipped)",
        decide("d1", g, "d1", req, dict(ok_checks, **{"selftest (3)": ["failure"]}))[0])
    # D378: the census rule.
    m = "2026-10-20T12:00:00Z"
    ok = [("success", "2026-10-20T11:00:00Z"), ("success", "2026-10-20T11:30:00Z")]
    arm("census control: every shard green before the merge ⇒ BEFORE", classify(m, [ok]) == "BEFORE")
    arm("the matrix completing AFTER the merge ⇒ AFTER",
        classify(m, [[("success", "2026-10-20T11:00:00Z"), ("success", "2026-10-20T13:00:00Z")]]) == "AFTER")
    arm("a CANCELLED shard is no matrix (all, not any) ⇒ NEVER",
        classify(m, [[("success", "2026-10-20T11:00:00Z"), ("cancelled", "2026-10-20T11:05:00Z")]]) == "NEVER")
    arm("no PR run at the merged head ⇒ NEVER", classify(m, []) == "NEVER")
    arm("a run with NO shards is not a matrix ⇒ NEVER", classify(m, [[]]) == "NEVER")
    arm("an older complete run before the merge counts beside a newer cancelled one ⇒ BEFORE",
        classify(m, [[("cancelled", "2026-10-20T12:30:00Z")], ok]) == "BEFORE")
    arm("a complete run BEFORE the merge and a re-run AFTER it ⇒ BEFORE (a later re-run undoes nothing)",
        classify(m, [[("success", "2026-10-20T14:00:00Z")], ok]) == "BEFORE")
    arm("a matrix completing AT the merge instant ⇒ BEFORE (the boundary is inclusive; paper's LOW on #150)",
        classify(m, [[("success", m)]]) == "BEFORE")
    arm("a SKIPPED shard is not a run shard ⇒ NEVER",
        classify(m, [[("skipped", "2026-10-20T11:00:00Z")]]) == "NEVER")
    print("fast-path selftest: %s (%d arms)" % ("CLEAN" if not bad else "FAIL", len(ran)))
    return 1 if bad else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--check", type=int, metavar="PR")
    g.add_argument("--census", action="store_true")
    g.add_argument("--selftest", action="store_true")
    ap.add_argument("--since", default="2026-10-14", metavar="DATE")
    a = ap.parse_args()
    if a.census:
        return census(a.since)
    return selftest() if a.selftest else check(a.check)


if __name__ == "__main__":
    sys.exit(main())
