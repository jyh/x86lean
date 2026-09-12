#!/usr/bin/env python3
"""Decide whether the `selftest` shards may be SKIPPED, keyed on a CONTENT DIGEST.

⚖️ RULED BY THE HELM 2026-09-11 on `CI-3`: *"SKIP AUTHORISED, KEYED ON THE CONTENT
DIGEST, NEVER A PATH LIST. A digest cannot be fooled by a path nobody enumerated;
a path list can."*  Two conditions, and both are load-bearing:

  (1) THE SKIP RECORDS WHAT IT MATCHED -- the digest AND the prior green sha it
      inherits -- so green-by-skip differs from green-by-run.  *"An unrecorded
      skip makes a job that never ran report GREEN, not UNKNOWN."*
  (2) THE DIGEST COVERS EVERYTHING THE SHARD CONSUMES.  *"You measure what it
      runs, so you define that set."*

WHY IT EXISTS.  Measured 2026-09-11: the six shards cost 522.6 runner-minutes
(8.7 runner-hours) per run, and 19 of the last 20 master commits touched no
Lean-relevant file.  Three consecutive runs re-tested a byte-identical artifact.

⛔ WHAT THIS IS NOT.  It is NOT `kernel_delta.null_pair_reason()`, and the helm
refused that port explicitly: *"Do NOT port the weaker predicate into the
stronger job."*  That predicate answers "did this RANGE change anything that
moves kernel time" -- a question about a diff, and a diff is a claim about the
paths somebody thought to enumerate.  This answers "is the artifact the shard
would build BYTE-IDENTICAL to one a green run already tested" -- a question about
CONTENT.  A rebase, a force-push, or a range whose endpoints hide an intermediate
change all defeat the first and none defeat the second.

CONDITION (2) -- THE CONSUMED SET, DERIVED BY MEASURING WHAT THE SHARD RUNS.
A shard runs exactly two commands:
    lake build x86lean-diff
    lake env .lake/build/bin/x86lean-diff selftest-shard <k> 6
`selftest-shard` dispatches to `driveWrong`, which is PURE COMPUTATION --
`emitAll`/`parseRecords`/`compareRecs`.  Measured: all four `IO.FS` sites in
`Main.lean` lie in other subcommands, and the selftest path spawns no process,
reads no file and reads no environment variable.  ⇒ the shard consumes the
COMPILED BINARY and nothing else at runtime.  So the set is what determines that
binary, plus the runner that invokes it:

    *.lean            every tracked Lean source
    lakefile.toml     targets, lean options
    lean-toolchain    the compiler pin
    lake-manifest.json  the dependency pin
    .github/workflows/ci.yml   THE SHARD RUNNER -- the matrix (6) and the two
                      commands live here.  A run inherited from a 6-shard green
                      run is not evidence about an 8-shard matrix.

⭐ THE SET IS DELIBERATELY WIDER THAN NECESSARY, AND THE ASYMMETRY IS THE SAFETY
ARGUMENT.  Not every `.lean` reaches `x86lean-diff`, and most `ci.yml` edits do
not touch this job.  A SPURIOUS member costs one extra run; a MISSING member
costs a false SKIP, which is a job reporting green having tested nothing.  The
errors are not symmetric, so the set errs toward running.

⛔ INVERTED DEFAULT, EVERYWHERE.  Unknown digest, unreachable API, no green run,
a prior sha not in this clone, any exception at all ⇒ MEASURE.  A skip is only
ever emitted on a POSITIVE match against a named green run.

⚖️ WHAT ITS ARMS ESTABLISH (row `LB`, declared not repaired):  **REACHABILITY, plus one
   deliberate structural substitute for RATE.** The arms drive both decisions and every
   refusal. **RATE is NOT established for the one failure that matters** — a consumed-set
   member I failed to LIST is undetectable by any arm this script owns, at any frequency.
   ⇒ That is why the consumed set is deliberately WIDER than necessary: the admission is made
   STRUCTURAL rather than written down, because a spurious member costs one run and a missing
   one costs a false SKIP.
   ⇒ 🔑 ***AN INSTRUMENT'S SILENCE IS NOT A MEASUREMENT OF THE THING IT WAS SILENT
     ABOUT*** (row `LB`, 2026-09-11, three seats independently). The remedy the row
     prescribes is DECLARATION, not more arms — most such arms cannot be strengthened,
     and the cost is that a reachability arm's silence gets read as coverage.

LANE.  Personal lane.  Reads this repository and the GitHub Actions API for this
repository's own runs.
"""
import argparse, hashlib, json, os, subprocess, sys

CONSUMED_GLOBS = ("*.lean",)
CONSUMED_EXACT = ("lakefile.toml", "lean-toolchain", "lake-manifest.json",
                  ".github/workflows/ci.yml")
WORKFLOW = "CI"


def is_shard_job(name):
    """True only for a SHARD of the selftest matrix, e.g. `selftest (3)`.

    ⛔⛔ THIS WAS A PREFIX TEST AND THE PREFIX TEST WAS A REAL BUG, CAUGHT BEFORE
    LANDING.  `"selftest"` also matches `selftest-gate` -- the job that DECIDES
    the skip.  On a run whose shards were skipped, the shard jobs are ABSENT and
    `selftest-gate` is present and green, so a prefix test would have found
    "every selftest* job succeeded" and let a skip INHERIT FROM A RUN THAT ITSELF
    SKIPPED.  A chain of skips with no measurement at its root is exactly the
    state the helm's condition (1) exists to prevent, arrived at from the other
    direction: not an unrecorded skip, but a skip recorded against another skip.
    ⇒ 🔑 A JOB-NAME PREFIX IS NOT A JOB IDENTITY, AND ADDING A JOB CAN SILENTLY
    WIDEN EVERY PREFIX TEST THAT ALREADY EXISTED.
    """
    return name == "selftest" or name.startswith("selftest (")


def git(args, cwd=None):
    r = subprocess.run(["git"] + args, cwd=cwd, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed rc={r.returncode}: {r.stderr.strip()}")
    return r.stdout


def consumed_paths(ref, cwd=None):
    """The paths of the consumed set present at `ref`, sorted."""
    out = git(["ls-tree", "-r", ref, "--name-only"], cwd=cwd).split("\n")
    keep = []
    for p in out:
        p = p.strip()
        if not p:
            continue
        if p in CONSUMED_EXACT or p.endswith(".lean"):
            keep.append(p)
    return sorted(keep)


def digest(ref, cwd=None):
    """sha256 over (path, blob-sha) for the consumed set at `ref`.

    Blob shas come from git rather than from reading content: they ARE content
    hashes, so this is exact, and it costs one `ls-tree` instead of N reads.
    """
    lines = git(["ls-tree", "-r", ref], cwd=cwd).split("\n")
    entries = []
    for ln in lines:
        if not ln.strip():
            continue
        meta, path = ln.split("\t", 1)
        _mode, _type, blob = meta.split()
        path = path.strip()
        if path in CONSUMED_EXACT or path.endswith(".lean"):
            entries.append((path, blob))
    entries.sort()
    h = hashlib.sha256()
    for path, blob in entries:
        h.update(path.encode()); h.update(b"\0")
        h.update(blob.encode()); h.update(b"\0")
    return h.hexdigest()[:16], len(entries)


def have_commit(sha, cwd=None):
    try:
        git(["cat-file", "-e", f"{sha}^{{commit}}"], cwd=cwd)
        return True
    except RuntimeError:
        return False


def last_green_selftest(branch, exclude_sha, limit=30):
    """The newest run on `branch` whose EVERY selftest shard concluded success.

    ⛔ A RUN'S CONCLUSION IS AN OR OVER ITS JOBS, so this reads PER-JOB
    conclusions and never the run's own.  [[feedback-an-expected-red-hides-an-unexpected-one]]
    Returns (sha, run_id) or None.  Any API failure returns None, which MEASURES.
    """
    try:
        runs = json.loads(subprocess.run(
            ["gh", "run", "list", "--workflow", WORKFLOW, "--branch", branch,
             "--limit", str(limit), "--json", "databaseId,headSha,status"],
            capture_output=True, text=True, check=True).stdout)
    except Exception:
        return None
    for r in runs:
        if r.get("status") != "completed" or r.get("headSha") == exclude_sha:
            continue
        try:
            jobs = json.loads(subprocess.run(
                ["gh", "run", "view", str(r["databaseId"]), "--json", "jobs"],
                capture_output=True, text=True, check=True).stdout)["jobs"]
        except Exception:
            continue
        if run_qualifies(jobs):
            return r["headSha"], r["databaseId"]
    return None


def run_qualifies(jobs):
    """Did this run ACTUALLY MEASURE the shards, all green?

    ⛔ THE SHARDS MUST HAVE RUN.  No shard job means the run SKIPPED them (or
    predates the job), and a conclusion of "skipped"/"cancelled" is not evidence
    either.  Only an ACTUAL green measurement may be inherited -- otherwise a
    skip can inherit from a skip and nothing at the root ever ran.
    ⇒ Pure, and therefore ARMED: the network path above cannot be driven in a
    selftest, so the decision it rests on is factored out to where it can be.
    """
    shards = [j for j in jobs if is_shard_job(j.get("name", ""))]
    if not shards:
        return False
    return all(j.get("conclusion") == "success" for j in shards)


def decide(ref="HEAD", branch="master", cwd=None, emit=None):
    """SKIP only on a positive digest match against a named green run."""
    try:
        head = git(["rev-parse", ref], cwd=cwd).strip()
        d, n = digest(ref, cwd=cwd)
    except Exception as e:
        return _out(False, None, None, n=0, reason=f"cannot compute this digest ({e})", emit=emit)

    print(f"selftest-skip: consumed set = {n} path(s); digest {d} at {head[:8]}")

    g = last_green_selftest(branch, head)
    if g is None:
        return _out(False, d, None, n, "no completed run on this branch has ALL selftest shards green "
                                       "(or the API was unreachable)", emit)
    gsha, grun = g
    if not have_commit(gsha, cwd=cwd):
        return _out(False, d, None, n, f"the green sha {gsha[:8]} (run {grun}) is not in this clone -- "
                                       "checkout needs fetch-depth: 0", emit)
    try:
        gd, _ = digest(gsha, cwd=cwd)
    except Exception as e:
        return _out(False, d, None, n, f"cannot compute the green digest ({e})", emit)

    if gd == d:
        return _out(True, d, gsha, n, f"byte-identical to green run {grun}", emit, run=grun)
    return _out(False, d, gsha, n, f"digest differs from green {gsha[:8]} ({gd})", emit, run=grun)


def _out(skip, d, inherits, n, reason, emit, run=None):
    verdict = "SKIP" if skip else "MEASURE"
    print(f"selftest-skip: {verdict} -- {reason}")
    if skip:
        # CONDITION (1): the record IS the output.  Green-by-skip must be
        # distinguishable from green-by-run by anyone reading the log.
        print(f"selftest-skip: RECORD digest={d} inherits={inherits} run={run} paths={n}")
    if emit:
        with open(emit, "a") as fh:
            fh.write(f"skip={'true' if skip else 'false'}\n")
            fh.write(f"digest={d or ''}\n")
            fh.write(f"inherits={inherits or ''}\n")
            fh.write(f"inherits_run={run or ''}\n")
    # CONDITION (1), made visible WITHOUT opening a log.  A record only a reader
    # who digs finds is a record that will not be read on the day it matters.
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a") as fh:
            if skip:
                fh.write(f"### selftest: SKIPPED (green-by-skip, not green-by-run)\n\n"
                         f"- consumed-set digest: `{d}` over {n} path(s)\n"
                         f"- inherits green from: `{inherits}` (run {run})\n"
                         f"- reason: {reason}\n")
            else:
                fh.write(f"### selftest: MEASURED\n\n- digest `{d}` over {n} path(s)\n"
                         f"- reason: {reason}\n")
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--digest", nargs="?", const="HEAD", metavar="REF",
                    help="print the consumed-set digest at REF (default HEAD)")
    ap.add_argument("--paths", action="store_true", help="list the consumed set at HEAD")
    ap.add_argument("--decide", action="store_true", help="SKIP/MEASURE decision")
    ap.add_argument("--branch", default="master")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args(argv)

    if a.selftest:
        return selftest()
    if a.paths:
        for p in consumed_paths("HEAD"):
            print(p)
        return 0
    if a.digest:
        d, n = digest(a.digest)
        print(f"{d}  ({n} paths at {a.digest})")
        return 0
    if a.decide:
        return decide(branch=a.branch, emit=os.environ.get("GITHUB_OUTPUT"))
    ap.print_help()
    return 64


# ---------------------------------------------------------------------------
# THE SELFTEST BUILDS A REAL FIXTURE REPO.  A digest gate tested only against
# the repository it ships in has been tested exactly where it cannot fail:
# every path is present and every answer is "unchanged".
# [[feedback-a-tool-tested-only-on-its-corpus]]
# ---------------------------------------------------------------------------
def selftest():
    import tempfile, shutil
    arms, red = [], 0

    def arm(name, cond, detail=""):
        nonlocal red
        arms.append(name)
        if cond:
            print(f"  v {name}")
        else:
            red += 1
            print(f"  x {name}  {detail}")

    print("selftest_skip --selftest")
    tmp = tempfile.mkdtemp(prefix="skipfix-")
    try:
        R = os.path.join(tmp, "repo")
        os.makedirs(os.path.join(R, ".github", "workflows"))
        git(["init", "-q", "-b", "master", R])
        git(["config", "user.email", "t@t"], cwd=R)
        git(["config", "user.name", "t"], cwd=R)

        def write(rel, s):
            p = os.path.join(R, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            open(p, "w").write(s)

        write("X86/Core.lean", "def a := 1\n")
        write("Main.lean", "def main := pure ()\n")
        write("lakefile.toml", 'name = "x"\n')
        write("lean-toolchain", "leanprover/lean4:v4.32.0-rc1\n")
        write("lake-manifest.json", "{}\n")
        write(".github/workflows/ci.yml", "name: CI\n")
        write("docs/NOTES.md", "prose\n")
        git(["add", "-A"], cwd=R); git(["commit", "-qm", "base"], cwd=R)
        base_d, base_n = digest("HEAD", cwd=R)

        # ---- CONTROL FIRST.  A plant probe whose control has not run says nothing.
        arm("control: the fixture digests, and the consumed set is the 6 declared paths",
            base_n == 6, f"got {base_n}")

        # ---- the set EXCLUDES docs: a docs-only commit must not move the digest.
        write("docs/NOTES.md", "different prose entirely\n")
        write("docs/OTHER.md", "new file\n")
        git(["add", "-A"], cwd=R); git(["commit", "-qm", "docs only"], cwd=R)
        d_docs, _ = digest("HEAD", cwd=R)
        arm("a docs-only commit does NOT move the digest (this is the whole point)",
            d_docs == base_d, f"{base_d} -> {d_docs}")

        # ---- each declared member MUST move it.  One arm per member: a single
        # combined arm would pass if ANY member worked.
        for rel, new in (("X86/Core.lean", "def a := 2\n"),
                         ("Main.lean", "def main := IO.println 1\n"),
                         ("lakefile.toml", 'name = "y"\n'),
                         ("lean-toolchain", "leanprover/lean4:v4.33.0\n"),
                         ("lake-manifest.json", '{"v":2}\n'),
                         (".github/workflows/ci.yml", "name: CI\njobs: {}\n")):
            before, _ = digest("HEAD", cwd=R)
            write(rel, new)
            git(["add", "-A"], cwd=R); git(["commit", "-qm", f"touch {rel}"], cwd=R)
            after, _ = digest("HEAD", cwd=R)
            arm(f"changing {rel} MOVES the digest", after != before, f"{before} -> {after}")

        # ---- a NEW .lean file must move it (a glob member, not an exact one)
        before, _ = digest("HEAD", cwd=R)
        write("X86/Extra.lean", "def b := 3\n")
        git(["add", "-A"], cwd=R); git(["commit", "-qm", "new lean"], cwd=R)
        after, n_after = digest("HEAD", cwd=R)
        arm("ADDING a .lean file moves the digest and grows the set",
            after != before and n_after == 7, f"{before} -> {after}, n={n_after}")

        # ---- DELETING a member must move it too: the gate must not be blind to
        # removal, which a naive "hash each present file" loop can be.
        before, _ = digest("HEAD", cwd=R)
        os.remove(os.path.join(R, "X86/Extra.lean"))
        git(["add", "-A"], cwd=R); git(["commit", "-qm", "del lean"], cwd=R)
        after, _ = digest("HEAD", cwd=R)
        arm("DELETING a .lean file moves the digest", after != before, f"{before} -> {after}")

        # ---- a commit that changes NOTHING in the set is identical again:
        # the digest is a function of CONTENT, not of history.
        git(["commit", "-q", "--allow-empty", "-m", "empty"], cwd=R)
        after2, _ = digest("HEAD", cwd=R)
        arm("an empty commit leaves the digest unchanged (content, not history)",
            after2 == after, f"{after} -> {after2}")

        # ---- the inverted default: an unknown sha MEASURES, never SKIPs.
        arm("a sha absent from the clone is reported absent (⇒ MEASURE)",
            not have_commit("0" * 40, cwd=R))

        # ---- JOB IDENTITY.  A prefix test would match `selftest-gate`, and on a
        # run whose shards SKIPPED that job is present and green -- so a skip
        # could inherit from a skip.  One arm per direction.
        arm("is_shard_job ACCEPTS the matrix shards",
            all(is_shard_job(n) for n in ("selftest", "selftest (1)", "selftest (6)")))
        arm("is_shard_job REJECTS the gate job and its neighbours",
            not any(is_shard_job(n) for n in
                    ("selftest-gate", "selftest-gate (1)", "build", "kernel-delta")))

        # ---- THE SKIP-CHAIN GUARD, driven both ways.
        arm("a run with all shards green QUALIFIES",
            run_qualifies([{"name": f"selftest ({i})", "conclusion": "success"} for i in range(1, 7)]))
        arm("⭐ a run whose shards were SKIPPED does NOT qualify "
            "(no shard jobs, only the green gate) -- no skip inherits from a skip",
            not run_qualifies([{"name": "selftest-gate", "conclusion": "success"},
                               {"name": "build", "conclusion": "success"}]))
        arm("a run with one shard FAILED does not qualify",
            not run_qualifies([{"name": "selftest (1)", "conclusion": "success"},
                               {"name": "selftest (2)", "conclusion": "failure"}]))
        arm("a run with a CANCELLED shard does not qualify",
            not run_qualifies([{"name": "selftest (1)", "conclusion": "success"},
                               {"name": "selftest (2)", "conclusion": "cancelled"}]))
        arm("a run with a SKIPPED shard does not qualify",
            not run_qualifies([{"name": "selftest (1)", "conclusion": "skipped"}]))

        # ---- ⛔⛔ THE SKIP PATH ITSELF, DRIVEN END TO END. Until 2026-09-12 this was
        # proven only IN PRODUCTION: the arms below test digest equality and
        # run_qualifies SEPARATELY, and nothing drove `decide()` to an actual SKIP.
        # A refactor could therefore break the PERMITTING path while all arms stayed
        # green -- and the permitting path is the one whose failure direction costs
        # something. (Maestro/KG, 2026-09-11: "A GATE IS ARMED ONLY IF EVERY
        # MECHANIZABLE ARM IS PROBED; A PROBE ON ONE ARM OF FOUR IS NOT COVERAGE,
        # IT IS A SAMPLE.")  A production observation is a point in time; an arm is
        # a standing guard.
        import io as _io, contextlib as _ctx
        _real = globals()["last_green_selftest"]
        head_sha = git(["rev-parse", "HEAD"], cwd=R).strip()
        prev_sha = git(["rev-parse", "HEAD~1"], cwd=R).strip()
        try:
            # (a) a green run at a digest IDENTICAL to ours ⇒ must SKIP
            globals()["last_green_selftest"] = lambda b, x, limit=30: (prev_sha, 999)
            git(["commit", "-q", "--allow-empty", "-m", "docs-only, digest unmoved"], cwd=R)
            buf = _io.StringIO()
            with _ctx.redirect_stdout(buf):
                decide(ref="HEAD", cwd=R)
            out = buf.getvalue()
            arm("⭐⭐ PLANT: decide() SKIPs end-to-end on an identical digest, and RECORDS "
                "the inherited sha", "SKIP --" in out and "RECORD" in out and prev_sha[:8] in out,
                out.strip()[:150])

            # (b) the SAME green run, but our digest MOVED ⇒ must MEASURE
            write("X86/Core.lean", "def a := 4321\n")
            git(["add", "-A"], cwd=R); git(["commit", "-qm", "move the digest"], cwd=R)
            buf = _io.StringIO()
            with _ctx.redirect_stdout(buf):
                decide(ref="HEAD", cwd=R)
            out2 = buf.getvalue()
            arm("⭐⭐ PLANT: the same green run + a MOVED digest MEASUREs "
                "(the two directions differ only by the artefact)",
                "MEASURE --" in out2 and "SKIP" not in out2, out2.strip()[:150])
        finally:
            globals()["last_green_selftest"] = _real

        # ---- and the API-failure path MEASURES.  Forced by pointing `gh` at a
        # branch that has no runs; any exception inside also returns None.
        g = last_green_selftest("branch-that-does-not-exist-xyzzy", "deadbeef", limit=1)
        arm("no green run / unreachable API ⇒ None ⇒ MEASURE", g is None, f"got {g}")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    print(f"\n  arms={len(arms)} red={red}")
    return 1 if red else 0


if __name__ == "__main__":
    sys.exit(main())
