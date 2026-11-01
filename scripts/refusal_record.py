#!/usr/bin/env python3
"""refusal_record.py — D381: a `kernel-delta` REFUSAL on a MASTER PUSH run is decided by the RECORD.

⚖️ THE RULING (the helm, 2026-11-01 05:45, desk XF, on D377 arm (C)). On a push to master, `kernel_delta.py`
exit 3 (the run could not measure) maps to a PASS with a `::warning::` naming the verdict of record, ONLY when
one exists:
  * a LEDGER ROW that prices the merged step `HEAD^ → HEAD` (by `kernel_drift`'s own join: `records_step`,
    and D372's slide), or
  * a `pull_request` CI run whose `kernel-delta` job concluded success at the merged PR head (`HEAD^2`).
Exit 1 (OVER) is never touched. Exit 3 with no record stays red. PR runs are unchanged: the flag that calls this
is passed by ci.yml on master push runs only.
⛔ A REFUSAL IS RECORDED, NOT ONLY ANNOTATED (condition 2). Every exit-3 run prints one `KERNEL-DELTA-REFUSED`
JSON row (units and kinds, the record it leaned on or `null`) in the job log and the step summary, and the run
reads the PREVIOUS master push run's row. **The same unit refusing on two consecutive master runs stays red
whatever the record says** — that is (B)'s escalation, kept mechanical, because nobody counts warnings.
⛔ AND WHEN THE PREVIOUS RUN CANNOT BE READ, THE REFUSAL STAYS RED: an escalation check that could not run is not
a check that passed.

LIMITS, carried beside the verdict (the warning text says them):
  * the record is a reading of the step on ANOTHER run or box; it is not this run's measurement.
  * a PR run's `kernel-delta` success is taken from its conclusion. A null-pair SKIP also concludes success; it
    cannot coincide with a push-run refusal unless the PR changed no reading input, which a refusal contradicts.
  * the escalation compares the refused UNIT NAMES of two consecutive runs; it does not see a unit that refuses on
    alternate runs, and "the previous run" is the latest COMPLETED one, so a predecessor still running is skipped
    (one missed pairing when two master pushes overlap; paper's LOW at its #153 read).

Usage:
  python3 scripts/refusal_record.py --selftest
  python3 scripts/refusal_record.py --fixture   # D381 condition (1): every refusal-only master red since 10-14,
                                                # derived from the forge, each with its record (network).
"""
import json
import os
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TAG = "KERNEL-DELTA-REFUSED"
REPO = os.environ.get("GITHUB_REPOSITORY", "jyh/x86lean")
WORKFLOW = ".github/workflows/ci.yml"
# ⛔ EVERY RUNS QUERY IS SCOPED TO THE WORKFLOW AT THE ENDPOINT, never filtered after it: an unscoped `actions/runs`
# page holds every workflow's runs (CI, Scrub, hwprobe), so a cap of N rows is not N CI runs. D377's counts were low
# for exactly this reason (paper's measurement, bus @94,466,603).
RUNS = f"repos/{REPO}/actions/workflows/ci.yml/runs"
LEDGER_PATH = "docs/delta-allowance-ledger.jsonl"


def git(*a, repo=ROOT):
    return subprocess.run(["git", *a], cwd=repo, capture_output=True, text=True, check=True).stdout.strip()


# ── what refused ─────────────────────────────────────────────────────────────
# The two exit-3 rows `kernel_delta.verdict` prints. The unit is the first 56 columns (a unit name can carry
# spaces: `Tests.Coverage @decl memDestSweep`). A leading Actions timestamp is stripped so a LOG parses the same.
_TS = re.compile(r"^\d{4}-\d\d-\d\dT[\d:.]+Z ")


def refused_units(lines):
    """[(unit, kind)] — kind `band` (UNMEASURABLE: the band straddles the budget) or `new` (a NEW unit this
    box has no ceiling for). Only rows AFTER the last `── measuring the delta` line count, so a log's selftest
    output (which prints these words in arm names) is never read as a refusal."""
    lines = [_TS.sub("", x) for x in lines]
    starts = [i for i, x in enumerate(lines) if x.startswith("── measuring the delta")]
    if starts:
        lines = lines[starts[-1]:]
    out = []
    for x in lines:
        s = x.rstrip()
        if s.endswith("UNMEASURABLE ⛔") and not s.startswith("⛔"):
            out.append((x[:56].strip(), "band"))
        elif "NEW — REFUSED ⛔" in s and not s.startswith("⛔"):
            out.append((x[:56].strip(), "new"))
    return out


def tagged_rows(lines):
    """The `KERNEL-DELTA-REFUSED` rows a run printed, parsed."""
    rows = []
    for x in lines:
        x = _TS.sub("", x)
        if x.startswith(TAG + " "):
            try:
                rows.append(json.loads(x[len(TAG) + 1:]))
            except ValueError:
                pass
    return rows


# ── the records ──────────────────────────────────────────────────────────────
def ledger_record(base, head, repo=ROOT):
    """(name, None) when a ledger row AT `head` prices `base → head`, else (None, why).

    ⛔ The ledger is read AT `head` (`git show head:…`), never from the working tree: that is the file the push
    run itself sees, and a fixture over historical runs must not credit a row written after the run."""
    import kernel_drift as kdr
    try:
        text = git("show", f"{head}:{LEDGER_PATH}", repo=repo)
    except subprocess.CalledProcessError:
        return None, f"no {LEDGER_PATH} at {head[:9]}"
    with tempfile.NamedTemporaryFile("w", suffix=".jsonl", delete=False, encoding="utf-8") as f:
        f.write(text + "\n")
        tmp = f.name
    try:
        ledger = kdr.load_ledger(tmp)
        anchor = kdr.gap_anchor(ledger, head, repo)
        if anchor is None:
            return None, "no ledger row's base is on this head's first-parent chain"
        steps = kdr.window_steps(anchor, head, repo)
        eff, slid = kdr.effective_ledger(ledger, steps, repo)
    except SystemExit as e:
        return None, f"kernel_drift refused the ledger (rc {e.code})"
    finally:
        os.unlink(tmp)
    rec = eff.get(base)
    if rec is None:
        return None, f"no ledger row prices {base[:9]} → {head[:9]}"
    land = rec.get("landed_on") or {}
    tail = (f"{land.get('a_prime_machine', '?')}, verdict {land.get('verdict', '?')}, "
            f"ms_rc {land.get('ms_rc', '?')}")
    for rb, b, h in slid:
        if b == base and h == head:
            return (f"ledger row {rb[:9]}→{str(rec.get('head'))[:9]} ({tail}), slid (D372) to "
                    f"{base[:9]}→{head[:9]}"), None
    if kdr.records_step(rec, base, head, repo):
        return f"ledger row {rec['base'][:9]}→{str(rec.get('head'))[:9]} ({tail})", None
    return None, f"the ledger row at {base[:9]} does not record the step to {head[:9]}"


def gh_api(path, raw=False):
    """`gh api` → JSON (or text). Raises on failure; callers decide what a failure means."""
    for extra in (["--allow-escape-sequences"], []):
        p = subprocess.run(["gh", "api", *extra, path], capture_output=True, text=True)
        if p.returncode == 0:
            return p.stdout if raw else json.loads(p.stdout)
        if "unknown flag" not in p.stderr:
            break
    raise RuntimeError(f"gh api {path}: rc {p.returncode}: {p.stderr.strip()[:200]}")


def pr_run_record(head, repo=ROOT, api=gh_api):
    """(name, None) when a pull_request CI run's `kernel-delta` job concluded success at `head^2`, else (None, why)."""
    parents = git("rev-list", "--parents", "-n", "1", head, repo=repo).split()
    if len(parents) != 3:
        return None, f"{head[:9]} is not a two-parent merge, so it has no merged PR head"
    pr_head = parents[2]
    try:
        runs = api(f"{RUNS}?head_sha={pr_head}&event=pull_request&per_page=100")
        for run in runs.get("workflow_runs", []):
            if run.get("path") != WORKFLOW:
                continue
            jobs = api(f"repos/{REPO}/actions/runs/{run['id']}/jobs?per_page=100")
            for j in jobs.get("jobs", []):
                if j.get("name") == "kernel-delta" and j.get("conclusion") == "success":
                    return f"PR run {run['id']} (kernel-delta success at {pr_head[:9]})", None
    except (RuntimeError, ValueError, KeyError) as e:
        return None, f"the forge could not be read ({e})"
    return None, f"no pull_request run's kernel-delta concluded success at {pr_head[:9]}"


def record_of_step(base, head, repo=ROOT, api=gh_api):
    """(name, None) or (None, [why, why]) — the ledger first, then the PR run."""
    rec, why1 = ledger_record(base, head, repo)
    if rec:
        return rec, None
    rec, why2 = pr_run_record(head, repo, api)
    if rec:
        return rec, None
    return None, [why1, why2]


def previous_refusals(run_id, api=gh_api):
    """(prev_run_id, {unit}) for the master push CI run before `run_id`, or (None, why) when it cannot be read.
    A previous run that printed a TAG row is read from the row; one from before D381 (a failed kernel-delta, exit 3)
    from its refused unit lines; a previous run whose kernel-delta passed refused nothing."""
    try:
        cur = api(f"repos/{REPO}/actions/runs/{run_id}")
        runs = api(f"{RUNS}?branch=master&event=push&per_page=30")
        prior = [r for r in runs.get("workflow_runs", [])
                 if r.get("path") == WORKFLOW and r["created_at"] < cur["created_at"]
                 and r.get("status") == "completed"]
        if not prior:
            return None, "no completed master push run before this one in the last 30"
        prev = max(prior, key=lambda r: r["created_at"])
        jobs = api(f"repos/{REPO}/actions/runs/{prev['id']}/jobs?per_page=100")
        kd = [j for j in jobs.get("jobs", []) if j.get("name") == "kernel-delta"]
        if not kd:
            return prev["id"], set()
        if kd[0].get("conclusion") not in ("success", "failure"):
            return None, f"the previous run {prev['id']}'s kernel-delta concluded {kd[0].get('conclusion')}"
        log = api(f"repos/{REPO}/actions/jobs/{kd[0]['id']}/logs", raw=True).split("\n")
    except (RuntimeError, ValueError, KeyError) as e:
        return None, f"the forge could not be read ({e})"
    rows = tagged_rows(log)
    if rows:
        return prev["id"], {u for r in rows for u, _ in r.get("units", [])}
    if kd[0].get("conclusion") == "failure":
        return prev["id"], {u for u, _ in refused_units(log)}
    return prev["id"], set()


# ── the decision (pure, so every arm can drive it) ───────────────────────────
def decide(rc, units, record, prev):
    """(rc, [lines]). `prev` is (prev_run, {unit}) or (None, why)."""
    if rc != 3:
        return rc, []                       # exit 0 needs nothing; exit 1 (OVER) is never touched
    names = [u for u, _ in units]
    rec, why = record
    prev_run, prev_units = prev
    out = []
    if prev_run is None:
        out.append(f"⛔ D381: refusal stays RED — the previous master run could not be read ({prev_units}), so "
                   f"the two-in-a-row check did not run.")
        return 3, out
    repeat = sorted(set(names) & set(prev_units))
    if repeat:
        out.append(f"⛔ D381: refusal stays RED — ESCALATED: {', '.join(repeat)} also refused on the previous "
                   f"master run {prev_run}. One refusal is noise; two consecutive is a pattern (D377 (B)).")
        return 3, out
    if not rec:
        out.append("⛔ D381: refusal stays RED — no verdict of record for this step: " + " · ".join(why))
        return 3, out
    if not units:
        out.append("⛔ D381: refusal stays RED — the gate refused but no refused unit could be parsed from its "
                   "rows, so this refusal could not be counted by the next run's two-in-a-row check.")
        return 3, out
    kinds = ", ".join(f"{u} ({k})" for u, k in units) or "(no unit row parsed)"
    out.append(f"::warning title=kernel-delta: pass by the record::pass by the record of {rec}; this run could "
               f"not measure: {kinds}. The record is another run's reading of this step, not this run's.")
    return 0, out


def tag_row(run_id, base, head, units, record, prev):
    rec, _ = record
    return TAG + " " + json.dumps({"run": run_id, "base": base, "head": head,
                                   "units": [[u, k] for u, k in units], "record": rec,
                                   "prev_run": prev[0]}, sort_keys=True)


def apply(rc, lines, base, head, repo=ROOT, api=gh_api, run_id=None):
    """The kernel_delta.py hook: rc in, rc out. Prints the TAG row and the decision; writes the step summary."""
    if rc != 3:
        return rc
    run_id = run_id or os.environ.get("GITHUB_RUN_ID", "local")
    units = refused_units(lines)
    record = record_of_step(base, head, repo, api)
    prev = previous_refusals(run_id, api) if run_id != "local" else (None, "not a CI run")
    new_rc, msgs = decide(rc, units, record, prev)
    row = tag_row(run_id, base, head, units, record, prev)
    print(row)
    for m in msgs:
        print(m)
    summ = os.environ.get("GITHUB_STEP_SUMMARY")
    if summ:
        with open(summ, "a", encoding="utf-8") as f:
            f.write(f"```\n{row}\n" + "\n".join(msgs) + "\n```\n")
    return new_rc


# ── selftest ─────────────────────────────────────────────────────────────────
def _row(u, v):
    return f"{u:<56}{100.0:>10.1f}{110.0:>10.1f}{10.0:>+10.1f}{'±8.8':>9}{3.0:>9.1f}{18.5:>9.1f}  {v}"


def selftest():
    arms, bad = [], []

    def check(name, got, want):
        arms.append(name)
        ok = got == want
        print(("  ✔ " if ok else "  ✘ ") + name + ("" if ok else f"  — got {got!r}, want {want!r}"))
        if not ok:
            bad.append(name)

    meas = ["── measuring the delta aaaaaaaaa → bbbbbbbbb"]
    band = meas + [_row("Tests.Vectors", "UNMEASURABLE ⛔"), _row("X86.Basic", "ok")]
    newu = meas + ["Tests.AnchorsVexSilC".ljust(56) + "   NEW    9715.0   -   141.2   720.0   -  NEW — REFUSED ⛔"]
    sp = meas + [_row("Tests.Coverage @decl memDestSweep", "UNMEASURABLE ⛔")]
    selftest_noise = [_row("an arm name", "UNMEASURABLE ⛔")] + meas + [_row("X86.Basic", "ok")]
    logged = ["2026-10-30T23:40:01.1234567Z " + x for x in band]

    check("parse: a band refusal row", refused_units(band), [("Tests.Vectors", "band")])
    check("parse: a NEW-unit refusal row", refused_units(newu), [("Tests.AnchorsVexSilC", "new")])
    check("parse: a unit name with spaces", refused_units(sp), [("Tests.Coverage @decl memDestSweep", "band")])
    check("parse: rows BEFORE the last measuring line are not refusals (a log's selftest)",
          refused_units(selftest_noise), [])
    check("parse: an Actions log's timestamps are stripped", refused_units(logged), [("Tests.Vectors", "band")])
    check("parse: the ⛔ summary line is not a unit",
          refused_units(meas + ["⛔ delta gate UNMEASURABLE ⛔"]), [])

    # ⛔ THE PRODUCER, not a row typed to look like it: `kernel_delta.verdict` on the gate's own UNMEASURABLE
    # fixture (D141's three-repeat pair), and the parser must find exactly that unit. A parser tested only on
    # rows its author formatted is correct only where its author is. (The NEW-unit row is NOT driven from the
    # producer here: it needs a ceilings registry fixture; that row's arm above is typed from a real log line.)
    import kernel_delta as kdm
    pattern = [-300.0, 0.0, +300.0]
    prc, plines = kdm.verdict(kdm._explicit([1000.0 + x for x in pattern], [1120.0 + x for x in pattern],
                                            unit="Tests.Vectors"),
                              None, {"Tests.Vectors": ("abs", 500.0)}, None, quiet=True)
    check("PRODUCER: kernel_delta.verdict's own UNMEASURABLE output exits 3 and parses to its unit",
          (prc, refused_units(plines)), (3, [("Tests.Vectors", "band")]))
    orc, olines = kdm.verdict(kdm._explicit([1000.0] * 3, [9000.0] * 3, unit="Tests.Vectors"),
                              None, {"Tests.Vectors": ("abs", 500.0)}, None, quiet=True)
    check("PRODUCER: an OVER from verdict exits 1 and parses to NO refusal", (orc, refused_units(olines)), (1, []))

    U = [("Tests.Vectors", "band")]
    REC = ("ledger row c0dfb01b7→dd5a67c90 (katmai, ms_rc 0)", None)
    NOREC = (None, ["no ledger row prices x → y", "no pull_request run's kernel-delta concluded success at z"])
    PREV_CLEAN = (41000000001, set())
    rc, out = decide(3, U, REC, PREV_CLEAN)
    check("(C) exit 3 + a record + a clean previous run ⇒ PASS", rc, 0)
    check("(C) …and the warning NAMES the record and says the run could not measure",
          bool(out) and "ledger row c0dfb01b7" in out[0] and "could not measure" in out[0]
          and out[0].startswith("::warning"), True)
    check("MUTANT 1: exit 3 with NO verdict of record stays RED", decide(3, U, NOREC, PREV_CLEAN)[0], 3)
    check("MUTANT 2: exit 1 (OVER) stays RED whatever record exists", decide(1, U, REC, PREV_CLEAN)[0], 1)
    check("exit 0 is untouched", decide(0, [], REC, PREV_CLEAN)[0], 0)
    # ⛔ paper's finding at its #153 read: a refusal whose rows do not parse would read GREEN and be recorded with
    # units [], so the two-in-a-row count could never see it. A refusal with no countable unit stays RED.
    check("an exit 3 with NO parsed unit stays RED even with a record (it could never be counted)",
          decide(3, [], REC, PREV_CLEAN)[0], 3)
    check("ESCALATION: the same unit refused on the previous master run stays RED with a record",
          decide(3, U, REC, (41000000001, {"Tests.Vectors"}))[0], 3)
    check("…a DIFFERENT unit on the previous run does not escalate",
          decide(3, U, REC, (41000000001, {"X86.Serialize"}))[0], 0)
    check("an UNREADABLE previous run stays RED (the check that could not run did not pass)",
          decide(3, U, REC, (None, "the forge could not be read"))[0], 3)

    # the TAG row round-trips through a log, and the escalation reads it from there
    row = tag_row(41000000002, "a" * 40, "b" * 40, U, REC, PREV_CLEAN)
    check("the TAG row round-trips (units read back by the next run)",
          tagged_rows(["2026-11-01T00:00:00.0Z " + row])[0]["units"], [["Tests.Vectors", "band"]])

    # the forge paths, with an injected api
    def api_factory(table):
        def api(path, raw=False):
            for k, v in table.items():
                if path.startswith(k):
                    return v
            raise RuntimeError("404 " + path)
        return api
    head = git("rev-parse", "HEAD")
    try:
        merge = git("rev-list", "--merges", "-n", "1", "HEAD")
    except subprocess.CalledProcessError:
        merge = ""
    if merge:
        prh = git("rev-parse", f"{merge}^2")
        ok_api = api_factory({
            f"{RUNS}?head_sha={prh}": {"workflow_runs": [{"id": 7, "path": WORKFLOW}]},
            f"repos/{REPO}/actions/runs/7/jobs": {"jobs": [{"name": "kernel-delta", "conclusion": "success"}]}})
        red_api = api_factory({
            f"{RUNS}?head_sha={prh}": {"workflow_runs": [{"id": 7, "path": WORKFLOW}]},
            f"repos/{REPO}/actions/runs/7/jobs": {"jobs": [{"name": "kernel-delta", "conclusion": "failure"}]}})
        other_wf = api_factory({
            f"{RUNS}?head_sha={prh}": {"workflow_runs": [{"id": 7, "path": ".github/workflows/x.yml"}]},
            f"repos/{REPO}/actions/runs/7/jobs": {"jobs": [{"name": "kernel-delta", "conclusion": "success"}]}})
        check("PR-run record: a success at HEAD^2 is a record", bool(pr_run_record(merge, ROOT, ok_api)[0]), True)
        check("PR-run record: a FAILED kernel-delta at HEAD^2 is not", pr_run_record(merge, ROOT, red_api)[0], None)
        check("PR-run record: another workflow's job is not", pr_run_record(merge, ROOT, other_wf)[0], None)
        check("PR-run record: an unreadable forge is not a record",
              pr_run_record(merge, ROOT, api_factory({}))[0], None)
    else:
        print("  ⚠️ no merge commit in this clone: the four PR-run arms were NOT run")
    check("PR-run record: a one-parent commit has no merged PR head",
          pr_run_record(git("rev-list", "--no-merges", "-n", "1", head), ROOT, api_factory({}))[0], None)
    prev_api = api_factory({
        f"repos/{REPO}/actions/runs/9": {"created_at": "2026-11-01T01:00:00Z"},
        f"{RUNS}?branch=master": {"workflow_runs": [
            {"id": 8, "path": WORKFLOW, "created_at": "2026-11-01T00:00:00Z", "status": "completed"},
            {"id": 10, "path": WORKFLOW, "created_at": "2026-11-01T02:00:00Z", "status": "completed"}]},
        f"repos/{REPO}/actions/runs/8/jobs": {"jobs": [{"name": "kernel-delta", "conclusion": "failure", "id": 88}]},
        f"repos/{REPO}/actions/jobs/88/logs": "\n".join(logged)})
    check("previous run: the run BEFORE this one (not a later one), its legacy refusal read from the log",
          previous_refusals(9, prev_api), (8, {"Tests.Vectors"}))

    n = len(arms)
    if bad:
        print(f"refusal_record selftest: FAIL ({len(bad)} of {n} arms)")
        return 1
    print(f"refusal_record selftest: CLEAN ({n} arms)")
    return 0


# ── the fixture: D381 condition (1) ──────────────────────────────────────────
def fixture(since="2026-10-14", api=gh_api):
    """Every master push CI run since `since` whose ONLY failing job is kernel-delta, derived from the forge,
    each with its exit code, refused units and verdict of record. Prints the query and the population."""
    q = f"{RUNS}?branch=master&event=push&per_page=100&created=>={since}"
    runs, page = [], 1
    while True:
        r = api(q + f"&page={page}")
        got = [x for x in r.get("workflow_runs", []) if x.get("path") == WORKFLOW]
        runs += got
        if len(r.get("workflow_runs", [])) < 100:
            break
        page += 1
    reds = [x for x in runs if x.get("conclusion") == "failure"]
    print(f"QUERY  gh api {q} (paginated), workflow {WORKFLOW}")
    print(f"POPULATION  {len(runs)} runs · {len(reds)} failure · as of the forge at this run")
    only, bad, greened = [], 0, 0
    order = sorted(runs, key=lambda r: r["created_at"])
    prev_of = {r["id"]: (order[i - 1] if i else None) for i, r in enumerate(order)}
    refused_by_run = {}

    def units_of(run):
        if run is None:
            return None
        if run["id"] not in refused_by_run:
            js = api(f"repos/{REPO}/actions/runs/{run['id']}/jobs?per_page=100")["jobs"]
            kd = [j for j in js if j.get("name") == "kernel-delta"]
            if not kd or kd[0].get("conclusion") != "failure":
                refused_by_run[run["id"]] = set()
            else:
                lg = api(f"repos/{REPO}/actions/jobs/{kd[0]['id']}/logs", raw=True).split("\n")
                refused_by_run[run["id"]] = {u for u, _ in refused_units(lg)}
        return refused_by_run[run["id"]]
    for x in sorted(reds, key=lambda r: r["created_at"]):
        jobs = api(f"repos/{REPO}/actions/runs/{x['id']}/jobs?per_page=100")["jobs"]
        failed = [j for j in jobs if j.get("conclusion") == "failure"]
        if [j["name"] for j in failed] != ["kernel-delta"]:
            continue
        log = api(f"repos/{REPO}/actions/jobs/{failed[0]['id']}/logs", raw=True).split("\n")
        m = re.findall(r"Process completed with exit code (\d+)", "\n".join(log))
        ec = m[-1] if m else "?"
        head = x["head_sha"]
        base = git("rev-parse", f"{head}^")
        units = refused_units(log)
        rec, why = record_of_step(base, head, ROOT, api)
        only.append(x["id"])
        if not rec:
            bad += 1
        print(f"  {x['id']}  {head[:9]}  {x['created_at']}  exit {ec}  "
              f"{', '.join(f'{u} ({k})' for u, k in units) or '(no unit row)'}")
        print(f"      ⇒ {rec if rec else 'NO RECORD: ' + ' · '.join(why)}")
        pv = prev_of.get(x["id"])
        pu = units_of(pv)
        prev = (pv["id"], pu) if pv is not None else (None, "no earlier run in the window")
        d_rc, d_out = decide(int(ec) if ec.isdigit() else 3, units, (rec, why), prev)
        greened += d_rc == 0
        print(f"      D381 on this run: rc {d_rc} (previous master run {prev[0]}: "
              f"{', '.join(sorted(pu)) if pu else 'refused nothing'})"
              + ("" if d_rc == 0 else f" — {d_out[0][:110] if d_out else ''}"))
    print(f"REFUSAL-ONLY  {len(only)} · with a record {len(only) - bad} · WITHOUT {bad} · "
          f"D381 would read GREEN on {greened} of {len(only)}")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    from portable import strict_flags
    strict_flags(__file__)
    if "--selftest" in sys.argv:
        sys.exit(selftest())
    if "--fixture" in sys.argv:
        sys.exit(fixture())
    print(__doc__)
    sys.exit(2)
