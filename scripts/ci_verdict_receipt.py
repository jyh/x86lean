#!/usr/bin/env python3
"""⭐⭐ THE CI VERDICT RECEIPT — because the runner's readings EVAPORATE and the
committed ones do not.

⚖️ **COMMISSIONED BY THE HELM, 2026-09-15, desk `OS`**, on paris's measurement of
x86lean's full run history: *"PERSIST THE VERDICT. Write each `kernel-delta`
outcome — rc, unit, delta, band, budget, and A′'s verdict in the same run — to a
committed receipt, not only to a job log GitHub will delete. Then the evidence
base accumulates instead of evaporating."*

## THE MEASUREMENT THAT MADE IT NECESSARY

Over **612** runs (paginated, never `--limit`), **261** carry a `kernel-delta`
job. The backfill of 2026-09-16, which is this file's first content:

```
  rc0                 26   the log survives and says CLEAN
  rc0~conclusion      74   the log is GONE; the job succeeded, so the gate exited 0
  rc3                  4   ALL on 2026-09-15, A′ clean in every one
  rc1                  0   a real breach has never been recorded here
  unparsed~skipped    67   · unparsed~cancelled 62 · unparsed~failure 28
```

⇒ 🔑 ***THE WHOLE rc-3 POPULATION IS ONE DAY OLD AND 39% OF THE HISTORY IS ALREADY
UNREADABLE.*** One of those four is the master push of `e5ec828` — a landing whose
red nobody had looked at until this file existed, which is the argument for it in
one line.

⇒ 🔑 ***39% OF THE EVIDENCE FOR A GATE'S BEHAVIOUR WAS ALREADY DESTROYED WHEN THE
QUESTION WAS FIRST ASKED***, and the destruction runs backwards from today — it
removes exactly the history a rule would be written on. The 404 was verified with
a control (a same-age job whose log still fetches), so the censoring is GitHub's
retention and not this instrument.

## WHAT IS *NOT* THE GAP, WHICH DECIDED THE DESIGN

⛔ **The LOCAL verdict is already committed.** Every landing writes a row to
`docs/delta-allowance-ledger.jsonl` carrying the ms verdict, the A′ verdict, the
machine and `landed_on`. Persisting it again would be a duplicate born in
agreement ([[feedback-duplicate-born-in-agreement]]).
✅ **What evaporates is the RUNNER's reading** — the one that read `rc 3` twice on
2026-09-15 while the same commit read CLEAN on the box and CLEAN in its own twin
run. That is what this file captures.

## THE REFUSAL THAT IS THE WHOLE POINT

⛔⛔ **A LOG THIS PARSER CANNOT CLASSIFY IS `unparsed`, NEVER `rc0`.** A parser
that defaulted to CLEAN would manufacture precisely the history the ruling exists
to measure — a clean base assembled from logs nobody read
([[feedback-a-classifiers-value-set-is-a-claim]]). The value set is SIX in the
FILE and eight in the SUMMARY, because the summary adds what the job's conclusion
says when the log is gone — labelled, never merged into the read classes:

```
  rc0        the log says `delta gate: CLEAN`
  rc1        the log says OVER — a real breach
  rc2        the log says REFUSED — structural, never a verdict about the change
  rc3        the log says UNMEASURABLE — the band straddles the budget
  skip       the log says `SKIP — NULL PAIR`: the gate DECLINED to measure because the
             range changes nothing `lake` reads. It exits 0 and is NOT a verdict.
  unparsed   anything else, INCLUDING a log that no longer exists (404)
  ── and in the summary only, from `effective()`:
  rc0~conclusion       the log is gone AND the job succeeded ⇒ the gate exited 0
  unparsed~<why>       the log is gone and the conclusion decides nothing
```

⚠️ `unparsed` is recorded as a ROW, not dropped. An absent log is a fact about
the population and a dropped row is an invisible one.

Usage:
  ci_verdict_receipt.py --run <id> [--out docs/ci-kernel-verdicts.jsonl]
  ci_verdict_receipt.py --backfill [--limit-runs N] [--out …]   every run that still has a log
  ci_verdict_receipt.py --summary [--out …]                     what the committed file now holds
  ci_verdict_receipt.py --selftest
"""
# ⛔ REFUSE AN UNKNOWN FLAG BEFORE ANY WORK HAPPENS — see portable.strict_flags.
if __name__ == "__main__":
    import os as _os, sys as _sys
    _sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
    from portable import strict_flags as _strict_flags
    _strict_flags(__file__)

import collections
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
REPO = "jyh/x86lean"
DEFAULT_OUT = os.path.join(ROOT, "docs", "ci-kernel-verdicts.jsonl")

# ── the classifier ──────────────────────────────────────────────────────────
# ⚠️ EACH MARKER IS A STRING THE GATE ITSELF PRINTS, quoted from `kernel_delta.py`'s
# own report path. A marker invented here would be a rule about a log format
# nobody writes.
MARKERS = (
    # ⛔⛔ `skip` COMES FIRST AND IT IS NOT A VERDICT. The gate prints this when the
    # range changes nothing `lake` reads: it DELIBERATELY DID NOT MEASURE, and exits
    # 0. Found by this file's FIRST live use on master (e488792, 2026-09-16), where
    # `effective()` would otherwise have called it `rc0~conclusion` — "the job
    # succeeded, so the gate exited 0 ⇒ CLEAN" — and written a clean verdict for a
    # run that measured nothing. ⇒ 🔑 THE REFUSAL I BUILT AGAINST UNREAD LOGS DID NOT
    # COVER A LOG THAT SAYS, IN WORDS, THAT THERE WAS NOTHING TO READ.
    ("skip", "SKIP — NULL PAIR"),
    ("rc3", "delta gate UNMEASURABLE"),
    ("rc1", "delta gate: OVER"),
    ("rc2", "delta gate: REFUSED"),
    ("rc0", "delta gate: CLEAN"),
)
TS = re.compile(r"^\d{4}-\d{2}-\d{2}T[\d:.]+Z\s?")
# the verdict table's own row shape, e.g.
#   Tests.Coverage       41650.0   43700.0   +2050.0   2631.2   4400.0   2998.8  UNMEASURABLE
ROW = re.compile(
    r"^(?P<unit>[A-Za-z][\w.]*(?: @\w+ [\w.]+| @residue)?)\s+"
    r"(?P<base>-?[\d.]+)\s+(?P<head>-?[\d.]+)\s+"
    r"(?P<delta>[-+][\d.]+)\s+(?P<band>[\d.]+)\s+(?P<range>[\d.]+)\s+"
    r"(?P<budget>[\d.]+)\s+(?P<verdict>ok|OVER|UNMEASURABLE|REFUSED)\b")


def classify(log):
    """(rc, [rows]) for one kernel-delta job log. `unparsed` when nothing matches —
    never `rc0`."""
    if log is None:
        return "unparsed", []
    rc = None
    for name, marker in MARKERS:
        if marker in log:
            rc = name
            break
    rows = []
    for line in log.splitlines():
        # ⛔ THE TIMESTAMP PREFIX IS STRIPPED AND THE MATCH STAYS ANCHORED. A job log
        # line is `2026-09-16T00:42:32.5712180Z <the tool's own line>`, so an
        # UNANCHORED search would read a unit row out of prose that merely quotes the
        # numbers — which the selftest plants. Caught by that arm, not by review.
        m = ROW.match(TS.sub("", line, count=1).lstrip())
        if m:
            g = m.groupdict()
            rows.append({"unit": g["unit"], "base_ms": float(g["base"]),
                         "head_ms": float(g["head"]), "delta_ms": float(g["delta"]),
                         "band_ms": float(g["band"]), "budget_ms": float(g["budget"]),
                         "verdict": g["verdict"]})
    return (rc or "unparsed"), rows


# ── the forge ───────────────────────────────────────────────────────────────
def gh(*args):
    r = subprocess.run(["gh", *args], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None


def jobs_of(run_id):
    out = gh("api", f"repos/{REPO}/actions/runs/{run_id}/jobs?per_page=100",
             "--jq", '.jobs[] | "\\(.name)\t\\(.conclusion)\t\\(.id)"')
    if not out:
        return {}
    return {n: (c, j) for n, c, j in (l.split("\t") for l in out.strip().splitlines())}


def run_meta(run_id):
    out = gh("api", f"repos/{REPO}/actions/runs/{run_id}",
             "--jq", "{id, name, event, head_sha, head_branch, created_at, conclusion}")
    return json.loads(out) if out else None


def job_log(job_id):
    return gh("api", f"repos/{REPO}/actions/jobs/{job_id}/logs", "--allow-escape-sequences")


def receipt_for(run_id):
    """One receipt dict for a run, or None when it carries no kernel-delta job."""
    meta = run_meta(run_id)
    if not meta:
        return None
    jobs = jobs_of(run_id)
    if "kernel-delta" not in jobs:
        return None
    kd_conc, kd_id = jobs["kernel-delta"]
    ku_conc = jobs.get("ku-delta", ("absent", None))[0]
    rc, rows = classify(job_log(kd_id))
    return {"run": int(meta["id"]), "event": meta["event"], "sha": meta["head_sha"],
            "branch": meta["head_branch"], "created_at": meta["created_at"],
            "kernel_delta_conclusion": kd_conc, "rc": rc,
            "ku_delta_conclusion": ku_conc, "units": rows,
            "source": "ci_verdict_receipt.py"}


# ── the file ────────────────────────────────────────────────────────────────
def read_out(path):
    if not os.path.exists(path):
        return []
    return [json.loads(l) for l in open(path, encoding="utf-8") if l.strip()]


def append(path, receipts):
    """⛔ KEYED BY RUN ID: re-running this never duplicates a row, and a row already
    written is never silently rewritten — a receipt is a reading, and a reading does
    not change."""
    have = {r["run"] for r in read_out(path)}
    new = [r for r in receipts if r["run"] not in have]
    if new:
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "a", encoding="utf-8") as fh:
            for r in sorted(new, key=lambda r: r["created_at"]):
                fh.write(json.dumps(r, sort_keys=True) + "\n")
    return len(new), len(receipts) - len(new)


def effective(r):
    """⭐ TWO SOURCES, NEVER COLLAPSED. The LOG is the strong one and it is used
    wherever it survives. When the blob is gone the job's CONCLUSION still carries
    something — the job fails on rc 1/2/3 and succeeds only on rc 0 — so a vanished
    log with `success` is `rc0~conclusion`, a WEAKER claim that says how it was made.
    ⛔ It is never written as plain `rc0`: a reading nobody read and a reading nobody
    could read are different facts, and this file exists because the second kind
    accumulates. [[feedback-two-readings-are-not-two-witnesses]]"""
    if r["rc"] != "unparsed":
        return r["rc"]                      # `skip` included: it is already the truth
    c = r.get("kernel_delta_conclusion")
    if c == "success":
        return "rc0~conclusion"
    if c in ("failure", "cancelled", "skipped", None):
        return f"unparsed~{c}"
    return "unparsed"


def summary(path):
    rs = read_out(path)
    if not rs:
        print(f"⛔ {os.path.relpath(path, ROOT)} holds NO rows. An empty receipt is "
              f"not evidence of a quiet gate; it is evidence of no harvest.")
        return 1
    by_rc = collections.Counter(effective(r) for r in rs)
    pairs = collections.Counter((effective(r), r["ku_delta_conclusion"]) for r in rs)
    print(f"{os.path.relpath(path, ROOT)}: {len(rs)} run(s), "
          f"{min(r['created_at'] for r in rs)} … {max(r['created_at'] for r in rs)}")
    for rc, n in sorted(by_rc.items()):
        print(f"  {rc:9} {n:>4}")
    print("  (rc, A′ in the same run):")
    for (rc, ku), n in sorted(pairs.items()):
        print(f"    {rc:9} A′={ku:<10} {n:>4}")
    rc3 = [r for r in rs if effective(r) == "rc3"]
    bad = [r for r in rc3 if r["ku_delta_conclusion"] != "success"]
    # ⚖️ THE TRIGGER IS THE HELM'S (desk OS, 2026-09-15), amended TWICE in the open:
    # first from "~5 instances" to a spread requirement, at 4 of ~5 rather than after
    # the fifth — "changing a threshold once the number has arrived is
    # indistinguishable from choosing the answer"; then from DISTINCT DAYS to a
    # DURATION, because this tool's own first summary read the same four instances as
    # 2 days (UTC) and 1 (this box): PR #22's run began 13 seconds after 00:00Z.
    # ⇒ 🔑 A CALENDAR-DAY COUNT MEASURES WHERE A MIDNIGHT FALLS, NOT WHETHER THE
    # EVIDENCE IS SPREAD. [[feedback-a-separator-that-means-two-things-is-not-a-boundary]]
    stamps = sorted(r["created_at"] for r in rc3)
    span_h = 0.0
    if len(stamps) >= 2:
        from datetime import datetime
        fmt = "%Y-%m-%dT%H:%M:%SZ"
        span_h = (datetime.strptime(stamps[-1], fmt) - datetime.strptime(stamps[0], fmt)).total_seconds() / 3600
    fires = len(rc3) >= 5 and span_h >= 48
    print(f"\n  ⏱️  desk OS re-decide trigger (helm, amended 2026-09-15 — a DURATION, not a calendar):")
    print(f"       5 rc-3 instances spanning ≥48 h first-to-last   "
          f"now {len(rc3)} over {span_h:.1f} h ⇒ {'FIRES' if fires else 'not yet'}")
    print(f"       OR A′ not clean at an rc-3 moment, even once    "
          f"now {len(bad)} ⇒ {'FIRES' if bad else 'not yet'}")
    return 0


# ── red-first ───────────────────────────────────────────────────────────────
FIXTURES = {
    "rc3": """2026-09-16T00:42:32Z UNIT                     base      head     delta   +-K*se    range   budget  VERDICT
2026-09-16T00:42:32Z Tests.Coverage        41650.0   43700.0   +2050.0   2631.2   4400.0   2998.8  UNMEASURABLE
2026-09-16T00:42:32Z ⛔ delta gate UNMEASURABLE — for the unit(s) below, this run's own uncertainty band
""",
    "rc0": """2026-09-16T00:12:14Z UNIT                     base      head     delta   +-K*se    range   budget  VERDICT
2026-09-16T00:12:14Z Tests.Anchors           929.5     985.5     +56.0     68.0    169.0    216.6  ok
2026-09-16T00:12:14Z delta gate: CLEAN
""",
    # ⚠️ SYNTHETIC, AND SAID SO: rc 1 has never occurred in this repository's whole
    # run history, so the only way to exercise the arm is to write the log the gate
    # would print. [[feedback-a-landed-corpus-cannot-measure-detection]]
    "rc1": """2026-09-16T00:12:14Z UNIT                     base      head     delta   +-K*se    range   budget  VERDICT
2026-09-16T00:12:14Z X86.Syntax              244.0     395.0    +151.0     15.6     37.0     45.6  OVER
2026-09-16T00:12:14Z delta gate: OVER
""",
    "rc2": """2026-09-16T00:12:14Z ⛔ delta gate: REFUSED — the profiler produced no reading for X86.Syntax
""",
    # quoted from master e488792's own run, not invented
    "skip": """2026-09-16T07:20:00Z ⏭️  SKIP — NULL PAIR: this range changes nothing `lake` reads, so the kernel delta is ZERO BY CONSTRUCTION and there is nothing here for this gate to read.
""",
}


def selftest():
    ok = True

    def check(name, cond):
        nonlocal ok
        print(("  ✔ " if cond else "  ✖ ") + name)
        ok = ok and bool(cond)

    for want, log in FIXTURES.items():
        rc, rows = classify(log)
        check(f"{want} log classifies as {want} (got {rc})", rc == want)
    # ⭐ THE ARM THE WHOLE DESIGN IS FOR: an unclassifiable log must NOT read clean.
    rc, _ = classify("2026-09-16T00:00:00Z Current runner version: '2.337.0'\n")
    check(f"a log with no gate line is `unparsed`, not rc0 (got {rc})", rc == "unparsed")
    rc, _ = classify(None)
    check(f"a MISSING log (404) is `unparsed`, not rc0 (got {rc})", rc == "unparsed")
    # the numbers are parsed, not merely the verdict word
    _, rows = classify(FIXTURES["rc3"])
    check("the rc3 fixture yields one unit row", len(rows) == 1)
    check("…with the delta, band and budget read off the table",
          rows and rows[0]["delta_ms"] == 2050.0 and rows[0]["band_ms"] == 2631.2
          and rows[0]["budget_ms"] == 2998.8 and rows[0]["unit"] == "Tests.Coverage")
    # ⛔ A CONTROL ON THE CONTROL: the parser must not read a row out of prose that
    # merely mentions the numbers.
    rc, rows = classify("2026-09-16T00:00:00Z a delta of +2050.0 was discussed in a comment\n")
    check("prose mentioning a delta yields NO rows and no verdict",
          rows == [] and rc == "unparsed")
    # ⭐⭐ THE ARM THIS FILE'S FIRST LIVE RUN BOUGHT: a gate that DECLINED to measure
    # must never become a clean verdict by way of its exit code.
    check("a SKIP — NULL PAIR log is `skip`, not rc0",
          effective({"rc": "skip", "kernel_delta_conclusion": "success"}) == "skip")
    check("…and it is not rc0~conclusion either, though the job succeeded",
          effective({"rc": "skip", "kernel_delta_conclusion": "success"}) != "rc0~conclusion")
    # ⭐ the two-source rule, both directions and the one that must stay weak
    check("a read log wins over the conclusion",
          effective({"rc": "rc3", "kernel_delta_conclusion": "success"}) == "rc3")
    check("a GONE log with a success conclusion is rc0~conclusion, never rc0",
          effective({"rc": "unparsed", "kernel_delta_conclusion": "success"}) == "rc0~conclusion")
    check("a GONE log with a failure conclusion stays unparsed",
          effective({"rc": "unparsed", "kernel_delta_conclusion": "failure"}).startswith("unparsed"))
    # append is keyed by run and idempotent
    import tempfile
    # ⛔ THE PREFIX IS A GATE, NOT A STYLE: `kernel_cost --selftest` requires every
    # temp call in scripts/ to name this campaign, so an orphaned directory can be
    # attributed to the seat that left it. A bare TemporaryDirectory() here turned
    # that arm red in CI on this file's first run — which is the arm working.
    with tempfile.TemporaryDirectory(prefix="x86lean-cireceipt-") as td:
        p = os.path.join(td, "r.jsonl")
        r1 = {"run": 1, "created_at": "2026-09-15T00:00:00Z", "rc": "rc3",
              "ku_delta_conclusion": "success"}
        n_new, n_dup = append(p, [r1])
        check("first append writes the row", (n_new, n_dup) == (1, 0))
        n_new, n_dup = append(p, [r1])
        check("re-appending the same run writes nothing", (n_new, n_dup) == (0, 1))
        check("the file still holds exactly one row", len(read_out(p)) == 1)
    print("✅ ci_verdict_receipt selftest: every class, both refusals, and the "
          "idempotent append" if ok else "⛔ ci_verdict_receipt selftest FAILED")
    return 0 if ok else 1


def backfill(out, limit_runs=None):
    """Every run that still carries a kernel-delta job, newest first. ⚠️ Runs whose
    log is already gone are recorded as `unparsed` rather than skipped: the hole is
    part of the measurement."""
    runs, page = [], 1
    while True:
        o = gh("api", f"repos/{REPO}/actions/runs?per_page=100&page={page}",
               "--jq", ".workflow_runs[] | .id")
        if not o or not o.strip():
            break
        got = [int(x) for x in o.strip().splitlines()]
        runs += got
        if len(got) < 100:
            break
        page += 1
    print(f"{len(runs)} run(s) over {page} page(s) — paginated, never --limit")
    if limit_runs:
        runs = runs[:limit_runs]
    receipts = []
    for i, rid in enumerate(runs, 1):
        r = receipt_for(rid)
        if r:
            receipts.append(r)
        if i % 25 == 0:
            print(f"  … {i}/{len(runs)} runs read, {len(receipts)} with a kernel-delta job",
                  flush=True)
    n_new, n_dup = append(out, receipts)
    print(f"appended {n_new} new receipt(s); {n_dup} already present")
    return summary(out)


def main():
    args = sys.argv[1:]

    def opt(name, default=None):
        return args[args.index(name) + 1] if name in args else default

    out = opt("--out", DEFAULT_OUT)
    if "--selftest" in args:
        return selftest()
    if "--summary" in args:
        return summary(out)
    if "--backfill" in args:
        lim = opt("--limit-runs")
        return backfill(out, int(lim) if lim else None)
    rid = opt("--run")
    if not rid:
        print(__doc__.strip().splitlines()[-5])
        print("⛔ --run <id>, --backfill, --summary or --selftest is required.")
        return 2
    r = receipt_for(rid)
    if r is None:
        print(f"⛔ run {rid} carries no `kernel-delta` job — nothing to record, and "
              f"that is not a clean verdict either.")
        return 2
    n_new, n_dup = append(out, [r])
    print(f"run {rid}: rc={r['rc']} A′={r['ku_delta_conclusion']} "
          f"units={len(r['units'])} ⇒ {'appended' if n_new else 'already present'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
