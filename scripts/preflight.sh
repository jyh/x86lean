#!/usr/bin/env bash
# preflight — the local gates AND master's LAST CI VERDICT, in one command.
#
# ⛔⛔ WHY THIS EXISTS, and it is a repair of my own release procedure.
#   2026-09-12: master's `build` was RED for THREE PUSHES and I did not know.
#   `690b0cf` and `201d346` both FAILED on a stale `n == 7` control arm; I found
#   that defect LOCALLY during an unrelated pass, and CI had already reported it
#   TWICE without my reading it. I then posted "Master 20319bf, green" — a sha
#   whose build had been CANCELLED and never reported at all.
#
#   THE MECHANISM WAS NOT CARELESSNESS. My habit was:
#       for g in check_*; do python3 scripts/$g.py; done
#   — a LOCAL sweep whose silence is a fact about my WORKTREE, read as a verdict
#   about ORIGIN/MASTER. Two different populations, and nothing in that loop ever
#   asked GitHub anything. Worse, the sweep passed *because I had already fixed
#   the defect locally* — a local green after a local fix says nothing about the
#   shas already on origin.
#   ⇒ 🔑 I SPENT THAT DAY FINDING "A NUMBER WITHOUT ITS POPULATION" IN DOCUMENTS
#     AND THEN RAN ONE AS MY RELEASE PROCEDURE.
#
# ⚖️ WHY IT IS THIS SHAPE (D211: a resolution is not a remedy).
#   "Remember to read CI" fails exactly when attention is elsewhere — which is
#   always, because the defect arrives while you are busy with its neighbour.
#   So the CI verdict is not a NEW habit: it is welded to the ONE I ALREADY HAVE.
#   The local sweep cannot be run without the remote verdict coming with it.
#   ⇒ THE TEST A REMEDY MUST PASS: does it still work when I am thinking about
#     something else? This one does, because there is nothing to remember.
#
# ⚖️ WHAT THIS ESTABLISHES (row `LB`, declared not repaired):
#   REACHABILITY for the local gates (each runs its own plants), and for the
#   remote half a REPORT rather than a gate: it states the last COMPLETED run's
#   per-job conclusions and refuses on a red or an absent verdict. It does NOT
#   establish that HEAD will pass — only what the last completed run said.
#   ⛔ An "unverified" HEAD is reported as UNVERIFIED, never as green: a sha whose
#     run was cancelled has NO verdict, and that is the exact hole that cost three
#     pushes. [[feedback-an-expected-red-hides-an-unexpected-one]]
set -uo pipefail
cd "$(dirname "$0")/.."
rc=0

echo "── local gates ──────────────────────────────────────────────"
for g in check_claims check_positioning_table check_citations check_coverage_prose \
         check_readme_snapshot check_readme_lean check_ci_shards check_corpus_claims; do
  if python3 "scripts/$g.py" >/dev/null 2>&1; then printf "  ok   %s\n" "$g"
  else printf "  ⛔ FAIL %s\n" "$g"; rc=1; fi
done
for a in --tree --history --messages; do
  if python3 scripts/check_private_paths.py $a >/dev/null 2>&1; then printf "  ok   private-paths %s\n" "$a"
  else printf "  ⛔ FAIL private-paths %s\n" "$a"; rc=1; fi
done

echo "── master's LAST CI VERDICT (the half my loop never asked) ───"
if ! command -v gh >/dev/null 2>&1; then
  # ⛔ A MISSING TOOL IS AN UNKNOWN VERDICT, NOT A PASS.
  echo "  ⛔ REFUSED: gh unavailable — master's verdict is UNKNOWN, not green."; exit 1
fi
head_sha=$(git rev-parse HEAD)
runs=$(gh run list --workflow CI --branch master --limit 12 \
        --json databaseId,headSha,status,conclusion 2>/dev/null) || runs=""
if [ -z "$runs" ]; then
  echo "  ⛔ REFUSED: could not reach the forge — verdict UNKNOWN, not green."; exit 1
fi
# ⛔⛔ THE DISTINCTION THAT COST THREE PUSHES: cancelled is NOT red and NOT green.
# It is NO VERDICT. A `grep` for `failure` treats it as clean, which is precisely
# how `20319bf` — whose build was cancelled — got reported by me as "green".
# ⇒ So walk back to the last run where `build` actually REACHED A CONCLUSION, and
#   report THAT, with how many shas ago it was. The useful question is not "what
#   did the newest run say" but "WHEN WAS MASTER LAST ACTUALLY CHECKED".
last_id=""; last_sha=""; last_concl=""; skipped=0
# ⛔⛔ DO NOT FILTER BY RUN STATUS. A run is `in_progress` until its SLOWEST job
# ends, while `build` may have concluded long before — so a run-level filter hides
# the freshest verdict behind an unrelated job. That is "a run's status is an OR
# over its jobs" committed inside the very script written to repair it; measured
# here when `fae2121`'s build was green while its run still showed in_progress.
# ⇒ Ask each run for the BUILD JOB's own conclusion, newest first.
for row in $(echo "$runs" | jq -r '.[]|"\(.databaseId):\(.headSha)"'); do
  id="${row%%:*}"; sha="${row##*:}"
  c=$(gh run view "$id" --json jobs --jq '[.jobs[]|select(.name=="build")][0].conclusion // empty' 2>/dev/null)
  if [ "$c" = "success" ] || [ "$c" = "failure" ]; then
    last_id="$id"; last_sha="$sha"; last_concl="$c"; break
  fi
  skipped=$((skipped+1))
done
if [ -z "$last_id" ]; then
  echo "  ⛔ REFUSED: no run in the last 12 has a CONCLUDED build — master has NO VERDICT."; exit 1
fi
echo "  last CONCLUDED build: run $last_id @ ${last_sha:0:8} ⇒ $last_concl"
[ "$skipped" -gt 0 ] && echo "  ⚠️  $skipped newer run(s) gave NO verdict (cancelled/in-flight). Not green — silent."
gh run view "$last_id" --json jobs --jq '.jobs[]|"    \(.name)=\(.conclusion)"' 2>/dev/null
if [ "$last_concl" = "failure" ]; then
  echo "  ⛔ MASTER'S LAST REAL VERDICT IS RED."; rc=1
fi
if [ "$last_sha" != "$head_sha" ]; then
  n=$(git rev-list --count "$last_sha..$head_sha" 2>/dev/null || echo "?")
  echo "  ⚠️  HEAD (${head_sha:0:8}) is $n commit(s) PAST the last verdict — UNVERIFIED, not green."
fi
exit $rc
