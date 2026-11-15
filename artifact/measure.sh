#!/bin/bash
# Times the cold Lean build inside the artifact image and records its peak memory (CAV AE: "an estimate of how long
# each non-trivial step is expected to take", and the host's memory requirement). Prints one MEASURE line per step.
# LEAN_NUM_THREADS defaults to 2, a laptop-shaped setting; the reviewer may raise it.
set -u
cd /x86lean || exit 9
: "${LEAN_NUM_THREADS:=2}"
export LEAN_NUM_THREADS
echo "MEASURE host nproc=$(nproc) mem_kb=$(awk '/MemTotal/{print $2}' /proc/meminfo) threads=$LEAN_NUM_THREADS"
# ⚠️ `lake build` runs BARE here on purpose: inside the artifact container there is no fleet lock to take, and the
# reviewer's machine runs one job. check_lean_route reads every tracked .sh and does NOT flag this line, because the
# call is prefixed by /usr/bin/time; that is a gap in the gate (STATUS-paris row 70), not an exemption it grants.
/usr/bin/time -v lake build > /tmp/build.log 2> /tmp/build.time
rc=$?
wall=$(grep -F 'Elapsed (wall clock) time' /tmp/build.time | awk '{print $NF}')
rss=$(grep -F 'Maximum resident set size' /tmp/build.time | awk '{print $NF}')
errs=$(grep -c -E ':[0-9]+:[0-9]+: error' /tmp/build.log)
echo "MEASURE lake-build rc=$rc wall=$wall max_rss_kb=$rss lean_errors=$errs"
tail -5 /tmp/build.log
exit $rc
