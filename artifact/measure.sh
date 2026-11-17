#!/bin/bash
# Times the cold Lean build inside the artifact image and records its peak memory (CAV AE: "an estimate of how long
# each non-trivial step is expected to take", and the host's memory requirement). Prints one MEASURE line per step.
# LEAN_NUM_THREADS defaults to 2, a laptop-shaped setting; the reviewer may raise it.
set -u
cd /x86lean || exit 9
: "${LEAN_NUM_THREADS:=2}"
export LEAN_NUM_THREADS
echo "MEASURE host nproc=$(nproc) mem_kb=$(awk '/MemTotal/{print $2}' /proc/meminfo) threads=$LEAN_NUM_THREADS"
# Through the repository's own door (scripts/lean_route.py): inside the container there is no fleet wrapper, so it takes
# bare `lake` and says so on stderr. /usr/bin/time measures the door and every child it starts.
/usr/bin/time -v python3 scripts/lean_route.py build > /tmp/build.log 2> /tmp/build.time
rc=$?
wall=$(grep -F 'Elapsed (wall clock) time' /tmp/build.time | awk '{print $NF}')
rss=$(grep -F 'Maximum resident set size' /tmp/build.time | awk '{print $NF}')
errs=$(grep -c -E ':[0-9]+:[0-9]+: error' /tmp/build.log)
echo "MEASURE lake-build rc=$rc wall=$wall max_rss_kb=$rss lean_errors=$errs"
tail -5 /tmp/build.log
exit $rc
