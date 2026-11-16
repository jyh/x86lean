#!/bin/bash
# Times the FULL differential run (scripts/run_differential.sh) inside the artifact image, stage by stage, so the
# artifact README can give "an estimate of how long each non-trivial step is expected to take" (CAV 2027 AE).
# Every line the run prints is stamped with seconds since start; each `──` stage header is also echoed as a MEASURE
# line, and the run's own exit code and comparison summary close the output.
set -u
cd /x86lean || exit 9
: "${LEAN_NUM_THREADS:=2}"
export LEAN_NUM_THREADS
t0=$(date +%s)
echo "MEASURE diff-host nproc=$(nproc) mem_kb=$(awk '/MemTotal/{print $2}' /proc/meminfo) threads=$LEAN_NUM_THREADS"
# The Lean side is built first, through the repository's own door (bare lake here: no fleet wrapper in the container).
python3 scripts/lean_route.py build > /tmp/build.log 2>&1
brc=$?          # captured at once: a $(date) in the echo below would reset $? to 0
echo "MEASURE diff-stage t=$(( $(date +%s) - t0 ))s lean-build rc=$brc"
bash scripts/run_differential.sh > /tmp/diff.log 2>&1 &
pid=$!
# Stamp the stage headers as they appear (the run writes them in order).
seen=0
while kill -0 "$pid" 2>/dev/null; do
  n=$(grep -c -F '── ' /tmp/diff.log)
  if [ "$n" -gt "$seen" ]; then
    grep -F '── ' /tmp/diff.log | sed -n "$((seen + 1)),${n}p" | while read -r h; do
      echo "MEASURE diff-stage t=$(( $(date +%s) - t0 ))s ${h}"; done
    seen=$n
  fi
  sleep 15
done
wait "$pid"; rc=$?
echo "MEASURE diff-total rc=$rc secs=$(( $(date +%s) - t0 ))"
grep -E 'oracle produced|cases|unexplained|leak|disagree' /tmp/diff.log | tail -8
tail -5 /tmp/diff.log
exit $rc
