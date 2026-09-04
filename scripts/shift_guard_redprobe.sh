#!/usr/bin/env bash
# ⭐⭐⭐ P2 BATCH 13 — THE PACKED SHIFTS' COUNT GUARD, DRIVEN RED.
#
# `vshiftLane` refuses to shift when the count reaches the lane width, and the
# SDM is the reason it returns 0 / sign-fill there.  But there is a SECOND reason
# the guard cannot be removed, and it is not visible in any theorem: for the LEFT
# shift the unguarded spelling does not merely give a wrong answer, it takes the
# toolchain down.
#
#     x <<< (4294967299 : Nat)   ⇒   INTERNAL PANIC: Nat.shiftl exponent is too big
#
# 4294967299 is 2^32 + 3 — a count `psllw %xmm1,%xmm0` reads whenever the count
# register's low quadword holds it, which the differential's own pre-state sweep
# produces in quantity.  A theorem cannot state this: a declaration that panics
# does not fail to elaborate, it kills the process.  So it is a PROBE, and the
# probe PLANTS the unguarded spelling rather than describing it.
#
# ⛔ THE ASYMMETRY IS THE POINT AND IT IS WHY THIS PROBE HAS FOUR ARMS.  Lean's
# `>>>` and `sshiftRight` already saturate correctly at any count, so a model
# with the guard removed would pass EVERY `psrl` and `psra` vector and take the
# build down only on `psll` at a large register count.  A partial repair — or a
# partial removal — is invisible to a run that only checks answers.
#
# ⚠️ CHEAP ON PURPOSE (a discipline expensive to exercise gets exercised less):
# four `lake env lean` invocations over a five-line file, well under ten seconds
# in total, so it runs on every push rather than behind a flag.
set -u
cd "$(dirname "$0")/.."
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
PASS=0; FAIL=0
BIG=4294967299

say() { printf '  %s %s\n' "$1" "$2"; }
run() { lake env lean "$1" 2>&1; }

# ── ARM 1 — CONTROL: the SHIPPED model at the same huge count ANSWERS. ────────
cat > "$TMP/a1.lean" <<'EOF'
import X86
open X86
-- the count `psllw %xmm1,%xmm0` reads when xmm1's low quadword is 2^32+3
#eval (vshiftApply .sll .w16 0x81234567_89abcdef_fedcba98_76543210 4294967299 == 0)
EOF
OUT="$(run "$TMP/a1.lean")"
if [ "$OUT" = "true" ]; then
  say "✔" "control: the SHIPPED vshiftApply answers 0 at a count of $BIG"; PASS=$((PASS+1))
else
  say "⛔" "control FAILED — the shipped model did not answer at $BIG: $OUT"; FAIL=$((FAIL+1))
fi

# ── ARM 2 — the guard REMOVED from the LEFT shift: the toolchain PANICS. ──────
cat > "$TMP/a2.lean" <<'EOF'
-- `vshiftLane`'s left branch with the `cnt ≥ w` guard DELETED, which is the
-- spelling a reader reaches for.  Nothing else differs.
def lane (x : BitVec 16) (cnt : Nat) : BitVec 16 := x <<< cnt
#eval (lane 0x8123 4294967299)
EOF
OUT="$(run "$TMP/a2.lean")"
case "$OUT" in
  *"Nat.shiftl exponent is too big"*)
    say "✔" "red: the UNGUARDED left shift panics — the guard is load-bearing"; PASS=$((PASS+1));;
  *)
    say "⛔" "red arm FAILED — the unguarded left shift did NOT panic, so this"
    say " " "   probe no longer demonstrates why the guard exists: $OUT"; FAIL=$((FAIL+1));;
esac

# ── ARM 3 — and it panics in the KERNEL too, not only in the interpreter. ─────
#    This is the arm that says the guard protects the THEOREMS as well as the
#    executable: `Tests/Coverage.lean` reduces `vshiftApply` under `decide`.
cat > "$TMP/a3.lean" <<'EOF'
def x : BitVec 16 := 0x8123
example : (x <<< (4294967299 : Nat)) = 0 := by decide
EOF
OUT="$(run "$TMP/a3.lean")"
case "$OUT" in
  *"Nat.shiftl exponent is too big"*)
    say "✔" "red: it panics in the KERNEL as well, so the guard protects the theorems"; PASS=$((PASS+1));;
  *)
    say "⛔" "red arm FAILED — the kernel did not panic; the claim in vshiftLane's"
    say " " "   docstring about BOTH tiers is now false: $OUT"; FAIL=$((FAIL+1));;
esac

# ── ARM 4 — THE HELD-OUT DIRECTION.  The two RIGHT shifts must NOT panic, ─────
#    because that is what makes the defect a partial one: a build that removed
#    the guard everywhere would still pass every psrl/psra vector.  An arm that
#    only ever fires on the left shift cannot see that, so the right ones are
#    asserted to be silent IN THE SAME RUN.
cat > "$TMP/a4.lean" <<'EOF'
def x : BitVec 16 := 0x8123
#eval (x >>> (4294967299 : Nat) == 0 && x.sshiftRight 4294967299 == 0xffff)
EOF
OUT="$(run "$TMP/a4.lean")"
if [ "$OUT" = "true" ]; then
  say "✔" "held out: the two RIGHT shifts saturate at $BIG and do NOT panic"
  say " " "   ⇒ removing the guard is invisible to every psrl/psra vector"
  PASS=$((PASS+1))
else
  say "⛔" "held-out arm FAILED — a right shift no longer saturates quietly: $OUT"; FAIL=$((FAIL+1))
fi

echo
if [ "$FAIL" -eq 0 ]; then
  echo "shift-guard red probe: PASS ($PASS arms — 1 control, 2 red, 1 held out)"
  exit 0
fi
echo "⛔ shift-guard red probe: FAIL ($FAIL of $((PASS+FAIL)) arms)"
exit 1
