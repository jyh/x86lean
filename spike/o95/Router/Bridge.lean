/-
# Router.Bridge — byte- and dword-level facts the abstraction bridge needs (no vir import; pure Lean + x86lean).
Written private; published 2026-11-01 (SPIKE-PLAN.md). EXPERIMENT FILE: alternative proofs of one statement are kept side by side until one builds.
-/
import X86

namespace Router.Bridge
open X86

set_option maxHeartbeats 2000000 in
/-- vir's `Val.rd` reads a little-endian dword out of four `UInt8`s as a `UInt32`; x86lean's `readN` reads it out of
four `BitVec 8`s as a `BitVec 64`. The two agree (stated with the bytes as variables, so it is a fact about the
encodings and not about any buffer). -/
theorem le32 (x0 x1 x2 x3 : UInt8) :
    (x0.toUInt32 ||| (x1.toUInt32 <<< 8) ||| (x2.toUInt32 <<< 16) ||| (x3.toUInt32 <<< 24)).toBitVec.setWidth 64 =
      ((((((0 : BitVec 64) <<< 8) ||| x3.toBitVec.setWidth 64) <<< 8 ||| x2.toBitVec.setWidth 64) <<< 8
        ||| x1.toBitVec.setWidth 64) <<< 8 ||| x0.toBitVec.setWidth 64) := by
  ext i hi
  match i, hi with
  | 0, _ => simp
  | 1, _ => simp
  | 2, _ => simp
  | 3, _ => simp
  | 4, _ => simp
  | 5, _ => simp
  | 6, _ => simp
  | 7, _ => simp
  | 8, _ => simp
  | 9, _ => simp
  | 10, _ => simp
  | 11, _ => simp
  | 12, _ => simp
  | 13, _ => simp
  | 14, _ => simp
  | 15, _ => simp
  | 16, _ => simp
  | 17, _ => simp
  | 18, _ => simp
  | 19, _ => simp
  | 20, _ => simp
  | 21, _ => simp
  | 22, _ => simp
  | 23, _ => simp
  | 24, _ => simp
  | 25, _ => simp
  | 26, _ => simp
  | 27, _ => simp
  | 28, _ => simp
  | 29, _ => simp
  | 30, _ => simp
  | 31, _ => simp
  | 32, _ => simp
  | 33, _ => simp
  | 34, _ => simp
  | 35, _ => simp
  | 36, _ => simp
  | 37, _ => simp
  | 38, _ => simp
  | 39, _ => simp
  | 40, _ => simp
  | 41, _ => simp
  | 42, _ => simp
  | 43, _ => simp
  | 44, _ => simp
  | 45, _ => simp
  | 46, _ => simp
  | 47, _ => simp
  | 48, _ => simp
  | 49, _ => simp
  | 50, _ => simp
  | 51, _ => simp
  | 52, _ => simp
  | 53, _ => simp
  | 54, _ => simp
  | 55, _ => simp
  | 56, _ => simp
  | 57, _ => simp
  | 58, _ => simp
  | 59, _ => simp
  | 60, _ => simp
  | 61, _ => simp
  | 62, _ => simp
  | 63, _ => simp
  | n + 64, h => omega

/-- `trunc .d` as a remainder, the form omega can use. -/
theorem trunc_d_toNat (v : Val) : (Value.trunc .d v).toNat = v.toNat % 2 ^ 32 := by
  simp only [Value.trunc, Size.mask, BitVec.toNat_and]
  rw [show (0xFFFFFFFF : BitVec 64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- A canonical address: anything below 2^47. -/
theorem canonical_of_lt (v : BitVec 64) (h : v.toNat < 2 ^ 47) : canonical v = true := by
  simp [canonical]
  left
  bv_omega

end Router.Bridge
