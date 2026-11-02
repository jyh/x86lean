/-
# Router.ByteSum — O95 layer B, its crux: four bytes OR-ed at their shifts are their little-endian sum

VIRP reads the wire as an Int sum, `rd32 w o = w[o] + 256·w[o+1] + 65536·w[o+2] + 2^24·w[o+3]`, and the machine reads
the same four bytes as a UInt32 OR of shifts (`Refines.rd32`). This is the equation between the two. No `bv_decide`
(TRUSTBASE): each OR becomes `+` by `Nat.shiftLeft_add_eq_or_of_lt`, because the partial sum is below the next shift.
-/
import Router.Bridge

namespace Router.ByteSum
theorem le32_toNat (x0 x1 x2 x3 : UInt8) :
    (x0.toUInt32 ||| (x1.toUInt32 <<< 8) ||| (x2.toUInt32 <<< 16) ||| (x3.toUInt32 <<< 24)).toNat =
      x0.toNat + 256 * x1.toNat + 65536 * x2.toNat + 16777216 * x3.toNat := by
  have h0 := x0.toNat_lt; have h1 := x1.toNat_lt; have h2 := x2.toNat_lt; have h3 := x3.toNat_lt
  have e : ∀ (x : UInt8) (k : Nat), k < 32 → x.toNat * 2 ^ k < 2 ^ 32 →
      (x.toUInt32 <<< (UInt32.ofNat k)).toNat = x.toNat * 2 ^ k := by
    intro x k hk hlt
    have hkn : (UInt32.ofNat k).toNat = k := by
      first | simp [UInt32.toNat, UInt32.ofNat, BitVec.toNat_ofNat]; omega | simp; omega | simp
    rw [UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, hkn, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hlt]
  have e1 := e x1 8 (by omega) (by omega)
  have e2 := e x2 16 (by omega) (by omega)
  have e3 := e x3 24 (by omega) (by omega)
  have q1 : (8 : UInt32) = UInt32.ofNat 8 := rfl
  have q2 : (16 : UInt32) = UInt32.ofNat 16 := rfl
  have q3 : (24 : UInt32) = UInt32.ofNat 24 := rfl
  rw [UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_or, q1, q2, q3, e1, e2, e3, UInt8.toNat_toUInt32]
  have or_add : ∀ (a b i : Nat), b < 2 ^ i → b ||| a * 2 ^ i = a * 2 ^ i + b := by
    intro a b i hb
    rw [Nat.or_comm, ← Nat.shiftLeft_eq]; exact (Nat.shiftLeft_add_eq_or_of_lt hb a).symm
  rw [or_add _ _ 8 (by omega), or_add _ _ 16 (by omega), or_add _ _ 24 (by omega)]
  omega

end Router.ByteSum
