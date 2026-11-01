/-
# Router.Refines — O95 step 3, layer 2: the repaired router REFINES vir's `F_exit` under I6.
Written private; published 2026-11-01 (SPIKE-PLAN.md). The specification is vir's, imported at a pinned sha (`lakefile.toml`), never copied.

THE ABSTRACTION, from an x86lean `Cpu` to `F`'s inputs (`b0 := .slice buf off len`, `st := .state σ`):
  * `len` is `%rsi` read UNSIGNED (E2's repair is exactly that this reading is the program's);
  * the buffer's bytes are memory at `%rdi + i` (`BufRel`);
  * `acl p t` is bit `t mod 8` of the byte at `ACL + 8p + t/8` (`AclRel`; the ACL table is a 64-bit row per sender);
  * `σ p` is the SIGNED dword at `%rdx + 4p + 0x3000`, read by x86lean's own `Value.sval .d` (`StRel`).
I6'S PRECONDITION, as it is used: `topic < 64` (E4), and the buffer disjoint from the CURRENT SENDER's bucket cell (the one
cell written; narrowed 2026-11-01 on vir's finding that disjointness from all 2^32 senders' cells excluded realistic layouts). ⚠️ I6 also asks
"code disjoint"; in x86lean a `Program` is not in memory, so that clause is VACUOUS here, and stated, not assumed.
The ACL table needs no disjointness: it is read before the one write.
-/
import Router.Paths
import Router.Bridge
import VIR.Exit

namespace Router.Refines
open X86

/-! ## The abstraction relations. -/
def BufRel (buf : ByteArray) (off len : Nat) (m : Mem) (base : BitVec 64) : Prop :=
  ∀ i, i < len → (buf.get! (off + i)).toBitVec = m.read (base + BitVec.ofNat 64 i)

def cell (rdx : BitVec 64) (p : UInt32) : BitVec 64 := rdx + p.toBitVec.setWidth 64 * 4 + 0x3000

def StRel (σ : VIR.State) (m : Mem) (rdx : BitVec 64) : Prop :=
  ∀ p : UInt32, σ p = Value.sval .d (m.readSize .d (cell rdx p))

def AclRel (acl : VIR.Principal → VIR.TopicId → Bool) (m : Mem) : Prop :=
  ∀ p t : UInt32, t.toNat < 64 →
    acl p t = (m.read (0x301d + p.toBitVec.setWidth 64 * 8 + BitVec.ofNat 64 (t.toNat / 8))).getLsbD (t.toNat % 8)

/-- What an exit of the machine MEANS, read against one of `F`'s outcomes (I6's convention). -/
def Exit (s t : Cpu) (p : UInt32) : VIR.Deep.DOut → Prop
  | .drop .truncated => t.rip = 0x1040 ∧ t.mem = s.mem
  | .drop .unauthOrRate => (t.rip = 0x1041 ∨ t.rip = 0x1042) ∧ t.mem = s.mem
  | .drop .badPayload => False
  | .ret (.state σ') (.slice buf' off' len') =>
      t.rip = 0x1043 ∧ t.regs.get .rax = s.regs.get .rdi + 24 ∧ t.regs.get .rdx = s.regs.get .rdx ∧
      len' = (t.regs.get .rsi).toNat ∧ BufRel buf' off' len' t.mem (t.regs.get .rax) ∧
      StRel σ' t.mem (s.regs.get .rdx) ∧
      t.mem = s.mem.writeSize .d (cell (s.regs.get .rdx) p)
        (Flags.subResult .d (s.mem.readSize .d (cell (s.regs.get .rdx) p)) (Value.trunc .d 1))
  | _ => False

/-! ## The dword bridge: vir's `rd` and x86lean's `readSize .d` are the same little-endian read. -/
def rd32 (m : Mem) (a : BitVec 64) : UInt32 :=
  (UInt8.ofBitVec (m.read a)).toUInt32 ||| ((UInt8.ofBitVec (m.read (a + 1))).toUInt32 <<< 8) |||
    ((UInt8.ofBitVec (m.read (a + 1 + 1))).toUInt32 <<< 16) |||
    ((UInt8.ofBitVec (m.read (a + 1 + 1 + 1))).toUInt32 <<< 24)

theorem readSize_d (m : Mem) (a : BitVec 64) : m.readSize .d a = (rd32 m a).toBitVec.setWidth 64 := by
  rw [rd32, Bridge.le32]
  simp [Mem.readSize, Size.bytes, Mem.readN]

theorem rd_toP (buf : ByteArray) (off len j : Nat) :
    ((VIR.Deep.Val.slice buf off len).rd j).toP =
      ((buf.get! (off + j + 0)).toUInt32 ||| ((buf.get! (off + j + 1)).toUInt32 <<< 8) |||
        ((buf.get! (off + j + 2)).toUInt32 <<< 16) ||| ((buf.get! (off + j + 3)).toUInt32 <<< 24)) := by
  simp only [VIR.Deep.Val.rd, VIR.Deep.Val.toP, Int.toNat_natCast]
  exact UInt32.ofNat_toNat

theorem rd_bridge {buf : ByteArray} {off len : Nat} {m : Mem} {base : BitVec 64}
    (hb : BufRel buf off len m base) (j : Nat) (hj : j + 4 ≤ len) :
    ((VIR.Deep.Val.slice buf off len).rd j).toP = rd32 m (base + BitVec.ofNat 64 j) := by
  rw [rd_toP, rd32]
  have e : ∀ k, k < 4 → buf.get! (off + j + k) = UInt8.ofBitVec (m.read (base + BitVec.ofNat 64 (j + k))) := by
    intro k hk
    apply UInt8.toBitVec_inj.mp
    rw [show off + j + k = off + (j + k) by omega, hb (j + k) (by omega)]
  rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega)]
  have a1 : base + BitVec.ofNat 64 (j + 1) = base + BitVec.ofNat 64 j + 1 := by bv_omega
  have a2 : base + BitVec.ofNat 64 (j + 2) = base + BitVec.ofNat 64 j + 1 + 1 := by bv_omega
  have a3 : base + BitVec.ofNat 64 (j + 3) = base + BitVec.ofNat 64 j + 1 + 1 + 1 := by bv_omega
  rw [a1, a2, a3, Nat.add_zero]

/-! ## Dword facts the conditions need (every dword here is a `UInt32` widened, so `trunc .d` is the identity). -/
theorem trunc_widen (x : UInt32) : Value.trunc .d (x.toBitVec.setWidth 64) = x.toBitVec.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [Bridge.trunc_d_toNat, BitVec.toNat_setWidth, UInt32.toNat_toBitVec]
  have := x.toNat_lt
  omega

theorem widen_toNat (x : UInt32) : (x.toBitVec.setWidth 64).toNat = x.toNat := by
  have := x.toNat_lt; simp [BitVec.toNat_setWidth]

theorem ne_of_cmp (x y : UInt32) (f : Flags) :
    Cc.eval .ne (Flags.sub .d (x.toBitVec.setWidth 64) (y.toBitVec.setWidth 64) f) = !decide (x = y) := by
  rw [cc_ne_of_sub]
  simp only [Value.isZero, Flags.subResult, Value.trunc_trunc]
  have hx := x.toNat_lt; have hy := y.toNat_lt
  by_cases hxy : x = y
  · subst hxy; simp [Value.trunc]
  · have hne : x.toNat ≠ y.toNat := fun e => hxy (UInt32.toNat_inj.mp e)
    have : Value.trunc .d (x.toBitVec.setWidth 64 - y.toBitVec.setWidth 64) ≠ 0 := by
      intro h0
      have := congrArg BitVec.toNat h0
      rw [Bridge.trunc_d_toNat, BitVec.toNat_sub, widen_toNat, widen_toNat] at this
      simp at this
      omega
    simp only [hxy, decide_false, Bool.not_false]
    simpa using this

theorem le_of_cmp0 (x : UInt32) (f : Flags) :
    Cc.eval .le (Flags.sub .d (x.toBitVec.setWidth 64) (Value.trunc .d 0) f) =
      decide (Value.sval .d (x.toBitVec.setWidth 64) ≤ 0) := by
  rw [cc_le_of_sub]
  have hx := x.toNat_lt
  have e0 : Value.trunc .d (0 : Val) = 0 := rfl
  have hs : Flags.subResult .d (x.toBitVec.setWidth 64) (Value.trunc .d 0) = x.toBitVec.setWidth 64 := by
    have e0' : Value.trunc .d (0#64) = 0#64 := rfl
    simp [e0, e0', Flags.subResult, trunc_widen]
  rw [hs]
  simp only [Flags.subOF, bne_self_eq_false, Bool.and_false, Value.isZero, Value.sval, Value.uval,
    trunc_widen, widen_toNat]
  have hz : (x.toBitVec.setWidth 64 == 0) = decide (x.toNat = 0) := by
    by_cases hz : x.toNat = 0
    · have : x.toBitVec.setWidth 64 = 0 := BitVec.eq_of_toNat_eq (by rw [widen_toNat, hz]; rfl)
      simp [this, hz]
    · have : x.toBitVec.setWidth 64 ≠ 0 := fun e => hz (by rw [← widen_toNat, e]; rfl)
      simp at this
      simp [this, hz]
  rw [hz]
  cases hm : Value.msb .d (x.toBitVec.setWidth 64)
  · simp only [Bool.bne_false, Bool.or_false, if_false, Bool.false_eq_true]
    by_cases h0 : x.toNat = 0 <;> simp [h0] <;> omega
  · simp [Size.bits]; omega

/-- The sign of a widened dword, as a comparison. -/
theorem msb_widen (x : UInt32) : Value.msb .d (x.toBitVec.setWidth 64) = decide (2 ^ 31 ≤ x.toNat) := by
  have h1 : Value.msb .d (x.toBitVec.setWidth 64) = x.toBitVec.msb := by
    simp [Value.msb, Size.signBit, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_setWidth]
  rw [h1, BitVec.msb_eq_decide]; simp

theorem sval_widen (x : UInt32) :
    Value.sval .d (x.toBitVec.setWidth 64) =
      if 2 ^ 31 ≤ x.toNat then (x.toNat : Int) - (2 ^ 32 : Int) else (x.toNat : Int) := by
  simp only [Value.sval, Value.uval, trunc_widen, widen_toNat, msb_widen, Size.bits]
  by_cases h : 2 ^ 31 ≤ x.toNat <;> simp [h]

/-- A positive count decrements without wrapping: `subl $1` on the cell is `σ p - 1`. -/
theorem sval_dec (x : UInt32) (hpos : 0 < Value.sval .d (x.toBitVec.setWidth 64)) :
    Value.sval .d (Flags.subResult .d (x.toBitVec.setWidth 64) (Value.trunc .d 1)) =
      Value.sval .d (x.toBitVec.setWidth 64) - 1 := by
  have hx := x.toNat_lt
  rw [sval_widen] at hpos ⊢
  have hlt : ¬ 2 ^ 31 ≤ x.toNat := by intro hh; simp [hh] at hpos; omega
  simp only [hlt, if_false] at hpos ⊢
  have hr : Flags.subResult .d (x.toBitVec.setWidth 64) (Value.trunc .d 1) = (x - 1).toBitVec.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [Flags.subResult, Bridge.trunc_d_toNat, widen_toNat, BitVec.toNat_sub, widen_toNat,
      show (Value.trunc .d (1 : Val)).toNat = 1 from rfl, UInt32.toNat_sub_of_le _ _ (by
        rw [UInt32.le_iff_toNat_le]; simp; omega)]
    simp; omega
  rw [hr, sval_widen, UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
  simp
  have : ¬ 2 ^ 31 ≤ x.toNat - 1 := by omega
  simp [this]; omega

set_option maxHeartbeats 4000000 in
/-- READ BACK: a dword written is the dword read. -/
theorem readSize_writeSize_same (m : Mem) (a v : BitVec 64) :
    (m.writeSize .d a v).readSize .d a = Value.trunc .d v := by
  have d1 : a + 1 ≠ a := by bv_omega
  have d2 : a + 1 + 1 ≠ a := by bv_omega
  have d3 : a + 1 + 1 + 1 ≠ a := by bv_omega
  have d21 : a + 1 + 1 ≠ a + 1 := by bv_omega
  have d31 : a + 1 + 1 + 1 ≠ a + 1 := by bv_omega
  have d32 : a + 1 + 1 + 1 ≠ a + 1 + 1 := by bv_omega
  simp only [Mem.readSize, Mem.writeSize, Size.bytes, Mem.readN, Mem.writeN]
  simp only [Mem.read_write_same, Mem.read_write_ne _ _ _ _ d1, Mem.read_write_ne _ _ _ _ d2,
    Mem.read_write_ne _ _ _ _ d3, Mem.read_write_ne _ _ _ _ d21, Mem.read_write_ne _ _ _ _ d31,
    Mem.read_write_ne _ _ _ _ d32, Mem.read_write_ne _ _ _ _ d1.symm, Mem.read_write_ne _ _ _ _ d2.symm,
    Mem.read_write_ne _ _ _ _ d3.symm, Mem.read_write_ne _ _ _ _ d21.symm, Mem.read_write_ne _ _ _ _ d31.symm,
    Mem.read_write_ne _ _ _ _ d32.symm]
  ext i hi
  match i, hi with
  | 0, _ => simp [Value.trunc, Size.mask]
  | 1, _ => simp [Value.trunc, Size.mask]
  | 2, _ => simp [Value.trunc, Size.mask]
  | 3, _ => simp [Value.trunc, Size.mask]
  | 4, _ => simp [Value.trunc, Size.mask]
  | 5, _ => simp [Value.trunc, Size.mask]
  | 6, _ => simp [Value.trunc, Size.mask]
  | 7, _ => simp [Value.trunc, Size.mask]
  | 8, _ => simp [Value.trunc, Size.mask]
  | 9, _ => simp [Value.trunc, Size.mask]
  | 10, _ => simp [Value.trunc, Size.mask]
  | 11, _ => simp [Value.trunc, Size.mask]
  | 12, _ => simp [Value.trunc, Size.mask]
  | 13, _ => simp [Value.trunc, Size.mask]
  | 14, _ => simp [Value.trunc, Size.mask]
  | 15, _ => simp [Value.trunc, Size.mask]
  | 16, _ => simp [Value.trunc, Size.mask]
  | 17, _ => simp [Value.trunc, Size.mask]
  | 18, _ => simp [Value.trunc, Size.mask]
  | 19, _ => simp [Value.trunc, Size.mask]
  | 20, _ => simp [Value.trunc, Size.mask]
  | 21, _ => simp [Value.trunc, Size.mask]
  | 22, _ => simp [Value.trunc, Size.mask]
  | 23, _ => simp [Value.trunc, Size.mask]
  | 24, _ => simp [Value.trunc, Size.mask]
  | 25, _ => simp [Value.trunc, Size.mask]
  | 26, _ => simp [Value.trunc, Size.mask]
  | 27, _ => simp [Value.trunc, Size.mask]
  | 28, _ => simp [Value.trunc, Size.mask]
  | 29, _ => simp [Value.trunc, Size.mask]
  | 30, _ => simp [Value.trunc, Size.mask]
  | 31, _ => simp [Value.trunc, Size.mask]
  | 32, _ => simp [Value.trunc, Size.mask]
  | 33, _ => simp [Value.trunc, Size.mask]
  | 34, _ => simp [Value.trunc, Size.mask]
  | 35, _ => simp [Value.trunc, Size.mask]
  | 36, _ => simp [Value.trunc, Size.mask]
  | 37, _ => simp [Value.trunc, Size.mask]
  | 38, _ => simp [Value.trunc, Size.mask]
  | 39, _ => simp [Value.trunc, Size.mask]
  | 40, _ => simp [Value.trunc, Size.mask]
  | 41, _ => simp [Value.trunc, Size.mask]
  | 42, _ => simp [Value.trunc, Size.mask]
  | 43, _ => simp [Value.trunc, Size.mask]
  | 44, _ => simp [Value.trunc, Size.mask]
  | 45, _ => simp [Value.trunc, Size.mask]
  | 46, _ => simp [Value.trunc, Size.mask]
  | 47, _ => simp [Value.trunc, Size.mask]
  | 48, _ => simp [Value.trunc, Size.mask]
  | 49, _ => simp [Value.trunc, Size.mask]
  | 50, _ => simp [Value.trunc, Size.mask]
  | 51, _ => simp [Value.trunc, Size.mask]
  | 52, _ => simp [Value.trunc, Size.mask]
  | 53, _ => simp [Value.trunc, Size.mask]
  | 54, _ => simp [Value.trunc, Size.mask]
  | 55, _ => simp [Value.trunc, Size.mask]
  | 56, _ => simp [Value.trunc, Size.mask]
  | 57, _ => simp [Value.trunc, Size.mask]
  | 58, _ => simp [Value.trunc, Size.mask]
  | 59, _ => simp [Value.trunc, Size.mask]
  | 60, _ => simp [Value.trunc, Size.mask]
  | 61, _ => simp [Value.trunc, Size.mask]
  | 62, _ => simp [Value.trunc, Size.mask]
  | 63, _ => simp [Value.trunc, Size.mask]
  | n + 64, h => omega

/-- Two senders' bucket cells never overlap (a sender is 32 bits, so 4·p never wraps). -/
theorem cells_disjoint (rdx : BitVec 64) (p q : UInt32) (hpq : q ≠ p) :
    ∀ a, Region (cell rdx q) 4 a → ¬ Region (cell rdx p) 4 a := by
  rintro a ⟨i, hi, rfl⟩ ⟨j, hj, he⟩
  have hp := p.toNat_lt; have hq := q.toNat_lt
  have hne : q.toNat ≠ p.toNat := fun e => hpq (UInt32.toNat_inj.mp e)
  have := congrArg BitVec.toNat he
  simp only [cell] at this
  have ep := widen_toNat p; have eq := widen_toNat q
  bv_omega

/-! ## The refinement. -/
theorem repaired_refines (acl : VIR.Principal → VIR.TopicId → Bool) (s : Cpu)
    (buf : ByteArray) (off len : Nat) (σ : VIR.State)
    (h : Live s) (hrip : s.rip = 0x1000)
    (hlen : len = (s.regs.get .rsi).toNat)
    (hbuf : BufRel buf off len s.mem (s.regs.get .rdi))
    (hacl : AclRel acl s.mem)
    (hst : StRel σ s.mem (s.regs.get .rdx))
    (htopic : 24 ≤ len → ((VIR.Deep.Val.slice buf off len).rd 8).toP.toNat < 64)
    (hdisj : ∀ i, i < len → ¬ Region (cell (s.regs.get .rdx) ((VIR.Deep.Val.slice buf off len).rd 4).toP) 4
      (s.regs.get .rdi + BitVec.ofNat 64 i)) :
    ∃ n, (runP repaired n s).stopped = true ∧
      Exit s (runP repaired n s) ((VIR.Deep.Val.slice buf off len).rd 4).toP
        (VIR.Deep.den acl (VIR.Deep.F (.slice buf off len) (.state σ))) := by
  rw [VIR.Deep.F_exit]
  by_cases hl : 24 ≤ (VIR.Deep.Val.slice buf off len).len
  · simp only [VIR.Deep.Val.len] at hl
    have hge : ¬ (s.regs.get .rsi).toNat < 24 := by omega
    simp only [VIR.Deep.Val.len, hl, if_true, VIR.Deep.Val.st]
    -- the three header dwords, as the machine reads them
    have hM : ((VIR.Deep.Val.slice buf off len).rd 0).toP = rd32 s.mem (s.regs.get .rdi) := by
      have := rd_bridge hbuf 0 (by omega); simpa using this
    have hP : ((VIR.Deep.Val.slice buf off len).rd 4).toP = rd32 s.mem (s.regs.get .rdi + 4) :=
      rd_bridge hbuf 4 (by omega)
    have hT : ((VIR.Deep.Val.slice buf off len).rd 8).toP = rd32 s.mem (s.regs.get .rdi + 8) :=
      rd_bridge hbuf 8 (by omega)
    generalize ((VIR.Deep.Val.slice buf off len).rd 0).toP = M at hM ⊢
    generalize eP : ((VIR.Deep.Val.slice buf off len).rd 4).toP = P at hP hdisj ⊢
    generalize eT : ((VIR.Deep.Val.slice buf off len).rd 8).toP = T at hT htopic ⊢
    have hT64 := htopic hl
    have hsend : sender s = P.toBitVec.setWidth 64 := by
      rw [sender, W, readSize_d, trunc_widen, ← hP]
    have htop : topic s = T.toBitVec.setWidth 64 := by
      rw [topic, W, readSize_d, trunc_widen, ← hT]
    have hmag : Cc.eval .ne (Flags.sub .d (Value.trunc .d (s.mem.readSize .d (s.regs.get .rdi)))
        (Value.trunc .d 0x4D534731) s.flags) = !decide (M = VIR.MAGIC) := by
      rw [readSize_d, trunc_widen, ← hM, show Value.trunc .d (0x4D534731 : Val) = VIR.MAGIC.toBitVec.setWidth 64 from rfl,
        ne_of_cmp]
    have hsh : (Value.sext .q (topic s)).sshiftRight 3 = BitVec.ofNat 64 (T.toNat / 8) := by
      rw [htop]
      have hs0 : Value.sext .q (T.toBitVec.setWidth 64) = T.toBitVec.setWidth 64 := by
        simp [Value.sext, Value.msb, Size.signBit, BitVec.getLsbD_setWidth, Value.trunc_q]
      rw [hs0, BitVec.sshiftRight_eq_of_msb_false (by rw [BitVec.msb_eq_decide]; simp [widen_toNat]; omega)]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, widen_toNat, Nat.shiftRight_eq_div_pow]; simp; omega
    have hbyte : aclByteA s = 0x301d + P.toBitVec.setWidth 64 * 8 + BitVec.ofNat 64 (T.toNat / 8) := by
      rw [aclByteA, hsh, hsend]
    have hbit : aclBit s = acl P T := by
      rw [hacl P T hT64, aclBit, hbyte, htop, widen_toNat]
      simp [Mem.readSize, Size.bytes, Mem.readN, BitVec.getLsbD_setWidth]
      omega
    have hcan : canonical (aclByteA s) = true := by
      apply Bridge.canonical_of_lt
      rw [hbyte]
      have := P.toNat_lt; have e := widen_toNat P
      have : T.toNat / 8 < 8 := by omega
      bv_omega
    have hcell : cellA s = cell (s.regs.get .rdx) P := by rw [cellA, hsend, cell]
    have htokv : tok s = (rd32 s.mem (cell (s.regs.get .rdx) P)).toBitVec.setWidth 64 := by
      rw [tok, hcell, readSize_d]
    have hσ : σ P = Value.sval .d (tok s) := by rw [hst P, ← hcell]; rfl
    have hle : Cc.eval .le (Flags.sub .d (tok s) (Value.trunc .d 0) s.flags) = !decide (0 < σ P) := by
      rw [hσ, htokv, le_of_cmp0]
      generalize Value.sval .d ((rd32 s.mem (cell (s.regs.get .rdx) P)).toBitVec.setWidth 64) = z
      by_cases hz : 0 < z <;> simp [hz] <;> omega
    by_cases hm : M = VIR.MAGIC
    · have hm' : Cc.eval .ne (Flags.sub .d (Value.trunc .d (s.mem.readSize .d (s.regs.get .rdi)))
          (Value.trunc .d 0x4D534731) s.flags) = false := by rw [hmag, hm]; simp
      by_cases ha : acl P T = true
      · have ha' : aclBit s = true := by rw [hbit, ha]
        by_cases ht : 0 < σ P
        · -- emit_slice
          have ht' : Cc.eval .le (Flags.sub .d (tok s) (Value.trunc .d 0) s.flags) = false := by rw [hle]; simp [ht]
          obtain ⟨t1, t2, t3, t4, t5, t6⟩ := path_ok h hrip hge hm' hcan ha' ht'
          refine ⟨17, t1, ?_⟩
          simp only [hm, ha, ht, and_self, if_true, VIR.Deep.Val.adv, Exit]
          refine ⟨t2, t3, t5, ?_, ?_, ?_, ?_⟩
          · rw [t4]; have := hge; rw [BitVec.toNat_sub]; simp; omega
          · intro i hi
            have hfr : AgreeOutside (Region (cell (s.regs.get .rdx) P) 4) s.mem (runP repaired 17 s).mem := by
              rw [t6, hcell]
              exact agreeOutside_writeSize (agreeOutside_rfl _ _) .d _ _ (fun k hk => ⟨k, hk, rfl⟩)
            rw [t3, show s.regs.get .rdi + 24 + BitVec.ofNat 64 i = s.regs.get .rdi + BitVec.ofNat 64 (24 + i) by bv_omega,
              ← hfr _ (hdisj (24 + i) (by omega)), ← hbuf (24 + i) (by omega), Nat.add_assoc]
          · intro q
            unfold VIR.decTokens
            have hfr : AgreeOutside (Region (cell (s.regs.get .rdx) P) 4) s.mem (runP repaired 17 s).mem := by
              rw [t6, hcell]
              exact agreeOutside_writeSize (agreeOutside_rfl _ _) .d _ _ (fun k hk => ⟨k, hk, rfl⟩)
            by_cases hq : q = P
            · rw [hq, if_pos rfl, t6, hcell, readSize_writeSize_same, hσ]
              have ht2 : 0 < Value.sval .d ((rd32 s.mem (cell (s.regs.get .rdx) P)).toBitVec.setWidth 64) := by
                rw [← htokv, ← hσ]; exact ht
              rw [show Value.trunc .d (Flags.subResult .d (tok s) (Value.trunc .d 1)) =
                  Flags.subResult .d (tok s) (Value.trunc .d 1) by simp [Flags.subResult], htokv, sval_dec _ ht2]
            · rw [if_neg hq, hst q,
                readSize_of_agreeOutside_disjoint hfr (cells_disjoint _ P q hq) .d _ (fun k hk => ⟨k, hk, rfl⟩)]
          · rw [t6, hcell, htokv, ← readSize_d]
        · -- drop_rate_limited
          have ht' : Cc.eval .le (Flags.sub .d (tok s) (Value.trunc .d 0) s.flags) = true := by rw [hle]; simp [ht]
          obtain ⟨t1, t2, t3⟩ := path_rate_limited h hrip hge hm' hcan ha' ht'
          exact ⟨13, t1, by simp only [hm, ha, ht, and_false, if_false, Exit]; exact ⟨Or.inr t2, t3⟩⟩
      · have ha' : aclBit s = false := by rw [hbit]; simpa using ha
        obtain ⟨t1, t2, t3⟩ := path_unauth_acl h hrip hge hm' hcan ha'
        exact ⟨11, t1, by simp only [hm, ha, false_and, and_false, if_false, Exit]; exact ⟨Or.inl t2, t3⟩⟩
    · have hm' : Cc.eval .ne (Flags.sub .d (Value.trunc .d (s.mem.readSize .d (s.regs.get .rdi)))
          (Value.trunc .d 0x4D534731) s.flags) = true := by rw [hmag]; simp [hm]
      obtain ⟨t1, t2, t3⟩ := path_unauth_magic h hrip hge hm'
      exact ⟨6, t1, by simp only [hm, false_and, if_false, Exit]; exact ⟨Or.inl t2, t3⟩⟩
  · have hlt : (s.regs.get .rsi).toNat < 24 := by simp [VIR.Deep.Val.len] at hl; omega
    obtain ⟨t1, t2, t3⟩ := path_truncated h hrip hlt
    exact ⟨3, t1, by simp only [hl, if_false]; exact ⟨t2, t3⟩⟩

end Router.Refines
