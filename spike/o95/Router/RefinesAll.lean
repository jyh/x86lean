/-
# Router.RefinesAll — O95 backend simulation, layer A: `repaired_refines` with NO topic premise (vir's arm R, 2026-11-02)

The same proof as `Router.Refines.repaired_refines`, with ONE relation widened and ONE premise gone. `AclRelAll` relates
the ACL to the machine bit for EVERY u32 (sender, topic), so a topic ≥ 64 reads the aliased row the machine reads, and
`htopic` (topic < 64) is no longer needed. Its only two uses were the `AclRel` rewrite and the canonical-address bound,
which now holds from topic < 2^32 alone. The published `repaired_refines` is left exactly as it was.
-/
import Router.Refines

namespace Router.Refines
open X86

/-- `AclRel` for EVERY u32 topic (arm R): no `t < 64` guard, so aliased rows are related as the machine reads them. -/
def AclRelAll (acl : VIR.Principal → VIR.TopicId → Bool) (m : Mem) : Prop :=
  ∀ p t : UInt32,
    acl p t = (m.read (0x301d + p.toBitVec.setWidth 64 * 8 + BitVec.ofNat 64 (t.toNat / 8))).getLsbD (t.toNat % 8)

theorem repaired_refines_all (acl : VIR.Principal → VIR.TopicId → Bool) (s : Cpu)
    (buf : ByteArray) (off len : Nat) (σ : VIR.State)
    (h : Live s) (hrip : s.rip = 0x1000)
    (hlen : len = (s.regs.get .rsi).toNat)
    (hbuf : BufRel buf off len s.mem (s.regs.get .rdi))
    (hacl : AclRelAll acl s.mem)
    (hst : StRel σ s.mem (s.regs.get .rdx))
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
    generalize eT : ((VIR.Deep.Val.slice buf off len).rd 8).toP = T at hT ⊢
    have hT32 := T.toNat_lt  -- arm R: the only bound the topic carries is its own width (it replaced `hT64`)
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
      rw [hacl P T, aclBit, hbyte, htop, widen_toNat]
      simp [Mem.readSize, Size.bytes, Mem.readN, BitVec.getLsbD_setWidth]
      omega
    have hcan : canonical (aclByteA s) = true := by
      apply Bridge.canonical_of_lt
      rw [hbyte]
      have := P.toNat_lt; have e := widen_toNat P
      have : T.toNat / 8 < 2 ^ 29 := by have := T.toNat_lt; omega
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
