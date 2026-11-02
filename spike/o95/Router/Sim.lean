/-
# Router.Sim — O95 layer B: the backend simulation in the council's shape (2026-11-02 §C), steps 1–2

STEP 1. `Fc` is the right-hand side of vir's `F_closed`, RESTATED here (vir `120c90662a3472277a64d1ebe06f2ac93bd2d541`,
`virp/VIRP/Router.lean:72`): `denote F env0 σ = Part.some (Fc σ)` is vir's theorem, checked in vir's tree. The restatement
keeps mathlib out of this spike (vir's offer @[bus], 11-02 12:16). `VStore`, `MAGIC`, `vrd32` and `VStore.dec` are
copied from `virp/VIRP/Semantics.lean` at the same sha.
STEP 2. The map from R's components to the inputs `repaired_refines_all` takes, and `entry`: under R, every one of its
hypotheses holds.
-/
import Router.RefinesAll
import Router.Layout
import Router.ByteSum

namespace Router.Sim
open X86 Router.Refines Router.Layout

/-! ## Step 1: vir's closed form, restated -/
inductive Code | truncated | unauthOrRate deriving DecidableEq
inductive Label | emit (off : Nat) | drop (c : Code) deriving DecidableEq

structure VStore where
  wire   : List Int
  bucket : Int → Nat
  acl    : Int → Int → Bool

def MAGIC : Int := 0x4D534731

def vrd32 (w : List Int) (o : Nat) : Int :=
  w.getD o 0 + 256 * w.getD (o + 1) 0 + 65536 * w.getD (o + 2) 0 + 16777216 * w.getD (o + 3) 0

def VStore.dec (σ : VStore) (p : Int) : VStore :=
  { σ with bucket := fun q => if q = p then σ.bucket q - 1 else σ.bucket q }

/-- `F_closed`'s right-hand side (vir 120c90662). -/
def Fc (σ : VStore) : VStore × Label :=
  if (σ.wire.length : Int) ≥ 24 then
    (if vrd32 σ.wire 0 = MAGIC ∧ σ.acl (vrd32 σ.wire 4) (vrd32 σ.wire 8) = true ∧ 1 ≤ σ.bucket (vrd32 σ.wire 4)
     then (σ.dec (vrd32 σ.wire 4), Label.emit 24) else (σ, Label.drop .unauthOrRate))
  else (σ, Label.drop .truncated)

/-! ## Step 2: the old inputs, and R ⇒ every hypothesis of `repaired_refines_all` -/
def toBuf (w : List Int) : ByteArray := ByteArray.mk (w.map fun x => UInt8.ofNat x.toNat).toArray
def toSt (b : Int → Nat) : VIR.State := fun p => (b p.toNat : Int)
def toAcl (a : Int → Int → Bool) : VIR.Principal → VIR.TopicId → Bool := fun p t => a p.toNat t.toNat

theorem toBuf_get (w : List Int) (i : Nat) (h : i < w.length) :
    (toBuf w).get! i = UInt8.ofNat (w[i]).toNat := by
  simp [toBuf, ByteArray.get!, h]

/-- Under R, all of `repaired_refines_all`'s hypotheses hold, at `toBuf`, `toSt`, `toAcl`. -/
theorem entry {w : List Int} {b : Int → Nat} {a : Int → Int → Bool} {s : Cpu} (hR : Rel w b a s) :
    Live s ∧ s.rip = 0x1000 ∧ w.length = (s.regs.get .rsi).toNat ∧
    BufRel (toBuf w) 0 w.length s.mem (s.regs.get .rdi) ∧
    AclRelAll (toAcl a) s.mem ∧
    StRel (toSt b) s.mem (s.regs.get .rdx) := by
  refine ⟨hR.live, hR.entry, hR.len, ?_, ?_, ?_⟩
  · intro i hi
    rw [Nat.zero_add, toBuf_get w i hi, hR.wire_eq i hi]
    simp
  · intro p t
    simp only [toAcl, hR.acl_eq p t, Layout.aclBit, Router.MultiCall.aclAddr]
  · intro p
    have hb := hR.bucket_eq p
    have hl := hR.bucket_lt p
    simp only [toSt]
    rw [readSize_d, sval_widen]
    rw [readSize_d, widen_toNat] at hb
    have : ¬ 2 ^ 31 ≤ (rd32 s.mem (Refines.cell (s.regs.get .rdx) p)).toNat := by omega
    rw [if_neg this, hb]

/-! ## Step 4: the exit label agrees with `Fc`'s (V5's reading) -/

/-- VIRP's Int wire read is the old slice read's value, under R. -/
theorem vrd_eq {w : List Int} {b : Int → Nat} {a : Int → Int → Bool} {s : Cpu} (hR : Rel w b a s)
    (j : Nat) (hj : j + 4 ≤ w.length) :
    vrd32 w j = ((((VIR.Deep.Val.slice (toBuf w) 0 w.length).rd j).toP).toNat : Int) := by
  rw [rd_toP, ByteSum.le32_toNat]
  have byte : ∀ k, k < 4 → ((((toBuf w).get! (0 + j + k)).toNat : Nat) : Int) = w.getD (j + k) 0 := by
    intro k hk
    have hi : j + k < w.length := by omega
    rw [Nat.zero_add, toBuf_get w (j + k) hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
      hR.wire_eq _ hi]
    simp
  have b0 := byte 0 (by omega); have b1 := byte 1 (by omega)
  have b2 := byte 2 (by omega); have b3 := byte 3 (by omega)
  simp only [Nat.add_zero] at b0 ⊢
  simp only [vrd32]; omega

/-- The label the machine's exit address means (A.4's exits: I6's convention). -/
def exitLabel (t : Cpu) : Option Label :=
  if t.rip = 0x1040 then some (.drop .truncated)
  else if t.rip = 0x1041 ∨ t.rip = 0x1042 then some (.drop .unauthOrRate)
  else if t.rip = 0x1043 then some (.emit 24) else none

theorem sim_label (σ : VStore) (s : Cpu) (hR : Rel σ.wire σ.bucket σ.acl s) :
    ∃ n, (runP repaired n s).stopped = true ∧ exitLabel (runP repaired n s) = some (Fc σ).2 := by
  obtain ⟨hl, hrip, hlen, hbuf, hacl, hst⟩ := entry hR
  obtain ⟨n, hstop, hex⟩ := repaired_refines_all (toAcl σ.acl) s (toBuf σ.wire) 0 σ.wire.length (toSt σ.bucket)
    hl hrip hlen hbuf hacl hst (hR.hdisj _)
  refine ⟨n, hstop, ?_⟩
  rw [VIR.Deep.F_exit] at hex
  simp only [VIR.Deep.Val.len, VIR.Deep.Val.adv, VIR.Deep.Val.st] at hex
  unfold Fc
  by_cases h24 : 24 ≤ σ.wire.length
  · have c24 : (σ.wire.length : Int) ≥ 24 := by omega
    rw [if_pos h24] at hex; rw [if_pos c24]
    have e0 := vrd_eq hR 0 (by omega); have e4 := vrd_eq hR 4 (by omega); have e8 := vrd_eq hR 8 (by omega)
    generalize ((VIR.Deep.Val.slice (toBuf σ.wire) 0 σ.wire.length).rd 0).toP = M at hex e0
    generalize ((VIR.Deep.Val.slice (toBuf σ.wire) 0 σ.wire.length).rd 4).toP = P at hex e4
    generalize ((VIR.Deep.Val.slice (toBuf σ.wire) 0 σ.wire.length).rd 8).toP = T at hex e8
    have hM : (M = VIR.MAGIC) ↔ vrd32 σ.wire 0 = MAGIC := by
      rw [e0, MAGIC, ← UInt32.toNat_inj]
      have : VIR.MAGIC.toNat = 0x4D534731 := rfl
      rw [this]; omega
    have hcond : (M = VIR.MAGIC ∧ toAcl σ.acl P T = true ∧ 0 < toSt σ.bucket P) ↔
        (vrd32 σ.wire 0 = MAGIC ∧ σ.acl (vrd32 σ.wire 4) (vrd32 σ.wire 8) = true ∧ 1 ≤ σ.bucket (vrd32 σ.wire 4)) := by
      rw [hM, e4, e8]; simp only [toAcl, toSt]
      exact and_congr Iff.rfl (and_congr Iff.rfl (by omega))
    by_cases hc : vrd32 σ.wire 0 = MAGIC ∧ σ.acl (vrd32 σ.wire 4) (vrd32 σ.wire 8) = true ∧ 1 ≤ σ.bucket (vrd32 σ.wire 4)
    · rw [if_pos (hcond.mpr hc)] at hex; rw [if_pos hc]
      simp only [Exit] at hex
      simp [exitLabel, hex.1]
    · rw [if_neg (fun h => hc (hcond.mp h))] at hex; rw [if_neg hc]
      simp only [Exit] at hex
      rcases hex.1 with h | h <;> simp [exitLabel, h]
  · have c24 : ¬ (σ.wire.length : Int) ≥ 24 := by omega
    rw [if_neg h24] at hex; rw [if_neg c24]
    simp only [Exit] at hex
    simp [exitLabel, hex.1]

/-! ## Step 5: R at the post-state (`sim_one`) -/

/-- The post-state relation: the store `Fc` returns, read against the machine's FINAL memory, at the entry state's
bases (the buffer at `rdi`, the buckets at `rdx`, the ACL at its absolute base). -/
structure Post (σ : VStore) (s t : Cpu) : Prop where
  wire_eq : ∀ i, (h : i < σ.wire.length) → σ.wire[i] = ((t.mem.read (s.regs.get .rdi + BitVec.ofNat 64 i)).toNat : Int)
  bucket_eq : ∀ p : UInt32,
    (σ.bucket p.toNat : Int) = ((t.mem.readSize .d (Refines.cell (s.regs.get .rdx) p)).toNat : Int)
  bucket_lt : ∀ p : UInt32, σ.bucket p.toNat < 2 ^ 31
  acl_eq : ∀ p q : UInt32, σ.acl p.toNat q.toNat = Layout.aclBit t.mem p q

theorem post_of_same {σ : VStore} {s t : Cpu} (hR : Rel σ.wire σ.bucket σ.acl s) (hm : t.mem = s.mem) : Post σ s t :=
  ⟨fun i h => by rw [hm]; exact hR.wire_eq i h, fun p => by rw [hm]; exact hR.bucket_eq p, hR.bucket_lt,
   fun p q => by rw [hm]; exact hR.acl_eq p q⟩

/-- A dword value whose signed reading is non-negative is its unsigned reading. -/
theorem toNat_of_sval {x : UInt32} {v : Int} (h : v = Value.sval .d (x.toBitVec.setWidth 64)) (hv : 0 ≤ v) :
    v = (x.toNat : Int) ∧ x.toNat < 2 ^ 31 := by
  rw [sval_widen] at h
  have := x.toNat_lt
  split at h <;> omega

theorem sim_one (σ : VStore) (s : Cpu) (hR : Rel σ.wire σ.bucket σ.acl s) :
    ∃ n, (runP repaired n s).stopped = true ∧ exitLabel (runP repaired n s) = some (Fc σ).2 ∧
      Post (Fc σ).1 s (runP repaired n s) := by
  obtain ⟨hl, hrip, hlen, hbuf, hacl, hst⟩ := entry hR
  obtain ⟨n, hstop, hex⟩ := repaired_refines_all (toAcl σ.acl) s (toBuf σ.wire) 0 σ.wire.length (toSt σ.bucket)
    hl hrip hlen hbuf hacl hst (hR.hdisj _)
  refine ⟨n, hstop, ?_⟩
  generalize runP repaired n s = t at hex ⊢
  rw [VIR.Deep.F_exit] at hex
  simp only [VIR.Deep.Val.len, VIR.Deep.Val.adv, VIR.Deep.Val.st] at hex
  unfold Fc
  by_cases h24 : 24 ≤ σ.wire.length
  · have c24 : (σ.wire.length : Int) ≥ 24 := by omega
    rw [if_pos h24] at hex; rw [if_pos c24]
    have e0 := vrd_eq hR 0 (by omega); have e4 := vrd_eq hR 4 (by omega); have e8 := vrd_eq hR 8 (by omega)
    generalize ((VIR.Deep.Val.slice (toBuf σ.wire) 0 σ.wire.length).rd 0).toP = M at hex e0
    generalize ((VIR.Deep.Val.slice (toBuf σ.wire) 0 σ.wire.length).rd 4).toP = P at hex e4
    generalize ((VIR.Deep.Val.slice (toBuf σ.wire) 0 σ.wire.length).rd 8).toP = T at hex e8
    have hM : (M = VIR.MAGIC) ↔ vrd32 σ.wire 0 = MAGIC := by
      rw [e0, MAGIC, ← UInt32.toNat_inj]
      have : VIR.MAGIC.toNat = 0x4D534731 := rfl
      rw [this]; omega
    have hcond : (M = VIR.MAGIC ∧ toAcl σ.acl P T = true ∧ 0 < toSt σ.bucket P) ↔
        (vrd32 σ.wire 0 = MAGIC ∧ σ.acl (vrd32 σ.wire 4) (vrd32 σ.wire 8) = true ∧ 1 ≤ σ.bucket (vrd32 σ.wire 4)) := by
      rw [hM, e4, e8]; simp only [toAcl, toSt]
      exact and_congr Iff.rfl (and_congr Iff.rfl (by omega))
    by_cases hc : vrd32 σ.wire 0 = MAGIC ∧ σ.acl (vrd32 σ.wire 4) (vrd32 σ.wire 8) = true ∧ 1 ≤ σ.bucket (vrd32 σ.wire 4)
    · rw [if_pos (hcond.mpr hc)] at hex; rw [if_pos hc]
      simp only [Exit] at hex
      obtain ⟨hr, -, -, -, -, hst', hmem⟩ := hex
      refine ⟨by simp [exitLabel, hr], ?_⟩
      have hfr : AgreeOutside (Region (Refines.cell (s.regs.get .rdx) P) 4) s.mem t.mem := by
        rw [hmem]; exact agreeOutside_writeSize (agreeOutside_rfl _ _) .d _ _ (fun i hi => ⟨i, hi, rfl⟩)
      rw [e4]
      refine ⟨fun i h => ?_, fun p => ?_, fun p => ?_, fun p q => ?_⟩
      · rw [← hfr _ (hR.hdisj P i h)]; exact hR.wire_eq i h
      · have hv := hst' p
        rw [readSize_d] at hv ⊢; rw [widen_toNat]
        simp only [VStore.dec, VIR.decTokens, toSt] at hv ⊢
        have hb1 := hc.2.2; rw [e4] at hb1
        by_cases hp : p = P
        · subst hp; simp only [if_true] at hv ⊢
          have := (toNat_of_sval hv (by omega)).1; omega
        · have hpn : ((p.toNat : Nat) : Int) ≠ ((P.toNat : Nat) : Int) := by
            intro e; exact hp (UInt32.toNat_inj.mp (by omega))
          simp only [hp, if_false, hpn] at hv ⊢
          exact (toNat_of_sval hv (by omega)).1
      · simp only [VStore.dec]; have := hR.bucket_lt p; split <;> omega
      · simp only [VStore.dec, Layout.aclBit]; rw [← hfr _ (hR.hacw P p q)]; exact hR.acl_eq p q
    · rw [if_neg (fun h => hc (hcond.mp h))] at hex; rw [if_neg hc]
      simp only [Exit] at hex
      refine ⟨?_, post_of_same hR hex.2⟩
      rcases hex.1 with h | h <;> simp [exitLabel, h]
  · have c24 : ¬ (σ.wire.length : Int) ≥ 24 := by omega
    rw [if_neg h24] at hex; rw [if_neg c24]
    simp only [Exit] at hex
    exact ⟨by simp [exitLabel, hex.1], post_of_same hR hex.2⟩

end Router.Sim
