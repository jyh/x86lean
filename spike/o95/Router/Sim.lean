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

end Router.Sim
