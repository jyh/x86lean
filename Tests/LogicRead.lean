/-
# Tests.LogicRead — R-READ in its terminal form (D308)

Its own module by D311's rule (one test module per witness family): a new unit is judged once against a
ceiling measured on its own machine, instead of as a delta against `Tests.Logic`'s budget.

LANE. Personal lane, public sources only.
-/
import Tests.Logic

namespace Tests.Logic
open X86

/-! ### R-READ, witnessed with a load that REALLY READS (D308)

The refuters' instance used `R = ∅` on a routine with no load, which exercises the definition and never its
read path. Here a one-byte load from `[rdi]` is read-safe for `R = {rdi}`, the same load from `[rdi+1]` is
NOT (a red control, proved as a negation), and a concrete run shows the load returns the byte at `R`. -/

def ldb : Program := { code := [(0x1000, ⟨.mov .b (.reg .rax) (.mem { base := some .rdi }), 3⟩)] }

def ldb1 : Program :=
  { code := [(0x1000, ⟨.mov .b (.reg .rax) (.mem { base := some .rdi, disp := 1 }), 3⟩)] }

def ldbPre (d0 : BitVec 64) (s : Cpu) : Prop :=
  s.ms = none ∧ s.rip = 0x1000 ∧ s.regs.get .rdi = d0

/-- The state after the load, before the halt at `0x1003`. -/
def ldbMid (s : Cpu) : Cpu :=
  { s with regs := s.regs.set .rax (Value.writeView .b (s.regs.get .rax)
             (s.mem.readSize .b (s.regs.get .rdi))),
           rip := 0x1003 }

theorem ldb_run (s : Cpu) (hms : s.ms = none) (hrip : s.rip = 0x1000) :
    runP ldb 2 s = (ldbMid s).halt (.outsideProgram "no instruction at RIP") := by
  have hst : ¬ s.stopped = true := by simp [Cpu.stopped, hms]
  have e1 : stepP ldb s = ldbMid s := by
    rw [stepP_at hst (by rw [hrip]; rfl), step_mov_reg_mem .b .rax _ hms rfl]
    simp [ldbMid, hrip, Ea.addr, Ea.offset]
  have hst1 : ¬ (ldbMid s).stopped = true := by simp [Cpu.stopped, ldbMid, hms]
  simp only [runP_succ, runP_zero, e1]
  exact stepP_off hst1 rfl

/-- ⭐ **The load reads only `[rdi]`.** For EVERY start state and every second memory agreeing with the
first at `d0`, the two runs end differing in memory alone — and they do not differ in memory either,
because the routine writes nothing. -/
theorem ldb_readsOnly (d0 : BitVec 64) : ReadsOnly ldb (fun a => a = d0) (ldbPre d0) := by
  rintro s₁ ⟨h1, h2, h3⟩
  refine ⟨2, ?_, ?_⟩
  · rw [ldb_run s₁ h1 h2]; simp [Cpu.halt, Cpu.stopped, ldbMid, h1]
  · rintro s₂ - ⟨m, rfl⟩ hag u rfl
    have hread : m.read d0 = s₁.mem.read d0 := (hag d0 rfl).symm
    have e₁ := ldb_run s₁ h1 h2
    have e₂ := ldb_run ({ s₁ with mem := m } : Cpu) h1 h2
    refine ⟨2, ?_, ⟨m, ?_⟩, fun a => Or.inr ⟨?_, ?_⟩⟩
    · rw [e₂]; simp [Cpu.halt, Cpu.stopped, ldbMid, h1]
    · rw [e₂, e₁]
      simp [Cpu.halt, ldbMid, h1, h3, Mem.readSize, Mem.readN, Size.bytes, hread]
    · rw [e₁]; simp [Cpu.halt, ldbMid, h1]
    · rw [e₂]; simp [Cpu.halt, ldbMid, h1]

def rs1 : Cpu := Cpu.setReg { rip := 0x1000 } .q .rdi 0x2000
def rs2 : Cpu := { rs1 with mem := Mem.write default 0x2001 0x5A }

/-- ⛔ **THE RED CONTROL: a load from `[rdi+1]` does NOT read only `[rdi]`.** Two states agreeing at `0x2000`
and differing at `0x2001` end with different `rax`. So `ReadsOnly` can FAIL, and fails exactly where the
access leaves `R`. -/
theorem ldb1_not_readsOnly : ¬ ReadsOnly ldb1 (fun a => a = 0x2000) (ldbPre 0x2000) := by
  intro h
  have hp1 : ldbPre 0x2000 rs1 := ⟨by decide, by decide, by decide⟩
  have hp2 : ldbPre 0x2000 rs2 := ⟨by decide, by decide, by decide⟩
  obtain ⟨n, hst, hall⟩ := h rs1 hp1
  have hag : AgreeOnMem (fun a => a = 0x2000) rs1.mem rs2.mem := by
    rintro a rfl; decide
  obtain ⟨n₂, hst₂, ⟨m', hm'⟩, _⟩ := hall rs2 hp2 ⟨_, rfl⟩ hag rs2 rfl
  have e1 : runP ldb1 n rs1 = runP ldb1 2 rs1 :=
    Spec.stopped_witness_unique hst (by decide)
  have e2 : runP ldb1 n₂ rs2 = runP ldb1 2 rs2 :=
    Spec.stopped_witness_unique hst₂ (by decide)
  have := congrArg (fun c : Cpu => c.regs.get .rax) hm'
  simp only [e1, e2] at this
  revert this; decide

/-- The positive witness is not vacuous: the precondition is met, and the load returns the byte at `R`. -/
theorem ldb_reads_R : ldbPre 0x2000 rs1 ∧
    (runP ldb 2 { rs1 with mem := Mem.write default 0x2000 0x5A }).regs.get .rax = 0x5A :=
  ⟨⟨by decide, by decide, by decide⟩, by decide⟩

end Tests.Logic
