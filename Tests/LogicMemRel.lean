/-
# Tests.LogicMemRel — `MemRel`'s write clause, pinned both ways (D316, repair (c) of the kit2 read)

Its own module by D311's rule (one test module per witness family). Inside `Tests.LogicRead` the red control's
`decide` over two concrete four-step runs moved that module from 11.0 to 28.5 ms against a budget of 6. A new unit
is judged once against a ceiling measured on its own machine, instead of as a delta against a sibling's budget.

LANE. Personal lane, public sources only.
-/
import Tests.LogicRead

namespace Tests.Logic
open X86

/-! ### `MemRel`'s write clause, pinned both ways (repair (c) of the kit2 read)

`ldb` writes nothing, so `ldb_readsOnly` discharges `MemRel` by its "neither run wrote" disjunct at every
address, and `ldb1_not_readsOnly` fails through a REGISTER. Deleting or loosening `MemRel` would leave both
standing. These two witnesses need its write-then-read-back clause. -/

def stb : Program := { code := [(0x1000, ⟨.mov .b (.mem { base := some .rdi }) (.reg .rax), 2⟩)] }

/-- The state after the store, before the halt at `0x1002`. -/
def stbMid (s : Cpu) : Cpu :=
  { s with mem := s.mem.writeSize .b (s.regs.get .rdi) (s.getReg .b .rax), rip := 0x1002 }

theorem stb_run (s : Cpu) (hms : s.ms = none) (hrip : s.rip = 0x1000) :
    runP stb 2 s = (stbMid s).halt (.outsideProgram "no instruction at RIP") := by
  have hst : ¬ s.stopped = true := by simp [Cpu.stopped, hms]
  have e1 : stepP stb s = stbMid s := by
    rw [stepP_at hst (by rw [hrip]; rfl), step_mov_mem_reg .b _ .rax hms rfl]
    simp [stbMid, hrip, Ea.addr, Ea.offset]
  have hst1 : ¬ (stbMid s).stopped = true := by simp [Cpu.stopped, stbMid, hms]
  simp only [runP_succ, runP_zero, e1]
  exact stepP_off hst1 rfl

/-- ⭐ **A store reads nothing (`R = ∅`), and `MemRel` holds at the cell it wrote by its FIRST disjunct.** The two
start memories are unrelated; both runs write the same byte at `rdi`, so the end memories agree there and nowhere
else is written. -/
theorem stb_readsOnly (d0 : BitVec 64) : ReadsOnly stb (fun _ => False) (ldbPre d0) := by
  rintro s₁ ⟨h1, h2, h3⟩
  refine ⟨2, ?_, ?_⟩
  · rw [stb_run s₁ h1 h2]; simp [Cpu.halt, Cpu.stopped, stbMid, h1]
  · rintro s₂ - ⟨m, rfl⟩ - u rfl
    have e₁ := stb_run s₁ h1 h2
    have e₂ := stb_run ({ s₁ with mem := m } : Cpu) h1 h2
    refine ⟨2, ?_, ⟨(stbMid { s₁ with mem := m }).mem, ?_⟩, fun a => ?_⟩
    · rw [e₂]; simp [Cpu.halt, Cpu.stopped, stbMid, h1]
    · rw [e₂, e₁]; simp [Cpu.halt, stbMid, h1]
    · rw [e₁, e₂]
      by_cases ha : a = d0
      · subst ha; left
        simp [Cpu.halt, stbMid, h1, h3, Mem.writeSize, Mem.writeN, Size.bytes, Cpu.getReg]
      · right
        simp [Cpu.halt, stbMid, h1, h3, Mem.writeSize, Mem.writeN, Size.bytes, Mem.read_write_ne _ _ _ _ ha]

/-- Load the byte at `[rdi+1]`, store it at `[rdi]`, then clear `al`, so the END REGISTERS carry nothing of
what was read. -/
def cpb : Program := { code := [
  (0x1000, ⟨.mov .b (.reg .rax) (.mem { base := some .rdi, disp := 1 }), 3⟩),
  (0x1003, ⟨.mov .b (.mem { base := some .rdi }) (.reg .rax), 2⟩),
  (0x1005, ⟨.mov .b (.reg .rax) (.imm 0), 2⟩)] }

/-- ⛔ **THE RED CONTROL FOR THE WRITE CLAUSE.** The same two starts as `ldb1_not_readsOnly`; the end registers
now agree (`cpb_regs_agree`), so the contradiction comes from `MemRel` at `0x2000`, the cell both runs wrote
with different bytes. -/
theorem cpb_not_readsOnly : ¬ ReadsOnly cpb (fun a => a = 0x2000) (ldbPre 0x2000) := by
  intro h
  have hp1 : ldbPre 0x2000 rs1 := ⟨by decide, by decide, by decide⟩
  have hp2 : ldbPre 0x2000 rs2 := ⟨by decide, by decide, by decide⟩
  obtain ⟨n, hst, hall⟩ := h rs1 hp1
  have hag : AgreeOnMem (fun a => a = 0x2000) rs1.mem rs2.mem := by
    rintro a rfl; decide
  obtain ⟨n₂, hst₂, _, hmr⟩ := hall rs2 hp2 ⟨_, rfl⟩ hag rs2 rfl
  have e1 : runP cpb n rs1 = runP cpb 4 rs1 := Spec.stopped_witness_unique hst (by decide)
  have e2 : runP cpb n₂ rs2 = runP cpb 4 rs2 := Spec.stopped_witness_unique hst₂ (by decide)
  have := hmr 0x2000
  simp only [e1, e2] at this
  revert this; decide

/-- The control is not a register failure in disguise: `rax` and `rip` agree at the end of both runs. -/
theorem cpb_regs_agree :
    (runP cpb 4 rs1).regs.get .rax = (runP cpb 4 rs2).regs.get .rax ∧
      (runP cpb 4 rs1).rip = (runP cpb 4 rs2).rip := by decide

end Tests.Logic
