/-
# Tests.CoverageVexMov — V9b (D354): the VEX move memory forms' vectors, and the alignment rule no vector can test

`vexMovVectors` is a fifth vector list beside `vectors`, `vexVectors`, `vex256Vectors` and `vexMemVectors`, and
these checks are a NEW kernel unit (`scripts/kernel_ceilings.txt`), declared up front: `Tests.CoverageVexMem`
checks that every row is a binary kind, and its delta budget is a fraction of its own size.

The checks:
1. the list has 72 rows (6 kinds × 2 widths × 2 directions × 2 aligned rows, plus 3 unaligned kinds × 2 × 2 × 2
   misaligned rows);
2. every row's mnemonic is a VEX table row;
3. every row is one of the four move memory constructors, and a row of an ALIGNED kind sits at a displacement of
   zero (so at RBX = 0x2000, aligned at both widths in every pre-state): no row is a one-sided refusal;
4. no row's id is an id of another VEX list.

And the rule the differential cannot see (x86isa executes every misaligned encoding, D91, re-read at P1):
5. an aligned kind at an address that fails its width's alignment FAULTS, load and store, at both widths;
6. an unaligned kind does not fault at ANY address (the half that says `aligned` does the discriminating);
7. ⭐ the 32 is not the 16: at 0x2010 an aligned VEX.128 access runs and the same kind's VEX.256 access faults.

LANE. Personal lane, public sources only.
-/
import X86
import Tests.Vectors

namespace X86.Tests.CoverageVexMov
open X86 X86.Tests

def vexMnemonics : List String := vexTable.map (·.row.mnemonic)

/-- 1. 48 aligned rows (every kind) and 24 misaligned rows (the three unaligned kinds). -/
theorem vexmov_vectors_size : vexMovVectors.length = 72 := by decide

/-- 2. Every mnemonic is a VEX table row. -/
theorem vexmov_vectors_have_rows :
    (vexMovVectors.all fun v => vexMnemonics.contains v.mnemonic) = true := by decide

/-- The row is a move memory form, and an aligned kind's row has no displacement. -/
def movRowOk (ea : Ea) (k : VMovKind) : Bool := !k.aligned || ea.disp == 0

/-- 3. Every row is a move memory form, and no aligned kind is placed where the model faults. -/
theorem vexmov_vectors_are_moves :
    (vexMovVectors.all fun v => match v.instr.op with
      | .vex (.vexload k _ ea) | .vex (.vexstore k ea _)
      | .vex (.vexload256 k _ ea) | .vex (.vexstore256 k ea _) => movRowOk ea k
      | _ => false) = true := by decide

/-- 4. Their ids are not the other VEX lists' ids. -/
theorem vexmov_ids_new :
    (vexMovVectors.all fun v =>
      !(vexVectors.any (·.id == v.id)) && !(vex256Vectors.any (·.id == v.id))
        && !(vexMemVectors.any (·.id == v.id))) = true := by decide

/-- `alignedVex false` is the legacy `aligned16`: one rule at VEX.128, not a second one. -/
theorem alignedVex_false : alignedVex false = aligned16 := by
  funext a; simp [alignedVex, aligned16]

/-! ### 5. An aligned kind at a misaligned address faults, at its own width. -/

theorem vexload_unaligned_faults (k : VMovKind) (d : XmmReg) (ea : Ea) (len : Nat) (s : Cpu) (h : Live s)
    (hl : ea.lock = false) (hk : k.aligned = true)
    (hU : alignedVex false (ea.addr s (s.rip + BitVec.ofNat 64 len)) = false) :
    (step ⟨.vex (.vexload k d ea), len⟩ s).stopped = true := by
  simp [step, h, hl, hU, hk, Cpu.halt, Cpu.stopped, Op.lockIllegal, Op.anyLocked, VexOp.anyLocked, Op.lockable]

theorem vexstore_unaligned_faults (k : VMovKind) (r : XmmReg) (ea : Ea) (len : Nat) (s : Cpu) (h : Live s)
    (hl : ea.lock = false) (hk : k.aligned = true)
    (hU : alignedVex false (ea.addr s (s.rip + BitVec.ofNat 64 len)) = false) :
    (step ⟨.vex (.vexstore k ea r), len⟩ s).stopped = true := by
  simp [step, h, hl, hU, hk, Cpu.halt, Cpu.stopped, Op.lockIllegal, Op.anyLocked, VexOp.anyLocked, Op.lockable]

theorem vexload256_unaligned_faults (k : VMovKind) (d : XmmReg) (ea : Ea) (len : Nat) (s : Cpu) (h : Live s)
    (hl : ea.lock = false) (hk : k.aligned = true)
    (hU : alignedVex true (ea.addr s (s.rip + BitVec.ofNat 64 len)) = false) :
    (step ⟨.vex (.vexload256 k d ea), len⟩ s).stopped = true := by
  simp [step, h, hl, hU, hk, Cpu.halt, Cpu.stopped, Op.lockIllegal, Op.anyLocked, VexOp.anyLocked, Op.lockable]

theorem vexstore256_unaligned_faults (k : VMovKind) (r : XmmReg) (ea : Ea) (len : Nat) (s : Cpu) (h : Live s)
    (hl : ea.lock = false) (hk : k.aligned = true)
    (hU : alignedVex true (ea.addr s (s.rip + BitVec.ofNat 64 len)) = false) :
    (step ⟨.vex (.vexstore256 k ea r), len⟩ s).stopped = true := by
  simp [step, h, hl, hU, hk, Cpu.halt, Cpu.stopped, Op.lockIllegal, Op.anyLocked, VexOp.anyLocked, Op.lockable]

/-! ### 6. An unaligned kind runs at any address. -/

theorem vexload_unaligned_kind_runs (k : VMovKind) (d : XmmReg) (ea : Ea) (len : Nat) (s : Cpu) (h : Live s)
    (hl : ea.lock = false) (hk : k.aligned = false) :
    (step ⟨.vex (.vexload k d ea), len⟩ s).stopped = false := by
  simp [step, h, hl, hk, Cpu.setXmmVex128, Cpu.setRip, Cpu.stopped, Op.lockIllegal, Op.anyLocked,
        VexOp.anyLocked, Op.lockable]

theorem vexstore_unaligned_kind_runs (k : VMovKind) (r : XmmReg) (ea : Ea) (len : Nat) (s : Cpu) (h : Live s)
    (hl : ea.lock = false) (hk : k.aligned = false) :
    (step ⟨.vex (.vexstore k ea r), len⟩ s).stopped = false := by
  simp [step, h, hl, hk, Cpu.writeMem128, Cpu.setRip, Cpu.stopped, Op.lockIllegal, Op.anyLocked,
        VexOp.anyLocked, Op.lockable]

theorem vexload256_unaligned_kind_runs (k : VMovKind) (d : XmmReg) (ea : Ea) (len : Nat) (s : Cpu) (h : Live s)
    (hl : ea.lock = false) (hk : k.aligned = false) :
    (step ⟨.vex (.vexload256 k d ea), len⟩ s).stopped = false := by
  simp [step, h, hl, hk, Cpu.setYmm, Cpu.setRip, Cpu.stopped, Op.lockIllegal, Op.anyLocked,
        VexOp.anyLocked, Op.lockable]

theorem vexstore256_unaligned_kind_runs (k : VMovKind) (r : XmmReg) (ea : Ea) (len : Nat) (s : Cpu) (h : Live s)
    (hl : ea.lock = false) (hk : k.aligned = false) :
    (step ⟨.vex (.vexstore256 k ea r), len⟩ s).stopped = false := by
  simp [step, h, hl, hk, Cpu.writeMem128, Cpu.setRip, Cpu.stopped, Op.lockIllegal, Op.anyLocked,
        VexOp.anyLocked, Op.lockable]

/-! ### 7. The 32 is not the 16. -/

/-- 0x2010 is 16-byte aligned and not 32-byte aligned. -/
theorem alignedVex_0x2010 : alignedVex false 0x2010 = true ∧ alignedVex true 0x2010 = false := by decide

/-- At an address aligned to 16, an aligned kind's VEX.128 load RUNS. With `vexload256_unaligned_faults` at
0x2010 (`alignedVex_0x2010`), this is the pair that says the VEX.256 rule is 32 and not 16. -/
theorem vexload_aligned16_runs (k : VMovKind) (d : XmmReg) (ea : Ea) (len : Nat) (s : Cpu) (h : Live s)
    (hl : ea.lock = false)
    (hA : alignedVex false (ea.addr s (s.rip + BitVec.ofNat 64 len)) = true) :
    (step ⟨.vex (.vexload k d ea), len⟩ s).stopped = false := by
  simp [step, h, hl, hA, Cpu.setXmmVex128, Cpu.setRip, Cpu.stopped, Op.lockIllegal, Op.anyLocked,
        VexOp.anyLocked, Op.lockable]

end X86.Tests.CoverageVexMov
