/-
# Tests.AnchorsVex — V3 (D341): the VEX.128 register twins, characterized

Three kinds of statement, in a module of their own so their kernel cost is a NEW unit
(`scripts/kernel_ceilings.txt`), the arm (A) rule the vector batches follow:

1. STEP EQUATIONS. Each VEX.128 twin writes `setXmmVex128 dst (legacy value)` and RIP, and
   nothing else; the legacy value takes VEX.vvvv's `src1` in the place the legacy form gives
   its destination.
2. THE UPPER-HALF RULE, BOTH DIRECTIONS. A VEX.128 twin leaves bits 255:128 of its destination's
   YMM register ZERO and every other register's upper half unchanged; the legacy `vmov`/`vbin`
   leave every upper half unchanged (SDM Vol. 1 §14.1.2).
3. SDM ANCHORS, by `decide` on concrete values, at the places the twins are easiest to get
   wrong: VPANDN complements SRC1, VPCMPGTB is SIGNED and asks SRC1 > SRC2, VPSUBD subtracts
   SRC2 FROM SRC1, VMOVDDUP duplicates the LOW quadword — each with a non-zero upper half in
   the pre-state, so the zeroing is visible.

The differential (D341's result paragraph) is the referee; these are what a proof downstream
can use without running it.

LANE. Personal lane, public sources only.
-/
import X86

namespace X86.Tests.Vex
open X86

variable {s : Cpu} {len : Nat}

/-! ## 1. Step equations -/

theorem step_vexmov (k : VMovKind) (d s' : XmmReg) (h : Live s) :
    step ⟨.vex (.vexmov k d s'), len⟩ s =
      { s with xmm := s.xmm.setVex128 d (s.getXmm s'),
               rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.stopped, Cpu.setXmmVex128, Cpu.setRip, Cpu.getXmm]

theorem step_vexddup (d s' : XmmReg) (h : Live s) :
    step ⟨.vex (.vexddup d s'), len⟩ s =
      { s with xmm := s.xmm.setVex128 d
                 (((((s.getXmm s').setWidth 64).setWidth 128) <<< 64)
                   ||| (((s.getXmm s').setWidth 64).setWidth 128)),
               rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.stopped, Cpu.setXmmVex128, Cpu.setRip, Cpu.getXmm]

theorem step_vexbin (k : VBinKind) (d s1 s2 : XmmReg) (h : Live s) (hk : k.vexTaken = true) :
    step ⟨.vex (.vexbin k d s1 s2), len⟩ s =
      { s with xmm := s.xmm.setVex128 d (vbinApply k (s.getXmm s1) (s.getXmm s2)),
               rip := s.rip + BitVec.ofNat 64 len } := by
  simp [step, h, Cpu.stopped, hk, Cpu.setXmmVex128, Cpu.setRip, Cpu.getXmm]

/-- A kind whose VEX twin is not taken is REFUSED, never given a semantics. -/
theorem step_vexbin_not_taken (k : VBinKind) (d s1 s2 : XmmReg) (h : Live s)
    (hk : k.vexTaken = false) (hs : k.vexSilTaken = false) :
    (step ⟨.vex (.vexbin k d s1 s2), len⟩ s).ms.isSome = true := by
  simp [step, h, Cpu.stopped, hk, hs, Cpu.halt]

/-! ## 2. The upper-half rule, both directions -/

/-- ⭐ VEX.128 zeroes bits 255:128 of the destination's YMM register. -/
theorem vexbin_zeroes_upper (k : VBinKind) (d s1 s2 : XmmReg) (h : Live s)
    (hk : k.vexTaken = true) :
    (step ⟨.vex (.vexbin k d s1 s2), len⟩ s).getYmmHi d = 0 := by
  rw [step_vexbin k d s1 s2 h hk]; simp [Cpu.getYmmHi]

theorem vexbin_keeps_other_upper (k : VBinKind) (d s1 s2 r : XmmReg) (h : Live s)
    (hk : k.vexTaken = true) (hr : d ≠ r) :
    (step ⟨.vex (.vexbin k d s1 s2), len⟩ s).getYmmHi r = s.getYmmHi r := by
  rw [step_vexbin k d s1 s2 h hk]; simp [Cpu.getYmmHi, hr]

theorem vexmov_zeroes_upper (k : VMovKind) (d s' : XmmReg) (h : Live s) :
    (step ⟨.vex (.vexmov k d s'), len⟩ s).getYmmHi d = 0 := by
  rw [step_vexmov k d s' h]; simp [Cpu.getYmmHi]

theorem vexddup_zeroes_upper (d s' : XmmReg) (h : Live s) :
    (step ⟨.vex (.vexddup d s'), len⟩ s).getYmmHi d = 0 := by
  rw [step_vexddup d s' h]; simp [Cpu.getYmmHi]

/-- ⭐ AND THE LEGACY FORMS PRESERVE EVERY UPPER HALF, the destination's included. -/
theorem vmov_preserves_upper (k : VMovKind) (d s' : XmmReg) (h : Live s) :
    (step ⟨.vmov k d s', len⟩ s).xmm.hi = s.xmm.hi := by
  rw [step_vmov k d s' h]; simp

theorem vbin_preserves_upper (k : VBinKind) (d s' : XmmReg) (h : Live s)
    (hk : k.isMinMax = false) :
    (step ⟨.vbin k d s', len⟩ s).xmm.hi = s.xmm.hi := by
  rw [step_vbin k d s' h hk]; simp

/-- ⭐ THE TWIN, STATED: on the LOW half a VEX.128 twin computes exactly what the legacy form
computes when the legacy destination holds `src1` — for `dst ≠ src2`, since the legacy form
reads a source that IS its destination after the copy. -/
theorem vexbin_low_is_legacy (k : VBinKind) (d s1 s2 : XmmReg) (h : Live s)
    (hk : k.vexTaken = true) (hm : k.isMinMax = false) (hd : d ≠ s2) :
    (step ⟨.vex (.vexbin k d s1 s2), len⟩ s).getXmm d
      = (step ⟨.vbin k d s2, len⟩ (s.setXmm d (s.getXmm s1))).getXmm d := by
  have hl : Live (s.setXmm d (s.getXmm s1)) := by
    show (s.setXmm d (s.getXmm s1)).ms = none
    rw [Cpu.setXmm_ms]; exact h
  rw [step_vexbin k d s1 s2 h hk, step_vbin k d s2 hl hm]
  simp [Cpu.getXmm, Cpu.setXmm, Xmms.get_set_ne _ _ _ _ hd]

/-! ## 3. SDM anchors, with a non-zero upper half in the pre-state -/

/-- The pre-state: XMM0, XMM1, XMM2 given, every upper half `0xA5…` (so a zeroing is
visible), RIP 0x400000. -/
private def pre (x0 x1 x2 : BitVec 128) : Cpu :=
  let c : Cpu := (((({ rip := 0x400000, oracle := Oracle.zero } : Cpu).setXmm .x0 x0).setXmm
    .x1 x1).setXmm .x2 x2)
  let hs : YmmHi := XmmReg.all.foldl
    (fun ys r => ys.set r (0xA5A5A5A5A5A5A5A5A5A5A5A5A5A5A5A5 + BitVec.ofNat 128 r.index.val)) c.xmm.hi
  { c with xmm := { c.xmm with hi := hs } }

/-- `vpandn %xmm1, %xmm2, %xmm0` (c5e9dfc1): XMM0 := (NOT XMM2) AND XMM1 — SRC1 (vvvv = xmm2)
is complemented, not SRC2 (SDM Vol. 2B, PANDN: VPANDN `DEST ← (NOT SRC1) AND SRC2`). -/
theorem anchor_vpandn :
    let t := step ⟨.vex (.vexbin .andn .x0 .x2 .x1), 4⟩
      (pre 0x1111 0x00FF00FF00FF00FF00FF00FF00FF00FF 0x0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F)
    t.getXmm .x0 = 0x00F000F000F000F000F000F000F000F0 ∧ t.getYmmHi .x0 = 0
      ∧ t.getYmmHi .x1 = 0xA5A5A5A5A5A5A5A5A5A5A5A5A5A5A5A6 ∧ t.rip = 0x400004 := by
  decide

/-- `vpcmpgtb %xmm1, %xmm2, %xmm0`: lane := SRC1 > SRC2, SIGNED.  Byte 0: 0x01 > 0x80 (−128) ⇒ FF;
byte 1: 0x80 > 0x01 is false ⇒ 00; the rest equal ⇒ 00. -/
theorem anchor_vpcmpgtb_signed :
    let t := step ⟨.vex (.vexbin .cmpgtb .x0 .x2 .x1), 4⟩ (pre 0x77 0x0180 0x8001)
    t.getXmm .x0 = 0xFF ∧ t.getYmmHi .x0 = 0 := by
  decide

/-- `vpsubd %xmm1, %xmm2, %xmm0`: XMM0 := XMM2 − XMM1, lane-wise (SRC1 − SRC2), wrapping. -/
theorem anchor_vpsubd :
    let t := step ⟨.vex (.vexbin .subd .x0 .x2 .x1), 4⟩
      (pre 0 0x00000001000000020000000300000004 0x00000000000000050000000A00000001)
    t.getXmm .x0 = 0xFFFFFFFF0000000300000007FFFFFFFD#128 ∧ t.getYmmHi .x0 = 0 := by
  decide

/-- `vmovddup %xmm1, %xmm0`: both quadwords of XMM0 := XMM1's LOW quadword; upper half zeroed. -/
theorem anchor_vmovddup :
    let t := step ⟨.vex (.vexddup .x0 .x1), 4⟩ (pre 0 0x11112222333344445555666677778888 0)
    t.getXmm .x0 = 0x55556666777788885555666677778888 ∧ t.getYmmHi .x0 = 0
      ∧ t.getYmmHi .x1 = 0xA5A5A5A5A5A5A5A5A5A5A5A5A5A5A5A6 := by
  decide

/-- And the legacy `movddup %xmm1, %xmm0` on the same pre-state KEEPS XMM0's upper half. -/
theorem anchor_movddup_keeps_upper :
    let t := step ⟨.vddupR .x0 .x1, 4⟩ (pre 0 0x11112222333344445555666677778888 0)
    t.getXmm .x0 = 0x55556666777788885555666677778888
      ∧ t.getYmmHi .x0 = 0xA5A5A5A5A5A5A5A5A5A5A5A5A5A5A5A5 := by
  decide

end X86.Tests.Vex
