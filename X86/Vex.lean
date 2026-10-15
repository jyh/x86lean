/-
# X86.Vex — the VEX.128 write and the YMM upper half's accessors (V3, D341)

`YmmHi.get`/`set` (copies of `Xmms.get`/`set`), the legacy setter's preservation
lemma `Xmms.set_hi`, the VEX.128 setter `Xmms.setVex128` (low half written, upper half
of that register zeroed — SDM Vol. 1 §14.1.2), and the `Cpu` helpers
`getYmmHi`/`setXmmVex128` with their frame lemmas.

⭐ A NEW MODULE, NOT AN ADDITION TO `X86.Basic`/`X86.State`, for the kernel-cost
reason recorded in `X86/YmmHi.lean`: new state and its lemmas are priced as new units.

LANE. Personal lane, public sources only.  See CLAUDE.md.
-/
import X86.State

namespace X86

namespace YmmHi

/-- Read bits 255:128 of one YMM register.  A copy of `Xmms.get`, field for
field, so the two cost the kernel the same. -/
def get (ys : YmmHi) : XmmReg → BitVec 128
  | .x0 => ys.hi0   | .x1 => ys.hi1   | .x2  => ys.hi2   | .x3  => ys.hi3
  | .x4 => ys.hi4   | .x5 => ys.hi5   | .x6  => ys.hi6   | .x7  => ys.hi7
  | .x8 => ys.hi8   | .x9 => ys.hi9   | .x10 => ys.hi10  | .x11 => ys.hi11
  | .x12 => ys.hi12 | .x13 => ys.hi13 | .x14 => ys.hi14  | .x15 => ys.hi15

/-- Write bits 255:128 of one YMM register. -/
def set (ys : YmmHi) : XmmReg → BitVec 128 → YmmHi
  | .x0, v => { ys with hi0 := v }    | .x1, v => { ys with hi1 := v }
  | .x2, v => { ys with hi2 := v }    | .x3, v => { ys with hi3 := v }
  | .x4, v => { ys with hi4 := v }    | .x5, v => { ys with hi5 := v }
  | .x6, v => { ys with hi6 := v }    | .x7, v => { ys with hi7 := v }
  | .x8, v => { ys with hi8 := v }    | .x9, v => { ys with hi9 := v }
  | .x10, v => { ys with hi10 := v }  | .x11, v => { ys with hi11 := v }
  | .x12, v => { ys with hi12 := v }  | .x13, v => { ys with hi13 := v }
  | .x14, v => { ys with hi14 := v }  | .x15, v => { ys with hi15 := v }

@[simp] theorem get_set_same (ys : YmmHi) (r : XmmReg) (v : BitVec 128) :
    (ys.set r v).get r = v := by cases r <;> rfl

@[simp] theorem get_set_ne (ys : YmmHi) (r r' : XmmReg) (v : BitVec 128) (h : r ≠ r') :
    (ys.set r v).get r' = ys.get r' := by
  cases r <;> cases r' <;> first | rfl | exact absurd rfl h

end YmmHi

namespace Xmms

/-- ⭐⭐ THE LEGACY SETTER PRESERVES THE UPPER HALF — by construction, since `set`
names a low field and never `hi`.  This is the rule legacy SSE obeys (SDM Vol. 1
§14.1.2: non-VEX SSE leaves bits MAXVL−1:128 unchanged), stated as a theorem so
no existing rule needed an edit to obey it. -/
@[simp] theorem set_hi (xs : Xmms) (r : XmmReg) (v : BitVec 128) :
    (xs.set r v).hi = xs.hi := by cases r <;> rfl

/-- ⭐⭐⭐ V3 (D341) — THE VEX.128 WRITE: the low 128 bits of `r` become `v`, and
bits 255:128 of YMMr become ZERO (SDM Vol. 1 §14.1.2; Vol. 2A §2.3.10: VEX.128
zeroes MAXVL−1:128).  Every VEX.128 rule writes through this and no legacy rule
does, so the rule is chosen by which setter is called, never by a flag a rule
could forget. -/
def setVex128 (xs : Xmms) (r : XmmReg) (v : BitVec 128) : Xmms :=
  { xs.set r v with hi := xs.hi.set r 0 }

/-- The low halves after a VEX.128 write are the low halves after a legacy one.
⚠️ PROVED BY A 16-WAY SPLIT ON THE READ REGISTER ONLY, and the two lemmas below
are rewrites through it: a direct 16×16 split (the shape of `get_set_ne`) cost
the kernel as much again as `get_set_ne` itself, measured by `kernel_delta.py`
(X86.Basic +54.9 ms against a 22.5 ms budget on the first build of this file). -/
theorem setVex128_get (xs : Xmms) (r r' : XmmReg) (v : BitVec 128) :
    (xs.setVex128 r v).get r' = (xs.set r v).get r' := by cases r' <;> rfl

@[simp] theorem setVex128_get_same (xs : Xmms) (r : XmmReg) (v : BitVec 128) :
    (xs.setVex128 r v).get r = v := by rw [setVex128_get, get_set_same]

@[simp] theorem setVex128_get_ne (xs : Xmms) (r r' : XmmReg) (v : BitVec 128) (h : r ≠ r') :
    (xs.setVex128 r v).get r' = xs.get r' := by rw [setVex128_get, get_set_ne _ _ _ _ h]

@[simp] theorem setVex128_hi (xs : Xmms) (r : XmmReg) (v : BitVec 128) :
    (xs.setVex128 r v).hi = xs.hi.set r 0 := rfl

theorem setVex128_hi_same (xs : Xmms) (r : XmmReg) (v : BitVec 128) :
    (xs.setVex128 r v).hi.get r = 0 := by simp

theorem setVex128_hi_ne (xs : Xmms) (r r' : XmmReg) (v : BitVec 128) (h : r ≠ r') :
    (xs.setVex128 r v).hi.get r' = xs.hi.get r' := by simp [h]

end Xmms

namespace Cpu

/-! ### V3 (D341): the YMM upper half, and the VEX.128 write -/

/-- Read bits 255:128 of YMMr. -/
def getYmmHi (s : Cpu) (r : XmmReg) : BitVec 128 := s.xmm.hi.get r

/-- ⭐⭐⭐ THE VEX.128 WRITE: XMMr := v and bits 255:128 of YMMr := 0.  The twin of
`setXmm`, which every legacy rule calls and which PRESERVES the upper half
(`setXmm_hi`).  A VEX.128 rule calls this one; that choice is the whole rule. -/
def setXmmVex128 (s : Cpu) (r : XmmReg) (v : BitVec 128) : Cpu :=
  { s with xmm := s.xmm.setVex128 r v }

@[simp] theorem setXmm_hi (s : Cpu) (r : XmmReg) (v : BitVec 128) :
    (s.setXmm r v).xmm.hi = s.xmm.hi := by simp [setXmm]
@[simp] theorem setXmmVex128_regs (s : Cpu) (r : XmmReg) (v : BitVec 128) :
    (s.setXmmVex128 r v).regs = s.regs := rfl
@[simp] theorem setXmmVex128_rip (s : Cpu) (r : XmmReg) (v : BitVec 128) :
    (s.setXmmVex128 r v).rip = s.rip := rfl
@[simp] theorem setXmmVex128_flags (s : Cpu) (r : XmmReg) (v : BitVec 128) :
    (s.setXmmVex128 r v).flags = s.flags := rfl
@[simp] theorem setXmmVex128_mem (s : Cpu) (r : XmmReg) (v : BitVec 128) :
    (s.setXmmVex128 r v).mem = s.mem := rfl
@[simp] theorem setXmmVex128_ms (s : Cpu) (r : XmmReg) (v : BitVec 128) :
    (s.setXmmVex128 r v).ms = s.ms := rfl
@[simp] theorem setXmmVex128_mxcsr (s : Cpu) (r : XmmReg) (v : BitVec 128) :
    (s.setXmmVex128 r v).mxcsr = s.mxcsr := rfl
@[simp] theorem getXmm_setXmmVex128_same (s : Cpu) (r : XmmReg) (v : BitVec 128) :
    (s.setXmmVex128 r v).getXmm r = v := by simp [getXmm, setXmmVex128]
theorem getXmm_setXmmVex128_ne (s : Cpu) (r r' : XmmReg) (v : BitVec 128) (h : r ≠ r') :
    (s.setXmmVex128 r v).getXmm r' = s.getXmm r' := by
  simp [getXmm, setXmmVex128, Xmms.setVex128_get_ne _ _ _ _ h]
@[simp] theorem getYmmHi_setXmmVex128_same (s : Cpu) (r : XmmReg) (v : BitVec 128) :
    (s.setXmmVex128 r v).getYmmHi r = 0 := by simp [getYmmHi, setXmmVex128]
theorem getYmmHi_setXmmVex128_ne (s : Cpu) (r r' : XmmReg) (v : BitVec 128) (h : r ≠ r') :
    (s.setXmmVex128 r v).getYmmHi r' = s.getYmmHi r' := by
  simp [getYmmHi, setXmmVex128, h]
@[simp] theorem getYmmHi_setXmm (s : Cpu) (r r' : XmmReg) (v : BitVec 128) :
    (s.setXmm r v).getYmmHi r' = s.getYmmHi r' := by simp [getYmmHi]

end Cpu

end X86
