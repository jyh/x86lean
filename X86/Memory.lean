/-
# X86.Memory — a TOTAL byte-addressed memory with an enumerable representation

Plan v1 §3.1 asks for "memory as a total `BitVec 64 → BitVec 8` with
little-endian helpers".  This file delivers exactly that AS THE SEMANTICS while
keeping the REPRESENTATION finite, and the difference matters enough to state:

* `Mem.read : Mem → BitVec 64 → BitVec 8` is total — every one of the 2^64
  addresses reads, with an implicit zero background.  That is what the frame
  lemmas and the characterization theorems quantify over, and it is why `step`
  needs no fault case for an ordinary load or store in the user-level subset.
* the representation is a finite association list, because the DIFFERENTIAL
  HARNESS (plan v1 §4.3) has to ENUMERATE a memory to ship it to ACL2 x86isa and
  to compare a full delta afterwards, and a function `BitVec 64 → BitVec 8`
  cannot be enumerated, shipped, or diffed.

A raw function field would have made the theorems marginally prettier and the
exit criterion — one differential run with zero unexplained disagreements —
unreachable.  The interface (`read`/`write`/`readSize`/`writeSize` plus the four
lemmas below) is the seam: P1 may swap the association list for a tree or an
array with every downstream proof untouched, which is the reason the seam is
here at P0 rather than after 300 forms are written against a concrete list.

⚠️ REPRESENTATION COST, NAMED SO NOBODY DISCOVERS IT LATER: `write` conses, so a
long run's list grows with the number of stores and `read` is O(n) in it.  For
P0's per-instruction differential runs (a handful of stores per state) this is
free.  It is a real P1 item and it is on the risk list in docs/DECISIONS.md.

LANE. Personal lane, public sources only.
-/
import X86.Value

namespace X86

/-- Byte-addressed memory: an association list read most-recent-write-first,
with an implicit zero background. -/
structure Mem where
  bytes : List (BitVec 64 × BitVec 8) := []
  deriving Repr, Inhabited, BEq

namespace Mem

/-- The empty memory: all bytes read as zero. -/
def empty : Mem := {}

/-- TOTAL read.  Every address is defined. -/
def read (m : Mem) (a : BitVec 64) : BitVec 8 :=
  match m.bytes.find? (fun p => p.1 == a) with
  | some p => p.2
  | none => 0

/-- Write one byte. -/
def write (m : Mem) (a : BitVec 64) (v : BitVec 8) : Mem :=
  { bytes := (a, v) :: m.bytes }

@[simp] theorem read_write_same (m : Mem) (a : BitVec 64) (v : BitVec 8) :
    (m.write a v).read a = v := by
  simp [read, write]

@[simp] theorem read_write_ne (m : Mem) (a a' : BitVec 64) (v : BitVec 8) (h : a' ≠ a) :
    (m.write a v).read a' = m.read a' := by
  simp [read, write, h.symm]

/-! ### Little-endian multi-byte access

SDM Vol. 1 §1.3.4: the processor stores the low-order byte at the lowest
address.  `readN`/`writeN` take the byte COUNT as a `Nat` rather than a `Size`
so that the recursion is structural; `readSize`/`writeSize` are the callers'
interface and are the only names the semantics uses. -/

/-- Read `n` bytes starting at `a`, little-endian, into the low `8*n` bits of a
`Val`.  Bytes above `n` read as zero. -/
def readN (m : Mem) (a : BitVec 64) : Nat → Val
  | 0 => 0
  | n + 1 => ((m.readN (a + 1) n) <<< 8) ||| (m.read a).setWidth 64

/-- Write the low `8*n` bits of `v` to `n` bytes starting at `a`, little-endian. -/
def writeN (m : Mem) (a : BitVec 64) (v : Val) : Nat → Mem
  | 0 => m
  | n + 1 => (m.write a (v.setWidth 8)).writeN (a + 1) (v >>> 8) n

/-- Read an `sz`-wide operand. -/
def readSize (m : Mem) (sz : Size) (a : BitVec 64) : Val := m.readN a sz.bytes

/-- Write an `sz`-wide operand. -/
def writeSize (m : Mem) (sz : Size) (a : BitVec 64) (v : Val) : Mem :=
  m.writeN a v sz.bytes

/-- The ADDRESSES an `sz`-wide access touches.  The differential harness diffs
exactly this set, and the frame lemmas quantify outside it. -/
def span (sz : Size) (a : BitVec 64) : List (BitVec 64) :=
  (List.range sz.bytes).map (fun i => a + BitVec.ofNat 64 i)

@[simp] theorem span_length (sz : Size) (a : BitVec 64) : (span sz a).length = sz.bytes := by
  simp [span]

/-- A read of `sz` bytes is determined by the bytes in its own span — the
statement that makes `readSize` a function of the span alone, which is what the
harness's delta comparison assumes. -/
theorem readN_congr (m m' : Mem) (a : BitVec 64) (n : Nat)
    (h : ∀ i, i < n → m.read (a + BitVec.ofNat 64 i) = m'.read (a + BitVec.ofNat 64 i)) :
    m.readN a n = m'.readN a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have h0 : m.read a = m'.read a := by
      have := h 0 (by omega); simpa using this
    have hrest : ∀ i, i < n →
        m.read (a + 1 + BitVec.ofNat 64 i) = m'.read (a + 1 + BitVec.ofNat 64 i) := by
      intro i hi
      have := h (i + 1) (by omega)
      have e : a + BitVec.ofNat 64 (i + 1) = a + 1 + BitVec.ofNat 64 i := by
        have hs : (BitVec.ofNat 64 (i + 1)) = BitVec.ofNat 64 i + 1 := by
          apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, Nat.add_mod]
        rw [hs]; ac_rfl
      rwa [e] at this
    show ((m.readN (a + 1) n) <<< 8) ||| (m.read a).setWidth 64
       = ((m'.readN (a + 1) n) <<< 8) ||| (m'.read a).setWidth 64
    rw [h0, ih (a + 1) hrest]

end Mem
end X86
