/-
# Router.Layout — O95, the backend simulation's layout relation: the placement and its separation lemmas (P1, P2)

Council 2026-11-02 §C: the backend theorem is stated UNDER A LAYOUT RELATION between VIR's typed, region-separated
store and the machine, so the layout lives in the relation ONCE and X-F1 becomes a property of it. vir ruled arm (R)
the same day: the relation carries the ACL's aliased rows (a topic ≥ 64 reads another principal's row, as the machine
does), so the ACL region is 2^35 + 2^29 bytes, which corrects X-F1's 2^35.

This file is the PLACEMENT (where the three regions sit, each below 2^64 and pairwise disjoint) and the facts the
old proof took as hypotheses, now DERIVED from it: `hdisj` (the buffer misses the sender's cell), `hacw` (the written
cell misses the ACL table, for EVERY u32 topic) and the two caller-side facts `two_calls` assumed. It is stated over
machine addresses only, so it imports nothing of VIR's.
-/
import Router.MultiCall

namespace Router.Layout
open X86 Router.Refines Router.MultiCall

/-- The bucket array: 2^32 senders × 4 bytes, from `rdx + 0x3000`. -/
def BUCKET_SPAN : Nat := 2 ^ 34
/-- The ACL table's base (A.4's absolute address). -/
def ACL_BASE : Nat := 0x301d
/-- The ACL table's span under arm (R): 2^32 principals × 8 bytes, plus `t / 8 < 2^29` for an aliased topic. -/
def ACL_SPAN : Nat := 2 ^ 35 + 2 ^ 29

/-- Where the regions sit. Each is below 2^64 (no BitVec wrap), and they are pairwise disjoint. -/
structure Placement (rdx rdi : BitVec 64) (len : Nat) : Prop where
  bk : rdx.toNat + 0x3000 + BUCKET_SPAN ≤ 2 ^ 64
  bf : rdi.toNat + len ≤ 2 ^ 64
  acl_bk : ACL_BASE + ACL_SPAN ≤ rdx.toNat + 0x3000 ∨ rdx.toNat + 0x3000 + BUCKET_SPAN ≤ ACL_BASE
  bf_bk : rdi.toNat + len ≤ rdx.toNat + 0x3000 ∨ rdx.toNat + 0x3000 + BUCKET_SPAN ≤ rdi.toNat
  bf_acl : rdi.toNat + len ≤ ACL_BASE ∨ ACL_BASE + ACL_SPAN ≤ rdi.toNat

theorem cell_toNat (rdx : BitVec 64) (p : UInt32) (k : Nat) (hk : k < 4)
    (hbk : rdx.toNat + 0x3000 + BUCKET_SPAN ≤ 2 ^ 64) :
    (Refines.cell rdx p + BitVec.ofNat 64 k).toNat = rdx.toNat + 0x3000 + 4 * p.toNat + k := by
  have hp := p.toNat_lt; have ep := widen_toNat p
  simp only [Refines.cell, BUCKET_SPAN] at *
  bv_omega

theorem aclAddr_toNat (p t : UInt32) : (aclAddr p t).toNat = ACL_BASE + 8 * p.toNat + t.toNat / 8 := by
  have hp := p.toNat_lt; have ht := t.toNat_lt; have ep := widen_toNat p
  have et : (BitVec.ofNat 64 (t.toNat / 8)).toNat = t.toNat / 8 := by
    simp only [BitVec.toNat_ofNat]; omega
  simp only [aclAddr, ACL_BASE]
  bv_omega

/-- `hdisj`, derived: no buffer byte lies in any sender's cell. -/
theorem buf_miss_cell {rdx rdi : BitVec 64} {len : Nat} (L : Placement rdx rdi len) (p : UInt32) :
    ∀ i, i < len → ¬ Region (Refines.cell rdx p) 4 (rdi + BitVec.ofNat 64 i) := by
  intro i hi ⟨k, hk, he⟩
  have hc := cell_toNat rdx p k hk L.bk
  have hb := L.bf; have hs := L.bf_bk; have hp := p.toNat_lt
  have ei : (rdi + BitVec.ofNat 64 i).toNat = rdi.toNat + i := by bv_omega
  have := congrArg BitVec.toNat he
  rw [ei, hc] at this
  simp only [BUCKET_SPAN] at *
  omega

/-- `hacw`, derived, for EVERY u32 topic (arm R): a sender's cell misses the whole ACL table. -/
theorem cell_miss_acl {rdx rdi : BitVec 64} {len : Nat} (L : Placement rdx rdi len) (P p t : UInt32) :
    ¬ Region (Refines.cell rdx P) 4 (aclAddr p t) := by
  rintro ⟨k, hk, he⟩
  have hc := cell_toNat rdx P k hk L.bk
  have ha := aclAddr_toNat p t
  have hP := P.toNat_lt; have hp := p.toNat_lt; have ht := t.toNat_lt
  have hs := L.acl_bk
  have := congrArg BitVec.toNat he
  simp only [ACL_BASE, ACL_SPAN, BUCKET_SPAN] at *
  omega

/-- The caller-side fact `two_calls` assumed (its second premise list): the buffer misses every cell byte. -/
theorem cells_miss_buf {rdx rdi : BitVec 64} {len : Nat} (L : Placement rdx rdi len) :
    ∀ p : UInt32, ∀ k, k < 4 → ¬ Region rdi len (Refines.cell rdx p + BitVec.ofNat 64 k) := by
  intro p k hk ⟨i, hi, he⟩
  exact buf_miss_cell L p i hi ⟨k, hk, he.symm⟩

/-- The other caller-side fact: the buffer misses the whole ACL table, for every u32 topic. -/
theorem acl_miss_buf {rdx rdi : BitVec 64} {len : Nat} (L : Placement rdx rdi len) (p t : UInt32) :
    ¬ Region rdi len (aclAddr p t) := by
  rintro ⟨i, hi, he⟩
  have ha := aclAddr_toNat p t
  have hb := L.bf; have hs := L.bf_acl
  have hp := p.toNat_lt; have ht := t.toNat_lt
  have := congrArg BitVec.toNat he
  have ei : (rdi + BitVec.ofNat 64 i).toNat = rdi.toNat + i := by bv_omega
  simp only [ACL_BASE, ACL_SPAN] at *
  omega

end Router.Layout
