/-
# Router.MultiCall — O95 (b): TWO successive calls of the repaired router refine F twice, the state threaded.
PRIVATE (SPIKE-PLAN.md). The helm's (b) ruling of 2026-11-01 07:11; priced @[bus]; arm (i) of the 07:4x finding.

⛔ THE FINDING THIS FILE STATES AS HYPOTHESES (posted before building): A.4 bounds no sender, so the ACL table it can read
is 2^35 bytes (ACL + 8p, p : UInt32) and the bucket array 2^34 (rdx + 4p + 0x3000). One call needs only the ONE written
cell (`hdisj`, narrowed). Two calls must carry `StRel` and `AclRel` — both ∀ p — across the CALLER's write of buffer 2,
so buffer 2 must miss the whole bucket array and the whole ACL table (`hbk2`, `hac2`), and call 1's written cell must miss
the ACL table (`hacw`). Satisfiable (a high-address layout, the witness below); no small realistic layout satisfies it.
-/
import Router.Refines

namespace Router.MultiCall
open X86 Router.Refines

/-- The ACL byte `AclRel` reads for (p, t). -/
def aclAddr (p t : UInt32) : BitVec 64 := 0x301d + p.toBitVec.setWidth 64 * 8 + BitVec.ofNat 64 (t.toNat / 8)

/-! ## The three abstractions survive any write confined to a region they avoid. -/
theorem bufRel_frame {R : BitVec 64 → Prop} {m m' : Mem} {buf : ByteArray} {off len : Nat} {base : BitVec 64}
    (hfr : AgreeOutside R m m') (hout : ∀ i, i < len → ¬ R (base + BitVec.ofNat 64 i))
    (h : BufRel buf off len m base) : BufRel buf off len m' base := by
  intro i hi; rw [h i hi]; exact hfr _ (hout i hi)

theorem stRel_frame {R : BitVec 64 → Prop} {m m' : Mem} {σ : VIR.State} {rdx : BitVec 64}
    (hfr : AgreeOutside R m m') (hout : ∀ p : UInt32, ∀ k, k < 4 → ¬ R (Refines.cell rdx p + BitVec.ofNat 64 k))
    (h : StRel σ m rdx) : StRel σ m' rdx := by
  intro p
  rw [h p, readSize_of_agreeOutside_disjoint (R' := fun a => ∃ k, k < 4 ∧ a = Refines.cell rdx p + BitVec.ofNat 64 k) hfr
    (by rintro a ⟨k, hk, rfl⟩; exact hout p k hk) .d _ (fun k hk => ⟨k, hk, rfl⟩)]

theorem aclRel_frame {R : BitVec 64 → Prop} {m m' : Mem} {acl : VIR.Principal → VIR.TopicId → Bool}
    (hfr : AgreeOutside R m m') (hout : ∀ p t : UInt32, t.toNat < 64 → ¬ R (aclAddr p t))
    (h : AclRel acl m) : AclRel acl m' := by
  intro p t ht
  rw [h p t ht, show (0x301d : BitVec 64) + p.toBitVec.setWidth 64 * 8 + BitVec.ofNat 64 (t.toNat / 8) = aclAddr p t
    from rfl, hfr _ (hout p t ht)]

/-! ## The caller, between the calls: it writes buffer 2 and nothing else, and re-enters at the routine. -/
structure Caller (rdx0 : BitVec 64) (t1 s2 : Cpu) (buf2 : ByteArray) (off2 len2 : Nat) : Prop where
  live : Live s2
  rip : s2.rip = 0x1000
  /-- the SAME bucket array: a parameter (call 1's base), because `Exit` states `rdx` kept only on the OK path. -/
  rdx : s2.regs.get .rdx = rdx0
  len : len2 = (s2.regs.get .rsi).toNat
  buf : BufRel buf2 off2 len2 s2.mem (s2.regs.get .rdi)
  frame : AgreeOutside (Region (s2.regs.get .rdi) len2) t1.mem s2.mem

/-- The state call 2 starts from: call 1's returned state on an OK, the same state on a drop. -/
def nextState (d : VIR.Deep.DOut) (σ : VIR.State) : VIR.State :=
  match d with
  | .ret (.state σ') _ => σ'
  | _ => σ

/-- Across call 1, the abstractions of the START of call 2 hold: tokens as `nextState`, the ACL unchanged. -/
theorem after_call1 (acl : VIR.Principal → VIR.TopicId → Bool) {s1 t1 : Cpu} {σ : VIR.State} {P : UInt32}
    {d : VIR.Deep.DOut} (hst : StRel σ s1.mem (s1.regs.get .rdx)) (hacl : AclRel acl s1.mem)
    (hacw : ∀ p t : UInt32, t.toNat < 64 → ¬ Region (Refines.cell (s1.regs.get .rdx) P) 4 (aclAddr p t))
    (hx : Exit s1 t1 P d) :
    StRel (nextState d σ) t1.mem (s1.regs.get .rdx) ∧ AclRel acl t1.mem := by
  match d, hx with
  | .drop .truncated, hx => obtain ⟨-, hm⟩ := hx; rw [hm]; exact ⟨hst, hacl⟩
  | .drop .unauthOrRate, hx => obtain ⟨-, hm⟩ := hx; rw [hm]; exact ⟨hst, hacl⟩
  | .ret (.state σ') (.slice _ _ _), hx =>
      obtain ⟨-, -, -, -, -, hs', hm⟩ := hx
      refine ⟨hs', ?_⟩
      have hfr : AgreeOutside (Region (Refines.cell (s1.regs.get .rdx) P) 4) s1.mem t1.mem := by
        rw [hm]; exact agreeOutside_writeSize (agreeOutside_rfl _ _) .d _ _ (fun k hk => ⟨k, hk, rfl⟩)
      exact aclRel_frame hfr hacw hacl

/-- ⭐ TWO CALLS. Call 1 refines `F b1 σ`; then, for ANY caller that writes only buffer 2 (which must miss the bucket
array and the ACL table) and re-enters with the same bucket base, call 2 refines `F b2 (nextState d1 σ)` — `F` applied to the
state call 1 RETURNED, which is exactly vir's `MultiCall` specification. Call 1's written cell must miss the ACL table. -/
theorem two_calls (acl : VIR.Principal → VIR.TopicId → Bool) (s1 : Cpu)
    (buf1 : ByteArray) (off1 len1 : Nat) (σ : VIR.State) (buf2 : ByteArray) (off2 len2 : Nat)
    (h : Live s1) (hrip : s1.rip = 0x1000)
    (hlen : len1 = (s1.regs.get .rsi).toNat)
    (hbuf : BufRel buf1 off1 len1 s1.mem (s1.regs.get .rdi))
    (hacl : AclRel acl s1.mem)
    (hst : StRel σ s1.mem (s1.regs.get .rdx))
    (htopic : 24 ≤ len1 → ((VIR.Deep.Val.slice buf1 off1 len1).rd 8).toP.toNat < 64)
    (hdisj : ∀ i, i < len1 → ¬ Region (Refines.cell (s1.regs.get .rdx) ((VIR.Deep.Val.slice buf1 off1 len1).rd 4).toP) 4
      (s1.regs.get .rdi + BitVec.ofNat 64 i))
    (hacw : ∀ p t : UInt32, t.toNat < 64 →
      ¬ Region (Refines.cell (s1.regs.get .rdx) ((VIR.Deep.Val.slice buf1 off1 len1).rd 4).toP) 4 (aclAddr p t)) :
    ∃ n1, (runP repaired n1 s1).stopped = true ∧
      Exit s1 (runP repaired n1 s1) ((VIR.Deep.Val.slice buf1 off1 len1).rd 4).toP
        (VIR.Deep.den acl (VIR.Deep.F (.slice buf1 off1 len1) (.state σ))) ∧
      ∀ s2 : Cpu, Caller (s1.regs.get .rdx) (runP repaired n1 s1) s2 buf2 off2 len2 →
        (∀ p : UInt32, ∀ k, k < 4 → ¬ Region (s2.regs.get .rdi) len2 (Refines.cell (s1.regs.get .rdx) p + BitVec.ofNat 64 k)) →
        (∀ p t : UInt32, t.toNat < 64 → ¬ Region (s2.regs.get .rdi) len2 (aclAddr p t)) →
        (24 ≤ len2 → ((VIR.Deep.Val.slice buf2 off2 len2).rd 8).toP.toNat < 64) →
        (∀ i, i < len2 → ¬ Region (Refines.cell (s1.regs.get .rdx) ((VIR.Deep.Val.slice buf2 off2 len2).rd 4).toP) 4
          (s2.regs.get .rdi + BitVec.ofNat 64 i)) →
        ∃ n2, (runP repaired n2 s2).stopped = true ∧
          Exit s2 (runP repaired n2 s2) ((VIR.Deep.Val.slice buf2 off2 len2).rd 4).toP
            (VIR.Deep.den acl (VIR.Deep.F (.slice buf2 off2 len2)
              (.state (nextState (VIR.Deep.den acl (VIR.Deep.F (.slice buf1 off1 len1) (.state σ))) σ)))) := by
  obtain ⟨n1, hs1, hx1⟩ := repaired_refines acl s1 buf1 off1 len1 σ h hrip hlen hbuf hacl hst htopic hdisj
  refine ⟨n1, hs1, hx1, ?_⟩
  intro s2 hc hbk2 hac2 htopic2 hdisj2
  obtain ⟨hst', hacl'⟩ := after_call1 acl hst hacl hacw hx1
  have hst2 := stRel_frame hc.frame hbk2 hst'
  have hacl2 := aclRel_frame hc.frame hac2 hacl'
  rw [← hc.rdx] at hst2 hdisj2
  exact repaired_refines acl s2 buf2 off2 len2 _ hc.live hc.rip hc.len hc.buf hacl2 hst2 htopic2 hdisj2

end Router.MultiCall
