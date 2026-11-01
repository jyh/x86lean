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

/-- Whatever call 1's outcome, memory outside the cell it may write reads as before. -/
theorem read_outside_cell {s1 t1 : Cpu} {P : UInt32} {d : VIR.Deep.DOut} (hx : Exit s1 t1 P d) (a : BitVec 64)
    (ha : ¬ Region (Refines.cell (s1.regs.get .rdx) P) 4 a) : t1.mem.read a = s1.mem.read a := by
  match d, hx with
  | .drop .truncated, hx => rw [hx.2]
  | .drop .unauthOrRate, hx => rw [hx.2]
  | .ret (.state _) (.slice _ _ _), hx =>
      obtain ⟨-, -, -, -, -, -, hm⟩ := hx
      rw [hm]
      exact ((agreeOutside_writeSize (agreeOutside_rfl _ _) .d _ _ (fun k hk => ⟨k, hk, rfl⟩)) a ha).symm

/-! ## THE WITNESS (mandatory, per the ruling): every hypothesis of `two_calls` holds of one concrete start state and one
concrete caller, so the theorem is not vacuous. The layout is the one the finding forces: bucket base 2^40 (its array spans
2^34), the ACL table at 0x301d (2^35), buffer 1 at 2^42, buffer 2 at 2^44. `acl` and `σ` are DEFINED from memory, so
`AclRel`/`StRel` hold by `rfl`; what the witness proves is that the REGION hypotheses and the caller are satisfiable. -/
def RDX : BitVec 64 := 0x10000000000
def B1 : BitVec 64 := 0x40000000000
def B2 : BitVec 64 := 0x100000000000
/-- A packet: magic, sender 0, topic 0, then 12 payload bytes (24 bytes). -/
def pkt : List (BitVec 8) := [0x31, 0x47, 0x53, 0x4D] ++ List.replicate 20 0
def bytesOf (l : List (BitVec 8)) : ByteArray := ⟨(l.map (fun b => UInt8.ofBitVec b)).toArray⟩
def putBytes (m : Mem) (a : BitVec 64) : List (BitVec 8) → Mem
  | [] => m
  | b :: bs => putBytes (m.write a b) (a + 1) bs
def wMem : Mem :=
  let m := putBytes {} B1 pkt
  let m := putBytes m B2 pkt
  let m := m.write 0x301d 1                               -- ACL bit (sender 0, topic 0)
  m.writeSize .d (Refines.cell RDX 0) 5                   -- 5 tokens for sender 0
def w1 : Cpu :=
  let c : Cpu := { rip := 0x1000, oracle := Oracle.zero }
  let c := { c with mem := wMem }
  ((c.setReg .q .rdi B1).setReg .q .rsi 24).setReg .q .rdx RDX
def wAcl (p t : UInt32) : Bool := (wMem.read (aclAddr p t)).getLsbD (t.toNat % 8)
def wσ (p : UInt32) : Int := Value.sval .d (wMem.readSize .d (Refines.cell RDX p))
/-- The caller: re-enter at the routine with buffer 2, the same bucket base, memory as call 1 left it. -/
def enter (t : Cpu) : Cpu :=
  let c : Cpu := { t with rip := 0x1000 }
  let c := { c with ms := none }
  ((c.setReg .q .rdi B2).setReg .q .rsi 24).setReg .q .rdx RDX

set_option maxRecDepth 100000 in
theorem w_buf (m : Mem) (base : BitVec 64) (hm : ∀ i, i < 24 → m.read (base + BitVec.ofNat 64 i) = pkt.getD i 0) :
    BufRel (bytesOf pkt) 0 24 m base := by
  intro i hi
  rw [hm i hi]
  revert i; decide

theorem w_region_lt {base a : BitVec 64} {len : Nat} (h : a.toNat + 0 < base.toNat) (hb : base.toNat + len < 2 ^ 64) :
    ¬ Region base len a := by
  rintro ⟨i, hi, rfl⟩; bv_omega

theorem cell_lt (p : UInt32) : (Refines.cell RDX p).toNat < 0x10400004000 := by
  have := p.toNat_lt; have e := widen_toNat p; simp only [Refines.cell, RDX]; bv_omega
theorem cell_ge (p : UInt32) : 0x10000000000 ≤ (Refines.cell RDX p).toNat := by
  have := p.toNat_lt; have e := widen_toNat p; simp only [Refines.cell, RDX]; bv_omega
theorem acl_lt (p t : UInt32) (ht : t.toNat < 64) : (aclAddr p t).toNat < 0x800000000 + 0x301d + 8 := by
  have := p.toNat_lt; have e := widen_toNat p; simp only [aclAddr]; bv_omega

/-- No ACL byte is in a bucket cell (the table sits below 2^36, the array above 2^40). -/
theorem w_acl_cell (p t q : UInt32) (ht : t.toNat < 64) : ¬ Region (Refines.cell RDX q) 4 (aclAddr p t) := by
  rintro ⟨k, hk, he⟩
  have h1 := acl_lt p t ht; have h2 := cell_ge q; have h3 := cell_lt q
  have := congrArg BitVec.toNat he; bv_omega
/-- No cell is inside a buffer at 2^42 or 2^44, and no buffer byte is in a cell. -/
theorem w_cell_buf (p : UInt32) (B : BitVec 64) (hB : B = B1 ∨ B = B2) (k : Nat) (hk : k < 4) :
    ¬ Region B 24 (Refines.cell RDX p + BitVec.ofNat 64 k) := by
  rintro ⟨i, hi, he⟩
  have h3 := cell_lt p; have := congrArg BitVec.toNat he
  rcases hB with rfl | rfl <;> simp only [B1, B2] at this <;> bv_omega
theorem w_buf_cell (p : UInt32) (B : BitVec 64) (hB : B = B1 ∨ B = B2) (i : Nat) (hi : i < 24) :
    ¬ Region (Refines.cell RDX p) 4 (B + BitVec.ofNat 64 i) := by
  rintro ⟨k, hk, he⟩
  have h3 := cell_lt p; have := congrArg BitVec.toNat he
  rcases hB with rfl | rfl <;> simp only [B1, B2] at this <;> bv_omega
theorem w_acl_buf (p t : UInt32) (ht : t.toNat < 64) : ¬ Region B2 24 (aclAddr p t) := by
  rintro ⟨i, hi, he⟩
  have h1 := acl_lt p t ht; have := congrArg BitVec.toNat he; simp only [B2] at this; bv_omega

set_option maxRecDepth 200000 in
theorem w_mem_b1 : ∀ i, i < 24 → wMem.read (B1 + BitVec.ofNat 64 i) = pkt.getD i 0 := by decide
set_option maxRecDepth 200000 in
theorem w_mem_b2 : ∀ i, i < 24 → wMem.read (B2 + BitVec.ofNat 64 i) = pkt.getD i 0 := by decide
theorem w_topic : ((VIR.Deep.Val.slice (bytesOf pkt) 0 24).rd 8).toP.toNat < 64 := by decide
theorem w_sender : ((VIR.Deep.Val.slice (bytesOf pkt) 0 24).rd 4).toP = 0 := by decide

/-- ⭐ THE WITNESS: two calls from one concrete state and one concrete caller; every premise of `two_calls` discharged. -/
theorem two_calls_witness :
    ∃ n1, (runP repaired n1 w1).stopped = true ∧
      ∃ n2, (runP repaired n2 (enter (runP repaired n1 w1))).stopped = true := by
  have hr : w1.regs.get .rdi = B1 ∧ w1.regs.get .rsi = 24 ∧ w1.regs.get .rdx = RDX := by decide
  obtain ⟨n1, hs1, hx1, hk⟩ := two_calls wAcl w1 (bytesOf pkt) 0 24 wσ (bytesOf pkt) 0 24
    rfl rfl (by rw [hr.2.1]; rfl) (by rw [hr.1]; exact w_buf _ _ w_mem_b1) (fun _ _ _ => rfl)
    (fun p => by rw [hr.2.2]; rfl) (fun _ => w_topic)
    (by rw [w_sender, hr.2.2, hr.1]; exact fun i hi => w_buf_cell 0 B1 (Or.inl rfl) i hi)
    (by rw [w_sender, hr.2.2]; exact fun p t ht => w_acl_cell p t 0 ht)
  refine ⟨n1, hs1, ?_⟩
  have he : ∀ t : Cpu, (enter t).mem = t.mem ∧ (enter t).regs.get .rdi = B2 ∧ (enter t).regs.get .rsi = 24 ∧
      (enter t).regs.get .rdx = RDX ∧ (enter t).rip = 0x1000 ∧ (enter t).ms = none := by
    intro t; simp [enter, Cpu.setReg, Value.writeView, Regs.get_set_ne]
  obtain ⟨m2, d2, l2, x2, r2, ms2⟩ := he (runP repaired n1 w1)
  have hc : Caller (w1.regs.get .rdx) (runP repaired n1 w1) (enter (runP repaired n1 w1)) (bytesOf pkt) 0 24 := by
    refine ⟨ms2, r2, by rw [x2, hr.2.2], by rw [l2]; rfl, ?_, ?_⟩
    · rw [d2]
      apply w_buf
      intro i hi
      rw [m2, read_outside_cell hx1 _ (by rw [w_sender, hr.2.2]; exact w_buf_cell 0 B2 (Or.inr rfl) i hi)]
      exact w_mem_b2 i hi
    · rw [m2]; exact agreeOutside_rfl _ _
  obtain ⟨n2, hs2, -⟩ := hk _ hc
    (by rw [d2, hr.2.2]; exact fun p k hk => w_cell_buf p B2 (Or.inr rfl) k hk)
    (by rw [d2]; exact fun p t ht => w_acl_buf p t ht)
    (fun _ => w_topic)
    (by rw [w_sender, hr.2.2, d2]; exact fun i hi => w_buf_cell 0 B2 (Or.inr rfl) i hi)
  exact ⟨n2, hs2⟩

end Router.MultiCall
