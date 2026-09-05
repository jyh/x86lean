# THE SOFT-FLOAT COMMISSION — a design freeze

**Opened 2026-09-05 by paris**, on the council's word (minute 2026-09-05 item 2(c): *"added as P3
on x86lean's queue — a design commission with its own freeze + refuter pass when paris reaches it"*),
after the two items ahead of it on the queue were discharged (D136, D138). Docketed since 2026-09-04
21:42 (helm) and posted unstarted since batch 19.

This is a **freeze**, not an implementation: a statement specific enough to be refuted, with its
premise, scope and price MEASURED rather than inherited, and its kill-checks named.

---

## §0 WHAT IS COMMISSIONED

A **soft-float IEEE-754 layer over Lean-core `BitVec`**, sufficient to give definitional,
kernel-reducible semantics to the floating-point instructions x86isa already executes — so that they
can become differential vectors like every other form in this repository.

⛔ **What is NOT commissioned:** a general-purpose floating-point library, a proof of IEEE-754
conformance, or anything that changes the axiom policy. The three standard axioms remain the
ceiling for `X86`; `native_decide` stays confined to the test tier.

---

## §1 THE PREMISE, TESTED AT THE OBJECT — NOT INHERITED

The commission has been carried since batch 19 on the sentence *"Lean's `Float` is an opaque extern
type the kernel cannot reduce."* That is a handed-on diagnosis, and a handed-on diagnosis is a
hypothesis ([[feedback-inherited-diagnosis-is-a-hypothesis]]). Run against `leanprover/lean4:v4.32.0-rc1`:

```
example : (2.0 : Float) + 2.0 = 4.0 := by rfl
  ⛔ error: Tactic `rfl` failed: 2.0 + 2.0 is not definitionally equal to 4.0

#print Float          structure Float where val : floatSpec.float
#print floatSpec      opaque floatSpec : FloatSpec          ← there is nothing to unfold

theorem fl : (2.0:Float) + 2.0 = 4.0 := by native_decide
  ⛔ error: failed to synthesize Decidable (2.0 + 2.0 = 4.0)

CONTROL, same run, same shape, over BitVec:
theorem bv : (2#8) + (2#8) = 4#8 := by decide
  ✔  'bv' does not depend on any axioms
```

**The premise is CONFIRMED, and it is stronger than it was stated.** `Float` is not merely
kernel-irreducible: it is built on an `opaque` constant, and the usual escape hatch is not available
either — propositional equality of `Float` has no `Decidable` instance, so `native_decide` cannot
close a `Float` equation at any axiom price. There is no route through `Float`. Meanwhile the
BitVec control in the same run closes with **zero axioms**.

⚠️ A second constraint, from this repository rather than from Lean: **no mathlib** (D1, and
`lakefile.toml` says so). The layer must be built on Lean core's `BitVec` alone. Any design that
reaches for a library is out of scope before it is evaluated.

---

## §2 THE SCOPE, RE-MEASURED

The figure carried since batch 19 is **25,688 instructions over 7 mnemonics**. That was true when
written. It is now wrong, because batches 29, 30 and 31 measured twenty more FP mnemonics as
executing on the oracle. Re-derived from the current measured availability table and `per_ext_map`:

```
40 (mnemonic, bucket) pairs, 36,925 instructions of census demand   (was 25,688 / 7 mnemonics)
```

⇒ 🔑 **The commission grew 44% while it sat docketed, and nothing would have said so**: its price
was a sentence in a bank, not a derived number. A cost carried in prose does not move when the
world does ([[feedback-a-citation-is-an-ungated-claim]]).

### The split that decides the plan

⛔ **They do not build together** — the same finding D119 made about the original six, one level
down and with the boundary now measured:

```
SUB-GROUP A — NO ROUNDING AT ALL
   12 pairs,  6,619 instructions   (17.9% of the commission)
   comisd 1,115 · comiss 819 · minsd 250 · maxss 230 · minss 215 · maxsd 194 ·
   ucomiss 187 · ucomisd 135 · maxps 20 · minps 17          (compare / min / max)
   cvtss2sd 2,949 · cvtsi2sdl 488                            (EXACT widenings — see §7)

SUB-GROUP A′ — a FIXED rounding mode, independent of MXCSR.RC
    2 pairs,    898 instructions   ( 2.4%)
   cvttsd2si 530 · cvttss2si 368     (truncation toward zero is not a mode choice)

SUB-GROUP B — arithmetic and inexact conversions: MXCSR.RC-DEPENDENT
   26 pairs, 29,408 instructions   (79.6%)
   mulss 5,698 · mulsd 5,482 · addss 4,696 · addsd 4,260 · subss 2,264 ·
   subsd 1,674 · cvtsd2ss 1,297 · divsd 1,252 · divss 606 · …
```

⚠️ **This split is the refuter pass's, not the freeze's first draft** — §7 records how the first
version of it was wrong, and in which direction.

---

## §3 K1 — A MEMBER OF SUB-GROUP A IS BUILDABLE TODAY, AND THIS IS THE EVIDENCE

The freeze does not assert sub-group A is cheap; it demonstrates it. `ucomisd`'s comparison rule,
written over Lean-core `BitVec` with no mathlib, and **decided by the kernel**:

```
def expo (x : BitVec 64) : BitVec 11 := (x >>> 52).truncate 11
def mant (x : BitVec 64) : BitVec 52 := x.truncate 52
def sign (x : BitVec 64) : Bool      := x.getMsbD 0
def isNaN (x : BitVec 64) : Bool     := expo x == 0x7ff#11 && mant x != 0#52
inductive Ord3 | lt | eq | gt | unord
def ucomisd (a b : BitVec 64) : Ord3 := …            -- ±0, sign split, magnitude order

example : ucomisd 0x4040404040404040#64 0x4020402040204020#64 = .gt    := by decide
example : ucomisd 0x0000000000000000#64 0x8000000000000000#64 = .eq    := by decide  -- +0 = -0
example : ucomisd 0xBFF0000000000000#64 0xC000000000000000#64 = .gt    := by decide  -- -1 > -2
example : ucomisd 0x7FF8000000000000#64 0x3FF0000000000000#64 = .unord := by decide  -- NaN
example : ucomisd 0xC000000000000000#64 0x3FF0000000000000#64 = .lt    := by decide

#print axioms k1   →   'k1' depends on axioms: [propext]
```

`propext` is one of the three standard axioms, so this is inside the policy. No `native_decide`,
no `ofReduceBool`, no mathlib.

⛔ **AND THE GREEN WAS CONTROLLED.** Seven passing `decide`s prove nothing if the propositions are
vacuous, so one expectation was planted wrong (`+0 vs -0` declared `.gt`) and the kernel refuted it:
*"Tactic `decide` proved that the proposition … is false"*. The checks evaluate
([[feedback-a-probe-must-create-its-condition]]).

⚠️ The four cases after the first exist because they are **exactly the ones a raw bitvector compare
gets wrong**: `+0 = -0` (distinct bit patterns, equal values), negative ordering (magnitude order
reverses), and NaN (unordered, not merely unequal). A design whose test vectors are all ordinary
positive normals would report success for a `BitVec.ult` that is not the rule at all.

---

## §4 THE KILL-CHECKS — what the refuter pass must attack

| # | claim | how it dies |
|---|---|---|
| **K1** | sub-group A is buildable over `BitVec`, kernel-reducible, ≤ 3 standard axioms | ✔ **VERIFIED §3**, with a planted-wrong control |
| **K2** | sub-group B needs rounding, so it needs a *rounding mode*, so it needs MXCSR state | ⛔ **REFUTED for two members — §7.** `cvtss2sd` and `cvtsi2sdl` are exact for every input. 3,437 instructions moved out of B |
| **K3** | MXCSR is one `Cpu` field, and adding it is cheap | ⛔ **DOUBTFUL** — [[feedback-a-state-field-costs-every-record-proof]]: two fields once blew three unrelated `rfl` record proofs. Measure the kernel delta on the CURRENT record before believing it |
| **K4** | a soft-float `mulsd` reduces in the kernel at a cost the delta gate accepts | build one, profile it; 52×52 mantissa multiply is not obviously cheap in the kernel |
| **K5** | the differential can compare FP results bit-for-bit | x86isa returns a bit pattern; NaN payloads and `-0` make "equal value" ≠ "equal bits" — the record must compare BITS |
| **K6** | sub-group A's 3,182 instructions are worth landing before B | check it against the delta gate's budget and the queue's other P-items |
| **K7** | no member of A secretly needs rounding | `min`/`max` return an *operand*, never a computed value (SDM Vol.2B: MINSD returns SRC1 or SRC2 in every branch, including the ±0 and NaN branches), and `comis`/`ucomis` write flags only. ✔ holds by the SDM's own rule shape |

---

## §5 THE PRICE, AND WHAT IS NOT PRICED

Sub-group A is priced by K1: the rule above is ~20 lines per width. Ten pairs, two widths, the flag
write, the vectors, one roster row — a normal batch, not a campaign.

⛔ **Sub-group B is NOT priced here, and that is deliberate.** Its cost is dominated by K3 and K4,
neither of which has been measured, and a number invented for them would be the third inherited
figure in this document's own history. It is priced when K3 and K4 are run, not before.

---

## §6 THE RECOMMENDATION

**Take sub-group A as an ordinary P2 batch; leave sub-group B frozen until K3 and K4 are measured.**

It is 8.6% of the commission's demand for a small fraction of its cost, it needs no new state field,
and it converts the commission from one undifferentiated 36,925-instruction block into a landed
piece plus a measured remainder. The 91.4% is not abandoned — it is un-priced, which is the honest
status, and K3/K4 are the two measurements that would price it.


---

## §7 THE REFUTER PASS — run in this seat, against this document

Kill-check **K2** claimed that sub-group B needs rounding, and therefore MXCSR, *as a block*. It was
attacked by asking the question the claim forbids: **is any member of B exact for every input?**

```
cvtss2sd   binary32 -> binary64 : 199,489 patterns   non-exact 0
cvtsi2sdl  int32    -> binary64 : 200,000 values     non-exact 0
CONTROL cvtsi2sdq int64 -> binary64 : 200,000 values   non-exact 198,824   <- the test SEES rounding
CONTROL cvtsi2ssl int32 -> binary32 : 200,000 values   non-exact 193,067
```

**K2 is refuted for two members.** binary64 carries an 11-bit exponent against binary32's 8 and a
52-bit mantissa against its 23, so *every* binary32 value — normal, denormal, infinity — widens
exactly; and every int32 fits in binary64's 53-bit significand. Neither can round, so neither reads
MXCSR.RC. **3,437 instructions move out of the rounding-dependent block**, and sub-group A more than
doubles, 3,182 → 6,619.

⭐ **The two controls are the point of the measurement, not decoration.** "Zero non-exact results"
is also what a broken exactness test prints. `cvtsi2sdq` and `cvtsi2ssl` were run through the *same*
instrument in the *same* run and came back 198,824 and 193,067 — so the zero above is a fact about
those two conversions and not about the test ([[feedback-a-probe-must-create-its-condition]]).

A third group separated itself while K2 was being attacked: `cvttsd2si` and `cvttss2si` **truncate**,
and truncation toward zero is fixed by the opcode, not chosen by MXCSR.RC. They still need conversion
logic and an invalid-operation result, so they are not free — but they do not need the rounding-mode
field, which is what K3 is expensive about.

### What this changes

The recommendation in §6 stands and gets stronger: the immediately-buildable group is **17.9% of
the commission's demand, not 8.6%**, and it still needs no new state field.

⇒ 🔑 **A block named for a shared blocker is a hypothesis about every member.** "Sub-group B needs
rounding" was written as a property of the group, and it was never true of two of its largest
members — one of which, `cvtss2sd`, has been carried inside the commission since batch 19 as one of
its original five. The category came from the *instruction class* (a conversion, an arithmetic op)
rather than from the *question* (can this result be inexact?), and no gate reads a category.
