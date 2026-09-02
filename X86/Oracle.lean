/-
# X86.Oracle — the adversarial undefined-bit oracle

WHAT INTEL LEAVES UNDEFINED IS NOT "ZERO" AND NOT "WHATEVER THE HARDWARE DID".
The SDM says of several flag results simply that they are *undefined* (e.g.
Vol. 2A, the `AND`/`OR`/`XOR`/`TEST` entries: "The AF flag is undefined"; the
`SHL`/`SHR` entries: OF is undefined for shift counts other than 1, AF is
undefined for any non-zero count).  A model that writes `false` there has
INVENTED a fact, and every theorem proved over it is a theorem about the
invention.

PUBLIC PRIOR ART (PROVENANCE.md).  ACL2 x86isa solves this with an `undef` field
in the machine state, seeded so that reading it yields a fresh unconstrained
value; the model's own comment describes it as seeding unknown values that
characterize commonly occurring undefined behaviour.  Sail spells the same idea
`undefined`/`Unspecified`.  This file is that discipline rendered positively in
Lean: the state carries an oracle whose bit stream is an ARBITRARY function
field, so a theorem quantified over all states cannot learn a single bit of it.

THE NONVACUITY OBLIGATION (plan v1 §4.5).  A model could satisfy the letter of
this by carrying an oracle it never reads.  For every bit this model marks
undefined, `Tests/Nonvacuity.lean` exhibits TWO oracles that make `step` produce
DIFFERENT results — which is what makes "undefined" a claim rather than a label.

LANE. Personal lane, public sources only.
-/
import X86.Value

namespace X86

/-- A stream of adversarially chosen bits, with a cursor into it.

`bits` is a plain function field, deliberately.  It is not `Nat → Bool` behind a
structure that could later be given a `Decidable` instance, and it is not a seed
plus a PRNG: a PRNG would make every "undefined" bit a THEOREM about that PRNG,
and the point of this record is that no such theorem exists. -/
structure Oracle where
  bits : Nat → Bool
  cursor : Nat := 0

namespace Oracle

/-- The all-zero oracle.  Used ONLY as a default for `Inhabited` and by the
harness when it deliberately wants a reproducible run; no theorem in `X86` may
mention it, and the axiom gate cannot see that rule, so it is a review rule
stated here and checked by `scripts/check_oracle_use.sh`. -/
def zero : Oracle := { bits := fun _ => false }

instance : Inhabited Oracle := ⟨zero⟩

/-- Draw one bit and advance the cursor. -/
def draw (o : Oracle) : Bool × Oracle :=
  (o.bits o.cursor, { o with cursor := o.cursor + 1 })

/-- Draw `n` bits as the low `n` bits of a `Val`, least-significant first. -/
def drawVal (o : Oracle) : Nat → Val × Oracle
  | 0 => (0, o)
  | n + 1 =>
    let (b, o₁) := o.draw
    let (v, o₂) := o₁.drawVal n
    ((v <<< 1) ||| (if b then 1 else 0), o₂)

@[simp] theorem draw_fst (o : Oracle) : o.draw.1 = o.bits o.cursor := rfl
@[simp] theorem draw_snd_bits (o : Oracle) : o.draw.2.bits = o.bits := rfl
@[simp] theorem draw_snd_cursor (o : Oracle) : o.draw.2.cursor = o.cursor + 1 := rfl

/-- Drawing never changes the stream, only the cursor.  This is the frame lemma
that lets a characterization theorem say "the oracle advanced by k" without
saying anything about what came out. -/
@[simp] theorem drawVal_bits (o : Oracle) (n : Nat) : (o.drawVal n).2.bits = o.bits := by
  induction n generalizing o with
  | zero => rfl
  | succ n ih => simp [drawVal, draw, ih]

@[simp] theorem drawVal_cursor (o : Oracle) (n : Nat) :
    (o.drawVal n).2.cursor = o.cursor + n := by
  induction n generalizing o with
  | zero => rfl
  | succ n ih => simp [drawVal, draw, ih]; omega

end Oracle
end X86
