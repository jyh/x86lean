# G2 — the undefined-bit section, drafted from the measured record

**Status: TECHNICAL CONTENT, NOT FINAL PROSE.** `docs/TACAS-G2-UNDEFINED-BITS.md` is the scope and the
comparative frame; this is the argument it maps out, written from `docs/DECISIONS.md` rather than
recalled. **It is FRAMING-INDEPENDENT by construction** — what the (a)/(b)/(c) choice decides is
whether this is a *section* or part of the *headline*, not what it says. *(Written while the framing
sat on `blocked-on-captain`, deliberately: treating an unruled prominence as a reason not to write the
content would be a deferral wearing a blocker's clothes.)*
⚖️ **The framing was RULED (c) on 2026-09-12** (`TACAS-PRICING.md` §2.1): the semantics paper is written
now, so **this is a SECTION of it**, and the paper's argument is validation. The prose lives in
`paper/x86lean-semantics.tex`; this file stays the register it was written from.

---

## 1. THE PROBLEM, IN THE SDM's OWN TERMS
x86 leaves bits undefined in three distinct ways, and a model that conflates them will be wrong
somewhere:
```
  a FLAG left undefined by a named clause     "SHL and SHR ... where the count is >= the size of
                                               the destination operand"            (D20)
  a RESULT left undefined                     shld/shrd at a count above the operand size: the
                                               DESTINATION and six flags together   (D52)
  a value that is merely UNSPECIFIED-looking  SAR at the same counts is fully DEFINED -- CF is the
                                               sign bit -- because the SDM has no such clause for it
```
⭐ **D20 is the shape of the whole problem.** `sar` shifting past its own width still has an answer:
every vacated position takes the sign. **The absence of an undefined clause is itself the
specification**, and a model that treats "past the width" as a uniform undefined case invents
undefinedness the manual does not grant.

## 2. THE FOUR DESIGNS, MEASURED AT EACH PROJECT'S OWN SOURCE
*(`TACAS-G1-POSITIONING.md` §1c.6 and §1c.10; every cell read at the source, not inferred.)*
```
  x86lean   a CONCRETE value drawn from an ORACLE in the state
  x86isa    `create-undef`, an `encapsulate`d CONSTRAINED function -- NOTHING about equality is
            provable. Its own docs: "an undefined value is different from another undefined value,
            and also all the known values."
  K         ONE CONSTANT, `undefMInt`/`undefBool`, written into the flag; 497 of 3,064
            per-instruction files
  Sail      Sail's builtin `undefined` via `undef_read_logic()`, plus a per-case `undefined_flags`
            MASK threaded through `write_user_rflags`
```
⛔ *This paragraph read "Ours is the only one that keeps the step function TOTAL AND EXECUTABLE at
those bits" until 2026-09-12 (D213). **False:** x86isa executes too, through its `:undef-flg` trust
tag (G1 §1c.10), and Sail's backends were never measured.* **What is measured and ours:** the function
that runs and the function theorems are about are the SAME definition, with undefinedness a
parameter; x86isa keeps a logical story (the constrained function) and an execution story (the trust
tag) apart.

## 3. WHAT WE ADD, AND IT IS THREE MECHANISMS RATHER THAN AN ORACLE
### 3.1 THE DRAW IS PART OF THE MODEL (D5)
A shift with a non-zero masked count draws exactly **three** bits in the order **CF, OF, AF** —
*whether or not each is undefined at that count* — and the logic group draws exactly **one** (AF).
⛔⛔ *This read "**The count may not vary with the operands** … it is what makes a disagreement
BISECTABLE" until 2026-09-12. **FALSE AGAINST THE SOURCE (D213):** a CL shift draws 0 or 3 bits by the
masked count, `bsf`/`bsr` draw a destination's width only at a zero source, `shld`/`shrd` draw 0, 2 or
6+width.* **The rule that holds is narrower:** once an instruction's branch is decided its draws are
unconditional — a bit is drawn for a flag whether or not that flag is undefined at these operands —
so the draw count does not depend on WHICH flags are undefined. **Evidence class: a design rule and
one example theorem (`cursor_independent_of_bits`); no general theorem; not gated.** The bisection
sentence is withdrawn: across a stream, an earlier draw can steer a later branch.

### 3.2 THE UNDEFINED SET IS DERIVED, NEVER DECLARED (D6)
`X86.undefinedFlags` runs the same step under **two opposite oracles** and reports which flags moved.
The harness holds no list **of flags**. ⚠️ *For REGISTERS it holds one on purpose* (P1 batch 14,
`declaredUndefGPRs`): a register set derived from the same two runs the leak check compares would
re-read every leak as "undefined here". So registers have two sources, the AST+SDM rule and the
observed runs, and the check is their equality. `undefinedLeaked` is the companion: if the two runs differ anywhere
**outside** the flags, an undefined bit has reached a register, RIP, memory or the model state.
⇒ **A declared list would be a second source of truth that goes stale silently — and in the PERMISSIVE
direction.** ⇒ 🔑 ***THIS IS THE PAPER'S CENTRAL CLAIM APPLIED TO UNDEFINEDNESS, NOT A NEIGHBOURING
IDEA.*** ⚠️ **And it is not unique:** K derives its own coverage with a script too (G6 §2). **What we
add is that CI FAILS when the derivation and the prose disagree** — a gate rather than a practice.

### 3.3 THE REFUSAL IS A THEOREM (D52)
`shld`/`shrd` at `.w` with a masked count above 16 leave the destination and six flags undefined.
With a **register** destination the model answers from the oracle. With a **memory** destination
there is no channel — `Main.undefinableFields` is flags and register names only — so **the model
REFUSES**, and the refusal is stated as `step_dshift_mem_undefined_refuses`.
⭐ **Nothing else in §2's table does this.** x86isa mints a constrained value, K writes a constant,
Sail returns its builtin. ⇒ **A machine-checked statement that the model declines a case it cannot
represent** is the one thing here that is ours.
⚠️ **Presented as a demonstrated discipline, not as coverage: it is ONE instruction pair.** And it is
self-enforcing — the oracle COMPUTES that case, so a vector there would be a refusal-class
disagreement rather than a test. **The gap cannot be filled by accident and cannot be forgotten.**
📌 **Not a corner case:** over this harness's own 82 pre-states, a CL-driven count lands above 16 in
**35** of them.

## 4. ⛔ THE PART THAT MUST GO IN, BECAUSE THE GATING CLAIM COMMITS US TO IT
A paper whose contribution is *"no ungated claim"* cannot omit the places where the oracle and the
manual part company:
```
  D91   the oracle does NOT implement `movdqa`'s alignment check ⇒ the model's most interesting new
        rule has NO SECOND SOURCE. Stated, not quietly dropped.
  D108  the oracle reads a packed-shift count from 128 bits where the SDM *and K* read 64, and
        CONTRADICTS ITSELF two shapes over. 8 unexplained disagreements in 78,584 -- the third time
        the differential was right and x86isa wrong.
  D115  the residue measured: the oracle REFUSES MORE OF THE GAP THAN IT EXECUTES.
```
⇒ 🔑 ***THESE ARE THE STRONGEST EVIDENCE FOR THE METHOD AND THE MOST UNCOMFORTABLE PARAGRAPHS IN THE
PAPER, AND THEY ARE THE SAME PARAGRAPHS.*** A referee who finds them unaided finds a weakness; a paper
that states them demonstrates the discipline it claims.
⚠️ **D108 is also the limit of "the oracle is evidence, not the specification":** agreement with a
model that does not implement a rule says nothing about that rule.

## 5. ⛔ WHAT MAY NOT BE WRITTEN YET
The sentence *"K's single constant makes two undefined flags the same term, so an equality test
between them is TRUE"* is **measured at both sources and UNRUN against K.** `kprove` may refuse to
decide it. ⇒ **It stays out until driven** — and driving it needs a K installation this campaign has
never had (no `kompile`/`krun`/`kprove` on this box; K's README pins a pre-`MInt`-syntax revision).
**Pricing that experiment is part of G2.**
