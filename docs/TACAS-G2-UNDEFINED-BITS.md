# G2 — the undefined-bit argument, scoped

**Why this file exists:** `docs/TACAS-PRICING.md` prices G2 at **2–3 days, "mostly extraction from
`docs/DECISIONS.md`"**, and calls it *"the hardest part of x86 and the most citable"*. This is the
SKELETON — the frame, the extraction map, and the one experiment that is not run. **It is not the
writeup.** Opened 2026-09-11 by paris, immediately after G1 closed, because G1's §1c.6 measured the
comparative half and a frame that is not written down has to be re-derived.

⛔ **THE SAME RULE AS G1 APPLIES AND IS GATED THE SAME WAY:** every claim about another system is
MEASURED at that system's own source or it does not appear. The comparative table below is
**imported from `TACAS-G1-POSITIONING.md` §1c.6, not restated from memory** — that file is the
register, this one cites it.

---

## 1. ⭐⭐ THE FRAME: FOUR SYSTEMS, FOUR ANSWERS, AND THEY DISAGREE ON THE QUESTION
Measured at the sources (G1 §1c.6; deriving commands and positive controls are there):

| | what an undefined bit IS | what it costs |
|---|---|---|
| **x86lean** | a value drawn from an **oracle in the state**, at a draw order and count fixed by the model (D5) | the model stays **total and executable**; undefinedness becomes a *parameter*, so a run is replayable from its seed and a disagreement is bisectable |
| **ACL2 x86isa** | a **fresh unique unknown** per read, minted by `undef-read` from a seed counter whose field is `push-untouchable` | two undefined reads are **distinguishable**; the model is not concretely executable at those bits without an oracle |
| **K x86-64** | a single distinguished **constant** `undefMInt`/`undefBool`, written straight into the flag (497 of 3,064 per-instruction files) | one term for every undefined value |
| **Sail-x86-from-acl2** | **nothing — dropped in translation.** `other_non_det.sail` is a 27-byte stub | the mechanism does not survive the translation that produced the model |

⭐ **AND x86isa's OWN SOURCE DOCUMENTS THE HAZARD THAT A SINGLE CONSTANT WALKS INTO.**
`unsafe-!undef`'s `:long`, verbatim: reusing a seed *"might contaminate our 'pool of undefined
values' … which would make the result of an equality test between them **equal instead of
indeterminate**."*
⛔⛔ **THIS IS THE PAPER'S SHARPEST SENTENCE AND IT IS ALSO THE ONE THAT IS NOT YET EARNED.** See §4.

---

## 2. WHAT WE HAVE THAT THE TABLE SHOWS NOBODY ELSE DOES — THE THREE DECISIONS TO EXTRACT
```
  D5   docs/DECISIONS.md:84    the draw ORDER and COUNT are part of the model
  D6   docs/DECISIONS.md:99    the "undefined" SET is DERIVED, never declared
  D52  docs/DECISIONS.md:1721  undefined in a REGISTER is answered; in MEMORY it is REFUSED
```
**D5 — determinism of the draw.** A shift with a non-zero masked count draws exactly three bits in
the order CF, OF, AF, *whether or not each is undefined at that count*; the logic group draws exactly
one. **The count may not vary with the operands**, or the oracle cursor stops being a function of the
instruction stream and a differential run cannot be replayed from its seed. ⇒ **The reason is
operational, not aesthetic: it is what makes a disagreement bisectable**, and that is the sentence the
paper needs, because it explains why a modelling choice is a *validation* choice.

**D6 — the set is derived.** `X86.undefinedFlags` runs the same step under **two opposite oracles**
and reports which flags moved; the harness holds no list of its own. `undefinedLeaked` is the
companion: if the two runs differ anywhere OUTSIDE the flags, an undefined bit has reached a register,
RIP, memory or the model state — which no tier admits.
⇒ 🔑 ***THIS IS THE PAPER'S CENTRAL CLAIM APPLIED TO UNDEFINEDNESS, NOT A SEPARATE IDEA.*** A declared
list would be a second source of truth that goes stale silently **and in the permissive direction**.
G2 is therefore a SECTION OF the gating argument, not a neighbour of it — and that is the structural
decision this skeleton exists to record.

**D52 — the refusal is a theorem.** `shld`/`shrd` at `.w` with a masked count above 16 leave the
destination and six flags undefined. With a **register** destination the model answers from the
oracle. With a **memory** destination there is no channel, so **this model REFUSES** rather than
widening its strongest gate as a side effect of one batch — and the refusal is stated as a theorem,
`step_dshift_mem_undefined_refuses`.
⭐⭐ **NOTHING ELSE IN §1's TABLE HAS THIS.** x86isa mints an unknown, K writes a constant, Sail
dropped the mechanism. **A machine-checked statement that the model declines a case it cannot
represent** is the one thing in this row that is ours, and it is worth more than the oracle design
itself. ⚠️ It is also a *small* claim over *one* instruction pair — the paper must present it as a
demonstrated discipline, not as coverage.
📌 And it is self-enforcing: the oracle COMPUTES that case, so a vector there would be a
refusal-class disagreement rather than a test. **The gap cannot be filled by accident and cannot be
forgotten either.**

---

## 3. THE EXTRACTION MAP — 76 mentions of `undef` in `docs/DECISIONS.md`
Beyond the three above, the per-instruction rulings that carry the argument's hard cases:
```
  D20   :483    SAR's CF is DEFINED where SHL's and SHR's is undefined
  D22   :538    a rotate's count is reduced twice, and its flags key off the FIRST
  D46   :1364   an instruction's own address is a legal answer
  D91   :3485   the oracle does not implement movdqa's alignment check -- no second source
  D108  :4844   the oracle reads a packed-shift count from 128 bits where SDM and K read 64
  D115  :5311   the residue: the oracle refuses more of the gap than it executes
```
⚠️ **D91, D108 and D115 are the uncomfortable ones and they belong in the paper.** They are places
where **our oracle and the SDM disagree, or where the second source is absent** — exactly what a
referee will look for, and exactly what the gating claim commits us to publishing.

---

## 4. ⛔⛔ THE ONE CLAIM THAT MAY NOT BE MADE YET, WRITTEN DOWN BEFORE THE WRITEUP STARTS
The natural paragraph — *"K's single constant makes two undefined flags the same term, so an equality
test between them is TRUE, which is the contamination x86isa designed against"* — is **a hypothesis,
not a finding.**
```
  MEASURED   K writes one constant, undefMInt, into the flag          (G1 §1c.6, at the source)
  MEASURED   x86isa mints a FRESH unknown per read and guards the seed (G1 §1c.6, at the source)
  NOT RUN    how kprove actually treats undefMInt under equality
```
⇒ **It does not go in the paper until it is driven against K.** `kprove` may well refuse to decide
it, in which case the sentence is wrong and the comparison is merely *different*, not *weaker*.
⛔ **THE EXPERIMENT IS NOT CHEAP HERE AND THAT IS THE POINT:** it needs a working K installation
(its README pins a pre-`MInt`-syntax K revision), which this campaign does not have and has never
needed — we read K's tree mechanically for the roster and have **never executed it** (G1 §1's
`executable` row says so). **Pricing it is part of G2, not a footnote to it.**
⇒ 🔑 ***THE SHARPEST SENTENCE IN A COMPARISON IS THE ONE MOST LIKELY TO BE WRITTEN FROM THE
MECHANISM INSTEAD OF FROM THE BEHAVIOUR*** — and this one is about someone else's system, which is
the half a referee can check and we cannot.

---

## 5. STATUS
**SKELETON ONLY. G2 is NOT started as a writeup** and remains priced at 2–3 days in
`TACAS-PRICING.md`. What this file changes is that the comparative frame is now **measured and
recorded** rather than owed, and the structural decision — *G2 is a section of the gating argument*
— is written down instead of being rediscovered at drafting time.
