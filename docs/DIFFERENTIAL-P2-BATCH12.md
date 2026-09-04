# P2 BATCH 12 — the permute group, and a rule the prose had inverted

> ⚠️ **TWO COUNTERS, BOTH SPELLED "P2 batch N".** This file is the **twelfth
> differential record** (`docs/DIFFERENTIAL-P2-BATCH*.md` is a contiguous 1..N
> sequence and `scripts/check_coverage_prose.py` enforces the contiguity). The
> same work is the seat's **batch 14** in `docs/DECISIONS.md` and in the code
> comments, because that counter also numbers batches which add no forms and
> therefore file no differential record. The offset is not constant; the mapping
> is recorded here rather than left for the next head to rediscover.

**Forms.** `pshufd` · `pshuflw` · `pshufhw`, each at both operand shapes
(`x,x,i` and `x,m,i`). Three roster rows, fourteen vectors, **no new state** —
the XMM file and the 128-bit memory path both landed earlier.

**Demand, measured rather than inherited.** Over the census's own `asm` class,
through the census's own disassembler invocation:

```
pshufd    9,049   (reg 8,887 · mem 162)      pshufw   642 — 642/642 MMX-REGISTER
pshuflw   2,660   (reg 2,638 · mem  22)               forms, DECLINED by register
pshufhw     355   (reg   355 · mem   0)               file, exactly as D107's 2,822
                                            ─────
BUILDABLE                                   12,064    memory-source share 1.53%
```

⛔ **`pshuflw` AND `pshufhw` ARE NOT IN `docs/P2-ROSTER.md` AT ALL** — its ranked
table stops around rank 40 — so two of the three numbers this batch is priced by
were never in the artifact the batch is supposed to be priced from. They were
re-derived here from the corpus, and §5 records what that re-derivation cost.

## 1. ⭐⭐⭐ The batch found a DEFECT IN WHAT IT INHERITED, one screen above its own arm

`Op.vshiftm` — P2 batch 13's memory-count shape for the packed shifts — carried:

> *"NO ALIGNMENT CHECK, unlike `vload`. The SDM states no alignment requirement
> for the shift forms, so there is no `#GP` branch to write — **the absence is
> the rule**."*

**That sentence is false**, and the chain that settles it is the SDM's own, three
quotable lines rather than a recollection of a table:

```
PSHUFD   Other Exceptions: … Table 2-21, "Type 4 Class Exception Conditions"
PAND     Other Exceptions: … Table 2-21, "Type 4 Class Exception Conditions"
MOVDQU   Other Exceptions: … Table 2-21, "Type 4 Class Exception Conditions"
MOVDQU   "the operand may be unaligned to any alignment WITHOUT causing a
          general-protection exception (#GP) to be generated"
MOVUPS   the same sentence, the same table
```

⭐ **THE EXEMPTION IS THE PROOF OF THE RULE.** MOVDQU and MOVUPS sit in Type 4 and
are given an explicit licence to be unaligned. *An exemption from a requirement
that does not exist is vacuous.* So Type 4 carries a 16-byte `#GP` for every
member not so exempted — and `psrlw xmm,m128`, `pshufd xmm,m128,imm8` and `pand
xmm,m128` are all unexempted members of it.

**x86isa says the same, in its own source, independently of the manual.**
`logical.lisp` implements the legacy `pand`/`por`/`pxor` check literally —

```lisp
;; Raise an error if addr is not 16-byte aligned.
((when (not (eql (mod addr 16) 0)))
 (!!ms-fresh :memory-address-is-not-16-byte-aligned addr))
```

— and turns it off for the VEX form with the comment *"There is no alignment
checking (see Intel Manual Volume 2 Table 2-21)"*, which is exactly the
legacy/VEX split Type 4 encodes.

### ⛔⛔ And why it survived — the first answer was WRONG, and the true one is worse

This record first said *"no vector could construct the violation; every memory
vector addresses `(%rbx)` = 0x2000, which is aligned."* **That is false.**

```
psraw_m_disp   psraw 0x8(%rbx), %xmm5     ← 0x2008. NOT 16-byte aligned.
```

The vector exists, **P2 batch 13 added it in the same commit as the defect**, and
it **passed** — 88 pre-states, zero disagreements, inside a run reporting
`unexplained=0` over 78,584 cases. Repairing `.vshiftm` is what surfaced it: the
differential came back **264 unexplained**, all of them this one vector (88
pre-states × `xmm5`, `rip`, `refused`) and no other.

⇒ 🔑 **IT PASSED BECAUSE THE MODEL'S MISSING CHECK AND THE ORACLE'S MISSING CHECK
ARE THE SAME OMISSION** — x86isa implements the 16-byte rule in one file of its
tree and not in `pshift.lisp`. A model that should have faulted was compared
against an oracle that also does not fault, and the run reported agreement.

⇒ 🔑 **TWO DEFECTS THAT CANCEL SURVIVE EVERY GREEN RUN THAT COMPARES THEM TO EACH
OTHER.** A differential is blind to exactly the errors its two sides share, and
nothing inside it can report that. What broke the tie was not a vector and not the
oracle: the SDM read for a DIFFERENT group one screen away, plus x86isa's own
source contradicting its own behaviour.

⚠️ The false claim came from checking the vectors being ADDED for alignment and
generalising to the vectors already there without grepping the table for a
displacement — the load-bearing half of the explanation, sitting in the
incidental half of a finding whose main half is sound.

## 2. ⭐⭐ The oracle contradicts itself across ONE exception class

88 pre-states, one run, all at the same unaligned address `8(%rbx)`:

```
pand   8(%rbx),%xmm0    refused 88 of 88   ← POSITIVE CONTROL: the refusal IS visible
pand    (%rbx),%xmm0    refused  0 of 88   ← negative control, same opcode, aligned
pshufd 8(%rbx),%xmm0    refused  0 of 88
psrlw  8(%rbx),%xmm0    refused  0 of 88
movdqa 8(%rbx),%xmm0    refused  0 of 88   ← D91's reading, reproduced
```

`grep -rln 16-byte-aligned` over x86isa's whole instruction tree returns **one
file**. ⇒ 🔑 **THE ORACLE'S ALIGNMENT BEHAVIOUR IS A PROPERTY OF THE FILE THAT
IMPLEMENTS THE INSTRUCTION, NOT OF THE INSTRUCTION'S CLASS.** D108 found the
oracle disagreeing with itself across two SHAPES of one mnemonic; this is the
same defect one level up — across three MNEMONICS of one class.

⛔ **So D91's sentence needed its scope corrected, in the direction nobody
polices.** *"ACL2 x86isa does not implement the alignment check"* was measured on
`movdqa` and is true of `movdqa`; as a statement about the oracle it is false,
and it is the sentence that would have told the next head not to look.

⭐ **And the positive control is what makes the negative readings mean anything.**
Without `pand`, "nothing refused" is indistinguishable from a harness that cannot
see a refusal at all.

## 3. THE RULE IS A THEOREM, AND BOTH HALVES WERE DRIVEN RED

No vector can validate it — the oracle executes where this model faults, so a
vector would be a one-sided refusal counted UNEXPLAINED. So it is kernel-checked:

```
vshufm_unaligned_faults · vshufm_aligned_runs        (this batch's forms)
vshiftm_unaligned_faults · vshiftm_aligned_runs      (batch 13's, repaired)
vshuf_reads_only_the_source                          (the destination is not read)
```

⛔ **AND THE GATES WERE PROVED TO HAVE TEETH, not assumed to.** Each alignment
branch was deleted in turn from the shipped `Semantics.lean` and the tree rebuilt:

```
delete .vshiftm's branch  ⇒  red at Theorems.lean:1664  = vshiftm_unaligned_faults
delete .vshufm's branch   ⇒  red at Theorems.lean:1640  = vshufm_unaligned_faults
```

Each arm took **its own** theorem down and no other — so these are two independent
gates, not one gate wearing two names.

## 4. THE PERMUTE ITSELF — and the discrimination is measured per vector

Four independent origins agree on the field order **before a line was written**:
the SDM's pseudocode (`ORDER[7:6]`…`ORDER[1:0]`), K's
`pshufd_xmm_xmm_imm8.k` (`imm[7:6]`→lane 3 down to `imm[1:0]`→lane 0), LLVM's
disassembler comment (`$0x1b → xmm1[3,2,1,0]`), and x86isa's `pshuf-body-gen`.

Every shipped form was then run against **three models** — the SDM's, the
reversed-field one, and the identity — over all 88 pre-states:

```
                                    sdm  rev  ident   discriminating  distinct sources
pshufd  $0x1b %xmm1                  88    0      0        88 of 88          76
pshufd  $0x93 %xmm1                  88    5      0        88               76
pshufd  $0xe4 %xmm1                  88    0     88        88 vs rev, 0 vs ident ⚠️
pshufd  $0x1b %xmm3 → %xmm2          88    0      0        88               76
pshuflw $0x1b %xmm1                  88   28     28        60 of 88  ⚠️      76
pshufhw $0x1b %xmm1                  88    6      6        82               76
pshufd  $0x1b (%rbx)                 88    0      0        88               33
pshuflw $0x1b (%rbx)                 88   28     28        60 of 88  ⚠️      33
pshuflw $0x1b -16(%rbx)              88    0      0        88                1  ⚠️
pshufhw $0x1b -16(%rbx)              88    0      0        88                1  ⚠️
```

⛔⛔ **`pshuflw` AT A REGISTER SOURCE IS BLIND IN 28 OF 88 PRE-STATES, AND THE
REASON IS STRUCTURAL.** `xmmPattern`'s low quadword is `c ^^^ (i *
0x1111111111111111)`, whose four **words** are identical wherever `c`'s are —
which is every adversarial constant in the sweep. **A word-level permutation is
the first operation in this model whose correctness is invisible unless the
source's LANES DIFFER**, and these pre-states were built for arithmetic, where
lane uniformity costs nothing.

⭐ **The fix needed no new pre-state.** `-16(%rbx)` is 0x1ff0 — 16-byte aligned,
inside the watched data window, and `baseMem` fills it with 0xA0…0xAF, sixteen
distinct bytes. 88 of 88 discriminating. ⚠️ **And its source never MOVES**, which
is D14's *"one test reported as eighty-eight"*. So both sources are in the table
and each is read for what it prices: `(%rbx)` varies and discriminates weakly,
`-16(%rbx)` discriminates completely and does not vary. **Neither alone is
enough, and the pairing is the claim.**

⚠️ `$0xe4` is in the table and **prices exactly one thing**. It selects (0,1,2,3),
so it cannot distinguish this model from one that ignores the immediate — 88 of
88 agree with the identity. It discriminates the field ORDER completely, and that
is the only column it is counted in.

⚠️ `$0x1b` is a **palindrome**: a model reading the fields backwards returns the
identity there, which looks like a plausible register rather than a scrambled
one. `$0x93` is in the table for that reason alone.

## 5. ⚠️ THE PRICING WAS RE-MEASURED, AND THE FIRST RE-MEASUREMENT WAS WRONG

The handover's numbers are **exactly confirmed** — 9,049 · 2,660 · 355 · 642, and
1.53% — but the first run of this batch's own probe said 18,498 / 5,640 / 826 and
2.07%. It had filtered the corpus with `is_elf_x86_64` instead of `elf_targets`,
and **doubled every column that ships `libfoo.so.N` beside `libfoo.so.N.M.P`**.

⇒ 🔑 **A RULE THAT LIVES IN A FUNCTION IS BYPASSED BY REACHING PAST THE
FUNCTION**, and the bypass looks like ordinary code. `demand_census.elf_targets`
documents that exact defect in a ⛔⛔ comment — on the function that was not called.

⚠️ **What caught it was not the ratio.** The MMX share was 100% and the memory
share ~2% either way: a defect that scales numerator and denominator is invisible
to every percentage. What caught it were the two columns that **matched the
published census exactly** (`vlc-codec` 190, `vlc-video_chroma` 2,921) — which are
precisely the two with no symlinks. **The columns that agreed located the error in
the columns that did not.**

## 6. ⛔⛔ THE KERNEL-COST GATE ACCUSED THIS BATCH OF A REGRESSION THAT IS THE MACHINE

First reading, with the batch applied: `@tail` **13,160** against a ceiling of
12,420 — 740 ms OVER, and against batch 13's recorded 11,670 an apparent
**+1,490 ms**, which would have been by far the most expensive batch in the
project's history. It is not the batch. Measured on **this** machine, in one
session, alternating:

```
PARENT COMMIT 144e9a3 (batch removed)   12,970 · 13,030 · 13,060   loads 5.2 · 6.7 · 7.3
THIS BATCH APPLIED                      13,040 · 13,160 · 13,680   loads 6.6 · 6.5 · 7.9
ceiling                                 12,420
batch 13's recorded reading, SAME commit as the parent row          11,670
```

⇒ **The parent commit is itself 550 ms OVER the ceiling today**, before this batch
exists. And the two bands OVERLAP: the batch's lowest reading (13,040) is below
the parent's highest (13,060). ⚠️ **They are not identical, and this record does
not claim they are** — the batch's high reading is 620 ms above the parent's high,
and its three readings average ~230 ms above the parent's three. What the pairs
support is the weaker, true statement: **this batch's cost is not separable from
the ambient at this measurement's resolution**, and it is nowhere near the
+1,490 ms the first single reading implied. `vectorCoverage` likewise: 1,290
(parent) → 1,320 · 1,370.

⇒ 🔑 **A CEILING WHOSE MARGIN IS UNDER THE MACHINE'S OWN SPREAD REPORTS THE
MACHINE, NOT THE CODE.** The margin batch 13 recorded was 750 ms (6.4%); the
same commit reads **1,320 ms higher** this afternoon (11%), and the within-session
spread at one commit is ~90 ms while the across-session shift is fourteen times
that. The gate cannot tell a batch from a busy afternoon, and today it blamed the
batch — by an amount roughly six times the batch's own likely cost.

⛔ **THE CEILING IS NOT RAISED.** Deriving a gate's new allowance from the thing
it checks is how a gate stops being one, and the matched A/B says the code did not
grow. What is repaired is the gate's **verdict**: at a load outside the band its own
note records as calibrated (2.2–4.1), `kernel_cost.py` now reports
**UNMEASURABLE** and names the load it saw, instead of reporting OVER. It still
exits non-zero — a refusal is not a pass — but it no longer attributes an ambient
shift to a commit.

⛔ **AND THE CONSEQUENCE IS STATED RATHER THAN HIDDEN: on this machine, at today's
loads, THE GATE IS NOW SILENT.** Every reading in the table above is outside the
calibrated band. That is a worse gate than one that worked and a better one than
one that lies, and it is deliberately uncomfortable, because the fix is a
redesign this batch declines to smuggle in: **gate the DELTA between two trees
measured in one session, not an absolute against a fixed number.** That is the
instrument the table above was produced by hand; making it the tool is priced as
the next batch's first item, and it needs its own red probes (a gate that measures
two trees has two ways to measure the wrong one).

⚠️ **AND D105's ARITHMETIC IS RETIRED, NOT MERELY FALSIFIED.** Batch 13 measured
"~+200 ms per batch" against a "480 ms margin ⇒ two batches". Both numbers were
read off absolute figures whose machine-to-machine term is 1,320 ms. The per-batch
cost cannot be recovered from unmatched absolute readings at all; only a matched
A/B in one session can measure it, and this batch's is the first one taken.

## 7. RECEIPTS

```
cases=79816 matched=59284 explained=29435 unexplained=0 oracle-divergence=171 oracle-leaks=0 missing=0
907 vectors · 88 pre-states · 79816 cases · 0 unexplained · 0 oracle leaks
```

⭐ **171 oracle-divergences, unchanged from batch 13** — 163 + 8, and this batch
adds none. The permute group agrees with x86isa at every form and every
pre-state; the only disagreement this batch produced was the one it was supposed
to produce, at `psraw_m_disp`, and that vector's address was the finding rather
than a fault in the model.

⛔ **THE FIRST RUN OF THIS BATCH WAS RED — 264 unexplained — AND IT IS RECORDED
HERE RATHER THAN QUIETLY RE-RUN.** All 264 were the single vector §2 describes,
88 pre-states across `xmm5`, `rip` and `refused`. The red was the alignment
repair working on a form that had been agreeing with a defective oracle.

⚠️ **The kernel-cost gate is UNMEASURABLE, not CLEAN, and this record does not
call it CLEAN.** See §6: at load 6.4–7.9 it cannot separate this batch from the
afternoon, and the parent commit reads over the same ceiling.

### The three planted models, all CAUGHT on the shipped binary

```
the permute's immediate fields are read in reverse order   1019 in xmm0
the permute reads its DESTINATION instead of its source       84 in xmm2
pshuflw/pshufhw permute all eight words instead of four      582 in xmm0
filtered selftest: PASS
```

⭐ **Each number says which vector is carrying the arm, and each is the one the
table was built for.** Arm 2's 84 is `pshufd_x2x3` alone — the only vector whose
destination and source differ — and it is 84 of 88 rather than 88 because in four
pre-states `xmm2` and `xmm3` happen to permute to the same value. Arm 3's 582 is
the word forms alone: `pshufd` is untouched by that model, because `128/32` and
`8/2` are both 4, which is exactly why `pshuflw`/`pshufhw` carry vectors of their
own instead of riding on the doubleword's.

⛔ **There is no fourth arm for the alignment rule, and the absence is stated
rather than left as a gap.** Every memory vector in this table is aligned, so a
model with the `#GP` branch deleted agrees with this one on all of them. That
rule is gated by the kernel instead, and its red direction was demonstrated by
deleting each branch in turn.

The remaining local gates and the CI run URL are in the commit message.
