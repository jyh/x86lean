# P2 BATCH 13 — the packed binary group at a memory source, and the first alignment claim a RUN can check

> ⚠️ **TWO COUNTERS.** This is the **thirteenth differential record**
> (`docs/DIFFERENTIAL-P2-BATCH*.md` is a contiguous 1..N sequence, enforced by
> `scripts/check_coverage_prose.py`). The same work is the seat's **batch 15** in
> `docs/DECISIONS.md` and in the code comments, because that counter also numbers
> batches which add no forms and file no record. The offset is not constant.

**Forms.** The nineteen operations `Op.vbin` has carried since batches 5 and 7 —
`pand`/`por`/`pxor`, `padd{b,w,d,q}`, `psub{b,w,d,q}`, and the eight unpacks — at
their **memory** source. One constructor, 22 vectors, no new roster row and no
new state.

## 1. ⛔⛔ THE BATCH ADDS NO COVERAGE. IT REMOVES AN OVER-CLAIM.

Measured over the census's `asm` class, through the census's own disassembler:

```
                total      reg      mem      MMX      the model already CLAIMS
paddd          35,926   32,229    3,212      485      all 35,926 as covered
paddw          21,185   15,333    1,686    4,166
pxor           17,569   15,216      284    2,069
por            14,920   14,477       39      404
punpcklwd      15,338   14,536       26      776
psubw          12,236    8,165    1,139    2,932
punpcklbw      12,099    9,562      156    2,381
… (19 mnemonics)
                                  ─────
BUILDABLE (non-MMX)           166,269      memory share 7,705 = 4.63%
```

⇒ **The published coverage number does not move by one instruction**, because the
census counts by MNEMONIC and has counted all 182,286 of these as covered since
batch 7. What moves is that **7,705 of them stop being a lie**: until this batch
the model claimed `paddd` and could not execute `paddd (%rbx),%xmm0`.

🔑 That is the trade `Op.vshiftm` made at 0.85% (D107) — *"declining it would be
an over-claim no gate in this repository could see"* — arriving one order of
magnitude larger. **An over-claim is invisible to the instrument that produces
it**, and the only defence is to price the shape rather than the mnemonic.

## 2. ⭐⭐⭐ THE ALIGNMENT RULE IS DIFFERENTIALLY VALIDATED, FOR THE FIRST TIME

D91 (batch 6) recorded that the 16-byte `#GP` could not be tested by any vector:
the oracle executes where this model faults, so a vector would be a one-sided
refusal counted UNEXPLAINED. It went further, and correctly:

> *"`movdqa` ignores its alignment requirement` cannot be caught by any vector
> that can exist, and an arm no vector can distinguish is not a weak test but a
> FALSE ENTRY in the gate's own inventory."*

That held for nine batches. **D110 found why, and in finding why found the
exception**: x86isa implements the 16-byte check in exactly one file of its whole
tree — `logical.lisp` — and that file implements `pand`, `por` and `pxor`.

⭐ **THE SPLIT WAS PREDICTED FROM THE SOURCE BEFORE IT WAS MEASURED**, which is
the strongest form this evidence can take:

```
                            predicted    MEASURED (88 pre-states)
por       8(%rbx),%xmm0     refuses      refuses    88 of 88
paddd     8(%rbx),%xmm0     executes     executes    0 refused
psubw     8(%rbx),%xmm0     executes     executes    0 refused
punpcklbw 8(%rbx),%xmm0     executes     executes    0 refused
```

One exception class (SDM Table 2-21, Type 4), one operand size, two behaviours —
and the line between them is **which file implements the instruction**, not
anything about the instruction. So `pand_m_unal`, `por_m_unal` and `pxor_m_unal`
are vectors in which BOTH models refuse: `bothRefused` reports agreement, and the
rule is carried by evidence for three of the nineteen.

⚠️⚠️ **AND AGREEMENT BY MUTUAL REFUSAL IS SILENCE UNLESS SOMETHING PRICES IT.**
Two sides refusing is indistinguishable from two sides broken. So the arm D91
recorded as impossible is now written — `wrongVbinmIgnoresAlignment`, a model
that executes at an unaligned address — and it reports in `refused`, not in a
value. **Those three vectors are worth exactly what that arm catches.**

## 3. THE ORACLE WAS MEASURED AT THIS SHAPE, NOT INHERITED FROM THE OTHER ONE

D108's law: oracle support is a fact about a **(mnemonic, SHAPE) pair**. All
nineteen are validated at the register shape and NONE of them had ever been asked
at a memory source. Measured first, all 88 pre-states, against this model's own
`vbinApply`:

```
all 19 forms   agree = 88 of 88   discriminating 65-88   refused 0
```

⚠️ `pand` is the lowest at 65: AND against a source sharing bits is the likeliest
of the nineteen to leave the destination unchanged, so 23 pre-states cannot tell
this model from one that does nothing. Recorded per form rather than pooled.

## 4. THE OPERAND ORDER IS THE CONTENT, AND EIGHT FORMS DEPEND ON IT

`vbinApply k dst mem` — destination first. Eleven of the nineteen commute and
would be identical either way; `psub*` and the eight unpacks would not, because
`vbinApply`'s unpack arm takes its first argument as the DESTINATION, whose lane
goes LOW in every interleaved pair. `wrongVbinmOperandsSwapped` is planted for
it, and ⚠️ **it is caught only at the twelve non-commuting forms** — 672
disagreements in `xmm0`, where the eleven commuting ones contribute nothing. That
minority is the number to read: an arm caught by a minority of a group's vectors
is an arm whose group needed exactly those vectors.

## 4a. ⚠️ THE ARMS AND THE DIFFERENTIAL DO NOT SHARE A DENOMINATOR

`driveWrong` emits over **`preStates seed 4` = 84** pre-states; the differential
runs over **88**. So `wrongVbinmIgnoresAlignment`'s **252 is `84 × 3` — every case
of all three vectors**, not 252 of 264.

⛔ **The previous batch's record got this wrong and invented a mechanism for the
difference** (D114). It is written here beside the numbers so the next reader does
not have to derive it: **an arm's count is out of 84 per vector, a differential's
out of 88, and the two numbers sit one screen apart in every batch record.**

## 5. RECEIPTS

```
cases=81752 matched=61220 explained=29435 unexplained=0 oracle-divergence=171 oracle-leaks=0 missing=0
929 vectors · 88 pre-states · 81752 cases · 0 unexplained · 0 oracle leaks
  spec: 0   refusal: 0   harness: 0   undefined-region: 29435   oracle-divergence: 171
```

⭐ **`refusal: 0` is the interesting zero, and it was checked POSITIVELY rather
than read off the total.** At `pand_m_unal`, `por_m_unal` and `pxor_m_unal` both
models refuse, so `bothRefused` reports no disagreement — which is
indistinguishable, in a total, from a channel that never fired. Evaluated
directly on the shipped `step`:

```
pand_m_unal · por_m_unal · pxor_m_unal    stopped = true    (the model refuses)
pand_m · por_m · pxor_m · paddd_m         stopped = false   (and runs when aligned)
```

and the oracle's half was measured separately at 88 of 88. **Two sides, each
confirmed on its own, before the silence between them was called agreement.**

⚠️ 171 oracle-divergences, unchanged from batch 13; this batch adds none.

The remaining local gates and the CI run URL are in the commit message.
