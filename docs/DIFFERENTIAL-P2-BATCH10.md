# P2 BATCH 10 — the move family, and a rank that could not be built

**Forms.** `movaps` · `movups` · `movss` · `movsd` — ranks 2, 5, 6 and 11 of the demand list **as it
stood before this batch**, worth **59,840 instructions, 11.2% of the then-534,576 gap**. Sixteen
vectors, four mnemonics, and **no new state**: the XMM file and the 128-bit memory path both landed
earlier, which is the whole reason this batch is cheap.

⭐ **AND THE PRICE WAS CONFIRMED BY A ROUTE THAT IS NOT THE ROSTER.** Regenerating the census against
the new 111-mnemonic model moves the uncovered gap **534,576 → 474,736 — a fall of exactly 59,840**,
the number the roster quoted from the other side of the join. The roster reads K's tree and ranks
demand; the census walks the corpus and splits covered from uncovered. They agreed to the
instruction, which is the check worth having and the one a single artifact cannot give.

Per-column coverage moves: dav1d 60.6→61.2 · vlc-video_chroma 75.6→76.4 · vpx 84.1→86.6 ·
x264 84.8→86.1 · ffmpeg 93.2→94.3 · glibc 85.6→88.4 · vlc-codec 97.2→98.4 · kernel 99.5 (unmoved —
the kernel runs almost no SIMD, which is why it is never pooled with the codecs).

⚠️ **The corpus was verified before it was believed.** It survives only in an old session's
scratchpad, and two candidate directories exist. A model change must move the covered/uncovered
SPLIT and nothing else, so the corpus-side totals are the invariant: all **11 columns' instruction
totals are byte-identical** across the regeneration. That is what says this is the same corpus and
not a plausible neighbour.

```
cases=73444  matched=53399  explained=28774  unexplained=0  oracle-divergence=159  oracle-leaks=0  missing=0
854 vectors · 86 pre-states · P1 roster unchanged at 500/525
```

16 new vectors × 86 pre-states = 1,376 new cases; `matched` rose by exactly 1,376 and `explained`
did not move at all — the right shape for a group that writes no flag, and also what a run would
look like if the new fields were not compared, which is why the batch is sealed on its ARMS.

## 1. ⛔ The batch is not the one the candidate list ranked first, and that is the finding

The relight handed on a candidate list "trustworthy for the first time": rank 1 `pmaddwd`, rank 2
`movaps`, rank 3 `psubusw`. **Two of those three cannot be built at all.** Re-measured live before
anything was written — nine seconds, both controls behaving:

```
✔ movaps    movaps (%rbx), %xmm0        refuses(CR4=0)   executes(CR4=0x600)
✔ pmaddwd   pmaddwd %xmm1, %xmm0        refuses          refuses
✔ psubusw   psubusw %xmm1, %xmm0        refuses          refuses
✔ CONTROL:mov     movl %ecx,(%rbx)      executes         executes
✔ CONTROL:movnti  movntil %ecx,(%rbx)   refuses          refuses
```

The knowledge was not new — `oracle_availability.py` has held the nine refusing mnemonics since P2
batch 1, gated in both directions. It was in the wrong file. The roster joins **demand** (the
census) against **supply** (K's tree) and consults no third artifact, so a form the ORACLE cannot
execute is priced exactly like one it can.

⇒ 🔑 **A ROSTER THAT PRICES DEMAND DOES NOT PRICE BUILDABILITY, AND THE TWO LOOK THE SAME IN A
RANKED TABLE.** This is D100's defect on the other side of the same join: there the demand belonged
to another instruction, here the supply is one the differential cannot ask about.

The roster now carries an `oracle` column, **emitted and consumed in the same batch**. What the next
head is handed after this batch reads, at a glance:

| rank | mnemonic | occurrences | oracle | |
|---|---|---|---|---|
| 1 | `pmaddwd` | 21,239 | ⛔ REFUSES | not buildable |
| 2 | `psubusw` | 17,214 | ⛔ REFUSES | not buildable |
| 3 | `vmovdqa` | 16,813 | ✔ | VEX — out of scope by `EXT_SCOPE` |
| **4** | **`psrad`** | **12,394** | **✔** | **the first buildable rank** |
| 5 | `vpaddw` | 11,682 | ⚠️ not measured | VEX — out of scope |
| 6 | `movq` | 11,109 | ✔ | ⛔ PHANTOM ROW (100% MMX) |
| 7 | `vpaddd` | 10,950 | ✔ | VEX — out of scope |
| **8** | **`pshufd`** | **9,049** | **✔** | **buildable** |

⇒ The next batch is the shift group (`psrad`, and `psllw`/`psrlw`/`psraw` below it) plus `pshufd` —
and that is now readable from the table instead of costing a measurement to rediscover.

## 2. ⭐⭐ "Executes" is not "implements", so the rule itself was probed

`movss`/`movsd` have two operation clauses under one mnemonic, and an oracle could execute both and
answer wrongly. So the RULE was measured, not the availability: xmm0 all-ones, xmm1 a byte ramp,
memory a second ramp, with **three controls covering all three candidate behaviours**.

| form | oracle returned | |
|---|---|---|
| `movdqa %xmm1,%xmm0` (control) | `0f0e…0100` | full copy ✔ |
| `movd %ecx,%xmm0` (control) | `ffff…05060708` | **merge** — x86isa's known defect, D93 |
| `movq %xmm1,%xmm0` (control) | zero-extends | ✔ |
| `movss %xmm1,%xmm0` | `ffffffffffffffffffffffff03020100` | **merge** ✔ SDM |
| `movsd %xmm1,%xmm0` | `ffffffffffffffff0706050403020100` | **merge** ✔ SDM |
| `movss (%rbx),%xmm0` | `000000000000000000000000a3a2a1a0` | **zero** ✔ SDM |
| `movsd (%rbx),%xmm0` | `0000000000000000a7a6a5a4a3a2a1a0` | **zero** ✔ SDM |

The oracle returns the SDM's answer in all four discriminating cases — which is what makes this
batch differentially validatable where batch 7's `movd` was not. ⭐ The `movd` control reproduced
D93 **from a route that is not the differential**, which is also what proves the probe discriminates
rather than merely agreeing.

## 3. The rule, and why it needed both shapes

The destination rule depends on **where the source lives** — the first form in this model whose
semantics reads the provenance of a value rather than the value:

* from a REGISTER the upper bits are **PRESERVED** (objdump prints the merge itself:
  `xmm0 = xmm1[0],xmm0[1,2,3]`);
* from MEMORY they are **CLEARED**.

⛔ A model that always merged and a model that always zeroed are each **bit-identical to this one on
half the vectors**, and both are indistinguishable from it at any pre-state whose destination XMM
register is zero. Both are planted, and they fire:

| arm | caught in |
|---|---|
| `movss`/`movsd` from a register ZERO the upper bits instead of preserving them | see §4 |
| `movss`/`movsd` from memory MERGE into the upper bits instead of clearing them | see §4 |
| `movss`/`movsd` ignore their register fields | see §4 |
| `movss` and `movsd` swap widths | see §4 |
| a scalar store writes all sixteen bytes | see §4 |

⚠️ `movss_x4x5` and `movsd_x4x5` exist **before** the run rather than after it. Batch 5 learned that
lesson the expensive way — with only x0←x1 vectors, a model ignoring the register fields is
bit-identical to the right one — and this batch did not re-learn it.

`movaps`/`movups` add no new state transition: they are the same 128-bit move under two more
opcodes. `aligned : Bool` therefore became `VMovKind`, a four-way mnemonic from which the alignment
rule is **derived** rather than stored beside it, and `vmov_aligned_irrelevant` became
`vmov_kind_irrelevant` over all four kinds. `vload_unaligned_faults` now quantifies over
`k.aligned = true`, so it covers `movaps` as well as `movdqa` — the theorem grew with the type
instead of being restated.

## 4. ARMS — and every count is accounted for

Five planted wrong models, all CAUGHT, in the field the bug is in:

| arm | caught in | of a possible |
|---|---|---|
| `movss`/`movsd` from a register ZERO the upper bits instead of preserving them | **151** (`xmm0`) | 164 |
| `movss`/`movsd` from memory MERGE into the upper bits instead of clearing them | **151** (`xmm0`) | 164 |
| `movss`/`movsd` ignore their register fields | **164** (`xmm4`) | 164 |
| `movss` and `movsd` swap widths | **234** (`xmm0`) | 328 |
| a scalar store writes all sixteen bytes | **164** (`mem@…1fe0`) | 164 |

⛔ **THREE OF THEM DO NOT FIRE IN EVERY CASE, AND THE SHORTFALL IS A MEASUREMENT ABOUT THE
PRE-STATES RATHER THAN A WEAKNESS IN THE ARM.** Batch 9 wrote a worry of this shape into an AST
comment and then measured it; here the numbers were closed rather than described.

`xmmPattern` gives register *r* the value `(a + r) : (c ⊕ r·0x1111…)`, so **xmm0 is `a : c`**. Merge
and zero are the same function exactly where the half that would be PRESERVED is already zero:

```
xmm0's bits 127:64 are zero in   8 of 82 pre-states   -> the movsd arms are blind there
xmm0's bits 127:32 are zero in   5 of 82 pre-states   -> the movss arms are blind there
                                ---
                                13 = 164 - 151        exactly, both arms
```

`a = 0` is in the adversarial list, which is why those 8 exist at all; and xmm4's high half is
`a + 4`, never zero over this list — which is why the register-fields arm fires in **all** 164.

The width-swap arm closes the same way: between registers the swap is visible in **every** case
(xmm1's low half is `c ⊕ 0x1111…` against xmm0's `c`, so their bits 63:32 always differ — 2 × 82 =
164), and at memory it is visible exactly when the loaded quadword's bits 63:32 are nonzero, which
is **35** of 82 pre-states — 2 × 35 = 70. **164 + 70 = 234.** Measured, not inferred.

⇒ 🔑 **AN ARM THAT FIRES IN 92% OF ITS CASES IS NOT A WEAKER ARM THAN ONE THAT FIRES IN 100% — IT IS
AN ARM WHOSE BLIND CASES YOU HAVE COUNTED.** The number that would have been the finding is a
*small* one: had these arms fired in 20 cases, the pre-states, not the model, would have been the
batch.

## 5. ⛔ The kernel-cost gate refused, and it named a cheaper build

`memDestSweep` measured **19,900 ms** against a 19,360 ms ceiling. The ceiling was registered at P1
batch 21 as `12,100 × 1.6`; the declaration has grown **62%** across the P2 wave and this batch is
the one that crosses.

⚠️ **Load was not the excuse, and the tool says so itself**: its own conditions line records that
this load band (2.2–4.1) has no measured effect on this module. A gate that prints its own
conditions is what makes that a fact rather than a hope.

**Where the money is, measured rather than assumed** — because a total cannot see its parts, and
this file has mis-attributed its own money once before (D62):

| conjunct | kernel ms |
|---|---|
| the loose-vs-strict string sweep over `Row.shapes` | **~18,800 of 19,600 (96%)** |
| `hasMemDestVector`'s 854-vector sweeps | ~800 |

⇒ 🔑 **`Row.shapes` IS A KERNEL-WALKED FIELD, SO PROSE IN IT IS A COST.** The four new rows carried
~340 characters of explanation and **1,500 ms** of kernel time with it. The explanation was not
deleted; it moved to the AST docstrings, where nothing reduces it. Trimmed: **18,400 ms**, three
readings within 1%.

⛔ **This is a REPEAT, not a discovery.** D94 recorded the identical mechanism in the identical
declaration and field. The lesson was written down and re-paid, because in an editor a string looks
like a comment. What is new is only the decomposition below.

⭐ **And the gate's conditions line earned itself, twice in one batch.** Run again while the full
100-arm selftest was executing on the same box, the same tree measured **~20,200 ms and the gate
FAILED** — inside the 4–8% contention penalty the tool prints about itself. Four readings on a box
not running the selftest: **18,500 / 18,400 / 18,400 / 18,500**.

⇒ 🔑 **A GATE CALIBRATED ON A QUIET MACHINE MUST BE RUN ON ONE**, and the way to know which you have
is that the tool says so in its own output rather than in a comment somebody has to remember. The
FAIL was not a regression and would have been read as one.

⛔ **AND THE PASS IS THIN, WHICH IS THE PART WORTH WRITING DOWN.** 18,400 of 19,360 is **95%** of the
ceiling. Read the margin, not the verdict: the next batch crosses again, and the answer then is not
a looser number — it is that the loose predicate walks a documentation field, and the disagreement
list it exists to pin down would change if it stopped. That is a design question, and it is now
priced.

## 6. What is NOT claimed

* The unaligned `movaps` fault is **proved, not vectored** — the oracle does not implement the check
  (D91), exactly as for `movdqa`. `movups_load_unal` is the unaligned case that CAN be validated.
* `movaps` and `movdqa` are one state transition here. The domain-crossing penalty that separates
  them on real silicon is **microarchitectural** and no architectural state in this model, or in the
  SDM, can observe it.
* ⚠️ `check_encodings.py` gates SEGMENT, LOCK and SYNONYM spellings and **not** operand register
  fields — a planted byte/AST mismatch passes it. That is its scope, not a defect: the differential
  covers the claim, because the oracle decodes the real bytes. Written here so the next reader does
  not mistake its green for a claim it never made.
