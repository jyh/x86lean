# P2 BATCH 19 — the bitwise complement, and a group that was never blocked

```
cases=85976  matched=65444  explained=29435  unexplained=0  oracle-divergence=171  oracle-leaks=0  missing=0
977 vectors · 88 pre-states · 85976 cases · 0 unexplained · 0 oracle leaks
```

> ⚠️ **TWO COUNTERS.** Nineteenth differential record; the seat's **batch 34** in
> `docs/DECISIONS.md` (D157).

**Forms.** `pandn`, `andnps`, `andnpd` — one function at three opcodes — and the
`ps`/`pd` spellings of AND/OR/XOR: `andps`, `andpd`, `orps`, `orpd`, `xorps`,
`xorpd`. **Nine roster rows, 21 vectors, ONE new function, NO new constructor and
NO new state**: they are `VBinKind` members, so `Op.vbin` and `Op.vbinm` carried
both operand shapes already. 3,556 instructions of assembly-class demand.

## 1. ⭐⭐⭐ THE GROUP WAS DERIVED, AND IT WAS THE COMPLEMENT OF A CORRECT PARTITION

`docs/QUEUE.md`'s P2 item 2 — *"land the buildable groups the census has
surfaced"* — never named a group, and the reason is worth more than the batch.
The P2 roster's ranked table prints its top FORTY rows, and every unclaimed row
there that the oracle executes is either VEX (a new capability) or scalar FP (the
soft-float commission). Read there, the residue looks blocked on one of two large
additions.

```
  64 unclaimed SSE-legacy (xmm) pairs EXECUTE on the oracle   47,965 instructions
− 40 that are the soft-float commission's                     36,925
= 24 pairs that need NO rounding rule at all                  11,040
```

⚠️ **THESE ARE PRE-BATCH FIGURES AND `p2_residue.py` NO LONGER PRINTS THEM.** Gap demand
for a COVERED mnemonic is zero, so landing the nine moved the residue to **55 pairs /
44,409** in the same instant. The number to re-derive is today's; `47,965` is a reading
dated 2026-09-06 and is kept because it is what made the group visible.

⇒ 🔑 **A CATEGORY NAMED FOR WHAT IT CONTAINS SAYS NOTHING ABOUT ITS COMPLEMENT.**
The commission partitioned the FLOATING-POINT mnemonics correctly and completely.
What nothing named was the set it left behind, whose members read as "FP" in a
ranked table only because their mnemonics end in `ps`/`pd`. **Being FP-TYPED is
not being FP-VALUED**: `xorps` reads no exponent, consults no MXCSR, rounds
nothing.

⭐ The split is DERIVED and GATED now, not asserted — `scripts/p2_residue.py`,
three gates, **selftest 4 of 4 arms with the control first**. Gate 3 re-derives
the commission's own published `12/6,619`, `2/898` and `26/29,408` from the live
census and refuses if they move: the defect the commission's §2 records about
itself, turned into a gate.
⛔ It proves the DOC AND THE CENSUS AGREE, not that either is right.

## 2. ⛔⛔ `ANDN` IS ASYMMETRIC, ON TWO INDEPENDENT SOURCES

`DEST ← (NOT DEST) AND SRC`: the DESTINATION is complemented. The model a reader
writes from the mnemonic is `DEST AND (NOT SRC)`, a different function everywhere
the operands differ.

⭐ Confirmed on K before a line was written: `pandn_xmm_xmm.k` reads
`andMInt(negMInt(DEST), SRC)` — and `negMInt` is **one's complement**, not
arithmetic negation, read off `sbbb_rh_imm8.k` where `a + negMInt(b)` is the CF=1
arm of `a − b − CF` and can only be bitwise NOT. A rule this easy to get backwards
is not taken from one reading.

## 3. ⚠️ SIX OF THE NINE ARE NEW ENCODINGS OF AN OPERATION ALREADY HERE

They are separate KINDS because the BYTES differ — `pand` `66 0f db`, `andps`
`0f 54`, `andpd` `66 0f 54`, measured on the assembler. That is the
`movdqa`/`movaps` rule (`VMovKind`), **not** the `pmovmskb` r32/r64 one, where
batch 18 refused a width field because the two spellings emitted identical bytes
and no encoding could set it.

⭐ Their semantics is shared by NOT branching on the kind: nine kinds, three arms
in `vbinApply`, one new function. And the identity claim is a **theorem**
(`bitwise_aliases_are_their_integer_siblings`), because **no differential vector
tests a spelling against its sibling** — each is tested only against the oracle,
so a mis-wiring would publish six wrong rows and no run would say so. Driven red:
routing `.andps` to `|||` breaks it.

## 4. THE RUN

`unexplained=0`, `oracle-leaks=0`, `missing=0` — the exit criterion, on the first run with
all 21 new vectors present. The 29,435 explained cases are all `undefined-region`, the
inherited class, and `spec`, `refusal` and `harness` are each **0**.

⚠️ **`oracle-divergence=171` IS UNCHANGED BY THIS BATCH, AND THAT IS CHECKED RATHER THAN
ASSUMED.** The declared list holds ten entries and `divergenceFor` matches a vector id by
EXACT equality after stripping the `/n` pre-state suffix — not by prefix — so `pandn_xx`
could not be captured by a `pand…` entry even if one existed. Verified both ways: none of
this batch's 21 ids equals a declared `vec`, and none is prefixed by one either.

## 5. ⛔ THE KERNEL-COST GATE REFUSED, AND THE ABSOLUTE CEILINGS WERE ALREADY OVER

```
⛔ UNMEASURABLE — one-minute load 16.28, outside the band this tool's effect
   measurement covers (0.0-4.1)
X86.Syntax                    236.0 / 200    OVER      ⚠️ over BEFORE this batch
Tests.Coverage @vectorCoverage 1860 / 1760   OVER
Tests.Coverage @residue       15660 / 12420  OVER      ⚠️ over BEFORE this batch
```

⛔ **THESE ARE READINGS, NOT A VERDICT.** The helm retired the absolute ceilings as a merge
gate on 2026-09-04 21:42; the merge gate is the kernel-DELTA gate (D111), which measures two
trees in ONE session so that shared conditions cancel. And two of the three overages are
inherited: batch 32's record already reports the base over `X86.Syntax 250/200` and
`Tests.Coverage @residue 15,210/12,420` before it touched anything.

⚠️ **AND THE LOAD FIGURE IS NOT COMPUTE.** Measured at the same moment: the box's top
consumers were `WindowServer` (33%), a Logitech agent (26%), two WebKit content processes
(22% each) and a wallpaper extension (13%) — **no Lean build was running at all**. That is
D149/D151's finding reproduced: a one-minute load is dominated by short-lived runnable
processes, so "load 16.28" and "load 4" can describe the same machine for compute purposes.
The gate is right to refuse — its band is calibrated in the units it has — but a reader
should not take 16.28 as evidence that this box was busy building.
[[feedback-a-measurement-without-its-conditions]]

## 6. ⛔⛔ THE CENSUS HAD TO BE REGENERATED, AND MY FIRST CORPUS WAS NOT THE SAME CORPUS

Any roster change makes `docs/DEMAND-CENSUS.md` stale — it records the model sha it was
generated against, and `demand_census.py --check` returns rc 1 until it is rebuilt. The
corpus is public Debian, downloaded and never vendored, and the recipe is in the document.

⛔ **THE FIRST REBUILD SILENTLY USED A DIFFERENT CORPUS.** The recipe says to unpack each
package into its column directory and let the script's own ELF walk choose; I hand-picked
files instead — `libc.so.6`/`libm.so.6`/`ld-linux*` for glibc, `usr/bin/*` for coreutils,
`cc1*` for cc1. Every gate would have passed. The document would have published coverage
percentages computed over a corpus nobody else can rebuild.

⭐ **WHAT CAUGHT IT WAS A FINGERPRINT, NOT A GATE**: the RAW per-column instruction totals,
which are a property of the corpus alone and must not move when the MODEL grows.

```
  column        committed      first rebuild
  cc1           5,379,923      5,272,820   ⛔ −107,103
  glibc           603,554        525,743   ⛔  −77,811
  coreutils       879,551        873,099   ⛔   −6,452
  dav1d · ffmpeg · vlc-* · vpx · x264 · vmlinux   ✔ identical
```

The three that moved are exactly the three I hand-picked; the six I unpacked whole matched
to the instruction. Rebuilt with whole trees, **all eleven columns reproduce exactly**, and
only the coverage attribution moves — which is what a roster change is supposed to move.

⭐⭐ **AND THE RECOMPUTED CENSUS AGREES WITH THE ROSTER TO THE INSTRUCTION.** The pooled
assembly class gained **+3,556** covered instructions — the same 3,556 this batch's nine
mnemonics are priced at by `p2_roster.bucket_demand`, computed by a different route from a
different input. Two independent sources, one number.
🔑 A regenerated artifact needs a quantity that must NOT change to prove the input was the
same one. [[feedback-two-readings-are-not-two-witnesses]]

## 7. THE ARMS — both caught, and the identical counts are the finding

```
harness selftest (filtered by "andn") — 2 of 123 arms
  ✔ andn complements its SOURCE instead of its destination   504 disagreements in xmm0 (588 total)
  ✔ andn is read as NAND, complementing the result           504 disagreements in xmm0 (588 total)
filtered selftest: PASS
```

⚠️ **BOTH NAMES CONTAIN `andn`, DELIBERATELY** — one filter selects both, the D116 §5 rule,
written after batch 17 shipped two arms sharing no substring so `selftest <pat>` ran half of them
and printed PASS.

⛔⛔ **AND THE TWO COUNTS ARE IDENTICAL, IN IDENTICAL FIELDS, WHICH IS THE SIGNATURE OF ONE ARM
WEARING TWO NAMES.** Checked rather than admired. Over all 60 register-shape pre-states:

```
  arm 1 (swap) fires on   60
  arm 2 (NAND) fires on   60
  INTERSECTION            60      ⇒ refuted on exactly the same cases
```

The models are genuinely different — `andn_is_not_its_operand_swap` and `andn_is_not_nand` are
separate witnesses, and neither equals the other. What is duplicated is not the MODEL but the
COVERAGE: `504` is a property of how many ANDN cases this vector table executes and compares, not
of either arm's discrimination. Arm 2 rules out a second misreading and adds **no case arm 1 did
not already cover**.

⇒ 🔑 Two arms that agree to the case are one measurement reported twice; say which of the two
things is duplicated before spending the second arm's wall-clock (≈13 min each here).
[[feedback-two-arms-that-agree-to-the-case]] [[feedback-an-implied-assertion-is-not-a-second-gate]]

## 8. THE MERGE GATE — 21 of 23 units `ok`, and the two refusals are the INSTRUMENT

`kernel_delta.py --base 8a74e36 --head 5c1f09e --repeats 3`, box `yukon.lan`, 14 cpus,
load(1/5/15) 9.62/11.15/10.66, passes alternated base/head at loads 11.90 7.62 12.24 9.19 11.91 13.64.

```
UNIT                                       base      head     delta    ±K*se   budget  VERDICT
Tests.Coverage                          24000.0   25100.0   +1100.0    204.7   1728.0  ok
Tests.Coverage @residue                 14840.0   15660.0    +820.0    207.2   2062.8  ok
Tests.Coverage @decl memDestSweep        5420.0    5580.0    +160.0    155.0    466.1  ok
Tests.Coverage @decl vectorCoverage      1660.0    1890.0    +230.0     39.2    260.6  UNMEASURABLE ⛔
X86.Coverage                                7.8       8.3      +0.5      8.5      6.0  UNMEASURABLE ⛔
X86.Syntax                                232.0     236.0      +4.0     24.2     43.4  ok
X86.Theorems                              953.0     979.0     +26.0     17.8    174.4  ok
                                    … 21 of 23 units ok …
```

⛔ **UNMEASURABLE IS NOT A GREEN, AND THIS RECORD DOES NOT CLAIM ONE.** What it does say is what
the two refusals are made of, because the word is the same in both and the readings are not:

* **`vectorCoverage` +230.0 against a budget of 260.6** — the point estimate is INSIDE the
  allowance at 88% of it, and the band `±39.2` straddles the line (`[190.8, 269.2]`). The worst
  case in that interval is 3% over. This is the batch's own cost: 21 vectors at ~11 ms each.
* **`X86.Coverage` +0.5 against a budget of 6.0** — a HALF-MILLISECOND delta, refused because the
  band (`±8.5`) is larger than the `@floor 6` budget itself. ⛔ **No repeat count fixes that**, and
  it is not a fact about this commit: it is QUEUE item 4 — the gated unit is noisier than the
  budget it is gated against — appearing on a unit this batch barely touched.

⛔ **THE GATE'S OWN ADVICE, AND WHY ONE ARM OF IT IS ALREADY REFUTED.** It offers: buy repeats,
quiet the box, or make the commit cheaper. **Repeats are the refuted route** — D153 measured the
spread SATURATING at n≈3-4, and `repeats_to_decide` models the band as falling like `1/sqrt(n)`
without a floor, so it will always name an N for a question no N answers. Its "~5 repeats a side
would decide it" is that projection, not a promise.

⭐⭐ **THE NUMBER THE NEXT BATCH NEEDS, AND IT IS THE REAL FINDING HERE.** At ~11 ms per vector
against a 260.6 ms allowance, `vectorCoverage` affords roughly **24 vectors per batch**. This batch
spent **21**. ⇒ The next vector batch on this declaration does not have room, whatever it contains,
and sizing it by vector count is no longer advice — it is arithmetic.
[[feedback-a-pass-at-97-percent-is-not-headroom]]

⚠️ Housekeeping, not a complaint: `git worktree list` shows two full checkouts left behind by an
EARLIER delta run (`x86lean-delta-9ceaj7ek/base` at `42f0a8b`, `/head` at `8a74e36`) plus
`/private/tmp/x86ci`. This run cleaned up after itself; those did not. They are stale registrations
and leaked disk, and `_own_tree` will count them as this repository's.
