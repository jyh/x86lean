# P2 BATCH 11 — the packed shifts, and a count that does not wrap

> ⚠️ **TWO COUNTERS, BOTH SPELLED "P2 batch N", AND THEY HAVE DRIFTED.** This file
> is the **eleventh differential record** (`docs/DIFFERENTIAL-P2-BATCH*.md` is a
> contiguous 1..N sequence, and `scripts/check_coverage_prose.py` enforces the
> contiguity). The same work is the seat's **batch 13** in `docs/DECISIONS.md`
> and in the code comments, because that counter also numbers batches which add
> no forms and therefore file no differential record — batches 12 and 13 of the
> decisions counter (D102–D105) were kernel-ceiling and CI work. The offset is
> not constant and never has been; the mapping is recorded here rather than left
> for the next head to rediscover.

**Forms.** `psllw`/`pslld`/`psllq` · `psrlw`/`psrld`/`psrlq` · `psraw`/`psrad` at **three count
shapes each**, plus the two whole-register byte shifts `pslldq`/`psrldq`. Ten roster rows,
twenty-six forms, thirty-nine vectors, and **no new state** — the XMM file and the 128-bit memory
path both landed earlier, which is what makes a batch this wide affordable.

⛔ **THE GROUP IS WORTH 32,882 INSTRUCTIONS, NOT THE 35,704 THE ROSTER RANKS.** The roster prices
demand by mnemonic; **2,822 of these instructions (7.9%) are MMX-register forms**, and this model
has no MMX register file. The two numbers were reconciled to the instruction rather than left to
disagree — see §4.

## 1. ⭐⭐⭐ The batch is the SATURATION RULE, and a green run without it means nothing

A packed shift whose count reaches the lane width does not wrap: the SDM sets the lane to all 0s for
a logical shift, and to the lane's own sign bit repeated for an arithmetic one (Vol. 2B,
PSLLW/PSRLW/PSRAW). **A model that took the count MODULO the lane width is bit-identical to the
right one at every in-range count** — which is every count a casual vector table contains.

⛔ **THE ORACLE WAS MEASURED BEFORE A LINE WAS WRITTEN, because the batch was handed on with the
sentence "the saturating-count rule measured IMPLEMENTED" and NO ARTIFACT IN THE TREE SAID SO.** An
oracle that had no rule for out-of-range counts would have agreed with any model over vectors that
never left the range ([[the-oracle-is-evidence-not-the-specification]]). Three models were compared
against x86isa's own answers in one run — the SDM's, the modulo one, and one reading only the
count's low byte:

```
42 rows, all 42 agree with the SDM
20 rows DISCRIMINATING — a wrong model gives a different answer there
22 rows priced at NOTHING, and printed as such rather than counted as support
```

⚠️ **The 22 unpriced rows are reported, not hidden.** Every in-range count (`$3`) agrees under all
three models, so those rows demonstrate that the harness runs — not that the rule holds. A probe
that counted them as passes would have been 42 for 42 and worth 20.

## 2. ⛔⛔ The guard is not the SDM's rule alone — the unguarded left shift KILLS THE TOOLCHAIN

`vshiftLane` refuses to shift when `cnt ≥ w`. For the two RIGHT shifts that guard is redundant:
Lean's `>>>` and `sshiftRight` already saturate at any count. For the LEFT shift it is not
redundant, and the failure is not a wrong answer:

```
x <<< (4294967299 : Nat)   ⇒   INTERNAL PANIC: Nat.shiftl exponent is too big
```

4294967299 is 2³² + 3 — a count `psllw %xmm1,%xmm0` reads whenever the count register's low quadword
holds it, and the differential's own pre-state sweep produces counts of that size in quantity.
Measured in **BOTH TIERS**: the interpreter (`#eval`) and the **kernel** (`by decide`), so the guard
protects the coverage theorems as well as the executable.

⇒ 🔑 **THE ASYMMETRY IS WHAT MAKES THIS DANGEROUS.** Remove the guard and every `psrl`/`psra` vector
still passes; only `psll` at a large register count fails, and it fails by taking the build down
rather than by disagreeing. A partial removal — or a partial repair — is invisible to any run that
only checks answers.

⛔ **A THEOREM CANNOT STATE THIS**: a Lean declaration that panics does not fail to elaborate, it
kills the process. So it is `scripts/shift_guard_redprobe.sh`, wired into CI, which **plants the
unguarded spelling** rather than describing it — 4 arms in 0.8 s (a control, two red, and one HELD
OUT: the right shifts must stay quiet, because their silence is the defect's cover).

## 3. The AST departs from `VBinKind`, and the burden is on the departure

`VBinKind` puts the lane width in the kind (`addb`/`addw`/`addd`/`addq`). The shifts use a
**product** — `VShiftOp × VShiftW` — with a `vshiftEncodable` table. The reason is that `VBinKind`
has **no hole**: add and sub exist at all four lane widths, so it never had an absent pair to
represent. The shifts have two, and both are encoding facts:

* there is no packed BYTE shift at any of the three operations;
* there is no `psraq` — `psllq` and `psrlq` exist, and the ARITHMETIC right shift stops at the
  doubleword. (`psraq` is real, and EVEX-only: the AVX-512 batch whose oracle this project has
  already measured it cannot answer.)

A flat eight-constructor list would have made "there is no `psraq`" an ABSENCE, and an absence in a
declared list falls the way the default points ([[a-declared-list-inherits-its-default]]). As data,
it is a table a theorem reads: `vshift_declined_pairs_are_exactly_the_unencodable_ones` states the
exact four pairs — **as pairs, not as a count**, because the pair a reader will get wrong is `sra`
at `w64`, precisely the one a count hides.

⭐ And `vshift_roster_names_exactly_the_encodable_pairs` gates it in **both directions**: a spare
`psraq` row would be an over-claim the forward direction cannot see.

## 4. ⭐⭐ TWO ROUTES, AND THEY DISAGREED UNTIL THE THIRD FACT WAS MEASURED

Batch 10's check is that the census's fall and the roster's demand — opposite sides of the same join
— agree to the instruction. They did not:

```
assembly-class gap  474,736 -> 441,854      fall = 32,882
the roster's number for the shift group                 35,704
                                            difference   2,822
```

⛔ **The difference was measured, not explained away.** Counting the group's operands directly:
**2,822 of the 35,704 are MMX-register forms** (`psllq` 36.4%, `psrlq` 24.3%, `psraw` 19.0%,
`psllw` 15.4%, … `psrad` 1.8%, `pslldq`/`psrldq` 0%), and the census correctly declines to count
them as covered because this model has no MMX register file. `35,704 − 2,822 = 32,882` — **exact**.

⭐ The per-mnemonic MMX shares independently reproduce the roster's own *"of it, MMX"* column, which
was derived by a different route. Three artifacts, one number.

⚠️ **All 11 columns' instruction totals are byte-identical across the regeneration**, which is what
says this is the same corpus and not a plausible neighbour — the invariant batch 10 established
after finding two candidate corpus directories.

## 5. The operand-shape split, measured, and why `x,m` was BUILT rather than declined

The census counts by MNEMONIC and says so: *"an operand shape the model lacks is still counted as
covered if the mnemonic matches."* So a batch that built `x,i` and `x,x` and declined `x,m` would be
counted at 100% of the group's demand while covering less, **and no gate in this repository could
see the difference.** Measured over the 6 codec columns, on BOTH candidate corpora, agreeing
exactly, and matching the census's per-mnemonic counts 10 of 10:

```
              x,i (immediate)   x,x (vector reg)   x,m (MEMORY)
   total           34,630              769             305
   share           96.99%            2.15%           0.85%
```

0.85% is small — and it is exactly the size of the over-claim that declining it would have made
invisible. The oracle was measured on the memory shape too, since **12 of 12 does not license the
13th** ([[a-batch-cannot-be-sampled]]): `x,m` had never appeared in any row of
`oracle_availability.py`. It executes, and returns the SDM value, with both controls behaving.

## 6. ⛔⛔ THE RUN FOUND A DEFECT IN THE ORACLE, and the memory shape is what proved it

```
cases=78584  matched=58052  explained=29435  unexplained=0  oracle-divergence=171  oracle-leaks=0  missing=0
893 vectors · 88 pre-states · P1 roster unchanged at 500/525
```

⚠️ **THAT IS THE SETTLED RUN.** The FIRST run of this batch reported `unexplained=8`
and `oracle-divergence=163`; the eight are the finding below, and once they are declared the
divergence count moves to **exactly 163 + 8 = 171** — a number predicted before the run and
checked after, which is what says every declared entry is live and none is stale.

Eight, all on the register-count shape, all at the ONE pre-state whose count register has a small
low quadword and a non-zero upper one. **ACL2 x86isa reads the count from all 128 bits** where SDM
Vol. 2B and K both read `SRC[63:0]`: flipping a single bit of the upper quadword flips its answer
from *shift by 3* to *all zeros*, while a control at a true count of 64 saturates correctly in the
same run.

⭐⭐ **AND THE ORACLE CONTRADICTS ITSELF**, which is stronger evidence than any manual:

```
psllw %xmm1, %xmm0    count 0xbfbebdbcbbbab9b8_0000000000000003  ⇒  0000…0000   (wrong)
psllw (%rbx), %xmm0   the same 128 bits, in memory              ⇒  5550…8890   (right)
```

⇒ **The `x,m` shape §5 nearly declined as "0.85%" is what turned a disagreement into a finding.**
Had it been left out, this would have been one more two-model disagreement against the more credible
model — D93's position, argued from the manual. With it, x86isa's own memory path is the witness.

Eight `knownDivergences` entries carry it, each with its K citation; `vshiftm` is deliberately NOT
declared, because it agrees and an entry that never diverges is a failure in that channel. See D108.

## 7. RECEIPTS

See the commit message for the run URLs and the local gate table.
