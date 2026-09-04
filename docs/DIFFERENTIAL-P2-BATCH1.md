# P2 BATCH 1 — the FS/GS segment base, a split `lea` is the only witness to, and two fields that blew three proofs

**Forms.** The segment base in `Ea` — P2 addition 1 of the three the Captain ordered, and the
first addition in this repository priced by **measured demand** rather than by a roster row:
**29,943 instructions** of the census's assembly class carry an FS or GS override, **3.26% of
the uncovered gap**, the commonest being the stack-protector load `movq %fs:0x28, %rax`.
Eight vectors, four selftest arms, four theorems and a red probe. It claims **no new roster
row** — a segment override is a prefix on rows already claimed — so the roster stands where it
did.

```
cases=67424  matched=47667  explained=28559  unexplained=0  oracle-leaks=0  missing=0
  spec: 0   refusal: 0   harness: 0   undefined-region: 28559
784 vectors · 86 pre-states · 84 mnemonics
```

## 1. What was added, and why it is not "segmentation"

In 64-bit mode segmentation is off for CS, DS, ES and SS: their bases are zero and their limits
are not checked (SDM Vol. 3A §3.4.4). **FS and GS are the exception** — a 64-bit base, loaded
from the IA32_FS_BASE / IA32_GS_BASE MSRs, is still added. So the whole addition is:

| | |
|---|---|
| `X86.Seg` | two constructors, `fs` and `gs` |
| `Cpu.fsBase`, `Cpu.gsBase` | two `BitVec 64` fields, MSR-loaded, written by no instruction |
| `Ea.seg` | one `Option Seg` field |
| `Ea.offset` / `Ea.addr` | the **split**: effective address vs linear address |

No descriptor, no selector, no limit, no expand-down segment, no #GP on a null selector. The
model is not more general than long mode is.

## 2. ⭐⭐ The split, and the one vector that can see it

`lea` writes the **effective address** — SDM Vol. 2A, LEA — so a segment prefix on it is
architecturally inert. Every other memory access adds the base. Before this batch there was one
function and the distinction could not be stated; writing one function and using it in both
places is the defect the split exists to prevent, and it is the model this batch was most likely
to have shipped.

⛔ **`leaq %fs:0x28, %rax` is the only vector in the repository that can distinguish them.**
Without it the split would be an assertion no vector could contradict. Planted (`wrongLeaAddsSegBase`),
it is caught in **82 of 82** cases — every pre-state the SELFTEST runs (`driveWrong` uses the
82-state set, not the differential's 86), because the difference does not depend on the swept
values at all: LEA must write 0x28 and the planted model writes 0x2000.

⭐ **And the oracle agrees independently.** x86isa's `x86-lea` uses `x86-effective-addr` and
never calls `ea-to-la`, while every memory read and write goes through `rme-size`/`wme-size`,
which do. In the run above, `lea_fs_abs_q` returns `rax=0x28` in all 86 cases while
`mov_fs_abs_q` beside it returns the value at 0x2000.

## 3. ⛔⛔ The bases are INPUTS, so the displacements are the whole test (D72)

No instruction in this roster writes either base, so by D27 — *a component nothing writes is a
constant, and a comparator watching a constant reports agreement it did not test* — they are
**deliberately absent from the compared record**. The only evidence the model uses them is the
address they produce.

That is what fixes the vectors' numbers. `%fs:0x28` with the base dropped is address **0x28**,
outside both watched windows, where our `Mem` reads 0 and the ACL2 driver renders an unmapped
byte as `00`: **both models unobserved, and agreement that tested nothing** — batch 12's
`leaveq` trap and batch 15's backward string step a third time. So:

```
fsBase = 0x1fd8   ->  %fs:0x28 = 0x2000   the swept operand      [0x2000] = c
gsBase = 0x1fe8   ->  %gs:0x28 = 0x2010   the second operand     [0x2010] = a XOR c
```

⚠️ **The two bases differ by 0x10 rather than being equal.** With one value for both, a model
that read GS's base for an FS access would agree in every case and half the addition would ship
untested. `X86.Seg` has two constructors and a pre-state that cannot tell them apart tests one.
Measured in the oracle's own output at case 70: `a = 0x5555…55`, `c = 0x0f0f…0f`, FS returns
`0x0f0f…0f` and GS returns `0x5a5a…5a = a XOR c`.

**And the claim is a theorem, not a note.** `segmentedAddressesLandInAWatchedWindow` asserts that
every segmented access resolves inside a watched window in every pre-state, and
`scripts/segment_redprobe.sh` arm **s4** moves the base to a *canonical* address outside the
windows and requires it to go `false` — the failure this design exists to avoid, created rather
than argued about.

## 4. ⭐⭐ Two fields on `Cpu` blew three proofs, and the repair is not a bigger margin (D71)

`fsBase` and `gsBase` are read by nothing in this batch except `Ea.addr`. Adding them made
`bitScanStep_mem`, `bitScanStep_rip` and `bitScanStep_zf` — three P1 batch 14 frame lemmas —
exceed `maxHeartbeats` **all at once, before a single instruction had been added**. Removing the
two fields and changing nothing else made all three pass, which is how the cause was established
rather than guessed.

The cause: those proofs closed with `split <;> rfl`, a defeq check over a `Cpu` record eight
updates deep, because `undefVal` — added in batch 14 *alongside these very proofs* — never got
the frame lemmas `undefBit` has had since P0. There was nothing for `simp` to push a projection
through.

⇒ 🔑 **THE COST OF A STATE FIELD IS PAID BY EVERY WHOLE-RECORD PROOF, NOT BY THE FORMS THAT USE
IT.** A `set_option maxHeartbeats` bump would have been one line and would have left the next
field to find the limit again. The five frame lemmas make the proofs independent of the field
count.

**The same finding shaped `Ea.addr` itself (D70).** Written as the SDM draws it —
`segBase seg + offset` — every unsegmented memory access in the model acquires a `BitVec 64`
addition of zero for the kernel to reduce. Matched on `ea.seg` instead, the unsegmented path is
byte-for-byte the old function. `Ea.addr_eq_segBase_add` keeps the SDM's reading as a theorem.

## 5. The four planted defects, all caught

| arm | field | caught |
|---|---|---|
| a segment override is ignored | `rax` | 276 |
| fs and gs read each other's base | `rax` | 290 |
| `lea` adds the segment base | `rax` | 82 |
| a segmented STORE lands at the effective address | `mem@…1fe0` | 112 |

Four **different claims**, not four spellings of one: each leaves the other three correct, so no
one of them is caught by another's vector.

⚠️ The first two perturb the PRE-STATE rather than the semantics, which is a different technique
from every other arm in the file and is the honest one here — "the base is ignored" *is* "the
base is zero", and a second copy of `Ea.addr` would have planted a defect in a copy of the code
rather than in the model under test.

## 6. ⭐ The gates that were named by a LITERAL, and stopped seeing the work

`check_coverage_prose.py` and `check_readme_snapshot.py` both globbed
`docs/DIFFERENTIAL-P1-BATCH*.md`. Read literally, the first P2 record is **invisible** to both:
the README's `cases` and `pre-states` would have gone on being checked against P1 batch 21's run
for ever, and the prose gate would have reported *"CLEAN — all 21 P1 batches"* while naming none
of P2.

⇒ **A GATE WHOSE SUBJECT IS NAMED BY A LITERAL STOPS SEEING THE WORK THE MOMENT THE WORK IS
RENAMED**, and it reports agreement rather than silence. Both now read `P<p>-BATCH<n>` and gate
per phase; the README publishes both counts.

The same shape, one layer down, is why `claimed_forms.py`'s exemption list became a table with a
**rule per entry**: the eight segment vectors resolve to no roster row, and filing them under a
label reading *"base %rsp forces a SIB byte"* would have been true of the two entries that were
there and false of the eight added beside them.

## 7. What is NOT closed, named rather than left to be found

x86isa's `ea-to-la` requires the resulting **linear** address to be canonical and faults if it is
not, for segmented and unsegmented accesses alike. This model checks canonicity on branch targets
only (D9) and on no data address at all. This batch neither widens nor closes that gap — and
`segmentedAddressesAreCanonical` bounds it: over the whole (segmented vector × pre-state) cross
product, every linear address this model computes is canonical, so the two models cannot disagree
about a fault neither can reach here. Red probe arm **s3** plants a non-canonical base and
requires it to go `false`.

Also unchanged: `wrfsbase`/`wrgsbase`/`wrmsr` are not modelled, so nothing in the model can
*write* a segment base. That is what makes the bases inputs, and what makes §3 necessary.

## 8. The kernel cost, measured — and NO ceiling was raised

```
                                      before D73's repair     after
  Tests.Coverage @tail                 12 770  (ceiling 12 420 ⛔)   8 480  ok
  Tests.Coverage total                 27 800                        23 500
  segmented_vectors_are_all_extracted   4 200                        (gone)
```

⚠️ **Both readings were taken on a machine at one-minute load 4.1–5.4**, above the 2.2–4.1 band
`scripts/kernel_cost.py` measured as having no effect on this module, so both are on the loose
side; the comparison between them is the part that is safe, because they were taken under the
same conditions minutes apart. A quiet re-measurement would move both down together.

The batch adds four theorems and a thirty-six-arm exhaustive match and leaves the module
**cheaper than it found it**, with every ceiling in `scripts/kernel_ceilings.txt` untouched. That
is the whole content of D73: the refusal was not an obstacle to route around.
