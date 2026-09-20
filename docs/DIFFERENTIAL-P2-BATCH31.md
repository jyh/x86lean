# P2 BATCH 45 — sub-group B4: the vectors, and the wrong models catch up with the fold

> ⚠️ **TWO COUNTERS.** Thirty-first differential record; the seat's **batch 45** in `docs/DECISIONS.md`
> (D276, on D275's fold). QUEUE P3, sub-group B's remainder, built and run on 2026-09-19.

**Forms.** The three `cvtsi2` pairings D275 made statable and deliberately did NOT claim: `cvtsi2sdq`
(int64 → binary64), `cvtsi2ssl` (int32 → binary32) and `cvtsi2ssq` (int64 → binary32). Three roster
rows, six vectors, **no new constructor and no new state field** — the fold already built the shape.
⚠️ "A′" elsewhere is the CI job's ku arm, not the sub-group.

## 1. THE RUN

```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=97416  matched=76811  explained=29435  unexplained=0  oracle-divergence=244  oracle-leaks=0  missing=0
1107 vectors · 88 pre-states · 97416 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 29435 · oracle-divergence: 244
```
Against batch 44's run, every moving number is accounted for: **+6 vectors ⇒ +528 cases** (6 × 88),
**+516 matched**, **+12 oracle-divergence** (232 → 244), and `explained` does not move at all.

## 2. ⛔⛔ THE FIRST RUN WAS NOT CLEAN — 12 UNEXPLAINED, AND THEY WERE A DECISION NEVER LANDED

```
  [spec] cvtsi2sdq_rcx_x0/53  lean=…ffffffff0000000000000000  oracle=…ffffffff8000000000000000
  [spec] cvtsi2ssl_ecx_x0/53  lean=…ffffffff0000000000000000  oracle=…ffffffff0000000080000000
```
**The sign of zero**: this model +0, x86isa −0, low lane only, on the round-down pre-states — four
vectors × 12 cases. It is D266 §4's known x86isa defect (`sse-cvt-int-to-fp` gives a zero result the
sign `(if (int= rc *rc-rd*) 1 0)`), reached again because that function serves every source width and
both destination formats.

⇒ 🔑 ***THE BATCH PLAN PREDICTED THESE EXACTLY, SAID THEY WOULD LAND EXPLAINED, AND THE EDIT THAT
WOULD HAVE MADE THAT TRUE WAS NEVER MADE.*** The prediction and the fork's resolution were written in
two separate seat files hours earlier. **A plan describes what WILL be true, so re-reading it confirms
the intent and says nothing about the state.** The differential is what told the difference, on the
first run of the new vectors, naming the four vectors and the exact bit.
✅ **That is the gate working.** The cost of the omission was about fifteen minutes.

### ⚠️ THE TRAP INSIDE THE FIX — THE DECLARED PAIR IS PER-FORMAT
The obvious repair is to add four ids to the existing `cvtsi2sdl` block. **That would have declared
nothing for three of them.** `pairMatches` requires both values to END in the declared pair and AGREE
before it, and that block's pair is the 64-bit `0000000000000000`/`8000000000000000`. A `cvtsi2ss`
record diverges in its **32-bit** lane, `00000000`/`80000000`, which the 64-bit pair cannot match.
⇒ Two blocks, two pairs, with the reason in a comment so the next reader does not merge them. Had the
ids gone into the one block, `spec` would have fallen 12 → 10 and read as "mostly fixed".

### WHAT IS DELIBERATELY NOT DECLARED
`cvtsi2sdq_mN1e` and `cvtsi2ssq_mN1e`, the two wide memory forms: their `-0x1e(%rbx)` source does not
reach zero in a round-down pre-state, so a declaration for them could never fire. **A declaration that
cannot fire is an untested claim** — the same rule that keeps `cvtsi2sdl_mN3` out of the older block.

## 3. THE WRONG MODELS WERE ONE BATCH BEHIND THEIR OWN CONSTRUCTOR

The fold gave `vcvtsi2` its `dbl`/`wide` flags; the wrong-model family kept the old shape. Three
defects, of which the plan knew one: the source was read at a **hard-coded 32 bits**; the destination
was written with a **hard-coded binary64 geometry**, wrong at *both* `cvtsi2ss` pairings and therefore
wrong even for the four arms whose defect is in the FLOAT path; and three arm **labels** say "int32" in
text the differential prints. Each would have made an arm wrong in a SECOND way, which
`wrongCvtWholeRegister`'s own docstring forbids.

✅ The repair copies the sibling family: `wrongCvttWith` (batch 40) already binds `dbl`/`wide` from the
constructor, because `vcvtt2si` carried them from the start. Source read and destination write are now
always correct; an arm plants in the conversion alone. Arms whose defect is not expressible at a
pairing return the correct value and say so (`Unsigned`, `SingleSignificand`, `IntMinSaturates` are
scoped to `wide=false`) — which would have left the two `wide` pairings with **no integer-path detector
while reading as covered**, so `wrongCvtIgnoresRexW` is added as `wrongCvtWholeRegister`'s mirror.
⇒ 🔑 ***A FAMILY THAT GAINS A PARAMETER OWES A SWEEP OF EVERYTHING WRITTEN AGAINST ITS OLD ARITY, AND
ITS SIBLING IS WHERE TO LOOK FOR THE ANSWER FIRST.***

## 4. ⛔ THE SELFTEST CANNOT SEE THE DEFECT THIS BATCH REPAIRED

`driveWrong` passes an arm when its hit list is non-empty; **the count is printed and not gated.** So
it asks *"is this arm caught somewhere?"*, never *"is it caught where it claims to be?"* — and would
have stayed green through all of §3, at all four pairings, for as long as one landed int32 vector kept
catching each arm. Declared here rather than fixed: making the count load-bearing changes every arm's
contract and is not this batch's to make.

## 5. THE ENCODINGS WERE MEASURED

All six were derived by hand and then measured — `clang -target x86_64-linux-gnu -c` then `objdump -d`
— with three controls sought **in `Tests/Vectors.lean`** rather than taken from the plan proposing
them, and `f3480f2a03` confirmed absent beforehand. All six matched.
⛔ `/usr/bin/xed` on the build box is **Xcode's file opener**, not Intel XED; Apple's `objdump` has no
raw-binary mode and `llvm-mc` is absent.
⭐ The corroboration is **not** the round trip — clang's assembler and objdump's disassembler are both
LLVM from the same tables, one mechanism in two directions. It is that `hwprobe/sse_ops.S` already
executes all four pairings on real silicon (488/488, two vendors, D274). Their bytes were measured from
the assembled object rather than read off the comments, **which validated four hand-written byte
annotations as a side effect** — controlling a hand derivation with another hand derivation is circular.
