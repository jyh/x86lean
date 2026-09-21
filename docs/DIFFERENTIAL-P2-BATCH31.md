# P2 BATCH 45 — sub-group B4: the vectors, and the wrong models catch up with the fold

> ⚠️ **TWO COUNTERS.** Thirty-first differential record; the seat's **batch 45** in `docs/DECISIONS.md`
> (D276, on D275's fold). QUEUE P3, sub-group B's remainder, built and run on 2026-09-19.

**Forms.** The three `cvtsi2` pairings D275 made statable and deliberately did NOT claim: `cvtsi2sdq`
(int64 → binary64), `cvtsi2ssl` (int32 → binary32) and `cvtsi2ssq` (int64 → binary32). Three roster
rows, six vectors, **no new constructor and no new state field** — the fold already built the shape.
They account for **2,127 instructions of assembly-class demand**, so sub-group B's unclaimed total falls
from 3,836 to **1,709**. ⚠️ The demand census was regenerated against the 184-mnemonic model: every
column's TOTAL is byte-identical and only `covered`/`pct` move, all upward — the corpus did not change,
three more mnemonics did.
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

## 6. THE KERNEL PINS — 85 OF 127, AND A′ IS CLEAN WITH 15.2 % MARGIN

The rows the differential cannot carry, pinned in the kernel by D267 §2's rule. **The selection is a
COMMAND, which is the thing that changes with this batch:**

```
  python3 hwprobe/reach_table.py
    p_cvtsi2ss    46 rows · pinned 32 · carried 14 · vectors mapped 2
    p_cvtsi2ssq   40 rows · pinned 25 · carried 15 · vectors mapped 2   (11 carried by ONE pair)
    p_cvtsi2sdq   41 rows · pinned 28 · carried 13 · vectors mapped 2   (9 carried by ONE pair)
    TOTAL 127 rows · PINNED 85 · CARRIED 42
```
`classify()` is passed `x86isa_diffs()`, so this is the **full** rule — *pinned iff x86isa disagrees or
cannot run it, OR no vector of the same form reaches its class over the 88 pre-states* — and not the
reach half alone. The split is **3 x86isa-differs and 82 unreached**.
⭐ **THE THREE ARE `cvtsi2ss_zero/down`, `cvtsi2ssq_zero/down`, `cvtsi2sdq_zero/down`**, and the reading
shows why: x86isa returns `…80000000` where the rule wants `…00000000` — **−0 for a +0 result at
round-down**, which is D274 §1's *"the three zero rows at round-down"*, confirmed from the DIFF lines
rather than from the prose.
⚠️ **Earlier batches' lists cite `b2_pin_rows.py` and `b3_pin_rows.py`; neither exists on any ref**
(driven four ways, firing control each). B2's and B3's selections are therefore not re-derivable from
this repository. **B4's is** — that is the whole reason `reach_table.py` was built.

### THE ENCODING FOLLOWS THE FOLD, AND THE DESTINATION REGISTER IS LOAD-BEARING
Each family steps `.vcvtsi2 dbl wide .x1 .rdi` from `b0Pre mx a b` — `(false,false)` · `(false,true)` ·
`(true,true)` for `ss` / `ssq` / `sdq`.
⛔ **The destination is `.x1`, NOT `.x0`.** `vcvtsi2` preserves the bits above the lane, so the binary32
forms must find the canary `5a5ac3c3` in bits 63:32 — and `b0Pre` loads **`x0` with the SOURCE**, which
would make those rows read their own input back. `b3_cvtsd2ss_pins` has the same shape for the same
reason. Visible in the rows themselves: a want of `0x5a5ac3c34b800000`.

### A′ — MEASURED ON THE DRAFT, AND THE PREDICTION WAS FILED FIRST
```
  ku_delta --arm a-prime  61123cd99 → 8dbd03680        (yukon.lan, load 4.50)
    Tests.Anchors      440,286 → 527,317    +87,031    allowance 102,587    84.8 %   CLEAN
    every other module                           +0
    ms ceilings        X86.Basic 29 % · X86.Syntax 39 % · X86.Theorems 34 % of ceiling
  gate: ku-delta (a-prime) CLEAN
```
**B4's own rate is `1,023.9 ku/pin-row`** — the cheapest this module has measured:
```
  B4 1,023.9   B3 1,076.3   B1 1,170   B2 1,270      break-even for 85 rows was 1,206.9
```
⇒ **THE STRADDLE NEVER BOUND.** The break-even sat between B1's and B2's rates, so on borrowed numbers
the batch looked like it might need splitting; **on its own rate it fits in one step with 15.2 %
margin.** QUEUE P3's warning was right to demand the measurement and right that no allowance should be
widened to fit its subject.
⚠️ **THE PREDICTION, SCORED HONESTLY:** filed before the run as **Δku ∈ [88,000, 100,000], verdict
CLEAN**, on the argument that B4 is structurally a *conversion* like B3 rather than binary arithmetic
like B1/B2. **The verdict HELD; the band MISSED LOW by 969** — and *"below 88,000 ⇒ the band is wrong
low, the `ss` forms are cheaper than B3's narrowing"* was one of the three falsifiers named in advance,
so the miss is the outcome that was written down, not one explained afterwards.
⚠️ **The second prediction — every module but `Tests.Anchors` at Δku ≈ 0 — HELD EXACTLY (`+0`),** which
is what a pins-only change should do and is worth stating because D267 §3 records a case where it was
not automatic.

### THE GREEN WAS EARNED, NOT ASSUMED
`Built Tests.Anchors (1.5 s)` is fast for 85 kernel `decide`s, so it was driven **RED BACKWARDS**: flip
one `want` field (`0x5a5ac3c34b800000` → `0x1a5ac3c3…`) and the build fails rc 1 with `is false`;
restore and it is green. `mk_anchors --check` passes byte for byte both times.
📌 `PENDING` is now empty — B4's three forms were the last held back — and `mk_anchors`' completeness
check (every row in a family or pending) covers that.
