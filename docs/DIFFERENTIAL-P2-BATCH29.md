# P2 BATCH 43 — sub-group B2: scalar add, subtract and divide, through the multiply's constructor

> ⚠️ **TWO COUNTERS.** Twenty-ninth differential record; the seat's **batch 43** in `docs/DECISIONS.md`
> (D271, on the fold of D270). QUEUE `P2-NEXT (B)`, built and run on 2026-09-18.

**Forms.** `addss`, `addsd`, `subss`, `subsd`, `divss` and `divsd`: six roster rows, 29 vectors, **no new constructor**
(D270's `VArithOp` made them expressible) and **no new state field**. The forms account for 14,752 instructions of
assembly-class demand. Sub-group B's unclaimed total is now 5,133.
⚠️ "A′" below is the CI job's ku arm (`ku-delta --arm a-prime`), not the sub-group.

## 1. THE CHANGE

- **The rule** (`SoftFloat.faddsub`, `SoftFloat.fdiv`) landed with the fold (D270) and is read here for the first time.
  - **A NaN:** the first source's, quieted, else the second's; IE on an SNaN.
  - **∞ − ∞, 0/0 and ∞/∞:** the QNaN indefinite with its sign bit SET, and IE.
  - **x/0,** for a finite non-zero x: ±∞ and ZE, and **NOT DE even when x is denormal.** SDM Vol. 1 §4.9.2 ranks
    divide-by-zero above the denormal-operand exception. Two processors read it before the batch (D269).
  - **An exact zero sum** is +0, and −0 under round-down. Two zeros of one sign keep it.
  - **A tiny sum is always exact,** so add and sub never raise UE. A divide is tiny AFTER rounding, as the multiply is.
  - **DE** is raised on a denormal operand beside an infinity, as the multiply's rule is.
- **The roster** gains six mnemonics in `rosterP0` and six rows in the coverage table.
- **`wrongSimdWith` takes a per-operation `arith`,** where it took the multiply's pair alone. B1's arms swap `.mul`
  only, B2's swap add, sub and div only, and B0's model-wide arms run the true rule, or `deAlways` over it, for all four.

## 2. THE RUN

```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=96624  matched=76031  explained=29435  unexplained=0  oracle-divergence=232  oracle-leaks=0  missing=0
1098 vectors · 88 pre-states · 96624 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 29435 · oracle-divergence: 232
```

Against the twenty-eighth record's `cases=94072 matched=73490 explained=29435 … divergence=221`:

```
cases       94,072 -> 96,624   (+2,552 = 29 vectors × 88)
matched     73,490 -> 76,031   (+2,541)
explained   29,435 -> 29,435   (unchanged)
divergence     221 ->    232   (+11: divsd_m10 4 · divss_m12 7 — 0/0, x86isa's indefinite unsigned)
unexplained      0 ->      0     oracle-leaks 0    missing 0
```

- **Pre-registered on the fleet bus (09/18 00:27) to the case, and confirmed in every field.**
- **The 11 are DECLARED, not excused.** `knownDivergences` gains one entry per format in D266's `pair` form. Each
  excuses only a disagreement whose two values END in `(fff8000000000000, 7ff8000000000000)` or
  `(ffc00000, 7fc00000)` and agree on every bit before it. The third source is the SDM's QNaN floating-point
  indefinite, whose sign is 1, and both processors' reading of `divsd_zero_zero` (D269). The mechanism is
  x86isa's `rtl::indef`, which has no sign bit (D265 §3).
- ⚠️ **The binary32 half was a named risk and it held.** No hwprobe row divides zero by zero at binary32; x86isa's
  `subss_infinf` reading implied the same `indef`, and the 7 `divss` cases confirm it.
- The run's trailing kernel-cost table is a reading of retired ceilings, taken at load 5.0. It is not this run's
  verdict; §6 is.

## 3. THE VECTORS — B1's RULE, UNCHANGED

A pass printed inputs only for the 88 pre-states: MXCSR, the 16 XMM registers, and the quad and double word at every
offset −32..+24 from RBX. Python classified every candidate by `hwprobe/mk_rows.py`'s `arith` rule, never the model:
6 forms × 1,168 candidates. Each form's table is the greedy cover over candidates writing xmm0, starting from `x1,x0`.
```
  addsd  x1,x0 · 0x10 · 0xa · -0x17           subsd  x1,x0 · 0x10 · -0x18 · 0xa · 0x11 · 0xc      divsd  x1,x0 · 0x10 · x13,x0 · 0xa
  addss  x1,x0 · 0x10 · 0xd · -0x17 · -0x1a   subss  x1,x0 · 0x14 · 0xd · -0x16 · -0x1b · 0x15   divss  x1,x0 · 0x12 · 0xd · x13,x0
```
- **Reached here and by no earlier form:** x/0, 0/0, a denormal dividend over zero (ZE-BEFORE-DE), and cancellation to
  −0 at round-down.
- ⛔ **Reached by no dst-xmm0 candidate:** ±∞ (no pre-state holds one, so ∞ − ∞, x/∞ and DE-WITH-INF never meet a
  vector), a binary64 SNaN beside a normal or a QNaN, and `addss` cancellation at round-up.
- Every memory operand reads inside the watched window (RBX = 0x2000; window 0x1fe0 + 64).
- `check_encodings`: all 1,098 forms agree with clang on length and bytes.
- B1's `maxRecDepth 32768` on the table, set "with room for B2", held: the 29 new entries compile at it.

## 4. ⛔ WHERE THE DIFFERENTIAL CANNOT CARRY IT — PINNED IN THE KERNEL

B0's rule (D267 §2): a row is pinned iff x86isa disagrees with it, or no vector of its form reaches its class over
the 88 states. The class is the form, the reference path, the flags, RC, the result's sign, whether it rounded away
from zero, tininess before ≠ after (divide), and a preset OE.
```
  x86isa differs (4)       subsd_infinf · divsd_zero_zero · divsd_inf_inf · subss_infinf   (the indefinite's sign)
  no vector reaches (35)   every ∞ · add overflow at every mode · cancellation and zero sums at the modes and signs
                           the vectors miss · a carry out of a tie · divide overflow and tininess at the modes they
                           miss · the SNaN pairings · an exact quotient
  carried by vectors (71)  everything else
```
- Six theorems (`b2_{add,sub,div}{sd,ss}_pins`: 15 · 3 · 11 · 6 · 1 · 3 rows), generated by `hwprobe/mk_anchors.py`
  from `b2_pin_rows.py`'s output. `PENDING` is now empty: every hwprobe row is in a family.
- **Planted wrong twice, in one elaboration of a copy:** x86isa's positive indefinite on `divsd_zero_zero`, and +0 on
  `addsd_cancel/down`. **Two errors, at `b2_divsd_pins` and `b2_addsd_pins`, and none elsewhere.**

## 5. THE ARMS

Thirteen wrong models, labelled `adds/subs/divs`, each swapping add, sub and div ALONE. The predictor printed each
vector's operands over driveWrong's 84 states (checked 84/84 against B1's independent record) and applied `mk_rows.py`'s
rule with each defect. Predictions were posted on the fleet bus (09/18 00:13) before the run.
```
  arm                                                          field       predicted   read
  ignores MXCSR.RC                                             xmm0            456      456
  RC's down and up exchanged                                   xmm0            612      612
  the source's NaN when both are NaNs                          xmm0             80       80
  zeroes the bits above the lane                               xmm0          2,249    2,249
  round-down's zero sum is +0                                  xmm0             19       19
  sub and div with the operands reversed                       xmm0          1,255    1,255
  a divide by zero raises DE too                               mxcsr.de         32       32
  a finite dividend over zero gives the indefinite             xmm0             43       43
  OE without PE                                                mxcsr.pe         16       16
  IE on a quiet NaN                                            mxcsr.ie        356      356
  UE on an exact tiny result                                   mxcsr.ue        270      270
  overflow is ±∞ in every mode                                 xmm0             12       12
  0/0 raises ZE instead of IE                                  mxcsr.ie          9        9
```
**Every arm is caught, and every score equals its prediction.** A control rode the same run: `wrongArithWith varithLow`,
the right parts, read ZERO. It was removed before the commit, and the table grows from 168 arms to 181.

**B0's model-wide arms now reach add, sub and div,** predicted and posted with the run:
```
  arm (x86lean-diff selftest mxcsr)                       field       record 28   predicted   read
  the flags replace the sticky bits instead of ORing      mxcsr.ze      1,140       1,711     1,711
  DE is raised beside a NaN (`deAlways`)                  mxcsr.de         24         123       123
  ucomis IE · min/max IE · cvtt PE                                   25 · 184 · 475   unchanged
```
- **The +99 on the DE arm is 67 at a NaN plus 32 at a denormal over zero.** `deAlways` is "DE on any denormal", so
  through `div` it also breaks ZE-BEFORE-DE. The first cut of the prediction said 67. It was corrected against
  `deAlways`'s definition before the post, and the two arms now cross-check: 99 = 67 + `zede`'s 32.
- **B1's nine read identically through the refactor** (`selftest mulsd/mulss`: 170 · 264 · 17 · 854 · 31 · 396 · 39 ·
  129 · 3, PASS). The change that let B2's arms exist moved nothing in the family before it.

## 6. THE LANDING MEASUREMENT — `513168b` → `5d9ebf1`

⛔ **RE-KEYED (D271 §9).** #33 landed between this measurement and the merge, so master's first-parent step is
`083c464 → db52c7f`, and the row below keyed `513168b → 5d9ebf1` priced nothing on it. The row is dropped. The step was
re-measured under its real key: A′ is identical module-for-module, and ms is CLEAN (`Tests.Anchors` +83.5 ±24.7). It is recorded
on the ms verdict. **The prices below stand. Their key does not.**

**The step:** `513168b` (PR #32's merge) → `5d9ebf1` (this batch's `.lean` commit, first on the branch, D264).
```
  ku-delta --arm a-prime   CLEAN, rc 0 (yukon.lan) — identical to the draft's reading
    Tests.Anchors   +49,533 of 80,143 · Tests.Coverage +227,931 of 609,953 · Tests.Vectors +7 of 105 · every other +0
  ms   kernel_delta --repeats 6   CLEAN, rc 0     loads 5.2–10.3, yukon.lan
         Tests.Anchors          +77.0  ±28.6    against   761.0     predicted +94 ±50     inside the band
         Tests.Coverage        +900    ±415     against 28,400      predicted +54 ±900    at the band's edge
         X86.Syntax              +2.0  ±32.4    against   306.5     predicted ~0 ±25      as predicted
         Tests.Vectors           +0.0 · Tests.Program −7.5 · every other unit inside its own noise
  D251 --record                  RECORDED        lands on the ms verdict
```
- **The predictions were posted on the fleet bus before the walk (09/18 03:40),** from the ku of the same step.
- ⚠️ **`Tests.Anchors` came in BELOW its centre: 1.55 ms per 1k ku, against B1's 1.90.** The post named the centre as
  the likeliest miss and bet the other way (a divide pin reducing a long `Nat` division). **The divide pins are cheaper
  per unfolding than the multiply's, not dearer.**
- ⚠️ **`Tests.Coverage`'s +900 is at the edge of a ±900 band, read at loads 5–10.** Of it, +650 is the residue and +175 is
  `vectorCoverage`, the declaration that grows with the table. B1's reading of the same unit was +500 ±706 at loads 3–6.
  It is inside the gate and is not claimed as a measurement of B2's cost.
