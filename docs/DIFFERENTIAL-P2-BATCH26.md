# P2 BATCH 40 — the truncations, and a rule the pre-states barely reach

> ⚠️ **TWO COUNTERS.** Twenty-sixth differential record; the seat's **batch 40** in `docs/DECISIONS.md`
> (D261). QUEUE `P2-NEXT (A′)`, built and run on 2026-09-16.

**Forms.** `cvttsd2si` · `cvttss2si`, each one census key at both destination widths: two roster rows, 13 vectors, two
AST constructors (`vcvtt2si`, `vcvtt2sim`), one function (`SoftFloat.truncToInt`), **no new state field**,
**930 instructions** of assembly-class demand (548 + 382). This is the whole of sub-group A′ of the soft-float
commission (D139): the rounding is fixed by the opcode, so no MXCSR.RC is read.
⚠️ "A′" in this record is that SUB-GROUP. The CI job is always called `ku-delta` here.

## 1. THE RULE

`truncToInt f w x` truncates the low `f`-format lane of `x` toward zero, as a `w`-bit integer (SDM Vol. 2A, CVTTSD2SI /
CVTTSS2SI):
- |x| < 1 gives 0;
- NaN, ±∞ and any result outside `[−2^(w−1), 2^(w−1) − 1]` give the integer indefinite `2^(w−1)`;
- INT_MIN itself is in range.

The destination width comes from REX.W and is a `Bool` in the AST (`wide`), not a `Size`. An int32 result is an ordinary
GPR write, so it is zero-extended.
**Checked first against an independent Python reference** (exact integers on the IEEE fields): 24,884 rows at both formats
and widths, 0 disagreements, and a planted row was reported.

## 2. ⛔ WHAT THE PRE-STATES CAN REACH, COMPUTED BEFORE ANY VECTOR WAS WRITTEN

Over the 88 pre-states, every xmm low lane and every memory offset present in all of them, classed by truncation:
```
  the range boundary (INT_MIN / INT_MAX)     0 of 88 at every source, both formats, both widths
  binary64, non-zero in-range result         0 of 88 on 15 of 16 lanes (xmm3 at r64: 3); at most 1 at any offset
  binary32, non-zero in-range result         xmm4, xmm12 at r32: 55 each · xmm3, xmm5 at r64: 19, 56
```
⇒ The binary64 truncation and both boundaries are pinned in the kernel (§4). x86isa truncates at every source, zeros
included, so unlike record 25 no source had to be avoided.

## 3. THE RUN

```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=93104  matched=72572  explained=29435  unexplained=0  oracle-divergence=171  oracle-leaks=0  missing=0
1058 vectors · 88 pre-states · 93104 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 29435 · oracle-divergence: 171
```

Against the twenty-fifth record's `cases=91960 matched=71428 explained=29435 … divergence=171`:

```
cases       91,960 -> 93,104   (+1,144 = 13 vectors x 88 pre-states, exactly)
matched     71,428 -> 72,572   (+1,144 — EVERY new case matched)
explained   29,435 -> 29,435   (unchanged: these forms mark nothing undefined)
divergence     171 ->    171   (unchanged)
unexplained      0 ->      0     oracle-leaks 0    missing 0
```

**Pre-registered on the fleet bus before the run, and CONFIRMED to the case.** The one risk named in advance was that
x86isa had never been driven here at a 64-bit destination. The four REX.W vectors matched in every state.

⛔ **A green that matches its prediction exactly is checked, not believed.** The oracle's post-state was compared with
the rule computed in Python from each PRE state, reading no Lean. The comparison covers the destination GPR, the other
fifteen GPRs, all sixteen XMM registers, RIP and the refusal flag.
**1,144 cases, 0 mismatches.** The write is visible in 63–88 of 88 states per vector. The results are 651 zeros, 286
indefinites and 207 other values.
⚠️ The script exited 2 on its trailing `kernel_cost` reading, which found `Tests/Coverage.lean` uncompiled before the roster
list named the two rows. That is not the verdict. The final binary re-emits the Lean side byte-identically
(sha256 `5fa461b2…`).

## 4. ⛔ WHERE NO VECTOR REACHES — PINNED IN THE KERNEL

`cvttsd2si_trunc` (28 values) and `cvttss2si_trunc` (16 values) in `Tests/Anchors.lean` are two kernel `decide`s, each at
both widths, `[propext, Quot.sound]`. They cover:
- zeros and denormals, and fractions either side of ½ and 1;
- INT_MIN, one step beyond it, INT_MAX, and the largest value below each limit;
- 2^53 + 2, ±2^63, the infinities and three NaNs.

Binary32 carriers hold junk above bit 31. The expectations come from the reference, not the model.
- **Executed on x86isa first:** 88 rows at `%eax` and `%rax`, plus a control placed last. 0 disagreements; a planted
  rounding row is reported 2 of 2.
- **Planted wrong once in the kernel:** the build failed at exactly `cvttsd2si_trunc`.

## 5. THE ARMS

Eight wrong models, all labelled `cvtt`, field `rax`. Nine of the thirteen vectors write `rax`, at both widths and both
source shapes. **Predicted over `driveWrong`'s own 84 states before the run**, from Python models written without reading
`Main.lean`'s. The population was dumped from Lean, and its seed-8 twin reproduces all 88 emitted states.
```
  arm                                                    predicted   x86lean-diff selftest cvtt
  rounds half away from zero instead of truncating            9          9
  rounds toward minus infinity                               66         66
  saturates instead of returning the indefinite              31         31
  returns 0 for a NaN                                       102        102
  ignores REX.W and writes an int32                         105        105
  reads a binary64 source as binary32                       146        146
  sign-extends an int32 result                              104        104
  keeps the upper half of a 32-bit destination              165        165
```
**Every arm caught, every score equal to its prediction.** The rounding arm is the lowest: only an in-range binary32
fraction of at least ½ reaches it, on the `rax`-writing vectors. That is why §4 carries the binary64 rounding rows.

## 6. THE LANDING MEASUREMENT

Step `6a3fb0c` → `29022ce` (this batch as one commit), measured on yukon.lan. The ms figures were predicted from the
`ku-delta` readings and posted on the fleet bus before the timing walk started.

```
  A′   ku-delta --arm a-prime     CLEAN, rc 0     every module inside
         Tests.Coverage         +79,980          against 597,116
         Tests.Anchors           +9,622          against  58,659
         X86.Theorems            +1,510          against  15,641
         X86.Syntax                +533          against   4,782
         X86.SoftFloat              +12          against      54
  ms   kernel_delta --repeats 6   CLEAN, rc 0     loads 7.5–17.1 (a loaded box)
         X86.Syntax               +12.0  ±23.2   against    53.7     predicted ~+8               as predicted
         X86.Theorems              +5.0  ±39.6   against   184.8     predicted +15 ±50           as predicted
         Tests.Anchors             −5.0 ±125.3   against   142.4     predicted +6..+12           inside the band
         Tests.Coverage          −250   ±939     against 2,016       predicted +800 ±650         neither confirmed nor refuted
  D251 --record … --a-prime       RECORDED        lands on the ms verdict; row 6a3fb0c → 29022ce; --gap 0
```

⚠️ **CLEAN, at a resolution the load made poor** (D261 §7). The deterministic `ku-delta` reading carries the size:
`Tests.Coverage` +79,980, as large as batch 39's.
