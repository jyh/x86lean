# P2 BATCH 39 — the exact widenings, and an oracle that cannot convert zero

> ⚠️ **TWO COUNTERS.** Twenty-fifth differential record; the seat's **batch 39** in `docs/DECISIONS.md`
> (D258). The conversion half of QUEUE `P2-NEXT`, built and run on 2026-09-16.

**Forms.** `cvtss2sd` · `cvtsi2sdl` (the census key for a 32-bit source at both shapes, D257): two roster rows,
10 vectors, three AST constructors (`vcvtss2sd`, `vcvtsi2sd`, `vcvt2sdm`), no new module, **no new state field**,
**4,385 instructions** of assembly-class demand (2,949 + 1,436). This is the rest of sub-group A of the soft-float
commission (D139).

## 1. THE RULES

SDM Vol. 2B, CVTSS2SD: `DEST[63:0] ← Convert_Single_Precision_To_Double_Precision_Floating_Point(SRC[31:0])`, and
CVTSI2SD: `DEST[63:0] ← Convert_Integer_To_Double_Precision_Floating_Point(SRC)`. In both, `DEST[MAXVL-1:64]` is
unmodified. Both conversions are exact, so neither reads MXCSR.RC.
- `SoftFloat.toBinary64` places a non-zero integer significand at a known scale. A normal binary32, a denormal and
  an int32 all go through it, so **a denormal is normalised by the same code as a normal**.
- A NaN keeps its sign, its payload moves up 29 bits, and the quiet bit is set, so **a signalling NaN is QUIETED**.
- ±0 and ±∞ pass through with their sign.

⚠️ **x86isa is a different mechanism.** It converts to a RATIONAL and back through `rtl::sse-post-comp` and
`rat-to-fp` (`cvt-spec.lisp`), with the NaN and ∞ cases in `sse-cvt-fp1-to-fp2-special`.

## 2. ⛔ THE ORACLE CANNOT CONVERT ZERO, AND THAT SHAPED EVERY VECTOR

`cvtss2sd` at a ±0 source is an ACL2 guard violation (`RTL::SSE-POST-COMP` requires a non-zero rational). **Driven
before any vector was written:** inside `x86l-run-all` the violation aborts the whole top-level form, so every case
after it goes unrun. So **every `cvtss2sd` source in this table is non-zero in all 88 pre-states.** Measured over the
five vectors × 88 states, the zero-source count is **0**.

A scalar memory operand has no alignment rule, so the sources include unaligned offsets. Classes over the emitted
pre-states:

```
  -0x3(%rbx)   sNaN 28 · ±normal 60                                zero-free
  0xe(%rbx)    +denorm 33 · −denorm 3 · qNaN 21 · ±normal 31       zero-free
  x1           ±normal 87 · +denorm 1                              zero-free
  x9           ±normal 88                                          zero-free
  (%rbx) · 0x10(%rbx) · x0 · x5 · x10 · x15                        reach ±0: not used as cvtss2sd sources
  ±∞           reached nowhere
  int32 (%ecx, %edx, (%rbx), -0x3(%rbx))   zero · INT32_MIN · negative · positive all reached (a zero int source
                                           executes on x86isa)
```

⚠️ The batch's own first reachability probe read two aligned offsets and reported the signalling NaN as unreachable.
Record 24 §2 and D253 §3 carry the same scope error, and now say so (D258 §2).

## 3. THE RUN

```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=91960  matched=71428  explained=29435  unexplained=0  oracle-divergence=171  oracle-leaks=0  missing=0
1045 vectors · 88 pre-states · 91960 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 29435 · oracle-divergence: 171
```

Against the twenty-fourth record's `cases=91080 matched=70548 explained=29435 … divergence=171`:

```
cases       91,080 -> 91,960   (+880 = 10 vectors x 88 pre-states, exactly)
matched     70,548 -> 71,428   (+880 — EVERY new case matched)
explained   29,435 -> 29,435   (unchanged: these forms mark nothing undefined)
divergence     171 ->    171   (unchanged)
unexplained      0 ->      0     oracle-leaks 0    missing 0
```

**Pre-registered on the fleet bus before the run, and CONFIRMED to the case.** `missing 0` is the reading that says
§2's constraint held: one zero-source `cvtss2sd` case would have aborted the oracle's run and turned every later case
into a `missing`.

⛔ **A green that matches its prediction exactly is checked, not believed.** The oracle's post-state was compared with
the SDM rule computed in Python from each PRE state, reading no Lean. It checks the destination's full 128 bits, the
other fifteen XMM registers, RIP and the refusal flag.
**880 cases, 0 mismatches.** The write is visible in 80–88 of 88 states per vector. Over the five `cvtss2sd` vectors,
the sources are 353 normals, 38 denormals, 21 quiet NaNs, 28 signalling NaNs and **0 zeros**.

## 4. ⛔ WHERE NO VECTOR REACHES, OR THE ORACLE CANNOT GO — PINNED IN THE KERNEL

`Tests/Anchors.lean` `cvtss2sd_ieee` (22 rows) and `cvtsi2sd_int32_ieee` (10 rows), each one `decide`, every carrier
with junk above bit 31:
- **x86isa:** 30 of 32 rows executed, 0 disagreements, RIP advanced in all 30. The two ±0 rows abort (§2).
- **Rosetta 2** (a translator, not an x86 processor), running the instructions from a clang x86-64 build: 32 rows
  including ±0, 0 disagreements. The same comparison against an unquieting rule reports the 4 sNaN rows.
- Kernel type checking is about 13 ms and 7 ms. `#print axioms` gives `[propext, Quot.sound]` for both.
- ⛔ **Planted wrong once:** an unquieted `+snan-min` expectation made `cvtss2sd_ieee`, and only it, fail to build.

⚠️ **This instrument is not the vector table and is never pooled with it.** It speaks about the lane rules, not about
`step`.

## 5. THE ARMS

```
  arm (all labelled `cvt`, field xmm0)             posted (88)  re-derived (84)  x86lean-diff selftest   light count
  passes a signalling NaN through unquieted              28            27               27                 27
  returns the default NaN (sign, payload dropped)        49            48               48                 48
  re-biases a denormal without normalising it            37            37               — (killed)         37
  zeroes the bits above the converted lane              560           532               — (killed)        532
  reads the int32 source as unsigned                    150           140               — (killed)        140
  keeps only 24 significant bits of the int32           117           102               — (killed)        102
  takes INT32_MIN's magnitude as INT32_MAX                9             9               — (killed)          9
  converts the whole 64-bit source register              78            70               — (killed)         70
  control: the eight arms on 40 non-cvt vectors x 8 states                                                   0
```

- ⛔ **The selftest filter (`x86lean-diff selftest cvt`, 8 of 146 arms) was killed by the harness after two arms**,
  for low system memory: a concurrent heavy job held most of the box. The other six were counted by a scratch
  `#eval` over `driveWrong`'s own population and this batch's vectors. That count reproduces the two selftest readings
  exactly. CI's selftest shards run all 146 arms through `driveWrong` itself.
- ⚠️ **The posted predictions were over the wrong population.** They used the emit's 88 pre-states, and `driveWrong`
  runs 84, whose 4 random states differ. The re-derived column was posted before arms 2–8 reported (D258 §7).
- ⭐ **The signalling-NaN arm scores 27, all at `-0x3(%rbx)`**, a source the batch's first reachability probe had not
  read.

## 6. THE LANDING MEASUREMENT

Step `18194ad` (master) → `35c5c15` (this batch as one commit), measured on yukon.lan and pre-registered on the fleet bus
before either profile started.

```
  ms   kernel_delta --repeats 6   CLEAN, rc 0     loads 5.2–8.9
         Tests.Coverage            +800  ±626.7  against 1,965.6     predicted ~0                  MISSED
         Tests.Anchors             +9.5   ±42.5  against   137.6     predicted ~+20                (lower)
         X86.Syntax               +10.5   ±23.1  against    53.0     predicted +25 to +45          REFUTED, below the range
         X86.SoftFloat             +0.5    ±0.4  against     6.0     predicted +1 to +3            (lower)
  A′   ku_delta --arm a-prime     CLEAN, rc 0     every module inside
         Tests.Coverage         +78,606          against 591,456     predicted +146k to +219k      REFUTED, below
         Tests.Anchors          +16,220          against  54,879     predicted +16,220             CONFIRMED
         X86.Theorems            +1,035          against  15,452
         X86.Syntax                +740          against   4,644     predicted ~+1,000
         X86.SoftFloat              +11          against      51     predicted +11                 CONFIRMED
  D251 --record … --a-prime       RECORDED        lands on the ms verdict; row 18194ad → 35c5c15; --gap 0
```

⚠️ **The two predictions read on the draft were exact. The two scaled from batch 38 missed, and the ms Coverage cell was
not predicted at all** (D258 §8). A vector's kernel cost belongs to its form, and batch 38's forms were different.
