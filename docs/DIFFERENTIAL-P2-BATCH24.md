# P2 BATCH 38 — min / max, and the vectors shaped by what the pre-states can reach

> ⚠️ **TWO COUNTERS.** Twenty-fourth differential record; the seat's **batch 38** in `docs/DECISIONS.md`
> (D253). The min/max half of QUEUE `P2-NEXT`, built and run on 2026-09-15.

**Forms.** `minss` · `minsd` · `maxss` · `maxsd` · `minps` · `maxps`: six roster rows, 15 vectors, two AST
constructors (`vminmax`, `vminmaxm`), two `VBinKind`s (`minps`, `maxps`), no new module, **no new state
field**, **926 instructions** of assembly-class demand. Sub-group A of the soft-float commission (D139).

## 1. THE RULE, AND WHY IT IS ONE COMPARISON

SDM Vol. 2B, MINSD: `MIN(SRC1, SRC2)` returns SRC1 only when `SRC1 < SRC2`. A NaN in either operand
returns SRC2, and so do two zeros of either sign. `SoftFloat.fmin f a b` is `if fcmp f a b == .lt then a
else b`, and `fmax` is the same with `.gt`. `fcmp` already has both exceptions as outcomes (`unord`,
`eq`), so neither needs a case of its own.

⛔ **The rule is not commutative, and that is its content.** Any symmetric model agrees with it on every
ordered pair of distinct values, and differs exactly on the NaN and zero pairs.

⚠️ **x86isa is not a copy of this rule.** `sse-max/min` (`arith-spec.lisp`) handles NaN, a zero pair and
the infinities in `sse-max/min-special`. It then compares RATIONALS and re-encodes the result through
`rat-to-fp`, taking the sign from whichever operand equals the chosen rational. Agreement with it is
therefore agreement between two different mechanisms, not a comparison of the same code.

## 2. WHAT THE PRE-STATES CAN REACH, COMPUTED BEFORE ANY VECTOR WAS WRITTEN

Operand classes over the 88 pre-states in `run/cases.lsp`:

```
  x1,x0 · x5,x3 (registers)   same-sign pairs ONLY, both formats; NaN vs number; zero vs number
  x9,x1 (registers)           OPPOSITE signs in all 88 states
  0x10(%rbx) vs xmm0          two zeros (−0/+0 once per format, +0/+0), NaN/NaN, NaN vs zero,
                              opposite signs, denormals
  nothing                     ±∞ · a signalling NaN · the zero pair in the (+0, −0) order
```

⚠️ *Scoped 2026-09-16 by D258 §2: "nothing" is over the registers and the offsets 0 and 0x10. An
unaligned offset (`-0x3(%rbx)`) holds a signalling NaN in 28 of 88 states. ±∞ and (+0, −0) are still
reached nowhere.*

⛔ **A register pair below x8 never presents opposite signs.** `xmmPattern` makes the XOR of two
registers' low quadwords `(i^^^j)` in every nibble. The sign is bit 3 of the top nibble, so it can differ
only when `i^^^j ≥ 8`. Every register vector in this table before this batch used x0–x7.
⇒ The second register pair is `x9,x1`, and this batch has the first vectors here that name xmm8–xmm15.

⭐ **A memory operand DOES reach the ±0 rule, which D140 §5 said it could not.** That sentence was true of
`(%rbx)`, which holds `c`, xmm0's own low quadword. It is false of `0x10(%rbx)`, which holds `a ^^^ c`:
against xmm0's `c` the XOR is `a` itself, a swept value rather than a nibble pattern. `c = a = 0x8000…`
presents dst −0 and src +0.

## 3. THE RUN

```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=91080  matched=70548  explained=29435  unexplained=0  oracle-divergence=171  oracle-leaks=0  missing=0
1035 vectors · 88 pre-states · 91080 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 29435 · oracle-divergence: 171
```

Against the twenty-third record's `cases=89760 matched=69228 explained=29435 … divergence=171`:

```
cases       89,760 -> 91,080   (+1,320 = 15 vectors x 88 pre-states, exactly)
matched     69,228 -> 70,548   (+1,320 — EVERY new case matched)
explained   29,435 -> 29,435   (unchanged: these forms mark nothing undefined)
divergence     171 ->    171   (unchanged)
unexplained      0 ->      0     oracle-leaks 0    missing 0
```

**Pre-registered on the fleet bus before the run, and CONFIRMED to the case.**

⛔ **A green that matches its prediction exactly is checked, not believed.** The oracle's post-state was
compared with the SDM rule computed on Python floats from each PRE state, reading no Lean. The result:
**1,320 cases, 0 mismatches.** The write is visible (xmm register changed) in between 22 and 88 of the 88
states per vector, so no vector is a no-op test.

## 4. ⛔ WHERE NO VECTOR REACHES — EXECUTED ON THE ORACLE, THEN PINNED IN THE KERNEL

Every pair from {±0, ±∞, qNaN, sNaN, ±1} that contains ±∞ or the sNaN, plus (+0, −0), gives 40 pairs
per format.
- Expectations come from the SDM Operation on Python floats.
- The same pairs were **EXECUTED on x86isa** as `minsd`/`maxsd`/`minss`/`maxss`, with junk above the lane
  in both registers.

```
  probe cases 160   RIP advanced in 160   write visible in 112   oracle vs SDM: 0 mismatches
```

Those 80 rows are `Tests/Anchors.lean`'s `minmax_ieee_binary64` / `minmax_ieee_binary32`, each one
`decide`:
- Kernel type checking is about 8.6 ms each.
- `#print axioms` gives `[propext, Quot.sound]`.
- ⛔ **Planted wrong once:** `min(+0, −0)` declared to return the destination made `minmax_ieee_binary64`,
  and only it, fail to build.

⚠️ **This instrument is not the vector table and is never pooled with it.** It speaks about the lane
rule, not about `step`.

## 5. THE ARMS

```
minmax returns the destination on a NaN or a tie             170 in `xmm0`   (170 unexplained)
minmax compares the bit patterns as signed integers          198 in `xmm0`   (213 unexplained)
minmax returns the negative zero of a zero pair (minNum)       2 in `xmm0`   (2 unexplained)
minmax zeroes the bits above the scalar lane                 620 in `xmm0`   (782 unexplained)
```

`x86lean-diff selftest minmax`, 4 of 138 arms, PASS.
- ⭐ **The minNum arm scored exactly the 2 pre-registered:** `minsd_m` and `minss_m`, at the one pre-state per format where
  `c = a = 0x8000…`.
- It is the arm D140 had to delete for `comis`, where no vector could reach the ±0 rule. The `0x10(%rbx)` vector is the whole
  difference.

## 6. THE LANDING MEASUREMENT

Step `e731c63` (master) → `b259049` (this batch as one commit), measured on yukon.lan and pre-registered on the fleet bus before
either profile started.

```
  ms   kernel_delta --repeats 6   CLEAN, rc 0     loads 3.5-6.1
         Tests.Coverage            +600  ±445.7  against 1,875.6     predicted ~+1,000        (lower)
         @decl vectorCoverage       +85   ±98.2  against   327.3     predicted ~+150          (lower)
         Tests.Anchors              +25   ±23.5  against   122.3     predicted ~+20           (as predicted)
         X86.Syntax                 +25   ±15.6  against    45.6     predicted +30 to +50     REFUTED, below the range
  A′   ku_delta --arm a-prime     CLEAN, rc 0     every module inside
         X86.SoftFloat               +0          against 51          predicted 0              CONFIRMED
         Tests.Coverage        +219,397          against 575,660
         Tests.Anchors          +14,308          against  47,971
         X86.Syntax                +683          against   4,516
         X86.Theorems              +526          against  15,356
  D251 --record … --a-prime       RECORDED        "ms verdict rc 0 · ARM A′ rc 0 on yukon.lan ⇒ lands on the ms verdict"
                                                  row e731c63 → b259049; --gap 0
```

⚠️ **Every ms prediction erred HIGH.** Batch 32's +550 for 8 vectors, scaled, over-priced 15 vectors by 40%. **A batch's vector count
is not its kernel cost**: the memory-operand vectors here share their `vbinm`/`readMem` reduction with vectors already in the table.
