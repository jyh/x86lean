# P2 BATCH 14 — the packed compares, picked from a measurement, and a control that shares its subject's blind spot

> ⚠️ **TWO COUNTERS.** This is the **fourteenth differential record**; the same
> work is the seat's **batch 17** in `docs/DECISIONS.md`. The offset is not
> constant and is recorded here rather than rediscovered.

**Forms.** `pcmpeq{b,w,d}` and `pcmpgt{b,w,d}`, at both operand shapes. Six roster
rows, 13 vectors, **no new constructor** — they join `VBinKind`, so `Op.vbin` and
`Op.vbinm` carry them and the 16-byte alignment rule comes with them.

## 1. ⭐ THE GROUP WAS PICKED FROM A MEASUREMENT, NOT FROM A RANK

D115 measured the residue the roster had been ranking as available work. **Every
other candidate of this size REFUSES on the oracle** — the whole saturating
add/subtract family, both averages, the unsigned min/max pair, four multiplies,
and both signed packs. The compares are what is left, and they execute at 88 of
88 at both shapes.

**7,454 buildable instructions** of the census's `asm` class (7,667 total, 213 of
them MMX-register and declined).

## 2. ⛔⛔ WHAT EACH VECTOR PRICES IS NOT UNIFORM, AND POOLING WOULD LIE

Measured per form on the oracle against three wrong models, 88 pre-states:

```
                          unsigned   boolean   swapped
pcmpeqb %xmm1,%xmm0            88         9        88
pcmpeqw %xmm1,%xmm0            88         9        88
pcmpeqd %xmm1,%xmm0            88        12        88
pcmpgtb %xmm1,%xmm0            61        34         0
pcmpgtw %xmm1,%xmm0            67        46         0
pcmpgtd %xmm1,%xmm0            73        53         0
pcmpeqb (%rbx),%xmm0           88         0        88
pcmpgtw (%rbx),%xmm0           15         8         0
pcmpgtd (%rbx),%xmm0           15         8         0
```

(a number is how many pre-states the WRONG model still agrees on; lower is a
sharper vector.)

⚠️ **`pcmpeq` prices nothing about signedness or operand order** — equality is the
same relation either way, so those two models agree with it at all 88 **by
construction**, not by luck. Counting the group's six mnemonics as six tests of
the signedness rule would be an over-claim of exactly half.

⭐ **The memory forms are the sharp ones**: `pcmpgtw (%rbx)` leaves the unsigned
model agreeing at 15 of 88 where the register form leaves it at 67, because the
memory source sweeps while `xmm1` is a fixed pattern.

## 3. ⛔⛔⛔ THE REGISTER-FIELD CONTROL IS BLIND TO THE SIGNEDNESS RULE

`pcmpgtb %xmm3,%xmm2` exists for the reason `movdqa_x4x5` does: with every vector
reading xmm1 into xmm0, a model that ignored the register FIELDS would be
bit-identical to this one (batch 5's finding, and it is not re-learned).

**Measured: the unsigned model agrees with the right one at ALL 88 pre-states on
that vector**, against 61 of 88 on `pcmpgtb %xmm1,%xmm0`. `xmmPattern` gives xmm2
and xmm3 byte lanes that never differ in sign in a discriminating way.

⇒ 🔑 **A CONTROL CAN SHARE THE BLIND SPOT OF THE THING IT CONTROLS.** The
register-field control is a perfectly good control *for register fields* and is
worth **zero** for the rule this batch is actually about. Both vectors are in the
table and neither substitutes for the other — and the only reason this is written
down rather than assumed is that the two numbers were measured separately instead
of being reported as "the pcmpgtb vectors".

## 4. THE SIGNED COMPARISON, AND WHY THE WRONG MODEL COMPILES

Lean's `<` on `BitVec` is **unsigned**. `pcmpgt` is signed (SDM Vol. 2B). So the
wrong model here is not a strawman — it is what a model written without noticing
the word "signed" type-checks to, and it is bit-identical wherever both lanes are
non-negative. `y.slt x` is the arm; `wrongVcmpUnsigned` is the plant.

⚠️ And the result is a **MASK, not a flag**: all ones or all zeros, never 1. That
model is bit-identical in the low bit of every lane — the bit a reader coming from
`Flags` is thinking about — and `wrongVcmpBooleanNotMask` is what prices it.

## 5. RECEIPTS

```
cases=82896 matched=62364 explained=29435 unexplained=0 oracle-divergence=171 oracle-leaks=0 missing=0
942 vectors · 88 pre-states · 82896 cases · 0 unexplained · 0 oracle leaks
  spec: 0   refusal: 0   harness: 0   undefined-region: 29435   oracle-divergence: 171
```

⚠️ 171 oracle-divergences, unchanged since batch 11; this batch adds none.

### ⛔ A PROCESS DEFECT WORTH RECORDING, BECAUSE IT COST A WRONG ARTIFACT

`Main.lean` was edited **while the differential's `lake build` was running**, and
the coverage table was then regenerated from a binary that predated the edit —
`check_coverage_prose.py` caught it as a stale narrative. Rebuilding and
regenerating fixed it, and no wrong artifact was committed.

⇒ 🔑 **A GENERATOR RUN FROM AN UNREBUILT BINARY PRODUCES A DOCUMENT THAT MATCHES
NEITHER THE SOURCE NOR THE PREVIOUS OUTPUT.** It is the
[[verify-what-the-build-command-builds]] law at the DOCUMENT boundary rather than
the test boundary. The discipline this session should have kept and broke three
times: **no edit to a tracked `.lean` while a differential is running**, because
the script rebuilds inside itself.

The remaining local gates and the CI run URL are in the commit message.
