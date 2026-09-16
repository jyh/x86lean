# P2 BATCH 32 — the first floating-point semantics, and two mnemonics that are one function

> ⚠️ **TWO COUNTERS.** Twenty-third differential record; the seat's **batch 32** in
> `docs/DECISIONS.md` (D140). Built 2026-09-05 as record 19 and held off `master` by the drift
> ledger (QUEUE item 4) while records 19–22 landed; re-run here on today's tree, 2026-09-15 (D251).

**Forms.** `comiss` · `comisd` · `ucomiss` · `ucomisd` — four roster rows, 8 vectors, one AST
constructor, one new module (`X86/SoftFloat.lean`), **no new state field**, **2,256 instructions**
of assembly-class demand. Sub-group A of the soft-float commission (D139).

## 1. THE PART THAT NEEDED A NEW MODULE, AND WHY IT IS NOT `Float`

Lean's `Float` is a structure over `opaque floatSpec : FloatSpec` — the kernel has nothing to
unfold — and propositional equality on it has no `Decidable` instance, so `native_decide` cannot
close a `Float` equation either. **No route at any axiom price.** `X86/SoftFloat.lean` is Lean-core
`BitVec` only (no mathlib, D1): a `Fmt` carrying exponent and mantissa widths, and ONE `fcmp` that
serves both formats — `comiss` and `comisd` are the same ordering at different parameters, and two
copies would be two things that can disagree.

## 2. THE FOUR CASES A RAW BITVECTOR COMPARE GETS WRONG

Each is a wrong model that agrees with the real one on ordinary positive normals:

* **`+0` and `-0` are EQUAL** with different bit patterns, so `a == b` is not equality of values;
* **either operand NaN is UNORDERED** — not "less", not "not equal": it sets CF, PF and ZF together,
  a combination no ordered outcome produces;
* **for two negatives the magnitude order REVERSES** (`-1 > -2` while `mag(-1) < mag(-2)`);
* **a signed compare of the whole word** gets negatives backwards and mishandles `-0`.

Denormals and infinities need no case of their own: IEEE-754's exponent-above-mantissa layout makes
the unsigned magnitude order the value order for a fixed sign. A model that special-cases them is
not more careful, only larger.

## 3. THE RUN

```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=89760  matched=69228  explained=29435  unexplained=0  oracle-divergence=171  oracle-leaks=0  missing=0
1020 vectors · 88 pre-states · 89760 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 29435 · oracle-divergence: 171
```

Against the twenty-second record's `cases=89056 matched=68524 explained=29435 … divergence=171`:

```
cases       89,056 -> 89,760   (+704 = 8 vectors x 88 pre-states, exactly)
matched     68,524 -> 69,228   (+704 — EVERY new case matched)
explained   29,435 -> 29,435   (unchanged: these forms mark no flag undefined)
divergence     171 ->    171   (unchanged: the new forms add none)
unexplained      0 ->      0     oracle-leaks 0    missing 0
```

⭐ **The same four deltas the batch produced on 2026-09-05 against record 18** (+704 / +704 / 0 / 0), now
against a tree that has taken four more records, a pinned oracle revision, and 338 commits (`c372d80..426c88f`). The three
numbers that did NOT move are the informative ones. `explained` is unchanged because `comis` marks
no flag undefined — every one of the six flags it touches is *defined* by the SDM in every case, which
is unusual in this table and is why these forms are worth having. `divergence` unchanged says the new
forms contribute nothing to the 171 the harness already carries.

> ⛔ **2026-09-15 (D254): the "818-case kernel differential" this record cites below, twice, was never kept.** No tracked file held
> it. The ±0 branch, and every opposite-sign pair, which no register vector below xmm8 can present (D253 §3), are now carried by
> `Tests/Anchors.lean` `fcmp_ieee_*`, executed on x86isa first. The text below is the record as written.

## 5. THE ARMS, AND THE ONE THAT WAS DELETED

```
comis calls NaN less-than instead of unordered     66 in `pf`     (132 unexplained)
comis compares the bit patterns as signed integers 167 in `cf`     (290 unexplained)
comis also writes its destination register         336 in `xmm0`   (588 unexplained)
```

✅ **Re-run 2026-09-15 on this tree (`x86lean-diff selftest comis`, 3 of 134 arms, PASS): all three
scores are IDENTICAL to 2026-09-05's** — 66/132, 167/290, 336/588 — so the 338 commits between the two
runs moved neither the pre-states these arms depend on nor what the oracle says about them.

Every one of the three is bit-identical to the real model on two ordinary positive normals; what
separates them is the pre-states carrying a NaN, a negative, or a non-zero destination. `pf` is the
field to watch — it is the flag that *means* unordered, and a model without a fourth case cannot
set it.

⛔⛔ **A FOURTH ARM WAS WRITTEN, SCORED ZERO, AND HAS BEEN DELETED.**
`comis makes +0 and -0 compare unequal` is a real wrong model, and the harness refused it:

```
⛔ comparator reported ZERO unexplained disagreements against a KNOWN-WRONG model.
   The comparator does not work.
```

I had written that arm *knowing* it was unreachable, with a comment calling itself "the standing
record of that gap". That is a **false entry in the gate's own inventory** — D91's rule, made about
`prefetch`'s locality hint one batch earlier — and its zero is indistinguishable from a broken
comparator, which is precisely what the harness reports.

⭐ **And the unreachability is a proof rather than an observation.** `xmmPattern` gives register `i`
the low quadword `c ^^^ (i * 0x1111111111111111)`, so for any two registers the XOR of their low
quadwords is `(i^^^j)` repeated in every nibble — **16 achievable values, all uniform-nibble
patterns**, and `0x8000000000000000` is not among them. No vector over this pre-state table can
present two operands differing only in the sign bit, at any register pair; and the memory window at
RBX holds `c`, which is xmm0's own low quadword, so a memory form compares EQUAL rather than as ±0.

⇒ 🔑 **An arm that cannot fire does not document a gap, it misreports the inventory.** The `±0`
branch is carried by §2's 818-case kernel differential, which does exercise it, and the two
instruments are named separately and never pooled.

## 4. ⛔ WHAT THESE VECTORS CANNOT REACH, MEASURED BEFORE THE RUN

`xmmPattern` gives register `i` the low quadword `c ^^^ (i * 0x1111111111111111)`, so xmm0 and xmm1
differ by a FIXED non-zero XOR in every pre-state. Predicted from the pre-states, before the oracle
ran, for `comisd %xmm1,%xmm0` over the 60 structured states:

```
comisd   lt 45 · gt 9 · unord 6 · eq 0
comiss   lt 39 · gt 9 · unord 12 · eq 0
```

⛔ **`eq` NEVER, in either format.** Two operands that always differ cannot compare equal, so the
rule's `eq` arm would have been carried by a differential that never once entered it — and the run
would have reported full agreement about it. `comisd_x0_x0` compares a register **with itself**,
which forces `eq` on every non-NaN pre-state; it is the only vector here that reaches that arm.

⛔ **And one arm stays unreached, which is stated rather than left quiet.** `+0 = -0` needs two
operands differing ONLY in the sign bit, and no pre-state can produce that — the XOR pattern cannot
make one. That branch is covered by the **818-case kernel differential against IEEE-754** (D140 §2),
not by this table. The two are different evidence and are not pooled.

⇒ 🔑 A differential's silence about a branch it never enters is not agreement
([[feedback-unobserved-regions-report-agreement]]). The reachable set was computed from the
pre-states, in Python, before the run — not read off the green afterwards.

## 6. THE DELTA GATE — AND THE LANDING, 2026-09-15

*(On 2026-09-05 this section recorded an UNMEASURABLE ms delta — `Tests.Coverage` +2,900 against 1,778 — at one-minute load
9.6–15.7, and held the batch off `master`. That reading is superseded here, not deleted: it is in D140 as written.)*

Step `53c4823` (master, after PR #17) → `327622b` (this batch as one commit), measured on yukon.lan, pre-registered on the fleet
bus before either profile started:

```
  ms   kernel_delta --repeats 6   CLEAN, rc 0     Tests.Coverage +550 ±228.1 against 1,818.0; loads 4.1-7.1
                                                  X86.SoftFloat NEW: head 2.8 ms against 50 @on yukon.lan
       predicted: at risk of OVER — REFUTED
  A′   ku_delta --arm a-prime     FAILED, rc 1    Δku X86.SoftFloat +221 against an allowance of 10 (a base of 0, the floor)
       predicted: FAILED on the new module — CONFIRMED; every other module inside (Tests.Coverage +126,977 / 566,517)
  D251 --record … --a-prime       REFUSED         a supplied A′ conviction stands whatever the ms verdict
```

⇒ **A′'s conviction was A′'s defect, not this batch's:** a module absent from the base was priced at `@floor`. D252 repairs it
the way D192 repaired the ms gate — a new module is judged against an absolute `@ku` registration — and A′ was **re-run**, because
D251 refuses a stored verdict its readings no longer reproduce:

```
  A′ (D252)                       CLEAN, rc 0     X86.SoftFloat NEW, 221 against `X86.SoftFloat @ku 221`; every ku reading
                                                  identical to the first run (an exact counter)
  --record … --a-prime KU32b      RECORDED        "ms verdict rc 0 · ARM A′ rc 0 on yukon.lan ⇒ lands on the ms verdict"
                                                  row 53c4823 → 327622b; ledger 23 → 24; --gap 0 unrecorded
```
