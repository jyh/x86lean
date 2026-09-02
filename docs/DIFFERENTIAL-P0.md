<!-- The P0 exit evidence. Regenerate with scripts/run_differential.sh. -->

# P0 differential run against ACL2 x86isa

**Plan v1 §5, the P0 exit criterion:** *one differential run of 20 scalar forms
against x86isa with zero unexplained disagreements, every disagreement filed
with its class.*

## Result

```
cases=2924  matched=2298  explained=694  unexplained=0
oracle-leaks=0  missing=0
  spec: 0          refusal: 0        harness: 0
  undefined-region: 694
```

**20 mnemonics · 43 forms · 68 pre-states each · 2924 cases · 0 unexplained.**

Oracle: ACL2 x86isa (BSD-3, © 2015 Regents of the University of Texas), built
natively on arm64 SBCL — see `docs/ORACLE-SETUP.md`. Reproduce with
`scripts/run_differential.sh`.

## What "explained" means, and why the number is not zero

A disagreement is EXPLAINED **only** when it lies inside the set of flags this
model marks undefined for that exact (instruction, state) — and that set is
**derived** by running the same step under two opposite oracles, never declared
by the harness (`docs/DECISIONS.md` D6). So the 694 are not a waiver; they are
the places where Intel declines to define a result, this model declines with it,
and x86isa's own undefined-value generator picked something different.

They land **exactly** where the SDM says they should:

| form | flags that differ | SDM rule |
|---|---|---|
| `and` `or` `xor` `test` (q) | AF only, 34 each | "The state of the AF flag is undefined" |
| `shl $1` (b, q), `shr $1` (b), `shr $3` (q), `shr $63` (q) | AF only | AF undefined for a non-zero count; OF is **defined** at count 1 |
| `shl $3` (q) | OF and AF | OF undefined when the count is not 1 |
| `shl $9` (b), `shr $9` (b) | **CF, OF and AF** | count 9 ≥ the 8-bit operand width, so CF is undefined too |
| `shl %cl` (q) | AF always, OF when CL ≠ 1 | the count is data, so the region varies per case |

That table is not a claim about the model — it is the measured output, and it
reproduces the SDM's three separate undefined regions for shifts without having
been told about them.

## Both models refuse the same instructions

**40 cases (20 `jmp *%rax`, 20 `call *%rax`) where BOTH models refused; 0 where
only one did.** The two models agree exactly on which branch targets are illegal.
A refused instruction has no post-state either model claims, so the comparator
counts agreement-in-refusal as agreement — but the count above is the check that
the path was *exercised* rather than quietly absent.

## ⭐ What the run FOUND — the model was wrong, and self-consistently so

The first run produced **80 unexplained disagreements, every one an indirect
branch to a non-canonical address**. This model set RIP to whatever the operand
named; x86isa raised `#GP(0)`.

Nothing inside this repository could have caught it. Every characterization
theorem about `jmp` and `call` was TRUE — of a model that was wrong. Every
anchor passed. The kernel was satisfied. **A second model was the only instrument
that could see it**, which is the entire argument for the differential run being
an exit criterion rather than a nice-to-have.

Fixed in `X86/Semantics.lean` (`canonical`, `Cpu.setRipChecked`), pinned by
`Tests/Anchors.lean` (the canonicality boundary in both directions, both halves
of the branch behaviour), and the branch characterization theorems now carry the
canonicality hypothesis they always needed — with `_noncanonical` companions so
the hypothesis cannot be quietly dropped.

**And a second defect, in the ordering:** a refused `call` disagreed on `rsp` and
on the stack window as well as on `rip` — three symptoms of one mistake. The
check has to precede the push; hardware raises #GP before writing the return
address. `step_call_indirect_noncanonical` states it: `regs` and `mem` are both
absent from the update.

## ⭐ And what the run found about the ORACLE

Two harness defects, both of which made the oracle's own answer invisible:

1. **`create-undef` is CONSTRAINED and non-executable in x86isa.** The first run
   died at case 817 — the first `and` — with *"cannot ev the call of
   non-executable function CREATE-UNDEF"*. x86isa refuses to invent undefined
   values for exactly the reason this project does, and cannot execute one
   without an attachment. That error is the two models agreeing about what
   neither knows. `scripts/x86isa_driver.lisp` attaches `nfix` — deliberately
   **not** a constant, because a constant `0` would have made x86isa's undefined
   bits agree with this model's all-zero oracle, the `undefined-region` class
   would never have fired, and the run would have looked cleaner while testing
   strictly less.
2. **x86isa records `#GP(0)` in its `fault` field, not in `ms`.** The driver read
   only `ms`, so all 80 non-canonical branches were reported as "x86isa did
   nothing and its RIP disagrees" — the oracle had given its explanation and the
   harness asking for it was not looking at that field.

⇒ **An oracle that cannot answer, and an oracle whose answer you do not read,
are indistinguishable from an oracle that agrees with you.**
