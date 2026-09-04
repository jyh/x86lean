# P2 BATCH 8 — the known-divergence channel: keeping a test alive when the ORACLE is wrong

**Forms.** None. **No instruction was added and no semantics changed.** What changed is the
comparator: two vectors deleted at batch 7 are **back in the table and compared on every run**.

```
cases=71380  matched=51335  explained=28774  unexplained=0  oracle-divergence=159  oracle-leaks=0  missing=0
830 vectors · 86 pre-states · P1 roster unchanged at 500/525
```

## 1. What it repays

Twice the differential has been right and the oracle wrong: `movdqa` at an unaligned address, which
x86isa does not fault on (D91, oracle *incomplete*), and `movd`/`movq` into an XMM register, which
x86isa merges where the SDM and K both say clear (D93, oracle *wrong*). Both times the remedy was to
**delete the vector** — and D93 said what that costs: *removing a vector stops the test permanently
and silently.*

`oracle-divergence` is now its own class in the header of every run. **Not matched, not explained** —
a disagreement this repository has measured, named, attributed and cited.

## 2. ⛔ The three things that keep a place-to-put-red honest

**Gated in the other direction.** An entry that produces no disagreement **fails**:

```
⛔ DECLARED ORACLE DIVERGENCES THAT DID NOT OCCUR:
   mov_q / rax (PROBE) — declared divergent against: FABRICATED for the probe
   Either the oracle was FIXED … or this model has drifted into agreeing with a known-wrong answer.
```

**Every entry carries an independent source** — K by file, the SDM by section. A two-model
disagreement names no culprit (D93); without a third source this list is just somewhere to put red.

**Narrow by construction:** one vector-id prefix, one field.

⚠️ **And the scoping.** `classify` takes the list as a *parameter*; `driveWrong` passes `[]`. The
selftest compares this model against a deliberately wrong copy of *itself*, where an oracle defect is
irrelevant — and the planted bug here, `wrongVmovgPreservesUpper`, is **exactly** the mistake x86isa
makes. Sharing one list would have let a declared oracle divergence excuse a planted bug.

## 3. Probed both ways

| plant | result |
|---|---|
| a declared divergence that does not occur | `rc=1`, names the stale entry and both causes |
| a real entry deleted | `rc=1`, `unexplained=81` resurfaces as `spec`, `oracle-divergence=78` |

The second proves the entries do work rather than decorate: delete one and the red returns at once.

⭐ The arm removed at batch 7 — *movd/movq into XMM merge instead of clearing* — is **restored with
its vectors**. See D95.
