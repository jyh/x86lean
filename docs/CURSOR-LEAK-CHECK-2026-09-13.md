# The leak check with its cursor conjunct, over the differential population — 2026-09-13

**Why this record exists (D226).** D213 left owed a harness change: compare `oracle.cursor` between the two
opposite-oracle runs inside `undefinedLeaked`. D226 adds it. The pinned reference run
(`docs/REFERENCE-PIN-RUN-2026-09-12.md`, `oracle-leaks=0`) was computed BEFORE the conjunct existed, so its
zero says nothing about cursors. A leak is a property of the Lean side alone (two Lean runs of one case, no
oracle), so the new conjunct can be measured on the whole differential population without ACL2: `emit` writes
the `LEAK` field of every case the differential compares.
⚠️ Deliberately NOT named `DIFFERENTIAL-P<p>-BATCH<n>.md`: it is not a batch and no oracle ran (the batch count
is derived from that filename pattern).

```
x86lean           the tree committed with this record (D226), built with `lake build`
command           .lake/build/bin/x86lean-diff emit <file>     then count the LEAK field
```

## The Lean side, verbatim
```
emitted 1012 vectors × 88 pre-states = 89056 cases → lean-n8.txt
```
```
grep -c '^CASE '   lean-n8.txt     89056
grep -c '^LEAK 0'  lean-n8.txt     89056
grep -c '^LEAK 1'  lean-n8.txt     0
```
cases=89056 leaks=0

⚠️ **No record other than its verdict could move, and none did:** the same `emit` built at `7c2af44` (the parent,
before the conjunct and the `movedRegs` refactor) wrote a file **byte-identical** to this one (`cmp`, 235,501,735
bytes; the two binaries differ in size, 4,470,352 vs 4,471,584, so they were different builds).
⚠️ **The control on that zero is the partition:** `LEAK 0` lines equal `CASE` lines, so the field is present on
every case and a zero count of `LEAK 1` is not an absent field.

## The conjunct can fire (the same tree, `x86lean-diff undefined-column`, which CI's build job runs)
```
  ✔ undefined column: all 158 rows match what the model draws
  ✔ oracle leaks: 0 of 85008 cases (every undefined register equals the AST-level declaration)
  ✔ cursor plant: the leak check fires on 27717 of 85008 cases, exactly the 27717 that draw a bit (a draw count that reads a drawn bit is caught)
```
`undefined-column` walks 84 pre-states per vector (`nRandom` 4), the differential 88 (`nRandom` 8).

**Deletion probe**, driven once on the developer box: with the line `&& a.oracle.cursor == b.oracle.cursor`
deleted from `undefinedLeakedBy` and the harness rebuilt, the same command printed
```
  ⛔ cursor plant: fires on 0 of 85008 cases, but 27717 draw a bit (cases emitted: 85008) — the leak check does not see the cursor
```
and exited 1. The file was restored byte-identical (`cmp`) and rebuilt before the measurements above.

## What this does and does not establish
- **Established, on these 89,056 cases:** no step's draw count differs between the all-zeros and the all-ones
  oracle — the per-instruction form of D5's rule, checked rather than exemplified.
- **Not established:** the rule for pre-states outside the population (there is still no general theorem), and
  a branch on a drawn bit that changes only the value a FLAG receives. Flags are the one channel whose undefined
  set is derived rather than declared, so such a difference is filed as undefined (D6's hazard) and the cursor
  comparison cannot see it. (The `undefined` column gate sees it only for a flag the form's row does not already
  name.) The same branch changing an undeclared register, an XMM register, RIP or memory is still a leak.
