# The differential, re-run at the re-pinned reference model — 2026-10-26 (D363)

**Why this record exists (D363).** The reference model moved from `c8897a34d3ef` to `babde610ed66`, the commit that fixes
x86isa's BT/BTS/BTR/BTC bit number for a negative register offset (acl2/acl2 #2067), and D331's 29 declared divergences were
deleted. This is the first run at the new pin; the 21 records before it ran at `c8897a3` and are listed under it in
`scripts/check_record_revision.py`'s `PRIOR_PINS`.
⚠️ Not named `DIFFERENTIAL-P<p>-BATCH<n>.md`: it is a re-run, not a batch (as `REFERENCE-PIN-RUN-2026-09-12.md`).

```
finished          2026-10-26T04:21 PDT, yukon
x86lean           paris/d363-oracle-2067, D331's entries deleted (the commit that carries this record)
reference-model:  acl2@babde610ed66311a80073b98e5efda3f03a61795
command           bash scripts/run_differential.sh     (log kept locally, not tracked)
```

## The three runs, one tree, one vector set (128,040 cases)
```
pin        entries   cases   matched  explained  unexplained  oracle-divergence  rc
c8897a3    present   128040  104719   34047      0            1144               0   (the baseline)
babde610   present   128040  104719   34047      0             820               1   (exactly the 29 D331 entries stale)
babde610   deleted   128040  104719   34047      0             820               0   (this record)
```
`oracle-divergence` falls by exactly 324 = the (vector, field, state) excusals D331's entries named; nothing else moves.

## The run, verbatim (its record lines)
```
── checking the reference model's pinned revision ──
reference-model: acl2@babde610ed66311a80073b98e5efda3f03a61795
driver-CR4 gate: CLEAN — through `x86l-run-case` itself, SSE forms execute with the shipped driver and REFUSE when its `*x86l-ctrs*` is planted back to `nil`; the scalar control executed in both arms and the refuse-always control refused in both.
── running the oracle (ACL2 x86isa) over run/cases.lsp ──
oracle produced 128040 case records
── comparing ──
cases=128040 matched=104719 explained=34047 unexplained=0 oracle-divergence=820 oracle-leaks=0 missing=0
```
