# The differential at acl2 `testing` — 2026-10-26 (D365)

**Why this record exists (D365).** The reference model moved from `babde610ed66` (D363, the BT fix alone) to `cbb699d89f5c`,
acl2 `testing`'s merge of #2067, which also carries the span's other x86isa fixes. This is the first run at the new pin.
⚠️ Not a batch record (as `REFERENCE-PIN-RUN-2026-10-26.md`, which ran at `babde610ed` and is listed under it in `PRIOR_PINS`).

```
finished          2026-10-26, yukon
x86lean           paris/d365-acl2-testing (D363 + D364 + D365's declarations), the commit that carries this record
reference-model:  acl2@cbb699d89f5c94792bcd6a8e59b3ac000ef0a71d
command           bash scripts/run_differential.sh     (log kept locally, not tracked)
```

| pin | cases | matched | explained | unexplained | oracle-divergence |
|---|---|---|---|---|---|
| `babde610` (D363) | 130064 | 106497 | 34407 | 0 | 820 |
| `cbb699d` (this) | 130064 | 106497 | 34407 | 0 | 820 |

Nothing the vectors see moved; D365 explains why (no RIP-relative or faulting vector for the mnemonics the span fixed).

## The run, verbatim (its record lines)
```
reference-model: acl2@cbb699d89f5c94792bcd6a8e59b3ac000ef0a71d
driver-CR4 gate: CLEAN — through `x86l-run-case` itself, SSE forms execute with the shipped driver and REFUSE when its `*x86l-ctrs*` is planted back to `nil`; the scalar control executed in both arms and the refuse-always control refused in both.
── running the oracle (ACL2 x86isa) over run/cases.lsp ──
oracle produced 130064 case records
── comparing ──
cases=130064 matched=106497 explained=34407 unexplained=0 oracle-divergence=820 oracle-leaks=0 missing=0
```
