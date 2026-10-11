# P2 BATCH 53 (W1b) — ADCX and ADOX against x86isa; MULX against two processors

Decision note: D330 (predictions committed before the hwprobe push, before any Rosetta run and before the differential;
re-based onto batch 52 with its re-run predicted in D330's dated note before the re-run).

## 1. THE RUN

```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=102960  matched=82131  explained=29699  unexplained=0  oracle-divergence=292  oracle-leaks=0  missing=0
1170 vectors · 88 pre-states · 102960 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 29699 · oracle-divergence: 292
```
Against batch 52's run (record 38: 102256 cases, 81427 matched, 29699 explained), **every field is as D330 §4 and its re-base
note predicted**: +8 vectors ⇒ **+704 cases**, **+704 matched**, `explained`, divergence and leaks unmoved. (First run, on
`cb08c68` before the re-base: 102608 cases, +704 matched against batch 51, identical per vector.)

⭐ **ATTRIBUTED PER VECTOR**, each id's records filtered out of `run/lean.txt` and `run/oracle.txt` and compared alone,
with `add_q` as the control:
```
  adcx_rr_q  adcx_rm_q  adcx_rr_d  adcx_rm_d     88 matched each
  adox_rr_q  adox_rm_q  adox_rr_d  adox_rm_d     88 matched each
  add_q (control)                                88 matched
```
Each id has 88 CASE records on BOTH sides. The `oracle_availability.py` gate in the same run read `adcx` and `adox`
`executes` 88/88, `mulx` `refuses` 88/88, and both controls executing.

## 2. THE PLANTS — the vectors are load-bearing, measured backwards
- `adox_rr_q`'s Lean records given `adcx_rr_q`'s POST states (the carry read from and written to CF instead of OF):
  **54 of 88 cases unmatched, 104 unexplained `spec` disagreements.** The 34 that survive are the pre-states where the two
  chains happen to agree.
- `adcx_rm_d`'s Lean records given `adcx_rm_q`'s POST states (the 64-bit rule at 32 bits): **88 of 88 unmatched, 157
  unexplained.**

## 3. MULX — the processor reading (hwprobe run 38096322511, both jobs `success`)

```
  leg                       processor                                CPUID.7.0.EBX  BMI2 ADX   integer rows   SSE rows
  referee (ubuntu-latest)   AMD EPYC 7763 64-Core Processor            219c07a9     1    1     384 / 0 diff   958 / 0
  referee (macos-15-intel)  Intel(R) Core(TM) i7-8700B CPU @ 3.20GHz   029c6fbf     1    1     384 / 0 diff   958 / 0
  integer controls, BOTH    plant rc=1, exactly one DIFF (adcxq_rr_zero_c0) · bad byte rc=2, REFUSED i_adcxq_rr
  SSE controls, BOTH        unchanged: plant 1 · badop 2 · pplant 1 · pbadop 2
```
The 384 `ok` lines of the two legs are an IDENTICAL file (checked with `cmp`; a one-character mutation of one line is
reported at that line). Two vendors, two microarchitectures, no difference — D330 §3's prediction. The 96 MULX rows are
pinned in `Tests/Anchors.lean` by `decide`; a mutant model that multiplies a memory source at 64 bits reds exactly the
`w1b_mulxl_rm_pins` family (the `.q` memory family, where the two rules coincide, stays green).
⚠️ **Rosetta 2** reports CPUID.7.0.EBX = 0 (no BMI2, no ADX): the probe REFUSES (exit 2), and with the feature check
removed the first ADCX row dies with SIGILL. So the emulator corroborates nothing here, and the guard is what stops a crash
being read as a disagreement.

## 4. WHAT IT CHANGES, AND WHAT IT DOES NOT SEE
- **Roster 197 → 199** (`adcx`, `adox`); `mulx` is modelled and listed in `docs/COVERAGE.md`'s own processor-refereed table,
  NOT in the roster, because no differential vector can test it.
- **The census, re-derived from the 1170-vector table:** 42 of 57 ALL COVERED (`vale-fadd` joins batch 52's `xxh32`, as
  predicted); the s2n-bignum appendix 202 → 206 of 332. `vale-fmul`, `s2n-bignum_mul_4_8` and `s2n-bignum_montmul_p256` each now lack only
  `mulxq` forms, which the census does not count: it counts a form only from a differential vector.
- **NOT SEEN:** MULX over the 88 pre-states (its rows are chosen, 96 of them); any processor but Zen 3 and Coffee Lake;
  ADCX/ADOX with a LOCK prefix or at a segment-overridden address; RFLAGS bits other than the six arithmetic flags.
