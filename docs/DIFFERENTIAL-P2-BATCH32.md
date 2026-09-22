# P2 BATCH 46 — S1: the five forms the CRC-32 routine executes and no vector covered

Desk `PE`, council 2026-09-21 — the Captain: *"fire v1 as priced"*. S1 of PROPOSAL v1 lands the
five differential vectors BEFORE the proof build, which is v1's own K11 repair.

## 1. THE RUN

```
reference-model: acl2@c8897a34d3efc37eb466d7ee50a2e3861c6e82db
cases=97856  matched=77207  explained=29479  unexplained=0  oracle-divergence=244  oracle-leaks=0  missing=0
1112 vectors · 88 pre-states · 97856 cases · 0 unexplained · 0 oracle leaks
  spec: 0 · refusal: 0 · harness: 0 · undefined-region: 29479 · oracle-divergence: 244
```
Against batch 45's run, every moving number is accounted for and the account CLOSES:
**+5 vectors ⇒ +440 cases** (5 × 88), **+396 matched**, **+44 explained**, and
`oracle-divergence` does not move at all (244 → 244).  **396 + 44 = 440.**

⭐ **ATTRIBUTED PER VECTOR, because an aggregate `unexplained=0` over 1,112 vectors is not evidence
about five of them.** Each new vector emitted 88 cases on BOTH sides (`id=<v>/` counted in
`run/lean.txt` and `run/oracle.txt`, against an existing vector as control), so none was skipped,
refused or silently dropped:
```
  mov_ri_d              88 matched      no declared-undefined component
  not_r_d               88 matched      no declared-undefined component
  lea_rip_q             88 matched      no declared-undefined component
  mov_mr_sib_nobase_d   88 matched      no declared-undefined component
  xor_rm_sib_nobase_d   44 matched + 44 explained
```
⚠️ **AND THE 44/44 SPLIT IS NOT A PARTIAL RESULT.** `xor` reaches `Flags.logic`, which leaves **AF**
to the undefined-bit oracle, so ALL 88 of that vector's cases carry a declared-undefined component —
in 44 the two models' AF happened to differ (counted `explained`) and in 44 it happened to coincide
(counted `matched`).  The split is a fact about the VALUES, not about coverage: 88 of 88 were
compared.  352 (the four clean vectors) + 44 = the 396 matched, exactly.

## 2. WHAT THE FIVE ARE, AND THE ABSENCE THAT COMMISSIONED THEM

PROPOSAL v1 §1.3 measured four forms the CRC-32 routine executes with no differential vector among
the 1,107.  **Every one was re-measured at the object before a line was written**, over the whole
population with a firing control on each needle:
```
  mov .d reg <- imm        0 entries      only the `.q` reg-imm form was vectored
  un .not .d               1, `not_m_l`   MEMORY only — the register form absent
  mem with index, no base  0 entries      the one `index :=` vector is a `lea` WITH a base
  ripRel                   1, `cmp_rip_q` and its displacement is NEGATIVE
```
All four confirmed.  The fifth vector is the matching base-less scaled-index STORE.
⚠️ **The first parser used to take that census saw 625 of 1,107 entries** — a brace-balancing regex —
**and nothing was read off it.**  Re-done by splitting on the entry marker: 1,112/1,112 against the
`grep -c` authority.  A census whose population is short is not a weak census, it is a different one.

## 3. ⛔ THE INDEX IS RBX, NOT THE ROUTINE'S RCX, AND THAT IS FORCED

The routine's own form is `xor eax, [rcx*4 + disp]`, where RCX is a table index bounded to 0..255 by
the `movzx`/`xor cl,al` pair before it.  **In this harness RCX carries a swept ADVERSARIAL 64-bit
value** (`mkPre`), so `rcx*4 + disp` addresses wild memory in every pre-state and lands outside both
watched windows — where our `Mem` reads 0 for an unwritten byte and the ACL2 driver renders an
unmapped read as `00`.  ⇒ **BOTH MODELS WOULD AGREE ON ZEROES AND THE VECTOR WOULD PASS BY
CONSTRUCTION.**  That is batch 12's `leaveq` trap and P1 batch 15's DF trap arriving a third time.

⇒ The index is RBX (fixed at 0x2000 in every pre-state, like RSP/RSI/RDI) and the displacement
COMPENSATES: `0x2000 * 4 = 0x8000`, less `0x6000`, is `0x2000` — the swept data word `[0x2000] = RCX`,
inside the data window (`0x1fe0`, 64 bytes).  The ADDRESS is constant across pre-states and the VALUE
LOADED SWEEPS, which is the shape every existing `M .rbx` vector already has.

⭐ **THE SCALE IS LOAD-BEARING AT 4**, and all three plausible wrong readings are observable: a model
reading the index as a BASE agrees at scale 1 and disagrees here; one dropping the displacement reads
`0x8000`, which is the STACK window and therefore watched; one dropping the scale reads
`0x2000-0x6000`, far outside both.  ⛔ And `lea_rip_q` carries a POSITIVE displacement precisely
because `cmp_rip_q` already carries a negative one — two vectors, two signs, one sign-extension rule.

## 4. ⭐ A GATE GAP THE VECTORS EXPOSED, FIXED RATHER THAN EXEMPTED

`scripts/claimed_forms.py` synthesises each roster row through a list of addressing `MODES`, and a
BASE-LESS SCALED INDEX was not among them — so two vectors resolved to NO ROSTER ROW and the gate
reported a finding about forms the roster genuinely covers (`xor r,m`, `mov m,r`).

The mode is added with its index as **`{B}`**, substituted from `MBASE` = (6,3,1,2) whose three low
bits all vary, so the **SIB INDEX FIELD BECOMES AN OPERAND BIT**.  ⛔ The pre-existing SIB mode
hard-codes `%rcx`, and the only pre-existing vector with an index happens to use `%rcx` — **so that
freeze had never been paid for and would have silently refused every other index.**

**Driven in isolation, each step measured separately: 3 unresolved → 1 (the mode alone) → 0 (the
`lea` change).**  All five then POSITIVELY resolve, read from `--json` rather than inferred from the
gate's silence: rows 256 `mov r,imm` · 273 `not r` · 18 `xor r,m` · 243 `lea r,m` · 185 `mov m,r`.

## 5. ⚠️ A DECLARED LIMIT: NO SCALAR VECTOR HAS EVER EXERCISED REX.R

`lea_rip_q` names `%rax`, not the `%r8` the routine uses.  `claimed_forms.py` spans a ModR/M register
field by perturbing `BANKS`, so all sixteen low encodings match; **`%r8` needs REX.R, a bit in the
REX PREFIX that no bank moves**, so it is frozen in every skeleton and a vector carrying it resolves
to no row.  Measured: of 1,112 vectors exactly TWO name an extended register, and the other
(`cvttss2si_x5_r9`) passes only because SIMD forms are EXEMPT from this P1 gate.
⇒ **That axis is genuinely uncovered for scalar forms.  It is left uncovered and named here**;
widening `RIDX`/`BANKS` to reach it is a change to a load-bearing gate this batch does not need.

## 6. ⛔ THE KERNEL-COST READING IS UNMEASURABLE, AND I ADDED THE LOAD

`kernel_cost.py` rc=3: *"one-minute load was 5.25, outside the band this tool's own effect measurement
covers (loads 0.0–4.1)"*.  The readings printed are NOT a verdict about this commit, and the tool says
so itself.  ⚠️ **The load was partly mine:** `claimed_forms.py --check` (which assembles hundreds of
roster instances through clang) and the `coverage` regeneration were run DURING the differential.
**Recorded so the reading is not mistaken for an ambient condition of the machine.**  The kernel-time
gate is `kernel_delta.py`, which is unaffected; `Tests.Coverage` growth is REPORTED at 30,300 ms =
164.7 ms/row over 184 rows.

## 7. WHAT THIS BATCH DOES NOT CLAIM

- It adds **no coverage ROW** — every mnemonic was already carried.  That is v1 §1.3's whole point:
  the coverage gate binds at the MNEMONIC (`Tests/Coverage.lean:16-17`), so a full row set is not
  per-form evidence, and the six gated numbers in `docs/COVERAGE.md` are unchanged.
- ⚠️ **`mov`'s coverage row UNDER-CLAIMS and this batch does not repair it.**  Its shapes string is
  `r,r · r,imm · r,m · m,r` and omits `m,imm`, yet `mov_mi_b/w/l/q` resolve to roster row 183
  `mov m,imm` at all four widths.  The direction is conservative, so nothing is unsafe — and the
  field is walked character-by-character inside a kernel `decide` at ~5 ms per character, where it
  has refused a batch twice (D94, D102).  **Reported, not silently widened.**
