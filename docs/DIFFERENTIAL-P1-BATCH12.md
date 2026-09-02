# P1 BATCH 12 — the near-free four of family 7, and the gate repairs that came with them

**Forms.** Roster family 7's `nop` (three shapes), `ud2`, `retq`, `leaveq` —
6 roster rows, 8 differential vectors, 388 of the 525 rows (74%).

```
cases=42160  matched=29720  explained=15500  unexplained=0  oracle-leaks=0  missing=0
  spec: 0   refusal: 0   harness: 0   undefined-region: 15500
527 vectors · 80 pre-states · 57 mnemonics
```

Gate met on the FIRST run.

## What the batch actually was

The four forms are one line of `step` apiece and not one of them writes a flag.
The work was everywhere else:

| # | finding | where |
|---|---|---|
| D30 (discharged) | the seven flags were hand-enumerated in **four** places — the bank said three — one of them the WIRE FORMAT, where a miss is silent | `X86/Basic.lean`, `X86/Serialize.lean`, `Main.lean` |
| D31 | `lake build` built neither the harness nor the test tier, so every deletion probe ran a stale binary | `lakefile.toml` |
| D32 | the memory-destination gate was green because **two** defects cancelled | `Tests/Coverage.lean` |
| D33 | no selftest arm could ever target the **refusal** channel | `Main.lean` |
| D34 | `retq` and `leaveq` were UNREACHABLE against every existing pre-state | `Tests/Vectors.lean` |
| D35 | `lods` — a bank-listed "cheap" candidate — is unimplemented in the ORACLE | (not shipped) |

## The probes, each run in both directions

**D30's guard.** `flagFields_covers_Flags` fails to COMPILE, not to prove.

| probe | result |
|---|---|
| add an 8th field to `Flags`, table untouched | ⛔ `Insufficient number of fields for ⟨...⟩ constructor: … has 8 explicit field, but only 7 were provided` |
| add the field, REPAIR the pattern, add no row | ⛔ `Tactic rfl failed` (lists differ in length) |
| give one row the wrong projection | ⛔ `Tactic rfl failed` (order differs) |
| neuter the guard, delete the `df` row | `df=` vanishes from **all 80 964** record lines ⇒ the table drives the wire |
| correct code | silent |

**Byte-identical, and the first attempt was vacuous.** Emitting before and after
gave identical files because `lake build` had not rebuilt the emitter — which is
D31, caught by this probe. Redone from a `git stash`-ed pristine tree with the
executable explicitly built: **52 089 879 bytes of records and 115 498 260 bytes
of ACL2 cases, byte-identical.**

**D32.** Repairing `claimsMemDest` alone ⇒ gate RED. Repairing
`isMemDestVector` alone ⇒ gate RED. Deleting the 16 `setcc` memory vectors with
both repaired ⇒ gate RED. Both repaired, vectors present ⇒ green, for the first
time for the right reason.

**D34.** `frameStates` removed ⇒ the `retq` arm catches **ZERO** ("the
comparator does not work") and `pre_states_have_a_returnable_frame` FAILS.
`frameStates` present ⇒ the arm catches exactly **2**. Removing **one of the
two** frame states ⇒ the assertion stays SILENT (D21's calibration: an
assertion narrower than the coverage it guards cries wolf).

## ⭐ The oracle confirmed the reachability argument from the other side

The claim behind `frameStates` is that the stack background reads as
`0x3736353433323130` at RSP, which is not canonical, so `retq` faults in 78 of
80 states. That is an argument about **our** model. ACL2 x86isa, executing the
same 80 pre-states from the same bytes, refused `retq` in **78** and executed it
in **2** — the same partition, computed independently.

| vector | oracle refused | oracle executed |
|---|---|---|
| `nop`, `nop_m_l` | 0 | 80 |
| `ud2` | **80** | 0 |
| `retq` | **78** | **2** |
| `leaveq` | 0 | 80 |

This also answers the question `bothRefused` always raises: two models that both
decline count as agreeing, so a form the oracle cannot execute would show as a
perfect green. `nop` and `leaveq` executed on both sides in all 80; `ud2`
faulted on both sides in all 80, which is the agreement being claimed; and
`retq`'s split is the one that could not have been faked.

## Arms

31 arms (27 + 4). The batch's pair doctrine, per D17:

* **easy halves** — `ud2 executes instead of faulting` (76 hits in `refused`, and
  the arm that exposed D33); `leaveq pops before it moves RSP` (76 hits in `rbp`);
* **hard halves** — `every nop advances RIP by one byte`, caught only by the
  multi-byte shapes, which is what says they are not redundant spellings;
  `retq jumps without popping`, caught by **2** cases and by nothing that
  existed before this batch.
