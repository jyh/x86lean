# P1 BATCH 13 — the flagless shifts and the byte-swapping move, and the oracle catalogue that was wrong twice

**Forms.** Roster family 15's `sarx`/`shlx`/`shrx` at `r,r,r` and `r,m,r`, and
`movbe` at `r,m` and `m,r` — **8 roster rows, 18 differential vectors**, taking
the model to **396 of the 525 rows (75%)**.

```
cases=43600  matched=31160  explained=15500  unexplained=0  oracle-leaks=0  missing=0
  spec: 0   refusal: 0   harness: 0   undefined-region: 15500
545 vectors · 80 pre-states · 61 mnemonics
```

Gate met on the FIRST run.

## What the batch actually was

The four mnemonics compute values this model already knew how to compute:
`Flags.shiftCount` and the three shift expressions are batch 7/8's, and
`Value.byteRev` is batch 10's. **Their content is entirely in what they do not
do** — `sarx`/`shlx`/`shrx` write no flag at any count, and `movbe` reverses at
the OPERAND width rather than at 64 bits. Both are negative claims, and a
negative claim is the kind a differential run cannot make on its own (D27).

| # | finding | where |
|---|---|---|
| **D36** | ⛔ the ORACLE's own catalogue is wrong in BOTH directions; D35's rule survives with its instrument replaced | `vendor/…/catalogue-data.lisp` (read), `docs/DECISIONS.md` |
| **D37** | the memory-destination gate was POSITION-BLIND, and only a three-operand row could show it | `Tests/Coverage.lean` |

## D36 — the catalogue said one thing and the machine said another

The batch-12 bank made "check `catalogue-data.lisp` FIRST" the rule for pricing
a form. Batch 13 obeyed it and then **ran the opcodes**: 36 hand-assembled forms
(every byte verified against clang first), one `x86-fetch-decode-execute` each,
about five seconds of ACL2.

| the `:doc` says | measured |
|---|---|
| §5.1.8 "Unimplemented: SCAS and LODS variations" | ⛔ **all eight execute** — `lodsq` loads 8 bytes and advances RSI by 8; `scasq` compares, sets flags, advances RDI |
| §5.1.16 LZCNT unimplemented | ⛔ **`lzcntq/l/w` execute**, and are really LZCNT: `lzcntq 0x123456789ABCDEF0` = 3, where a `bsr` reading the same bytes answers 60 |
| §5.1.16 lists BLSI in neither set | ⛔ **`blsiq/l` execute** |
| §5.1.16 ANDN BEXTR BLSMSK BLSR BZHI PDEP PEXT MULX RORX unimplemented | ✔ all nine refuse |
| §5.1.13 MOVBE, §5.1.16 SARX/SHLX/SHRX/TZCNT implemented | ✔ all execute |

⭐ **The probe refused nine forms and executed twenty-seven in the same run**, so
neither "everything executes" nor "everything refuses" is a reading a broken
instrument could have produced. That two-sided calibration is why the
measurement outranks the prose.

⇒ **A catalogue's prose is a claim ABOUT a model, not a measurement OF it.**
`lods`, `scas`, `lzcnt` and `blsi` are back on the candidate list.

## D37 — a gate repaired twice, still wrong in a dimension no row varied

`sarx`/`shlx`/`shrx` are the coverage table's first THREE-operand rows. Their
shapes read `r,r,r · r,m,r`, and `r,m,r` **contains the substring `m,r`** —
whose `m` is the SOURCE. `mem_dest_claims_are_backed` went RED on a true claim.

Respelling the shapes column until the pattern stopped firing was the cheap way
out and is exactly the failure the gate exists to catch, so the repair went into
the predicate: **a memory destination is an `m` in the FIRST operand position of
some shape**, followed by `,` or `(`. A bare first-position `m` is still a
memory SOURCE, which is what keeps `push` out.

## The probes, each run in both directions

**The rewritten memory-destination gate.**

| probe | result |
|---|---|
| `movbe`'s `m(w)` claim with no `isMemDestVector` case | ⛔ RED |
| `setcc`'s `m8(w)` claim with its case removed (D32's half, re-checked under the NEW predicate) | ⛔ RED |
| `sarx` respelled to claim a first-position `m,r` it has no vector for | ⛔ RED |
| `push` respelled as a written `m(w),r` | ⛔ RED (a bare `m` is still read as a source) |
| the tight rule made to stop reading the parenthesised kind | ⛔ RED |
| correct code | silent |

**The rewrite audit.** `mem_dest_rewrite_changed_exactly_the_three_operand_rows`
states the rows the OLD rule claims and the new one does not, as the list
`["sarx","shlx","shrx"]` — not as a count, which any three rows would satisfy.
⚠️ The first probe of it was ILL-CHOSEN: respelling `movbe` to `r,m,r · m(w),r`
left both rules answering *true*, so the GREEN it returned proved nothing. The
probe that means something respells `mov` so **only** the loose rule reads a
destination ⇒ ⛔ RED.

**The new coverage is load-bearing, measured.** `wrongMovbeFullWidth` reverses
64 bits at every width — a model that is CORRECT at `.q`.

| probe | result |
|---|---|
| all six `movbe` vectors | ✔ caught, 121 disagreements in `rax` |
| the four narrow-width vectors deleted | ⛔ **caught ZERO** — "comparator reported ZERO unexplained disagreements against a KNOWN-WRONG model" |

⇒ The `.w` and `.d` vectors are not width-padding; they are the **only** thing
that can tell the two models apart.

**"Flags Affected: None", measured rather than asserted.** In `run/lean.txt`,
**245 of the 545 forms draw undefined bits** and all **11** batch-13 forms draw
**zero**. ⚠️ The first attempt at this count used a field name the records do not
carry, so its zeros were vacuous and its positive control was silent — the count
above is the one with a control that fires.

## The three new selftest arms

| arm | field | caught |
|---|---|---|
| `shlx/shrx/sarx write the flags a shift writes` | `cf` | 264 |
| `movbe reverses 64 bits at every width` | `rax` | 121 |
| `movbe moves without reversing` | `mem@0000000000001ff0` | 123 |

The third names the DATA WINDOW rather than a register deliberately: the store
direction is the half a register field cannot see.

## Cost

| item | measured |
|---|---|
| differential, 43600 cases | **1 m 08 s** ⚠️ the batch-12 bank said "~10 min"; that figure is wrong — artifacts verified fresh (43600 records, 27.7 MB) |
| full 34-arm selftest | see the bank |
| filtered selftest, one arm | 50 s |
| `Tests.Coverage` kernel time | **16 400 ms** against a ceiling of 19 560 (84%) — of which **5 800 ms is the D37 audit theorem alone** (measured by deleting it: 10 600 ms) |
| ACL2 oracle reachability probe, 36 forms | 4.8 s |

⚠️ **The kernel ceiling is the next batch's inherited problem.** `Tests.Coverage`
now sits at 84% of its registered ceiling and the audit theorem is a third of the
module. It is kept because it is the only thing standing between a gate rewrite
and a silent weakening — but the next head should expect to either raise the
ceiling deliberately (as batch 3 did, with the reason recorded) or make
`claimsMemDestLoose` cheaper, and should not discover this at the end of a batch.

## What is NOT claimed

`movbe` at `.b` and `sarx`/`shlx`/`shrx` at `.b`/`.w` have **no encoding**, and
`movbe r, r` has none either; `step` declines all of them by
`.illegalOperands` rather than answering. `mulx`, `rorx`, `andn`, `bextr`,
`blsr`, `blsmsk`, `bzhi`, `pdep` and `pext` are the rest of roster family 15's
BMI group and are **not** differentially validatable against this oracle — that
is a measurement (D36), not a reading.
