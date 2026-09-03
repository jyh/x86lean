# P1 BATCH 19 — no new forms: the coverage number, made DERIVED, was eleven LOW

**Forms.** ⭐ **NONE.** This batch adds no vector, no mnemonic and no semantics. It replaces
the coverage claim — a hand-maintained literal since P0 — with a derivation, and the
derivation disagrees with the literal.

```
cases=57400  matched=38603  explained=27195  unexplained=0  oracle-leaks=0  missing=0
  spec: 0   refusal: 0   harness: 0   undefined-region: 27195
700 vectors · 82 pre-states · 83 mnemonics
```

The differential run is UNCHANGED and that is the point: the batch is not entitled to move
it. It was re-run anyway, because "no semantics changed" is a claim about a diff and not a
measurement — see the conditions recorded below.

## What was wrong

Until this batch `Main.lean` published `covering **N of the 525 forms**` as a literal. Its
value was a running sum of **eighteen independent `awk` counting rules**, one written into a
comment at the batch that added it, and **nothing had ever checked that those eighteen rules
partition the roster.** Batch 18's handover named the symptom precisely: of the 72 rows it
believed remained, it could account for only 32, and the other ~40 carried base names the
model already implements. It could not close the residue and said so.

**The derived answer is 469 of the 525 rows. The literal said 453. It was SIXTEEN LOW.**

⇒ 🔑 **THE DIRECTION IS THE FINDING.** An over-claim reads as a mistake and gets looked
for; an under-claim reads as modesty and does not. Eighteen batches of arithmetic rested on
a number no gate read in either direction, and the error it accumulated was the one nobody
was ever going to go looking for.

## How it is derived — two sources that are not derived from each other

`scripts/claimed_forms.py`, 1.3 s, no oracle needed:

* **SOURCE S — the vector's own text.** Each vector's AT&T `asm` string, the one clang
  assembles and `check_encodings.py` already gates, parsed against the roster's own shape
  vocabulary. Deliberately GENEROUS: `%al` is offered as both `r` and `al`, `$1` as both
  `imm` and `one`, a symbol as `label`, `rel8` and `rel32`.
* **SOURCE E — the roster row's own encoding.** Every one of the 525 rows is synthesised
  into a canonical instance and assembled by clang, with no reference to any vector.

**A vector may claim only a row whose encoding it MATCHES**, and a row's encoding is its
FORM SKELETON: the bits that survive perturbations which move only operand values. A
mis-parse does not survive the gate — reading `andb $0x5a,%al` as the generic `r,imm` form
offers a three-byte ModRM encoding against a two-byte accumulator one. A vector that
resolves to nothing is a finding and the tool exits non-zero. **It never guesses.**

All 700 vectors resolve. None splits across two forms.

## The residue, named

⭐ **143 of the 525 rows are alias SPELLINGS of another row** — `jz`/`je`, `setz`/`sete`,
`cmovz`/`cmove`, `sal`/`shl`, `loopz`/`loope`, `xchg ax,r`/`xchg r,ax`, `movs -`/`movs m,m`.
clang says so, not a hand-written synonym list. **This is why base-name arithmetic could
never partition the roster**: the model decodes BYTES, so a vector spelled `je` exercises
the `jz` row exactly as much, but `$4 ~ /^(je)$/` claims three rows and leaves three
identical ones behind.

The document now publishes both denominators, and the alias claim is visible rather than
silent:

| | |
|---|---|
| roster rows claimed | **469 of 525** |
| — spelled by a vector | 346 |
| — same encoding, other spelling | 123 |
| distinct machine forms claimed | **322 of 374** |

⛔ **AND TWO ROWS DESCRIBE NO ENCODING AT ALL.** `jecxz rel32` and `jrcxz rel32` exist
because K's grammar generates them; the assembler refuses both — *"value of 200 is too large
for field of 1 byte"* — because those instructions have only an 8-bit displacement. They are
denominator that cannot be earned, and the tool names them on every run instead of leaving
them among the 61 rows that remain.

## What remains, fully accounted for the first time

Batch 18 handed on "72 rows remain, and I can account for only 32 of them." **56 remain,
and every one is now named:**

| | |
|---|---|
| oracle UNAVAILABLE — the nine BMI forms x86isa refuses | 18 |
| **NO ENCODING EXISTS** — `jecxz rel32`, `jrcxz rel32` | 2 |
| genuinely available work | **36** |

The 36: `sub` 8 · `add` 7 · `mov` 2 · `push` 2 · `xchg` 2 · `adc` 2 · `sbb` 2 · one each of
`jmp` `neg` `callq` `movnti` `not` `pop` `bt` `btc` `btr` `bts` `cmpxchg8b`.
`scripts/claimed_forms.py --remaining` prints them with their shapes and widths, so the
next batch derives its scope instead of guessing at an `awk` pattern. They are mostly the memory-DESTINATION and accumulator-short forms of the
arithmetic P0 shipped at `r,r` — `add m,r`, `sub r,imm`, `add al,imm` — which is a coherent
next batch rather than a residue.

⚠️ **WHERE THE SIXTEEN ROWS WENT CANNOT BE ATTRIBUTED TO A BATCH, AND THAT IS ITSELF THE
FINDING.** The counting rules for batches 13–18 are written down in `Main.lean` and can be
re-run; the rules for batches 1–12 never were. Ten of the 123 alias-only rows have a base
name that a base-name rule would have caught (`movs m,m`, `cmps -`, `scas m`, `lods m`,
`xchg r,eax`, `xchg r,rax` and their kin), which is suggestive and is not proof.
⇒ 🔑 **AN UNRECORDED RULE CANNOT BE AUDITED EVEN AFTER THE FACT.** The number could be
corrected only by recomputing it from scratch, which is what this batch did.

## ⛔ AND THE FIRST VERSION OF THE TOOL REPEATED THE VERY DEFECT IT EXISTS TO CATCH

It under-claimed by one row. The first claim rule grouped rows into aliases only when their
skeleton sets were EQUAL **and** their roster `widths` strings matched — so `stos m`
(widths `bw`) never joined `stos -` (widths `blqw`), although `stos m` at byte width IS the
`0xaa` that vector `stos_b` assembles to. It is the only strict-subset pair in the roster.

It was caught by running a **second claim rule** and diffing: *a row is claimed iff some
vector's bytes match one of its own encodings*, with no parse consulted at all. The two
rules agreed on 464 rows and disagreed on exactly one. The claim is now the byte rule and
the parse is its CHECK — the gate requires every row claimed by bytes to share an encoding
with a row the parse independently identified, which is what stops an over-masked skeleton
matching rows that are not the same instruction.

⇒ 🔑 **A CONSERVATIVE RULE IS STILL A WRONG RULE, and it is wrong in the direction that does
not announce itself.** Writing a whole batch about an unpoliced under-claim did not stop me
shipping a smaller one inside the instrument built to catch it. Only the second rule did.

⛔ **AND THEN IT HAPPENED AGAIN, FOR FOUR MORE ROWS.** The alias relation was still EQUALITY
after that repair, but K's grammar writes some rows as a RESTRICTION of another, so the
relation is CONTAINMENT — and a symbolic-immediate row (`cmp m,label`) was synthesised with
an unperturbed `$NEAR`, leaving its immediate bytes as literal zeros that were read as
OPCODE. Found by a THIRD check: **a row's skeleton may not match a canonical instance of a
row it is not related to.** That is the only one of the three able to catch an OVER-masked
skeleton, because under-masking makes the held-out reading stop matching while over-masking
is SILENT — matching more never makes anything fail. 465 → **469**.

⇒ 🔑 **THREE CORRECTIONS, ALL IN THE SAME DIRECTION.** Each was an under-claim; each was
invisible to the gate that existed when it was made; each was found only by adding a route
to the answer that did not go through the rule under test. **A published number is worth as
much as the number of INDEPENDENT routes that agree on it**, which is why the tool now
carries three — and reports the single place they cannot separate: `0x90` is both `nop` and
`xchg eax,eax`, the SDM defines that byte as NOP precisely so it does not zero-extend RAX,
and no byte-level rule can tell them apart. The collision is printed on every run and
becomes a FINDING only if a row is ever claimed solely through it — an arm of the selftest
deletes the vector that independently supports `xchg eax,r` and requires exactly that.

## The three defects found building it, which are one defect

Every one was found by the tool REFUSING to resolve a vector that plainly belongs to a row.

1. ⛔ **Two register banks cannot span a three-bit field.** Bits that happened to agree in
   both banks were frozen into the skeleton as opcode, and `and %ecx,%eax` failed to match
   the `and r,r` row it is an instance of. Four banks now cover every bit of every operand
   position.
2. ⛔ **A "complement" that was not one.** The displacement pair `0x12345678`/`0x6dcba987`
   differs in every bit but the TOP one, so bit 31 was read as opcode and the one vector
   with a negative displacement did not match its row. ⚠️ **The held-out control was silent,
   because its value was positive too and agreed with the perturbations on exactly the bit
   they missed.** The held-out values are negative now.
3. ⛔ **A silently lost label.** `objdump` prints one symbol per address, so **4713 of 4714
   encodings vanished** and were reported as "rows with no assemblable form" — a sentence
   that reads like an answer. `assemble` now counts its labels and refuses rather than
   returning a short table.

⇒ 🔑 A perturbation must reach not just the FIELD but **every bit of it**, and a control
drawn from the same half of the space as the perturbation says nothing about the other half.

⭐ A fourth, of the same family: clang accepts an UNSUFFIXED spelling and picks a default
width, so a reading meant to be `btw` came back as `btl` and four `bt` rows held the `l`
encoding at `w` and `q`. **A row whose roster widths are distinct must have distinct
encodings at them** — now a control, and the readings that fail it are voided and named.

## The gate, and its selftest

`python3 scripts/claimed_forms.py --check` gates **all six published numbers** against the
derivation, reading them out of the GENERATED `docs/COVERAGE.md` rather than out of the
generator's own source. `--selftest` has five arms and takes 6 s:

```
  ✔ control: the repository as it stands
  ✔ a vector whose bytes match no roster row
  ✔ a vector whose text and bytes disagree
  ✔ a row left claimed only through a colliding encoding
  ✔ the published number carries an OVER-claim of one row
  ✔ the published number carries an UNDER-claim of one row
```

⚠️ **THE THIRD ARM IS BUILT FROM DATA, NOT FROM A CODE HOOK, AND THAT WAS A REPAIR.** Its
first version set an environment variable that made every mask total — and it went red by
tripping the WIDTH control instead, i.e. for a reason other than the one the arm is named
after. **A red light in the wrong lamp is not a test of the gate beside it.**

⚠️ **The last two arms are the batch's own lesson made mechanical.** A gate that fired only
on over-claims would have passed this repository for eighteen batches.

See `docs/DECISIONS.md` D56, D57, D58.
