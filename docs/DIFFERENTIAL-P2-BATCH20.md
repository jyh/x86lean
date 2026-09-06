# P2 BATCH 20 — the `66` spellings, and a batch whose own vectors are not its witness

```
cases=86680  matched=66148  explained=29435  unexplained=0  oracle-divergence=171  oracle-leaks=0  missing=0
985 vectors · 88 pre-states · 86680 cases · 0 unexplained · 0 oracle leaks
```

> ⚠️ **TWO COUNTERS.** Twentieth differential record; the seat's **batch 35** in
> `docs/DECISIONS.md` (D159). Code comments use the SEAT number, this document
> and the coverage prose use the RECORD number.

**Forms.** `movapd` (`66 0f 28` / `66 0f 29`) and `movupd` (`66 0f 10` /
`66 0f 11`) — the `pd` spellings of the two 128-bit moves. **Two roster rows, 8
vectors, NO new constructor, NO new function and NO new state**: they are two new
`VMovKind` members, so `Op.vmov`, `Op.vload` and `Op.vstore` carried all three
operand shapes already. 2,533 instructions of assembly-class demand
(`movapd` 2,420 · `movupd` 113).

Roster 144 → **146**, vectors 977 → **985**, runs 260 → **264**.

## 1. ⛔⛔ WHAT THIS RUN'S GREEN DOES NOT CONTAIN

Every one of the 704 new cases MATCHED, and every other figure is byte-identical
to batch 19's: `explained` unchanged at 29,435, `oracle-divergence` unchanged at
171, leaks and missing at zero. That is exactly what it should be, and **it is
almost no evidence about this batch.**

`movapd` moves the same 128 bits as `movaps`, under the same alignment rule, at a
different opcode. **A model that decoded `66 0f 28` as `movaps` would score
identically on all 86,680 cases.** No differential vector that can exist
distinguishes the spellings, because the `66` prefix selects a MNEMONIC and
changes nothing the architecture can observe about the transfer.

⇒ **the witness for this batch is `scripts/check_encodings.py`**, which assembles
each vector's own AT&T text and compares BYTES — and the `66` is precisely the
byte it compares. `encoding cross-check: CLEAN — 985 forms, every `Instr.len` and
every byte string agrees with the assembler.` Same instrument, same reason, as the
`movdqa`/`movaps` pair (batch 11) and the four `PREFETCHh` hints (batch 22), where
a wrong-model arm would have been a FALSE ENTRY in the gate's own inventory (D91).

⚠️ The eight vectors carry the FULL shape set anyway — register, load, store, and
an unaligned load — rather than one token vector per mnemonic. The roster claims
three shapes for each row, and a claimed shape with no vector is the under-claim
this repository does not police. ⛔ There is no unaligned `movapd` vector, for the
reason there is no unaligned `movaps` one: the oracle does not implement the #GP
check (D91), so such a vector would test the harness rather than the model.

## 2. ⭐⭐ THE GATE THAT SAID IT WAS EXHAUSTIVE AND WAS FOUR LITERALS

`Tests.vmov_alignment_is_by_kind` asserted the aligned/unaligned partition over
`dqa`/`aps`/`dqu`/`ups`. Its docstring said:

> *"Written as a claim about the derived flag rather than as four separate cases,
> so a fifth mnemonic cannot be added without answering the question."*

It is four separate cases. **This batch added a fifth and a sixth, and the theorem
stayed TRUE, GREEN and SILENT about both.** The sentence described the theorem its
author meant to write, and a reader auditing whether the alignment rule was gated
would have read the sentence and stopped.

⇒ 🔑 **PROSE ASSERTING THAT A CHECK IS EXHAUSTIVE READS AS THE EXHAUSTIVENESS
CHECK.** This is the same shape as D158's sizing rule, found the same night: a
true-sounding sentence standing where a mechanism was assumed to be.

**Repaired.** `VMovKind.all` lists every kind, and

```lean
theorem vmov_kinds_are_all_listed : ∀ k : VMovKind, VMovKind.all.contains k = true := by
  intro k; cases k <;> decide
```

holds the list to the TYPE — `cases` is exhaustive by construction, so a new
constructor now fails to COMPILE rather than passing unmentioned. The alignment
claim is then quantified over `VMovKind.all` and means "every kind there is".

⛔ **DRIVEN RED-FIRST**, and the plant is the strong one: a seventh kind wired
fully through `aligned`, `mnemonic` AND `all`, so that everything else still
compiles and only the gate under test can speak. `vmov_alignment_is_by_kind` goes
red — *"Tactic `decide` proved that the proposition is false"*. Reverted after.

⚠️ Note for the next head: `∈` on a `List` has no derived `Decidable` instance
here; `List.contains` does, and keeps the exhaustive `cases`.

## 3. WHAT THE BATCH COST, AGAINST A PREDICTION MADE BEFORE IT WAS BUILT

D158 measured the growth law the same night: `vectorCoverage` is quadratic in
(rows × runs) and **flat in vectors**, at ~25 ms per new MNEMONIC and 0.0 ms per
vector, against a budget of 15.7% of the base. `scripts/p2_batch_size.py` priced
2 mnemonics at **+40 to +65 ms** before a line of this batch was written.

That is a sealed prediction this batch's delta gate can score, and it is the first
out-of-sample test the tool has had that is not its own calibration replay.

## 4. THE SHAPE, FOR THE RECORD

```
  roster rows   144 -> 146       runs   260 -> 264       vectors  977 -> 985
  cases       85976 -> 86680     (+704 = 8 new vectors x 88 pre-states)
  matched     65444 -> 66148     (+704 — every new case matched)
  explained   29435 -> 29435     oracle-divergence 171 -> 171 (unchanged)
```

⚠️ Two derived lists had to gain these rows and only a TYPE ERROR said so: the
`memDestSweep` exception list and the corollary that restates it are two copies
that must agree, and adding a row to one and not the other fails several hundred
lines from the edit, as a mismatched type rather than a wrong answer.
