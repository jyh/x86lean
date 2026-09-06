# P2 BATCH 22 — the two-source shuffles, four inert spellings, and a form the oracle never ran

```
cases=89056  matched=68524  explained=29435  unexplained=0  oracle-divergence=171  oracle-leaks=0  missing=0
1012 vectors · 88 pre-states · 89056 cases · 0 unexplained · 0 oracle leaks
```

> ⚠️ **TWO COUNTERS.** Twenty-second differential record; the seat's **batch 37**
> in `docs/DECISIONS.md` (D168, D169, D170). Code comments use the SEAT number,
> this document and the coverage prose use the RECORD number.

**Forms.** `shufps` (1,545) · `shufpd` (70) · `unpcklps` (64) · `unpcklpd` (45) ·
`unpckhps` (40) · `unpckhpd` (16) — 1,780 instructions of the 1,833 the residue
measured. **Six roster rows, 12 vectors, one new kind, two new constructors, one
new combinator, no new state.**

⛔ **THE SEVENTH MNEMONIC, `movmskps` (53), IS NOT HERE AND ITS ABSENCE IS THE
BATCH'S FINDING** — see §3.

Roster 152 → **158**, vectors 1000 → **1012**, runs 270 → **282**.

## 1. FOUR OF THE SIX ARE SPELLINGS, AND NO VECTOR CAN SAY SO

`unpcklps ≡ punpckldq` · `unpckhps ≡ punpckhdq` · `unpcklpd ≡ punpcklqdq` ·
`unpckhpd ≡ punpckhqdq`. Each is tested only against the oracle, never against its
sibling, so a model decoding `0f 14` as `punpckldq` scores identically on all
89,056 cases. The bytes are held apart by `scripts/check_encodings.py` (CLEAN over
1012 forms); the semantics is held together by
`unpack_aliases_are_their_integer_siblings`.

⛔⛔ **A TEXT DIFF OF K WOULD HAVE SPLIT THEM 2/2.** Whitespace-normalised, the two
`pd` pairs are byte-identical and the two `ps` pairs differ at char 122 of 345 —
pure re-association of `concatenateMInt`, which is associative on bit strings.
Under the leaf-sequence normal form all four agree and three controls differ. The
split falls along `ps`/`pd`, so a byte comparison offers a self-consistent WRONG
design with its own explanation attached. LLVM's disassembler agrees with the leaf
reading independently, printing one operand comment per pair.

## 2. THE TWO-SOURCE SHUFFLES ARE 88% OF THE DEMAND AND THE ONLY NEW SEMANTICS

`VShufKind` was the wrong home and the reason is structural, not stylistic: every
member of that kind selects from ONE source and `vshufApply` takes a single `src`.
`shufps` reads BOTH operands. `Op.vshufp`/`Op.vshufpm` carry `VShufpKind`.

```
   shufps   lane0 ← DEST[imm[1:0]]  lane1 ← DEST[imm[3:2]]
            lane2 ← SRC [imm[5:4]]  lane3 ← SRC [imm[7:6]]
   shufpd   qword0 ← DEST[imm[0]]   qword1 ← SRC[imm[1]]
```
Decided on K, checked against the SDM's `Select4`, and confirmed by a third source
before a line was written: LLVM renders `shufps $0x1b,%xmm1,%xmm0` as
`xmm0 = xmm0[3,2],xmm1[1,0]`. The anchors quote LLVM's own example immediate, so
their expected values come from a source independent of the rule under test.

⚠️ **THE DESTINATION IS READ**, which no other shuffle here does — `Op.vshuf`
overwrites its destination without consulting it.

## 3. ⛔⛔⛔ `movmskps` STALLS ON THE ORACLE, AND TWO GATES CALLED IT FINE

The first run of this batch returned **unexplained=464**, every one `movmskps`.
Measured at the object over 88 pre-states per vector:

```
   movmskps_x1_eax   88/88  RIP NEVER ADVANCES, refused-flag = 0
   movmskps_x5_ecx   88/88  RIP NEVER ADVANCES, refused-flag = 0
   pmovmskb_x1/x5    88/88  executes     ← same constructor, same shape
   unpcklps_xx/_m    88/88  executes     ← also a NO-PREFIX SSE form
   shufps/shufpd     88/88  executes, and matched
```

Two positive controls in the same run, chosen to differ in the two dimensions a
reader would blame — the constructor and the prefix/feature class — so the stall is
a fact about this MNEMONIC. It is the only form in the table that stalls with the
refusal flag CLEAR, which is why the differential filed 464 field mismatches as
`spec`: as THIS MODEL being wrong about a rule the oracle never evaluated.

⛔ **AND `oracle_availability.py` — the gate built so the unavailable list would be
measured rather than declared — answered `executes 88/88`.** Its classifier was
`if refused=1 then refused else EXECUTED`, so `executed` was a RESIDUAL. ⇒ 🔑 **a
two-valued classifier over a three-valued world scores the unseen state as
whichever value is the residual**, and here the residual was SUCCESS, in the one
gate whose purpose is to stop unavailable work being invented.

Repaired three-valued (`refuses · executes · stalls`), `movmskps` declared `stalls`
and now measured. The ten BMI forms and `movnti` still read `refuses` in the same
run — the control that the new branch did not swallow the refusal class.

**The model keeps `movmskps`**: `VMovMskKind.ps`, its semantics and five kernel-
checked anchors against K and LLVM. It is not CLAIMED, because a roster row here
means *differentially tested*. The day x86isa executes it the availability gate goes
RED — declared `stalls`, measured `executes` — and names the row that can land.

## 4. THE ARMS

Two new wrong models, sharing the substring `Shufp` so one filter selects them:
`wrongShufpAllFromSource` — every lane from the source, i.e. the `pshufd` reading,
which is **the design D167 refused, planted so the refusal is tested rather than
asserted** — and `wrongShufpOperandSwap`.

⛔ Two EXISTING arms would otherwise have run on the four new unpack vectors and
been no-ops: `wrongUnpackHalf` ends in `| other => other` and `wrongUnpackOrder`
names its eight members and falls through to the GOOD model. Both were extended;
the second was found by grepping the file for the shape after fixing the first.
