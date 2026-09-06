# P2 BATCH 21 — the half-move family, where the ModRM `mod` field selects the MNEMONIC

```
cases=88000  matched=67468  explained=29435  unexplained=0  oracle-divergence=171  oracle-leaks=0  missing=0
1000 vectors · 88 pre-states · 88000 cases · 0 unexplained · 0 oracle leaks
```

> ⚠️ **TWO COUNTERS.** Twenty-first differential record; the seat's **batch 36** in
> `docs/DECISIONS.md` (D160). Code comments use the SEAT number, this document
> and the coverage prose use the RECORD number.

**Forms.** The six remaining members of the half-move family: `movhlps` (1,341) ·
`movhpd` (556) · `movddup` (506) · `movlhps` (340) · `movlpd` (274) · `movlps`
(101) — 3,118 instructions of assembly-class demand. **Six roster rows, 15
vectors, THREE new constructors and TWO NEW FIELDS on two existing ones, no new
state.**

Roster 146 → **152**, vectors 985 → **1000**, runs 264 → **270**.

## 1. ⛔⛔ THE `mod` FIELD SELECTS THE MNEMONIC, WHICH IS NEW VOCABULARY HERE

Every earlier batch that shared an opcode across forms shared it across *operand
shapes* of ONE instruction. These do not:

```
  0f 12  mem   movlps    dst[63:0]  <- m64          0f 13 mem   movlps  (store)
  0f 12  REG   movhlps   dst[63:0]  <- src[127:64]
  0f 16  mem   movhps    dst[127:64] <- m64         0f 17 mem   movhps  (store)
  0f 16  REG   movlhps   dst[127:64] <- src[63:0]
  f2 0f 12     movddup   BOTH halves <- the low quadword     (REG and mem)
```

`0f 12` is **four mnemonics** and `0f 16` is **two**. ⭐ AND THAT RETROACTIVELY
JUSTIFIES A CHOICE ALREADY IN THE TREE: `movlps`/`movhps` have no
register-to-register encoding at all, so `vloadq`/`vstoreq` having no `x,x` shape
is the ENCODING and not a convenience. The low pair is built the same way.

## 2. ⛔⛔ WHAT THIS RUN'S GREEN DOES NOT CONTAIN — AND FOR A THIRD OF THE BATCH IT IS NEARLY NOTHING

Every one of the 1,320 new cases MATCHED, and every other figure is byte-identical
to record 20's: `explained` unchanged at 29,435, `oracle-divergence` unchanged at
**171**, leaks and missing at zero. The delta is exactly 15 vectors × 88
pre-states with nothing else moved.

**`movlpd` and `movhpd` are not witnessed by one case of it.** They are
bit-identical to `movlps`/`movhps` — not by assumption from the prefix rule but
MEASURED, in `vendor/k-x86-64`, in all four positions:

```
  movlps/movlpd xmm,m64   parent[0,192) ++ Mem64                     LOW  written
  movhps/movhpd xmm,m64   parent[0,128) ++ Mem64 ++ parent[192,256)  HIGH written
  movlps/movlpd m64,xmm   stores parent[192,256)                     the LOW  quadword
  movhps/movhpd m64,xmm   stores parent[128,192)                     the HIGH quadword
```

So a model that decoded `66 0f 12` as `movlps` would score **identically on all
88,000 cases**. This is record 20's finding arriving again one batch later, and
the response is the same two instruments: `check_encodings.py`, which assembles
each vector's AT&T text and compares BYTES — the `66` is exactly the byte it
compares — and a THEOREM, `quad_spelling_is_inert`, which states over both types
what no vector can distinguish:

```lean
  theorem quad_spelling_is_inert (h : VHalf) (k k' : VQuadKind) … :
      step ⟨.vloadq h k d ea, len⟩ s = step ⟨.vloadq h k' d ea, len⟩ s
```

⇒ 🔑 **THE CLAIM A DIFFERENTIAL CANNOT MAKE IS THE ONE THAT HAS TO BE PROVED.**
Batch 19 proved the `andps`/`pand` identity for this reason; this is the same
shape, and the kind field is what makes it statable at all.

## 3. K WAS THE DECIDING SOURCE, AND IT ALSO RE-CONFIRMED AN INHERITED RULE

Every rule above was read off K before a line of semantics was written, rather
than off the SDM. That also settled `movhlps`/`movlhps`, whose names invite the
wrong reading — `movhlps` WRITES the low half, so a reader matching half-to-half
gets it backwards:

```
  movhlps R1,R2   R2[0,192) ++ R1[128,192)                   dst LOW  <- src HIGH
  movlhps R1,R2   R2[0,128) ++ R1[192,256) ++ R2[192,256)    dst HIGH <- src LOW
  movddup R1,R2   R2[0,128) ++ R1[192,256) ++ R1[192,256)    BOTH     <- src LOW
```

⭐ And it re-confirmed the INHERITED `movhps` rule from batch 20 against a source
batch 20 did not use: batch 20 cited the SDM and the oracle, and K agrees with
both. A rule that was right is the least re-read kind.

⚠️ A third independent measurement of the encoding table came free: assembling
all fifteen forms with `clang -target x86_64-unknown-linux-gnu` and disassembling
agrees exactly with the two the queue already had, and LLVM's own operand
comments (`movhlps: xmm0 = xmm1[1],xmm0[1]`) are a fourth witness to the
half-selection.

## 4. ⭐⭐⭐ THE EVIDENCE: SIX WRONG-MODEL ARMS, ALL CAUGHT, EVERY SILENT CASE ACCOUNTED FOR

```
  movlps CLEARS the high half instead of preserving it   228  `xmm0`
  movlps loads into the HIGH quadword                    208  `xmm0`
  movlps stores the HIGH quadword                        208  `mem@0000000000001fe0`
  movhlps/movlhps read the destination's own half        336  `xmm0`
  movddup PRESERVES the high half instead of writing it  146  `xmm0`  (reach 230)
  movddup duplicates the HIGH quadword                    84  `xmm0`
```
⚠️ HEADER COUNTS READ, NOT THE PASS LINES: `3 of 129`, `1 of 129`, `2 of 129` — six arms, which is
the batch's six, and 129 is 123 + 6. D117's rule is that a filter which quietly selects fewer arms
than intended still prints PASS, so the subject's size is the only thing that says the run happened.

**⭐ AND THE SILENT CASES ARE DERIVED, NOT SHRUGGED AT.** Each count is a joint fact about the model
and the PRE-STATES (D117), and here every gap has a closed form in `xmmPattern`, which gives
register `r` the halves `hi := a + r.index` and `lo := c ^^^ (r.index * 0x1111111111111111)`, over
88 pre-states of which **28 are diagonal** (`a = c`) and **12 have `a = 0`**:

| arm | reach | caught | silent | why, exactly |
|---|---|---|---|---|
| CLEARS high | 3 load vec × 88 = 264 | 228 | 36 | right `(a, m64)` vs wrong `(0, m64)` ⇒ agree iff `a = 0`: 12 states × 3 vectors |
| loads HIGH | 264 | 208 | 56 | right `(a, c)` vs wrong `(c, c)` ⇒ agree iff `a = c`: 28 diagonal × the **2** vectors reading the window `mkPre` fills with `c` (the `disp 4` vector reads a shifted window and is never blind) |
| stores HIGH | 3 store vec × 88 = 264 | 208 | 56 | agree iff the SOURCE's halves are equal; xmm0 has `hi = a`, `lo = c`, so 28 diagonal × 2 xmm0 vectors — the %xmm5 vector never agrees |
| cross moves | 4 vec × 88 = 352 | 336 | 16 | agree where the source's opposite half already equals the destination's own |
| movddup PRESERVES | 2 xmm0 vec × 88 = 176 | 146 | 30 | agree where dst's high already equals src's low |
| movddup dups HIGH | 1 vec × 88 = 88 | 84 | 4 | agree iff **xmm1's own halves are equal**, which happens in 4 states |

⇒ 🔑 **A COUNT WITH NO ACCOUNT OF ITS MISSES IS HALF A READING.** Batch 20 recorded its 152 as a
joint fact and stopped there; these are stated as *predicates*, so a later change to `xmmPattern`
that quietly removed the diagonal states would show up as a number that no longer matches its own
formula rather than as a slightly different total nobody re-derives.

## 5. ⛔ TWO THINGS THIS BATCH LEARNED ABOUT THE INSTRUMENT, NOT ABOUT x86

**(a) AN ARM'S SCORE IS A LOWER BOUND ON ITS REACH.** `movddup PRESERVES` reports **146** in `xmm0`
while its total unexplained is **230**: the third `movddup` vector writes **%xmm5**, and `driveWrong`
counts only disagreements in the single declared `expectField`. Nothing is wrong here — 146 > 0 is
the claim — but had that batch contained ONLY the %xmm5 vector, a perfectly working arm would have
scored **0 in `xmm0`** and reported *"fires on the wrong thing"*. ⇒ **`expectField` is a bet that
every vector an arm reaches writes the same register**, and the bet is invisible while it holds.
Batch 20 carries the same shape (`movhps_load_x5`), so this is a convention with an unstated
precondition rather than a defect introduced here.

**(b) D117's NAMING RULE HAS A COST ITS OWN NOTE DOES NOT MENTION.** Batch 20 named its three arms
to share the substring `movhps` *"so ONE filter selects all three"*. I named these six after their
own mnemonics — correct per mnemonic, and three of them do share `movlps` — but **the BATCH has no
shared token**, so no single filter selects all six. `driveWrong` recomputes the GOOD model once per
process, so each filter invocation re-pays that baseline: the first arm of a filter costs ~12 min
and the rest ~3. Running the batch as three filters cost the baseline **three times**.
⇒ **Give every arm of a batch a shared batch token ALONGSIDE its mnemonic**, so the per-mnemonic
filter and the per-batch filter both work. Recorded rather than retro-fitted: renaming now would
cost a rebuild and a 20-minute re-run for no new evidence.
