# G1 — positioning x86lean against the existing x86 semantics

**Why this file exists:** *"why another x86 semantics?"* is the first referee question, and
`docs/TACAS-PRICING.md` prices answering it at 1–2 days. **G1 is now CLOSED: every cell is MEASURED,
RECORDED, or a stated NOT-APPLICABLE with its reason — none is estimated, and none is OWED.**
*(It read "the skeleton with our column measured and the others' columns explicitly OWED" until
2026-09-11, when the remaining **fifteen** table cells were read at the sources — §1c. ⛔ Not
"eight": that was my own from-inspection guess, corrected by parsing the table — see §2.)*

⛔⛔ **THE RULE THIS FILE IS BUILT ON.** Every cell is one of:
* **MEASURED** — derived from this tree today, with the deriving command named;
* **RECORDED** — a figure this repository already carries with a source (`PROVENANCE.md`);
* **OWED** — *not known here*, and it must be read from that project's own documentation before it
  appears in a paper.
**No cell is estimated.** A comparison table is exactly where a plausible number about someone else's
system does the most damage, because it is the one claim a referee can check against the source and we
cannot.
✅ **AND THE RULE IS NOW GATED, NOT MERELY STATED** — `scripts/check_positioning_table.py`, run in CI:
a cell carrying none of the three markers is a FINDING, and §2's declared count must equal the count
derived from the table. *Prose does not refuse; §2 records what it cost to learn that here.*

---

## 1. THE TABLE

| | **x86lean** (this work) | **ACL2 x86isa** | **K x86-64** | **Sail-x86-from-acl2** |
|---|---|---|---|---|
| **prover / host** | Lean 4 + mathlib4 — MEASURED | ACL2 — RECORDED (`PROVENANCE.md`) | K framework — RECORDED | **Sail — and no prover: it is a MODEL, not a proof development** (§1c.5). *The Sail project ships a `sail_lean_backend`, and using it is OUR P3b plan — not a property of this model* — **RECORDED** (`PROVENANCE.md`) |
| **scale** | 158 mnemonics · 1,012 differentially tested forms · 500/525 roster rows · 351/374 distinct machine forms — **MEASURED AND CI-GATED** | *"400+ opcodes … Intel's 64-bit mode"* — **RECORDED** (§1b, Goel arXiv 1705.01225). ⛔ Its opcode **maps** carry 3,192 `INST` entries, which is a DECODE census and NOT this row (§1c.3) | 3,155 variants / 774 mnemonics, Haswell user-level — **RECORDED** (K's own coverage target list) | a **configured slice** of x86isa — 63 `.sail` files, 2,123,049 B in `model/`; exactly one x86isa file excluded wholesale (`fp-structures`) and `defthm` forms excluded by design. **No instruction count is published by the project** — **MEASURED AT THE SOURCE** (§1c.5) |
| **executable** | yes — the model runs; `run_differential.sh` drives it — MEASURED | yes — it is our primary executable oracle — MEASURED (by use) | **yes** — *"fully executable … more than 7,000 instruction-level test cases and the GCC torture test suite"* — **RECORDED** (§1b). We still have never executed it; we read its tree mechanically for the roster | **yes** — `make x86_emulator` builds an emulator from the model snapshot; its validation guide runs an ELF and co-simulates **against K's single-instruction tests** — **MEASURED AT THE SOURCE** (§1c.5) |
| **role here** | the proving model | primary differential oracle | roster/coverage source, read mechanically | third reference, spike only — never the proving model |
| **axiom base of theorems** | exactly `[propext, Classical.choice, Quot.sound]`, CI-gated over the library — **MEASURED** | **zero** `defaxiom`, **zero** `skip-proofs` in 190 `.lisp` files; 6 `defttag` in 5 files, all in execution/instrumentation/syscall/virtualization layers — **MEASURED AT THE SOURCE** (§1c.1) | **not well-posed** — K is a rewriting logic, not a proof assistant with an axiom list; its prover is `kprove` + Z3, so the trust base is K + the SMT solver — **RECORDED** (§1c.4) | **not applicable — the translator ignores `defthm` wholesale**, so the Sail model carries no theorems to have an axiom base — **MEASURED AT THE SOURCE** (§1c.5) |
| **proof support demonstrated** | 7 machine-checked memory-safety theorems over 4 routines; cost model `19 + ~7.7/label` measured at 2–7 labels — **MEASURED** | 8 verified program families (**559** theorem forms) over a separate 24,707-line / 603-form proof-utility library; `copyData-is-correct` is **full functional correctness + fault-freedom for an unbounded loop** — **MEASURED AT THE SOURCE** (§1c.2) | 10 `kprove` reachability specs over 13 claim rules, with functional post-conditions and loop invariants, plus an 846-line / 201-rule verification-lemma library. Its README calls these *"few applications of our formal semantics"* — **MEASURED AT THE SOURCE** (§1c.4) | **NONE, BY CONSTRUCTION** — `tr_ignore`: *"forms we can ignore wholesale. E.g. `defthm`"* — **MEASURED AT THE SOURCE** (§1c.5) |
| **undefined-bit treatment** | explicit oracle in the state; `UNDEF`-seeding precedent taken from x86isa — RECORDED | an `undef` **seed counter** in the state; `undef-read` mints a *fresh unique unknown* per read and the field is `push-untouchable` — **MEASURED AT THE SOURCE** (§1c.6) | a single distinguished **constant** `undefMInt` (and `undefBool`) written straight into the flag, in 497 of 3,064 per-instruction files — **MEASURED AT THE SOURCE** (§1c.6) | **DROPPED IN TRANSLATION** — `other_non_det.sail` is a 27-byte stub (`$include "./syscalls.sail"`) and `rflags_spec.sail` contains no `undef` — **MEASURED AT THE SOURCE** (§1c.6) |
| **decode** | Intel XED consumed as the AST; decode trust named in `TRUSTBASE.md` — MEASURED | a **22,042-line in-tree ACL2 transcription of SDM Vol. 2 Appendix A**, from which the dispatch functions are *generated* in ACL2 — ⚠️ **but NOT purely SDM: 186 of its 3,192 entries (5.8%, the x87 escape block) were machine-generated from XED data files by `xedscan.py`, and 9 more cite `xed-isa.txt` for UNDOCUMENTED encodings** — **MEASURED AT THE SOURCE** (§1c.3, §1c.9) | ⛔ **IT DOES NOT DECODE MACHINE BYTES AT ALL.** `x86-loader.k` parses GNU **assembler source** (`.text`, `.data`, `.globl`, `.comm`); `syntax Opcode ::= "adcb"` is a MNEMONIC, not a byte. **Zero** files mention `modrm`, `ModRM` or `REX` — **MEASURED AT THE SOURCE** (§1c.8) | inherited from x86isa's maps via the translator; `decoding_and_spec_utils.sail` + the generated `*_opcodes_dispatch.sail` — **MEASURED AT THE SOURCE** (§1c.5) |

---

## 1b. ⭐ FOUR CELLS FILLED FROM THE SOURCES THEMSELVES, 2026-09-11
⛔ **READ THIS SECTION AS A NARRATIVE, NEVER AS THE TABLE'S STATE.** Its fills were written here and
**not into §1's cells**, which went on reading `OWED` for the rest of that morning — the defect §2
dissects. The table above is the only register; this section says where four of its figures came from.
**K x86-64 — its own README, verbatim:**
* *"3155 instruction variants, corresponding to 774 mnemonics"* — confirms the figure `PROVENANCE.md`
  already carried, now at the source;
* *"all the non-deprecated, sequential user-level instructions of the x86-64 Haswell instruction set
  architecture"*;
* *"The semantics is fully executable and has been tested against more than 7,000 instruction-level
  test cases and the GCC torture test suite."* ⇒ **its executability cell is no longer OWED, and its
  validation is STRONGER than this table assumed.**

**ACL2 x86isa — from Goel's own paper (arXiv 1705.01225), extracted locally:**
* *"a specification of **400+ opcodes** executing in Intel's 64-bit mode of operation"*;
* it runs *"co-simulations against an actual x86 processor for model validation"* ⇒ **hardware
  co-simulation is theirs already**, which matters because our plan names the same technique.
⚠️ **A web search reported "413 instructions implemented". I am NOT recording that number** — the
primary source says "400+", the 413 could not be verified at `IMPLEMENTED-OPCODES` (HTTP 403), and a
search summary is not a source. **400+ is what the author wrote; 413 stays unrecorded.**

## 1c. ⭐⭐ THE REMAINING CELLS, READ AT THE SOURCES — 2026-09-11

**Where the sources are.** ACL2 + x86isa and the K semantics are cloned locally under `vendor/`
(recipe in `docs/ORACLE-SETUP.md`; the tree is deliberately not vendored into this repository).
Sail-x86-from-acl2 is not local and was read over the network from the project's own files at
`github.com/rems-project/sail-x86-from-acl2@master`, HTTP 200 recorded for each fetch.
⚠️ **`vendor/acl2` and `vendor/k-x86-64` are inside this repository's `.gitignore` (`/vendor/`)**, and
this repository's `grep` is a wrapper honouring ignore files. **Every count below was re-driven with
`command grep` over an explicit `find` list**, and each absence carries a positive control.

### 1c.1 x86isa — AXIOM BASE. **Zero added axioms. The trust tags are all in execution layers.**
```
  population          190 .lisp files under books/projects/x86isa/   (find, no ignore-file involved)
  (defaxiom           0 files          skip-proofs   0 files          (program) mode   0
  (defttag            6 occurrences in 5 files:
      tools/execution/top.lisp           :other-non-det, :undef-flg
      tools/execution/instrument/top.lisp :instrument
      virtualization/top.lisp            :virtualization
      linux/doc.lisp                     :tty-raw
      machine/syscalls.lisp              :syscall-exec   -- guarded by X86ISA_EXEC /
                                         build-with-full-exec-support, i.e. an EXECUTION build
  POSITIVE CONTROL, same needles, books/ at depth<=3:  defaxiom 28 files · skip-proofs 144 files
```
⇒ **The absence is real, not an instrument artifact** — the control fires hard one directory up.
⇒ 🔑 ***THE HONEST READING IS THAT x86isa's THEOREMS REST ON THE ACL2 LOGIC WITH NOTHING ADDED***, and
its raw-Lisp escapes are confined to execution, instrumentation, syscalls and virtualization —
**structurally the same discipline as our own axiom gate**, which confines `bv_decide`/`ofReduceBool`
to test executables. This cell does not separate us from them and the paper should not pretend it does.

### 1c.2 x86isa — PROOF SUPPORT. **Stronger than ours, and the shape of the gap is specific.**
```
  proof family            .lisp   lines    theorem forms (defthm|defthmd|def-gl-thm|defrule)
  utilities                 30   24,707        603      <- the reusable proof library
      utilities/sys-view     22   21,763                 <- 88% of it is SYSTEM-level (paging)
      utilities/app-view      3      945                 <- the like-for-like comparator, with
      utilities/*.lisp        5    1,999                    the 1,999 top-level lines: 2,944
  wordCount                  2    7,153        242
  zeroCopy                   6   14,530        141      <- marking AND non-marking memory views
  dataCopy                   4    2,918        109
  factorial                  2    1,493         45
  codewalker-examples        3      968          8
  dissertation-examples      3      378          7
  popcount                   2    1,433          5      <- def-gl-thm, i.e. bit-blasting
  powOfTwo                   1      345          2
```
`dataCopy/dataCopy.lisp:1595 copyData-is-correct` is **full functional correctness plus
fault-freedom, for a loop of unbounded length `n`** — destination equals source after `(x86-run
(program-clk n) x86)`, source unmodified, `ms` and `fault` both `nil`.
⚠️ **THE TOTAL IS 1,162 AND IT IS NOT THE HEADLINE NUMBER.** 603 of those forms are the reusable
`utilities` LIBRARY, not proofs about programs; the **8 program families carry 559**. My first draft
of the table cell said *"8 verified program families (1,162 theorem forms)"*, which silently credited
the library to the programs. ⇒ 🔑 ***A TOTAL OVER A COLUMN WHOSE ROWS ARE NOT THE SAME KIND OF THING
IS A CONFLATION WEARING A SUM'S CLOTHES*** — and it inflated the comparator we are measured against,
i.e. it ran AGAINST us, which is why it survived a read: an unflattering error does not trip the
instinct that catches a flattering one.
⇒ ⛔ **SAY THIS PLAINLY IN THE PAPER:** our 7 memory-safety theorems over 4 routines are a **weaker
claim over a smaller sample** than x86isa's. Their app-view proof library alone is **2,944 lines**
against our frame library, and `popcount` establishes the GL/bit-blasting tier we keep separate.
⭐ **WHAT IS OURS AND IS NOT THERE:** a **published per-label cost law**. I searched their tree for a
figure of the form "lines of proof per instruction/label" and found none — ⚠️ **stated at its real
strength: I did not find one in the tree I have. I have NOT swept the literature, so "nobody publishes
this" is NOT a claim I am making here.**

### 1c.3 x86isa — DECODE. **An in-tree SDM transcription, from which dispatch is generated.**
```
  machine/inst-listing.lisp        22,042 lines   defsection opcode-maps, its own :short --
      "ACL2 representation of x86 Opcode Maps (see Intel Manuals, Vol. 2, Appendix A)"
      four maps: *pre-one-byte* · *pre-two-byte* · *pre-0F-38-three-byte* · *pre-0f-3a-three-byte*
      3,192 (INST "...") entries · 1,285 distinct mnemonic strings
  machine/dispatch-creator.lisp       503 lines   :short -- "Utilities to generate opcode dispatch
                                                  functions from the annotated opcode maps."
  machine/catalogue-base.lisp         381 lines   keep-implemented-insts / keep-unimplemented-insts,
                                                  an instruction is IMPLEMENTED iff (inst->fn i)
  machine/catalogue-data.lisp       1,127 lines   def-sdm-instruction-section, catalogued against
                                                  SDM Vol. 1 Chapter 5 section numbers
```
⛔⛔ **THE TRAP IN THIS ROW, AND IT IS WHY THE NUMBER IS NOT IN THE SCALE CELL.** `3,192` sits one
rounding away from K's `3,155 instruction variants`, **and they count different things**: K's figure is
its SEMANTICS coverage claim; x86isa's 3,192 is its DECODE TABLE, which its own tree distinguishes from
what has semantics (`inst->fn` non-nil). Goel's paper says **400+ opcodes** for the semantics.
⇒ 🔑 ***TWO NUMBERS THAT NEARLY MATCH ARE THE MOST DANGEROUS KIND, BECAUSE THE COINCIDENCE READS AS
CORROBORATION.*** Putting 3,192 beside 3,155 in a positioning table would be the single most
misleading thing this file could do, and it would look like diligence.
⇒ **THE CONTRAST THAT IS REAL:** their decode trust base is the **fidelity of a 22,042-line hand
transcription of SDM Appendix A**, checkable by reading; ours is **Intel XED**, an external library we
do not verify, named as such in `TRUSTBASE.md`. Neither is uniformly better and the paper should say
which risk it took and why.
⭐ **AND ONE THING TO STEAL:** x86isa publishes DECODED-vs-IMPLEMENTED as a first-class distinction,
catalogued by SDM section. `docs/COVERAGE.md`'s 500/525 is the same idea; their presentation is better.

### 1c.4 K x86-64 — PROOF SUPPORT. **10 programs, `kprove` + Z3, functional post-conditions.**
```
  program-veriifcation/   (sic; the README spells it program-verification)  10 directories
    add_two_numbser(sic) 1 rule   76 lines      popcnt           1 rule   76
    decrement            2 rules 206            popcnt_loop      1 rule   84
    get_sign             1 rule   95            safe_addrptr_32  1 rule   98
    magic                1 rule  123            safe_addrptr_64  1 rule   95
    sum_to_n             2 rules 204            sum_to_n_32_bit  2 rules 221
                                                            13 claim rules total
  semantics/x86-verification-lemmas.k    846 lines, 201 rules   <- their verification lemma library
  discharged by:  kprove test-spec.k ... --smt_prelude .../z3/basic.smt2     (its own README)
```
`sum_to_n/test-spec.k` claims `RAX = N*(N+1)/2` over a **loop**, with the pre/post state written as a
K reachability rule — i.e. **functional correctness, not just safety.**
📌 **Its README's own words for this directory: *"Hosts few applications of our formal semantics."***
That is the project's own scoping and the paper should quote it rather than characterise it.
⇒ **Trust base:** K's rewriting engine plus **Z3**. There is no "axiom list" to compare against ours;
the table now says so instead of leaving a cell that invites a false comparison.
⚠️ **A NOTE ON OUR OWN CHECKOUT, because it nearly cost me this cell.** `vendor/k-x86-64` is a
**partial clone** (`git remote -v` shows `[blob:none]`) containing only `semantics/`. The verification
material and the test suites live in `vendor/k-x86-64.FULL-BACKUP`, same commit `592380a`.
⇒ 🔑 ***AN ABSENCE READ FROM A PARTIAL CLONE IS A FACT ABOUT THE CLONE.*** Had I greped the working
checkout I would have recorded "K demonstrates no program proofs", which is false.

### 1c.5 Sail-x86-from-acl2 — ALL THREE CELLS, from the project's own files.
```
  model/                       63 .sail files, 2,123,049 B   (evex_opcodes_dispatch.sail alone 832,877)
  executable?   YES   validation Readme: "make x86_emulator" in model/, worked ELF example ending
                      "Steps = 10", and CO-SIMULATION AGAINST THE K FRAMEWORK SINGLE INSTRUCTION TESTS
  scope         A CONFIGURED SLICE. translator/config_patterns.py, its own header: "Mostly used to
                exclude certain forms or files in order to translate only a slice of the model,
                rather than the whole thing."  exclusions_files = ['fp-structures']  -- ONE file
                wholesale.  NO instruction count is published anywhere in the project's own docs.
  proofs        NONE, BY CONSTRUCTION.  translator/specialTokens.py:831  def tr_ignore(...)
                """There are some forms we can ignore wholesale.  E.g. `defthm`."""
                and config_patterns.py: "Only used once: in a `defthm` - we ignore `defthm`s"
                Repo top level: doc · model · test-generation-patches · translator -- no proof tree.
  repo meta     default_branch=master, pushed 2024-11-29, "Sail x86 model automatically translated
                from the ACL2 model"
```
⛔ **AND ONE MORE CELL WAS CONFLATING THEIR SYSTEM WITH OUR PLAN.** The `prover / host` cell read
*"Sail → Lean backend — RECORDED"*. The Lean backend belongs to the **Sail project** and using it is
**our P3b spike**; it is not a property of `sail-x86-from-acl2`, which has no prover and, per the
measurement above, no theorems to prove. ⇒ 🔑 ***A COMPARISON TABLE'S WORST FAILURE MODE IS PUTTING
OUR INTENTION IN THEIR COLUMN***, because it reads as a fact about them and nothing in the row marks
it as ours.

⇒ **The scope cell is now better than a number would have been:** the honest sentence is *"a
configured slice of x86isa's definitions, with its theorems excluded by design, and no coverage
figure published by the project"* — which is what a referee needs and what a guessed count would have
hidden. **Our previous parenthetical, "inherits x86isa's scope", is REFUTED as stated.**

### 1c.6 ⭐⭐ UNDEFINED BITS — FOUR SYSTEMS, FOUR DIFFERENT ANSWERS, AND THIS IS G2's SPINE
```
  x86lean   an ORACLE in the state supplying CONCRETE values  -> model stays total and executable
  x86isa    machine/register-readers-and-writers.lisp:1545
            an `undef` SEED COUNTER in the state; undef-read returns (create-undef seed) -- a FRESH
            UNIQUE unknown -- and increments it; (push-untouchable (!undef$inline)) so the only way
            to mint one is undef-read.  Doc topic: characterizing-undefined-behavior.
  K         semantics/x86-mint-wrapper.k:19  syntax MInt ::= "undefMInt"  (+8/16/32/64, undefBool)
            written STRAIGHT INTO THE FLAG:  registerInstructions/shlq_r64_one.k:18  "AF" |-> (undefMInt)
            497 of 3,064 per-instruction .k files mention undef   [POS CONTROL: 930 mention "CF"]
            DENOMINATOR DEFINED: the five dirs the K README's own directory guide names as holding
            per-instruction semantics -- registerInstructions 1147 · memoryInstructions 1474 ·
            immediateInstructions 320 · systemInstructions 122 · extras 1.  The three it does not
            name (common 14 · mmx 2 · pseudoTestInstructions 1) hold 0 undef, so 497/3,081 either way.
            SPLIT: register 161 · memory 227 · immediate 109 · system 0 · extras 0 -- undefined
            flags are a DATA-instruction phenomenon in K and absent from its system instructions.
            token census: undefMInt 1,073 · undefBool 310 · undefMInt64/32/16 4 each
  Sail      DROPPED. model/other_non_det.sail is 27 bytes: $include "./syscalls.sail"
            model/rflags_spec.sail: 10,005 B, 38 functions, ZERO undef  [the size IS the pos control]
```
⭐ **x86isa's own source documents the hazard that K's design walks into**, in `unsafe-!undef`'s
`:long`: reusing a seed *"might contaminate our 'pool of undefined values' … which would make the
result of an equality test between them equal instead of indeterminate."* K uses **one constant**, so
two undefined flags are the **same term**.
⚠️ **STATED AT ITS REAL STRENGTH: the mechanism is measured; the consequence is a HYPOTHESIS.** I have
NOT verified how `kprove` treats `undefMInt` under equality, and it may well refuse to decide it. **Do
not put the consequence in the paper until it is driven against K.** Recording it here as the next
experiment, not as a finding.
⇒ 🔑 ***THIS ROW, NOT SCALE, IS WHERE THE FOUR SYSTEMS ACTUALLY DISAGREE*** — and G2 (priced at 2–3
days, "the hardest part of x86 and the most citable") now has its comparative frame measured rather
than asserted.

### 1c.8 ⛔⛔ K DOES NOT DECODE MACHINE CODE — AND THIS CORRECTS A CELL I WROTE AN HOUR EARLIER
```
  semantics/x86-loader.k     parses GNU ASSEMBLER SOURCE: rules for .section .rodata, .data,
                             .bss, .text, .globl, .file, .comm -- it loads a .s, not an ELF
  semantics/x86-syntax.k:25  syntax Opcode          <- a SORT
                       :340  syntax Opcode ::= "adcb"   <- whose members are MNEMONIC STRINGS
  per-instruction files mentioning modrm / ModRM / REX:  0 / 0 / 0
        [POSITIVE CONTROL on the same population: 3,085 files mention 'rule']
  any file reading ELF or raw bytes:  none found
  and the program-verification specs carry instructions as TEXT, e.g.
        iloc ( mi(64,0)) |-> storedInstr ( movl %edi , -20 ( %rbp ) , .Operands )
```
⇒ **K's semantics is defined over PARSED ASSEMBLY. The decoding is done outside K, by the toolchain,
before the model sees anything.** x86isa decodes bytes from its own SDM transcription; we decode bytes
via XED; **K decodes nothing.**
⛔ **THIS CELL FIRST READ** *"decode is part of the K definition itself (`x86-fetch-execute.k`,
`x86-syntax.k`); no external decoder — RECORDED (its README's directory guide)"*. **That is wrong in
its subject and it was wrong in the flattering direction for K** — I inferred "K defines its own
decode" from a README line listing files as *"the semantics of execution environment"*, which says
nothing about bytes. ⇒ 🔑 ***A DIRECTORY LISTING TELLS YOU WHAT FILES EXIST, NEVER WHAT THEY DO*** —
and I had already recorded, in §1c.4 an hour earlier, a spec carrying `storedInstr ( movl %edi , … )`,
which is the refutation in plain sight in my own evidence.
⇒ 🔑 ***AND IT CHANGES A NUMBER'S MEANING ELSEWHERE IN THIS TABLE:*** K's *"3,155 instruction
variants"* is a count over **assembly forms**, while our `351/374 distinct machine forms` is a count
over **encodings**. They are not the same population and the paper must not subtract them.
⭐ **This is the row where our column is strongest and it is not close:** a semantics over decoded
bytes answers *"what does this binary do"*; a semantics over assembly text answers *"what does this
listing mean"*, and the gap between them is exactly where real x86 defects live.

### 1c.9 ⛔⛔ x86isa's DECODE TRUST BASE IS NOT PURELY THE SDM — AND THIS CORRECTS **BOTH** SOURCES
This campaign's own provenance verdict of 2026-09-02 — a private-lane document, cited here for its
claim only — says *"x86isa itself uses XED's tables via `xedscan.py`"*. §1c.3, written this morning, says its maps are an SDM transcription.
**Neither is right, and the truth is more interesting than either.**
```
  machine/xedscan.py   Sol Swords (Kestrel), 2024-25, its own usage text:
       "At the moment this is a small PROOF OF CONCEPT for generating inst-listing.lisp
        opcode map entries by parsing XED data files."
       and its comment: designed "to pick up the X87 instruction set which was MISSING
        from our opcode maps" -- the #xD8..#xDF escape opcodes
  inst-listing.lisp:1748  ";; X87 instruction entries (#xD8 through #xDF) generated from xed
                            datafiles using:  xedscan.py ~/work/xed/datafiles/xed-isa.txt xed-x87.txt"
  MEASURED SHARE:   186 of 3,192 INST entries = 5.8%   (the x87 escape block)
  PLUS              9 sites commented ";; Undocumented (from xed-isa.txt):"
```
⇒ **The brief over-generalised a proof-of-concept covering 8 escape opcodes into "the decoder".
§1c.3 omitted it entirely.** Both errors were in the direction of a cleaner story.
⇒ 🔑 ***AND IT DESTROYS THE TIDY CONTRAST I HAD WRITTEN.*** I had it as *"their decode trust is a
hand transcription of the SDM; ours is XED"*. **Both models reach for XED, and x86isa reaches for it
exactly where the SDM is weakest** — the x87 escape encodings the manual tables separately, and
instructions the manual does not document at all. That is a better sentence for the paper than the
clean one, and it is the one that is true.
📌 **What remains genuinely different is the SHARE and the DECLARATION**, not the presence: XED is our
decode path for everything and is named as a trust component in `TRUSTBASE.md`; for x86isa it is 5.8%
of the maps plus nine citations. ⚠️ **I have NOT checked whether x86isa states a trust position on
XED anywhere, and I am not claiming it does not.**
⇒ ⛔ **THIS IS THE SECOND DECODE CLAIM I HAVE HAD TO CORRECT TODAY** (§1c.8 was the first, about K).
Both were written from a plausible structural reading rather than from the file that decides it.
**Decode is where this table is most inviting to reason about and least safe to.**

### 1c.7 ⛔⛔ THE FINDING THAT CHANGES A CLAIM WE ALREADY MAKE: THE ORACLES ARE NOT INDEPENDENT
```
  Sail-x86-from-acl2  IS A MECHANICAL TRANSLATION OF x86isa        (the repo's own description)
  ...and it is VALIDATED BY CO-SIMULATION AGAINST K's SINGLE-INSTRUCTION TESTS  (its validation Readme)
```
⇒ 🔑 ***AGREEMENT BETWEEN OUR MODEL AND SAIL-x86 TESTS THE TRANSLATOR, NOT A SECOND SEMANTICS.*** A
differential-validation claim that counts x86isa, K and Sail as **three witnesses over-counts**: there
are **two origins** (the ACL2 model and the K definition), with Sail derived from the first and
cross-checked against the second's tests.
📌 **This does not weaken anything we have actually done** — `PROVENANCE.md` already records Sail as a
*"Spike-only third reference (plan P3b). Never the proving model"*, and no differential record to date
uses it. **It constrains what the PAPER may say**, and it is far cheaper to find now than in a
referee's report.
[[feedback-two-readings-are-not-two-witnesses]]

## 2. ✅ NOTHING IS OWED — AND THIS SECTION IS NOW **DERIVED FROM THE TABLE**, NOT REMEMBERED
```
  OWED-CELLS-NOW: 0
```
**That literal is GATED.** `scripts/check_positioning_table.py` parses §1's TABLE — never this prose —
and refuses if the count disagrees, or if any cell carries no MEASURED/RECORDED/OWED marker at all.
⛔ **The history, with the prose's claims separated from the table's facts, because they never agreed:**
```
                      the TABLE (derived)     the PROSE claimed
  2026-09-11 morning        15                      9
  after §1b                 15   (unchanged!)       5     <- §1b's fills never reached the table
  after §1c                  0                      0
```
⛔⛔ **AND THE REASON THIS SECTION IS NOW DERIVED IS THAT ITS OWN LIST WAS WRONG BY A FACTOR OF
THREE.** Until this edit it read *"**Five** OWED cells"* and then named **seven**: x86isa axiom
base · proof support · decode; K proof support; Sail scale · executability · proof support.
**Parsed mechanically, the table at `4359f6f` carried FIFTEEN:**
```
  x86isa   scale · axiom base · proof support · decode                            4
  K        executable · axiom base · proof support · undefined-bit · decode        5
  Sail     scale · executable · axiom base · proof support · undefined-bit · decode 6
                                                                          total  15
  the prose said:  "Five OWED cells"        the prose listed:  seven
```
⭐ **THE MECHANISM, AND IT IS NOT CARELESSNESS.** §1b filled four cells *"at the sources"* and wrote
the fills **into §1b's prose**, leaving the TABLE's cells reading `OWED`. §2 was then updated to agree
with **§1b**, not with the **table**. So the document had three registers — a table, a fill narrative,
and a debt list — and only the first was load-bearing.
⇒ 🔑 ***A FILL WRITTEN INTO PROSE DOES NOT REACH THE TABLE, AND THE DEBT LIST TRACKED THE PROSE.***
⇒ 🔑 ***EVERY ONE OF THE ERRORS RAN THE SAME WAY: UNDER-REPORTING THE DEBT.*** A list of what is
missing, maintained by hand beside the thing it describes, decays toward "less is missing".
⚠️ **AND MY OWN FIRST NUMBER HERE WAS ALSO WRONG.** Before parsing it I wrote **eight** into this
paragraph from inspection, and measured **fifteen**. That is the third estimate of this quantity in
this file's history and the first one derived. **The 8 was mine, this shift, while writing the
paragraph about not doing this.**
📌 Same defect the fleet map records one level up — *a map that names a repo only inside a paragraph
about something else has not listed it.* **The fix is not a more careful list; it is to stop keeping
a second list.**

⚠️ **WHAT "NOT OWED" DOES AND DOES NOT MEAN.** Every cell now carries MEASURED / RECORDED / a stated
NOT-APPLICABLE with its reason. **It does not mean every cell is a number** — three of the best cells
are deliberately not numbers (Sail's scope, K's axiom base, x86isa's decode trust), because in each
case a number would have been the misleading answer. ⇒ **G1's reading task is DONE and the table may
go in a paper.** What may NOT go in it is §1c.6's consequence about K's equality-of-undefined, which
is marked as an unrun experiment.

## 3. ⭐ THE ONE CLAIM THAT IS ALREADY DEFENSIBLE, AND IT IS NOT SCALE
On scale we are **smaller than K by construction** — 158 mnemonics against 774 in its target list —
and we should say so rather than let a referee find it.
**The defensible claim is the GATING**, and it is measured:
> every coverage number in this repository is DERIVED from two independent sources — each vector's own
> AT&T text, and each roster row's own encoding assembled by clang — and **CI fails if the prose
> disagrees with the derivation.**
⇒ 🔑 ***THE CONTRIBUTION IS NOT "MORE INSTRUCTIONS", IT IS "NO UNGATED CLAIM ABOUT WHICH
INSTRUCTIONS".*** That is checkable by a referee in one clone, and it is the axis on which this work is
actually unusual. **It is also the claim `TACAS-PRICING.md` §4 recommends building paper 1 on.**
