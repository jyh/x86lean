# G6 — related work, with every at-source claim RE-DRIVEN 2026-09-11

**Why this file exists.** `docs/TACAS-PRICING.md` prices G6 at 2 days and used to call it *"not
started"*. It was not: this campaign's 2026-09-02 provenance verdict (a private-lane document)
carries a ten-element prior-art table, positively tested — for each design element, the **public**
artifact that already does it. **The citations are public facts and travel; the file does not.** This
is the lane-clean re-derivation, with each claim re-driven at the source rather than transcribed.

⛔⛔ **AND THE RE-DRIVE IS THE POINT: THREE OF NINE AT-SOURCE CLAIMS DID NOT SURVIVE** (D201). The
verdicts below are this shift's, not 09-02's. **Framing-independent by construction** — it records
what exists and who did it first, which is true under any of `TACAS-PRICING.md` §2.1's three framings,
so it does not wait on the Captain's and the helm's choice.

---

## 1. THE RE-DRIVE VERDICTS
| # | claim as carried since 09-02 | verdict 2026-09-11 |
|---|---|---|
| 1 | x86isa: `x86-fetch-decode-execute` over the `x86` STOBJ with an `app-view` switch | ✅ **VERIFIED verbatim** — `machine/x86.lisp:207`; the switch's own doc in `machine/state.lisp` |
| 2 | x86isa `UNDEF`: *"Field that seeds unknown values that characterize commonly occurring undefined behavior"* | ✅ **VERIFIED verbatim** — `machine/state.lisp`, and see §3 |
| 3 | *"x86isa itself uses XED's tables via `xedscan.py`"* | ⛔ **REFUTED** — a self-described *"small proof of concept"*; **186 of 3,192** map entries (5.8%), the x87 escape block, plus 9 sites citing `xed-isa.txt` for undocumented encodings |
| 4 | *"K: an explicit list of supported vs unsupported variants"* | ⛔ **MIS-STATED** — see §2 |
| 5 | *"Sail: `Unspecified`-valued results"* | ⛔ **TERM NOT PRESENT** — 0 of 14 model files (202,493 B; positive control fires in 12). The mechanism is Sail's builtin `undefined`; see §3 |
| 6 | K: co-simulation against a real machine, per-instruction compare | ✅ **VERIFIED verbatim** — its README's *"Testing the semantics"* |
| 7 | LNSym: `cosim` conformance testing, `benchmarks` target | ✅ **VERIFIED** — its README, lines 19–20, 41, 45 |
| 8 | x86isa `proofs/` tree | ✅ **VERIFIED in detail** — 8 program families, 559 theorem forms, over a 24,707-line proof library (`TACAS-G1-POSITIONING.md` §1c.2) |
| 9 | Sail: `test-generation-patches/` + validation scripts | ✅ **VERIFIED** — repo listing and the validation guide |

⇒ 🔑 ***AN AT-SOURCE ANNOTATION NOBODY RE-DRIVES IS WRONG AT ABOUT ONE IN THREE, AND — MEASURED — THE
ERRORS WERE PRESENT AT BIRTH, NOT ACQUIRED.*** The underlying files had not changed. That is a worse
finding than staleness and a better argument for this paper, because it **cannot be answered by
re-checking more often; it requires the check to be mechanical.**

---

## 2. ⭐ CLAIM 4 IN FULL — K DERIVES ITS OWN COVERAGE AND PUBLISHES DISCLAIMED LISTS ABOUT OTHERS
```
  scripts/find_unsupported_insttructions.pl   (sic)  DERIVES unsupported instructions by scanning
        semantics/{register,immediate,memory,system}Instructions and extras
  a checked-in list of K's OWN supported variants:   NONE
        [POSITIVE CONTROL: 27,422 tracked files; the grep finds 16 other supported/unsupported files]
  docs/instruction-summary   mode 160000, a GITLINK with NO .gitmodules -- an UNREGISTERED
        submodule, empty in ANY clone.  Its emptiness is a fact about K's repo, not our checkout.
  docs/relatedwork/          checked-in supported/unsupported lists for OTHER systems:
        acl2/supportedInfo.txt (830 lines) · acl2/supportedOPcodes.txt (293 mnemonics) ·
        strata/ (12 STOKE/Strata list files)
```
⇒ **K derives its own coverage rather than declaring it** — the same discipline as our D6
(`X86.undefinedFlags` derives the undefined SET; `claimed_forms.py` derives the coverage claim).
**Worth knowing before claiming novelty: "derive, don't declare" is not ours alone.** What we add is
that **CI fails when the derivation and the prose disagree**, which is a gate rather than a practice.

⛔⛔ **AND A SOURCE THAT REFUSES ITS OWN USE AS EVIDENCE.** `docs/relatedwork/README.md`, verbatim:
> *"The statistics and results were for our internal usage and are **not updated**. Hence, the reader
> is advised **not to draw any conclusions about the status of related projects** from these results."*

**I was one step from recording its 293 as a second source for x86isa's implemented-opcode count** —
the very number this campaign refused from a web search (400+ is what Goel wrote; 413 stays
unrecorded). **293 stays unrecorded too, and for a better reason: the source says not to.**
⇒ 🔑 ***A DATASET'S OWN README CAN BE A REFUSAL, AND READING THE DATA WITHOUT READING IT IS HOW A
DISCLAIMED NUMBER ENTERS A PAPER WEARING A CITATION.***
📌 **Distinguish this from the disclaimer defect `check_readme_snapshot.py` exists for**, where a
disclaimer protected a live claim and made it *unreadable as wrong*. Here it **withdraws the artifact
from evidentiary use**. Same syntax, opposite function — and only the second is honest.

---

## 3. ⭐⭐ THE UNDEFINED-BIT LINEAGE — FOUR DESIGNS, AND CHASING CLAIM 5 CORRECTED TWO OF OUR OWN CELLS
```
  x86lean   a CONCRETE value from an ORACLE in the state; draw order and count fixed by the model
            (D5) -> total, executable, replayable from a seed, so a disagreement is bisectable
  x86isa    create-undef, an `encapsulate`d CONSTRAINED function -- NOTHING about equality is
            provable.  Its own :long: "an undefined value is different from another undefined
            value, and also all the known values."     <- design rationale, not a misuse warning
  K         ONE CONSTANT, undefMInt/undefBool, written into the flag; 497 of 3,064 per-instruction
            files
  Sail      Sail's builtin `undefined` via undef_read_logic(), plus a per-case undefined_flags
            MASK threaded through write_user_rflags
```
⚠️ **Our own table had recorded Sail as having DROPPED the mechanism and x86isa merely as "a fresh
unique unknown". Both were wrong** (`TACAS-G1-POSITIONING.md` §1c.10, D201) — found by chasing claim
5, i.e. **re-driving someone else's table corrected two cells of ours.**
📌 The Sail prelude's own comment — *"In the ACL2 model, undefined values for things like flags just
return zero"* — is about x86isa's **EXECUTION** path; the constrained function is its **LOGIC**. Both
true at different levels; **the paper must not collapse them.**

---

## 4. THE PRIOR-ART SPINE, BY DESIGN ELEMENT — what to cite, and for what
| our element | public prior art | what it establishes |
|---|---|---|
| total step function per form over one state | x86isa `x86-fetch-decode-execute`; K's rewrite rules over a configuration; Sail's generated `step`; **LNSym**'s Arm `stepi` in Lean 4 | the shape is standard; LNSym is the Lean-4 precedent specifically |
| undefined-bit oracle | x86isa's `UNDEF` seed + constrained `create-undef` (§3) | **ours is x86isa's discipline, made concrete and executable** — say so plainly |
| fidelity tier as a per-form datum | x86isa's `app-view`/`sys-view` + its machine-generated catalogue; K's derived support status (§2); Verbeek/Roessle/Bockenek (CPP 2019, PLDI 2022) over-approximative semantics | the concept is public; **the names T-exact/T-frame/T-absent are our coinage and the plan says so** |
| characterization theorem + frame predicates | **Myreen et al., FMCAD 2012** (decompilation into logic; machine-code Hoare triple with the frame rule); x86isa's read-over-write packs; seL4/AutoCorres practice; LNSym's per-instruction lemma packs | the frame discipline is decades old — cite, never claim |
| differential testing against executable models | **Dasgupta et al., PLDI 2019** (K vs STOKE and the manual, 7,000+ tests); **Heule et al., PLDI 2016** (stratified synthesis vs hardware) | our method's direct ancestors |
| hardware co-simulation | K's gdb-driven `--xstate`/`--kstate`/`--compare`; **Armstrong et al., POPL 2019** (Sail ARM vs hardware); LNSym's `cosim`; x86isa's own co-simulation | ⛔ **already theirs — we may not present it as new** |
| kernel-cost discipline | Myreen FMCAD 2012 (pre-derived per-instruction theorems so evaluation never unfolds the model); LNSym's lemma packs and `benchmarks` target | the technique is prior art; the **measured per-label cost law** is what we add |
| BitVec-native arithmetic in Lean 4 | **LNSym** — the public proof that native `BitVec` carries an ISA model | our encoding choice has a precedent, and it was chosen by measurement |
| decoder as an external trusted component | x86isa uses XED for the x87 block and undocumented encodings (§1, claim 3); Sail/Isla and LNSym trust external disassembly for tests | ⛔ **not a clean contrast: BOTH reach for XED. What differs is the SHARE and the DECLARATION** |

---

## 5. WHAT IS STILL OWED FOR A FINISHED SECTION
```
  full bibliographic records (authors, venue, year, DOI) for each paper cited above   NOT DONE
  a read of Verbeek/Roessle/Bockenek beyond the over-approximation claim              NOT DONE
  a decision on whether LNSym is RELATED WORK or PRECEDENT -- it is Arm, not x86,
     and it is the closest Lean 4 neighbour, so it is arguably both                   NOT RULED
```
⚠️ **The prose is not written and this file does not pretend otherwise.** What it removes from G6's
2 days is the *discovery* and the *verification*; what remains is bibliography and writing.
