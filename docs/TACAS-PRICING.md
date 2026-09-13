# TACAS regular track — what a 10–15 page submission needs, priced

**Routed by the helm at council close, 2026-09-11:** *"x86lean is a TACAS regular-track candidate —
price what a 10–15 submission needs, as a file"*, alongside *"two papers, semantics first, the Hoare
logic + saltbench-x86 following and citing it."* This file prices **paper 1, the semantics.**

⚠️ **THIS IS A PRICE, NOT A PLAN, AND EVERY NUMBER IN §1 IS TAKEN FROM THE TREE RATHER THAN
REMEMBERED.** Where I could not measure something I say so rather than estimating it — an unmarked
estimate in a pricing document is the defect this campaign has spent the most time correcting.

---

## 1. WHAT EXISTS TODAY, MEASURED AT `7bb57ee`

```
  QUANTITY                    AT 7bb57ee   THE DENOMINATOR, WHICH USED TO BE UNSTATED
  Lean library modules ......      12      X86/*.lean
  Tests modules .............       6      Tests/*.lean
  total .lean lines .........  18,824      X86/ + Tests/ + X86.lean + Tests.lean
                                           ** EXCLUDES Main.lean (4,390), AxiomGate, X86Native **
                                           all tracked .lean is 23,352 -- a 24% difference
  theorems + lemmas .........     616      X86/ + Tests/, lines matching
                                           ^(theorem|lemma|private theorem|protected theorem)
                                           all tracked .lean gives 618
  recorded decisions ........     200      ^## D[0-9] in docs/DECISIONS.md
  differential records ......      44      docs/DIFFERENTIAL-*.md
  design documents ..........      55      docs/*.md AT DEPTH 1 -- ** EXCLUDES docs/seals/ (4) **
                                           docs/**/*.md gives 59
```
⛔⛔ **EVERY ONE OF THESE NUMBERS IS CORRECT AT `7bb57ee`, AND UNTIL THIS EDIT NOT ONE DENOMINATOR WAS
STATED. I RE-DERIVED THEM AND GOT THREE OF SEVEN WRONG.** Reaching for the obvious command — all
tracked `.lean` files, `docs/**/*.md` — gave 23,352 / 618 / 59, and I spent several minutes believing
this file was **stale by 24%**. It is not. **I was counting a different population.**
⇒ 🔑 ***A CORRECT NUMBER WITH AN UNSTATED DENOMINATOR FAILS REPRODUCTION EXACTLY LIKE A WRONG ONE —
AND FAILS WORSE, because the author defends it and neither side can see why they disagree.***
✅ **AND THE STRUCTURAL FIX LANDED THE SAME DAY: `docs/CLAIMS.tsv`**, where every published number
carries **the command that derives it**, gated by `scripts/check_claims.py` in CI. The denominator
stops being prose beside the claim and becomes the claim's own derivation, so the two cannot drift —
there is no second register to keep in step. ⚠️ **This does NOT re-derive §1's frozen figures**: those
are a measurement AT `7bb57ee` and stay that way. The manifest carries the LIVE values, and where the
two differ (`decisions` 205 vs 200, `design_documents` 59 vs 55) it says so.
⇒ ⛔ **THIS IS A MEASURED REFUTATION OF G5's PRICE, one table down.** G5 said artifact evaluation is
*"unusually cheap here: every headline number is already CI-gated and derived, so 'reproduce the
claims' is largely 'run the gates'."* **These seven are NOT gated** — `claimed_forms.py` gates the six
COVERAGE numbers below, and nothing reads these. **An evaluator running the obvious command gets a
different answer for at least three of seven and reports that the claims do not reproduce.**
📌 **Which have MOVED since `7bb57ee`, measured at HEAD:** decisions 200 → 202 and design documents
55 → 59, both by this shift's own work; the rest are unchanged. **The movement is correct behaviour,
not decay — a measurement is a claim about its sha.** The defect was never staleness.

**Coverage, and these six numbers are GATED** — `scripts/claimed_forms.py` derives them from two
independent sources (every vector's own AT&T text, and every roster row's own encoding assembled by
clang) and **CI fails if the prose disagrees with the derivation**:
```
  158 mnemonics in 1,012 differentially tested forms
  500 of 525 roster rows      351 of 374 distinct machine forms
  375 of the 500 spelled by a vector; 125 the same encoding under another spelling
```
**Oracles on record:** `x86isa`/ACL2 (73 mentions across the differential records), XED (24). Sail and
K are cited in `PROVENANCE.md` as sources, and I have **not** verified today whether either was used
as a live oracle — that is a gap in my knowledge, not a claim either way.

**The P2 proof interface**, landed this shift (council ruling ⑧):
```
  naive (if-chain invariant, by_cases per label) ....  152 lines  ≈ 25   / label
  + stepP_at / stepP_off / atTable ..................   88        ≈ 12   / label
  + runP_code .......................................   67        ≈  9.6 / label
  + round 4 (regcalc, defeq) ........................   57        ≈  7.6 / label
  measured across FOUR routines, 2–7 labels:  19 + ~7.7 / label, constant 7.5–8.1
  ⇒ ~173 lines at twenty labels  ⛔ NOT "tens of lines"
```

---

## 2. WHAT A TACAS REGULAR-TRACK PAPER NEEDS THAT WE DO NOT HAVE

### 2.1 ⛔ A STATED, DEFENSIBLE CLAIM — and ours is currently a NEGATIVE RESULT
The P2 work answers the commission *"provable in tens of lines"* with **~173 lines at twenty labels**,
i.e. **the target is not met by a lemma library**, and the finding is that **the TIER decides it**
(frame ≈ 1 line/instruction vs labelled ≈ 7.7 lines/label — a factor of eight).
⇒ **That is a real result and it is not the result the commission asked for.** A regular-track paper
must decide which claim it is making. Three honest framings, and **I am not choosing between them —
that is the Captain's and the helm's:**
* **(a) a validated executable semantics** — the coverage table is the contribution, the proofs are
  evidence it is usable. Strongest on what is measured; least novel.
* **(b) a negative/roadmap result** — "a lemma library cannot reach tens of lines; here is the measured
  law and why a tactic or VC generator is required." Honest, and TACAS rarely rewards it alone.
* **(c) hold paper 1 until the Hoare logic exists** and make THAT the claim, with the semantics as
  infrastructure. Strongest paper, latest date.

⚖️ **RULED 2026-09-12 at council — (c), WITH §4's STAGED HEDGE.** The Captain, verbatim: *"yes (c)"*
(desk `KW` → DONE). Put to him with §2.1, §4 and §4a, including the against-myself half. **What it
means for the work:** the Hoare logic is the headline claim and belongs to the second paper; **the
semantics paper is written NOW** as a validated executable semantics, the tier law is a *section* and
not the headline, and G4 (the benchmark) moves to the second paper. The remaining gaps are therefore
**G2 · G5 · G6**, and §2.2's total is the only place their sum lives.
⛔ **READ (c)'s OWN WORDS WITH CARE:** *"hold paper 1"* holds the **claim**, not the writing. This
file's "paper 1" is the semantics paper, and it proceeds on the TACAS clock (desk `KQ`, 2026-10-15).

### 2.2 THE GAPS, PRICED
| # | gap | why a reviewer asks | price |
|---|---|---|---|
| G1 | ✅ **CLOSED 2026-09-11** — `docs/TACAS-G1-POSITIONING.md`, every cell MEASURED / RECORDED / stated NOT-APPLICABLE, **none OWED**, and the marker rule is now gated in CI (`check_positioning_table.py`). D200. | "why another x86 semantics?" is the first referee question | **priced 1–2 days; spent ~1.** ⛔ It did **not** come out where this row assumed: the data did *not* mostly exist in `COVERAGE.md` + `PROVENANCE.md` — 15 of the table's cells had to be read at the other projects' own sources. |
| G2 | **Undefined-bit / flag semantics.** ⭐ **TECHNICAL CONTENT DRAFTED 2026-09-12** — `docs/TACAS-G2-SECTION-DRAFT.md`, written from `DECISIONS.md` rather than recalled, and **framing-independent by construction**. | it is the hardest part of x86 and the most citable | ✅ **DRAFTED 2026-09-12 — priced 2–3, spent ~2, 0 remains as a gap** (§4.3's last two paragraphs landed the same day). *This cell read "~1.5 spent, ~0.5 remains" until then.* ✅ **PROSE DRAFTED 2026-09-12** in `paper/x86lean-semantics.tex` §3 and §4.3, and the prominence is ruled (a section). **Remaining:** §4.3's cost-of-a-divergence and ceiling paragraphs (the ceiling needs the live `P2-ROSTER.md` figures at a pinned sha). ⛔ **Drafting it found two false sentences in the technical content** (D213: the draw count DOES vary with operands; "only we stay executable" is false) **and one wrong bibliography title** (D214). ✅ **K's equality-of-undefined is no longer on the path:** the prose states no claim about it, so the unrun experiment is a sentence NOT written rather than a day owed. |
| G3 | ✅ **CLOSED 2026-09-12** — `docs/TACAS-G3-TIMING-CLAIMS.md`, derived by `scripts/ranking_stability.py`, five numbers gated in `CLAIMS.tsv`. D210. | "does it scale?" | **priced 1 day; spent ~1.** ⚖️ It was never a robust-estimator problem: the block I had priced was **on the wrong instrument** (the CI runner, not the developer boxes). What the paper carries is the concordance, the 25 inverting pairs, and the 111 non-inverting pairs **as an enumeration with its power** — never "stable". ⛔ Absolute wall-clock stays out on any box. |
| G4 | **The five proof problems are a sample, not a benchmark.** Four routines, 2–7 labels. | "is 19 + 7.7/label general?" | **unpriced — needs the benchmark freeze** (helm item 4, P2 in the design lane, with bench). |
| G5 | **No artifact-evaluation packaging.** TACAS AE wants a container that builds and reproduces every claim. | AE badge is near-mandatory | ⛔ **RE-PRICED 2026-09-11 → 3–4 days.** The old cell said *"unusually cheap … every headline number is already CI-gated"*. **Measured (§1): the seven §1 numbers are NOT gated, and three of seven do not reproduce under the obvious command because their denominators were unstated.** The six COVERAGE numbers *are* gated and that half of the claim holds. **AE work is therefore not "run the gates" — it is "state every denominator, then run the gates."** ✅ **The denominators are now stated MACHINE-READABLY in `docs/CLAIMS.tsv`, which is this gap's spine: "reproduce every claim" becomes one command, and a reviewer reads each derivation instead of trusting it.**  ⭐ **SCOPED 2026-09-12 → `docs/TACAS-G5-ARTIFACT.md`.** ⛔ **Its first finding is the largest AE hole: the reference model's revision is neither pinned by `setup_oracle.sh` nor recorded in any differential record.** Price unchanged until the AE call is read. |
| G6 | **Related work.** ⚠️ **NOT "not started" — a 10-element PRIOR-ART TABLE already exists** (this campaign's 2026-09-02 provenance verdict, a private-lane document), with named public prior art per design element and an evidence class on each: Myreen FMCAD 2012 · Dasgupta PLDI 2019 · Heule PLDI 2016 · Armstrong POPL 2019 · Verbeek/Roessle/Bockenek CPP 2019 + PLDI 2022 · LNSym · seL4/AutoCorres. | required | ✅ **RE-DRIVEN AND TRANSPLANTED 2026-09-11 → `docs/TACAS-G6-RELATED-WORK.md`** (D201). **Discovery and verification are now SPENT; what remains is bibliography and prose.** ~~Still ~2 days~~ ⚖️ **RE-PRICED 2026-09-12 → ~1:** the two paragraphs resting on measured cells are PROSE in `paper/x86lean-semantics.tex` §7, and every DOI record was fetched per entry (which found **3 of 8 rows wrong**, D214). **Left:** the Myreen record (needs a browser), a read of Roessle/Verbeek beyond the over-approximation claim, and the frame-discipline sentences. |
| G7 | ⛔ **THE SECTIONS NOBODY PRICED — ADDED 2026-09-12.** G1–G6 price what the paper LACKS; the prose of what it HAS was in no addend: the abstract, §1 introduction, §2 the model, §4.1–4.2 the harness and the two origins, §5 gated claims, §6 proofs, §8 conclusion — **about nine LNCS pages**, counted from the draft's placeholders. | a paper is its prose | ⚠️ **ESTIMATED, NOT MEASURED — 3–4 days.** Basis, stated so it can be argued with: on 2026-09-12 about five drafted pages took one session, and **verifying them against the source found five false or overstated sentences** (D213 ×2, D214 ×3), so the price is dominated by re-driving claims, not by typing. ⇒ It re-prices the TOTAL **upward**, against this file's recorded bias: every earlier error here under-reported the debt. |

**Sum of what is priceable — SHOWN AS ITS PARTS, so it can be checked in place rather than trusted:**
```
  BEFORE OCT 15:  G6 1 · G7 1 (ESTIMATED) · data statement ~0.25 (ESTIMATED)  ⇒  ~2.25 working days
  AFTER, IF AE:   G5 3-4, due 2027-01-11 (§3a: voluntary, after notification)
      (re-sequenced 09-12 by reading the call, §3a; the total below this line is superseded)
  G2  0     G5  3-4   G6  1   G7  1 (ESTIMATED)     ⇒  REMAINING: 5-6 working days
      (G2 and G7 re-priced 09-12, same session: every section of paper/x86lean-semantics.tex is now
       DRAFTED except §7's read-dependent sentences; G7 keeps ~1 for citing §6's line counts to the
       manifest and a full revision pass. ⚠️ G7's 3-4 estimate was retired within the session that
       set it -- the drafting took one sitting, and overclaims were narrowed against their sources
       before landing in §2, §5, §6 and the summary sections (commit messages c8adecd, 0f82b21,
       acbf246, d33fba8 name each; §4.1-4.2 in 7a765ae had none). The estimate's stated basis, "the
       price is verification", held and its size did not.)
       [this note first read "every section it drafted carried at least one overclaim" -- written
        from inspection, and 7a765ae is the counterexample]
      (G7 ADDED 09-12: the prose of the sections that are not gaps was in no addend)
      (G6 re-priced 2 -> 1 on 09-12: two paragraphs drafted, every DOI fetched)
      (G2 re-priced 1-2 -> 0.5 on 09-12: prose drafted, prominence ruled, two paragraphs left)
      (G2 re-priced 2-3 -> 1-2 earlier: the technical content was drafted)
      G1 SPENT (~1) · G3 SPENT (~1) · G4 unpriceable until the benchmark exists
                                             (G5 re-priced 2-3 -> 3-4 by §1's measurement;
                                              G3 closed 09-12, so it leaves the addends)
  G1  SPENT (priced 1-2, took ~1)          G4  unpriceable until the benchmark exists
```
⛔⛔ **THIS TOTAL WAS WRONG TWICE AND THE SECOND TIME WAS MINE, TODAY, IN THE SAME SHIFT AS §2.**
It read *"8–13 working days"*: the parts were G1 1–2 · G2 2–3 · G3 1 · G5 2–3 · G6 2, which sum to
**8–11**, so the maximum overstated by two days. Then I closed G1 and wrote *"leaving 7–11"* — by
**subtracting G1 from the wrong total instead of re-deriving from the parts**, which carried the bad
maximum forward and added a bad minimum.
⇒ 🔑 ***A TOTAL EDITED BY SUBTRACTION INHERITS EVERY ERROR IN THE TOTAL IT WAS EDITED FROM.*** The
parts were correct and present, three lines above, the whole time.
⇒ **Third instance today of one defect** — §2's debt list, §2.4's nine-day-old at-source annotation,
and this. **All three were hand-maintained summaries sitting beside the data that contradicted them,
and all three were edited rather than re-derived.** That is why the sum is now printed as its parts.
✅ **AND THE PARTS FORM PAID FOR ITSELF WITHIN THE HOUR:** G5 was re-priced 2–3 → 3–4 by §1's
measurement, and because the total sits beside its addends the stale sum was **impossible to miss and
trivial to re-derive**. In its old form it would have read `7–9` indefinitely and nobody would have
had the parts to check it against.

### 2.3 ⛔⛔ TWO THINGS G1 FOUND THAT CHANGE WHAT THIS PAPER MAY CLAIM (D200)
**(a) THE ORACLES ARE NOT THREE INDEPENDENT WITNESSES — THEY ARE TWO ORIGINS.**
`sail-x86-from-acl2` is, in its own repository's words, a model *"automatically translated from the
ACL2 model"*, and its validation guide **co-simulates it against K's single-instruction tests**.
⇒ 🔑 ***AGREEMENT WITH SAIL-x86 TESTS THE TRANSLATOR, NOT A SECOND SEMANTICS.*** Nothing built is
affected — `PROVENANCE.md` already scopes Sail to a P3b spike and no differential record uses it —
but **a validation claim in this paper may not count three.**
**(b) ON PROOF SUPPORT WE LOSE TOO, AND IT IS NOT CLOSE.** x86isa's `copyData-is-correct` is full
functional correctness *plus* fault-freedom for a loop of **unbounded** length; K proves functional
post-conditions over loops for 10 programs via `kprove` + Z3. Our 7 memory-safety theorems over 4
routines are **a weaker claim over a smaller sample.**
⇒ **§4's recommendation is unchanged and is now better supported, not worse.** The paper's claim was
never "more instructions" or "harder theorems" — it is that **no claim in the repository is ungated**.
G1 measured the two axes on which we lose and the one on which nothing else in this space competes,
which is exactly what makes the honest version defensible. ⭐ **And `TACAS-G1-POSITIONING.md` §1c.6 handed G2 its frame:**
the four systems make four *different* choices about undefined bits, and x86isa's own source documents
the hazard K's choice walks into. That is the most citable row in the table and it is now measured.

### 2.4 ⛔ G6's MATERIAL EXISTS AND THAT IS NOT THE SAME AS G6 BEING CHEAPER
The provenance verdict's kill-check (2) table covers ten design elements — total step function,
the undefined-bit oracle, fidelity tiers, characterization theorems + frame predicates, differential
testing, hardware co-simulation, oracle nonvacuity, kernel-cost discipline, the arithmetic encoding
choice, and the external decoder — each with **public** prior art and an evidence class
(VERIFIED-AT-SOURCE vs LITERATURE). That is most of a related-work section's skeleton.
✅ **THE TABLE HAS NOW BEEN RE-DRIVEN IN FULL. THREE OF ITS NINE AT-SOURCE CLAIMS DO NOT SURVIVE.**
```
  1  x86isa x86-fetch-decode-execute over the x86 STOBJ, app-view switch   VERIFIED verbatim
  2  x86isa UNDEF "seeds unknown values ... undefined behavior"            VERIFIED verbatim
  3  "x86isa itself uses XED's tables via xedscan.py"                      REFUTED -- a self-
       described PROOF OF CONCEPT; 186 of 3,192 entries (5.8%), the x87 escape block
  4  "K: an explicit list of supported vs unsupported variants"            MIS-STATED -- K has a
       DERIVATION SCRIPT for its own support and NO checked-in list of it.  Its checked-in
       supported/unsupported lists are about OTHER systems, and that folder's own README says they
       are "not updated" and "the reader is advised not to draw any conclusions" from them.
  5  "Sail: `Unspecified`-valued results"                                  TERM NOT PRESENT -- 0 of
       14 model files read (202,493 B; positive control fires in 12).  The real mechanism is Sail's
       builtin `undefined` via undef_read_logic(), plus a per-case undefined_flags MASK.
  6  K README's co-simulation-against-a-real-machine passage               VERIFIED verbatim
  7  LNSym `cosim` conformance testing + `benchmarks` target               VERIFIED (README 19-20,41,45)
  8  x86isa proofs/ tree                                                   VERIFIED in detail
  9  Sail test-generation-patches/ + validation scripts                    VERIFIED (repo listing)
```
⭐ **CLAIM 5's FAILURE PAID FOR ITSELF: it is what found the error in our OWN undefined-bit row**
(`TACAS-G1-POSITIONING.md` §1c.10) — I had recorded Sail as having *dropped* the mechanism, and it
has not. **Re-driving someone else's table corrected two cells of mine.**
📌 **The evidence-class column earned its keep:** all three failures sit in rows the verdict itself
marked VERIFIED-AT-SOURCE, which is where a re-drive should look first. **A table without such a
column cannot be audited at all.**

⛔ **TWO REASONS THE PRICE STAYS AT 2 DAYS ANYWAY, AND BOTH ARE NOW MEASURED:**
1. **THREE OF NINE AT-SOURCE CLAIMS DID NOT SURVIVE (above).** ⇒ 🔑 ***A VERIFIED-AT-SOURCE
   ANNOTATION IS A CLAIM ABOUT THE DAY IT WAS TAKEN — and, measured, about one in three was not true
   on that day either.*** The table must be re-driven, not transcribed.
2. **IT IS A PRIVATE-LANE DOCUMENT AND THIS REPOSITORY IS PUBLIC.** The *citations* are public
   facts and flow freely; the *file* does not get copied across. The section is re-derived here
   against the sources, which is what item 1 requires anyway.
   📌 **This paragraph was itself caught by the gate one draft ago** — it named the private document
   by its repo-relative PATH, `check_private_paths --tree` and `--history` both fired, and the commit
   was amended rather than baselined because it was not yet pushed. ⛔ **The bare NAME, which the
   path-matching gate cannot see, had to be removed by hand afterwards.** ⇒ 🔑 ***A GATE THAT MATCHES
   PATHS DOES NOT MATCH NAMES, AND THE LANE RULE IS ABOUT REFERENCE, NOT SYNTAX.***
📌 **What DOES change:** G6 is no longer a blank page, and its hardest part — *"which public work
already does each thing we do"*, answered POSITIVELY per element — is already thought through. The
2 days is now verification and writing rather than discovery.

---

## 3. ⛔ ONE THING THAT MUST BE FIXED BEFORE ANY TIMING CLAIM IS PUBLISHED
The delta gate's dispersion estimate is **not robust to outliers**, measured this shift across seven
runs (four null pairs on the runner, three real ones locally):
```
  the MEDIAN is stable ......... local family 1.06x across independent runs
  the BAND is not .............. 326 – 1739 on the runner (5.3x) at identical load
  per-pass, one run ............ Tests.Coverage  min 26,800 / median 27,150 / max 73,500
```
**Five of six passes are tight; one or two explode.** ⇒ **Any per-module timing figure published from
this gate would carry an error bar driven by outlier passes rather than by measurement uncertainty.**
📌 The remedy is a robust estimator; D150 already measured a candidate (median |consecutive
difference|) giving 0.29 where CV gave 0.73. **It is gate design and therefore the helm's, not mine
to take** — but it is on the critical path of G3, so it is priced here as a **blocker, not a task.**

---

## 3a. ⭐⭐ THE CALL, READ AT ITS SOURCE — 2026-09-12, AND IT RE-SEQUENCES EVERYTHING BELOW

**Read verbatim** at `etaps.org/2027/cfp/` and `etaps.org/2027/conferences/tacas/` (HTTP 200, both
fetched and grepped for the quoted phrases; not recalled, not taken from a summariser's paraphrase).
```
  deadline        "Submission deadline for ESOP-round 2, iFS, FoSSaCS, TACAS: Thursday, October 15, 2026"
  length          "TACAS: regular research papers, case study papers, and regular tool papers of max 18 pp"
                  "All page limits are given excluding the bibliography"
  format          "use the llncs.cls class"
  data statement  "Data availability statement in proceedings papers is mandatory ... placed just before
                   the references and does not count into the page limit"
  blind           "double-blind reviewing (in the case of TACAS and iFS, only for regular research papers).
                   Authors are asked to omit their names and institutions; refer to prior work in the third
                   person ... If authors do not obey the double-blind submission policy ... this may result
                   in a desk rejection"
  AE              research papers: "not mandatory but strongly encouraged"; case-study papers: "currently
                  not mandatory"; "Artifact submission deadline ... TACAS voluntary artifacts: Monday,
                  January 11, 2027" -- AFTER "Paper notification ... Tuesday, December 22, 2026"
  arXiv           "we strongly encourage authors to not put the work on arXiv (or similar repos) around 2 weeks
                   before and after the submission deadline"
  research paper  "identify and justify a principled advance to the theoretical foundations for the
                   construction and analysis of systems"
  case study      "the application of techniques developed by the community to a single problem or a set of
                   problems of practical importance"
```
### ⇒ WHAT CHANGES
1. ⛔ **G5 LEAVES THE CRITICAL PATH.** Artifact evaluation is voluntary and its deadline is 2027-01-11,
   after notification. What the Oct-15 submission needs from G5 is the **data availability statement**
   (small) — not the container. `docs/TACAS-G5-ARTIFACT.md` §1 (pin the reference model) stays owed,
   because the statement must name what a reader can reproduce.
2. ⚖️ **THE CATEGORY IS A FORK, AND IT IS THE CAPTAIN'S (desk `JU`: "the Captain (venue)").**
   * **(R) regular research paper** — double-blind. The draft's *"checkable in one clone of a public
     repository"* cannot be said with the URL; the author, `\institute`, every self-citation and the
     artifact link need anonymizing (an anonymized mirror). And the category asks for *"a principled
     advance to the theoretical foundations"*, which §4a already judged this paper is not.
   * **(C) case-study paper** — not double-blind; *"the application of techniques developed by the
     community to … a set of problems of practical importance"* is what §4a says the paper IS: known
     techniques (differential testing, derived claims) applied to building an x86-64 semantics, with the
     measured negative results as the evidence.
   * ⚖️ **RECOMMENDATION: (C)**, and the draft proceeds on it — no anonymization work is done. **Against
     myself:** a case-study paper may be read as the weaker category, and (R)'s bar is where §4a's
     "does it read thin" risk lives either way. A later (R) ruling costs the anonymization pass (~0.5 day,
     ESTIMATED) and nothing already written.
3. ⛔ **THE arXiv-FIRST RULE HAS A WINDOW** (desk `JU`: *"Datable-first to arXiv"*). TACAS asks for no
   arXiv posting ~2 weeks either side of Oct 15 ⇒ **post before ~Oct 1 or after ~Oct 29.** Stated here so
   nobody discovers it on Oct 10.
4. 📐 **LENGTH:** the draft is 12 pp including bibliography and placeholders, against 18 pp excluding it.

## 4. RECOMMENDATION — MINE; **RULED (c) BY THE CAPTAIN 2026-09-12** (§2.1)
**(c) with a staged hedge.** Write paper 1 as the validated semantics **now** (G2 + G5 + G6 + G7; **§2.2 prints
their parts and is the only place the total lives** — *this parenthesis carried its own figure, "6–8
days", until 2026-09-12, and it went stale the same hour G2 was re-priced: the second register this
section's own note below warns about, one paragraph above that note*) and let the measured tier law stand as a *section*, not as the paper's claim.
It is publishable on the coverage and the gating discipline alone, and it is the paper the second one
must cite.
⚠️ **THAT SENTENCE WAS WRITTEN BEFORE G1 MEASURED THE NEIGHBOURS. §4a RE-ANSWERS IT AND KEEPS IT —
with the confidence lowered and the reason stated.**
⛔ **The thing I would NOT do is submit the tier law as the headline before the benchmark exists** —
four routines is a sample, and a referee will say so correctly.
📌 **Precedence is now THIRD** (SaltBench · twin primes · x86lean · verso · jas), so the remaining
paper work runs alongside the benchmark freeze that is P2 in the design lane.
⛔ *This sentence said **"8–13 days"** until 2026-09-11 — the ORIGINAL total, never updated when G1
closed, when the sum was corrected to 8–11, or when G5 was re-priced. **The fourth instance in one
day of a number restated in prose away from its parts.** It now names no figure at all: §2.2 prints
the parts and is the only place a total belongs. ⇒ 🔑 **PRINTING THE PARTS FIXES THE PLACE YOU PRINT
THEM; A PROSE RESTATEMENT ELSEWHERE IS STILL A SECOND REGISTER.***

## 4a. ⭐⭐ "DOES IT READ THIN ALONE?" — THE JUDGMENT DESK ROW `KQ` ASSIGNS TO ME, RE-ANSWERED AFTER G1

`KQ` asks paris to say *"whether it reads thin alone."* §4 answered **no** before G1 measured
anything about the neighbours. G1 now has, and **it went against us on both of the axes a referee
reaches for first.** So the judgment is re-taken rather than left standing on a superseded premise.

### THE SCOREBOARD, MEASURED, NOT REMEMBERED
```
                        x86lean        the strongest neighbour on that axis
  instruction scale     158 mnemonics  K: 774            ⇒ WE ARE THIRD OF THREE
  proof strength        7 memory-safety thms / 4 routines
                                       x86isa: full functional correctness + fault-freedom
                                       for an UNBOUNDED loop; a 24,707-line proof library
                                       K: functional post-conditions over loops, 10 programs
                                                         ⇒ WE ARE THIRD OF THREE
  decode                bytes, via XED, trust NAMED in TRUSTBASE.md
                                       x86isa: bytes, SDM transcription + 5.8% XED
                                       K: DOES NOT DECODE BYTES AT ALL   ⇒ we are second of three
  claim gating          every coverage number derived from TWO independent sources, CI failing
                        if the prose disagrees; the undefined SET derived not declared; a
                        REFUSAL stated as a theorem       ⇒ NOTHING ELSE IN THE TABLE DOES THIS
```

### ⚖️ THE ANSWER, AND IT IS NOT THE COMFORTABLE ONE
**It reads thin as a SEMANTICS paper. It does not read thin as a "how do you know your semantics is
right" paper.** Those are different submissions and only the second one is ours to write.
⇒ **A referee opening this as "another x86 semantics" finds a model smaller than K and weaker on
proofs than x86isa, and is right to.** The scale and proof-strength paragraphs cannot be the setup —
they have to be the *concession*, made early and in our own words, or the paper is arguing from a
position a reader has already refuted.
⇒ **The contribution that survives contact with the table is the GATING**, and it survives because it
is the one axis where the neighbours' own sources show nobody competing — not because it is grander.

### ⛔ AND THE PART AGAINST MYSELF, BECAUSE §4 IS MINE AND I AM RE-CONFIRMING IT
**The gating discipline is not novel IN KIND.** Deriving a claim from two sources and failing CI on
disagreement is ordinary software engineering. What is unusual is applying it to a formal semantics'
**coverage claims**, and being able to hand a referee a clone in which the gate runs.
⚠️ **Whether that clears a TACAS regular-track bar is genuinely uncertain, and I am not going to talk
myself past it.** The honest risk is a referee reading "they CI-gated their README" as hygiene rather
than contribution. ⇒ **The mitigation is not rhetoric, it is the NEGATIVE result**, and §2.4 has
now sharpened it into a number: re-driving this campaign's own nine-day-old prior-art table found
**three of its nine VERIFIED-AT-SOURCE claims do not survive**, and this repository's own debt list
under-reported by a factor of three. That is an argument from data rather than from principle.
⚠️ **AND THE MECHANISM IS NOT THE ONE I FIRST WROTE HERE.** This sentence said such claims *"rot on a
timescale of days"*. **They do not: the underlying files had not changed, so the errors were present
at birth.** ⇒ ***UNGATED CLAIMS ABOUT FORMAL ARTIFACTS ARE WRONG AT ABOUT ONE IN THREE THE DAY THEY
ARE WRITTEN.*** That is a **worse** finding than rot and a **better** argument for the paper, because
it cannot be answered with "re-check more often" — it requires the check to be mechanical.
📌 **What would make it unambiguously not thin is the Hoare logic** — which is paper 2 and is
correctly sequenced there. **§4's recommendation stands; my confidence in it is lower than when I
wrote it, and the reason is that I now know what we are standing next to.**
⇒ 🔑 ***A "DOES IT READ THIN" JUDGMENT TAKEN BEFORE MEASURING THE NEIGHBOURS IS A JUDGMENT ABOUT
YOUR OWN TREE, AND THAT IS NOT THE QUESTION.***

⛔ **CORRECTION TO THIS FILE, SAME DAY, AND IT WAS MINE.** This paragraph first read: *"those two are
the same critical path, since G4 depends on the benchmark — an argument for doing the benchmark first
and the paper around it, not beside it."* **That contradicts §4 of this very file**, which recommends
writing the semantics paper now with the tier law as a SECTION rather than the headline.
⇒ 🔑 ***G4 IS A BLOCKER ONLY UNDER THE FRAMING I ARGUED AGAINST.*** If the paper's claim is the
validated semantics, "four routines is a sample" is a limitation of a section, not a gap in the
contribution — and the benchmark belongs to **paper 2**, the Hoare logic, exactly as desk row `KQ`
splits it: *"the semantics paper … is written from what is built; the Hoare logic proved sound over
x86lean + the saltbench-x86 task family is the follow-on."*
✅ **So `KQ`'s default is right and my sequencing note was wrong:** the semantics paper proceeds on the
TACAS clock **independently** of the benchmark. I had posted the opposite to the helm twice before
re-reading the row.
📌 And the freeze is not mine to start unilaterally in any case — `KQ` gates it on **P1's brownfield
task shape landing** (evidence's, carried dark), and it *"never blocks a P1 run."*
