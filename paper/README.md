# paper/ — the x86lean semantics paper (draft)

`x86lean-semantics.tex` is the draft of the semantics paper (LNCS format, TACAS 2027
case-study track, ruled 2026-09-13). Its framing was ruled on 2026-09-12 and is recorded in `docs/TACAS-PRICING.md` §2.1:
a validated executable semantics, with the Hoare logic left to a second paper.

Every number, and every claim about another system, carries a `\src{...}` comment naming the file in
this repository it was taken from. The macro expands to nothing in the PDF, so the sources travel with
the text and never print.

Build:

```
cd paper && tectonic x86lean-semantics.tex
```

The PDF is a build product and is not tracked.

## Status

| section | state | register it is written from |
|---|---|---|
| 2 The Model | drafted | `X86/State.lean`, `X86/Coverage.lean`, `TRUSTBASE.md`, `docs/COVERAGE.md` |
| 3 The Semantics by Example | drafted 2026-10-02 on his read ("we owe at least some representative examples"); nine listings, each GENERATED from its source by `scripts/check_listings.py` and gated in CI; listings chosen by paris | `X86/State.lean`, `X86/Semantics.lean`, `X86/Flags.lean`, `X86/Theorems.lean`, `Tests/Program.lean` |
| 4 Undefined Behaviour (was 3) | drafted | `docs/TACAS-G2-SECTION-DRAFT.md`, `docs/DECISIONS.md` D5 D6 D20 D52 D213 D226 |
| 4.3 Where the Reference Model Is Not the Specification | drafted | D91, D108, D115; `docs/P2-ROSTER.md` |
| 5 Gated Claims | drafted | `scripts/claimed_forms.py`, `docs/CLAIMS.tsv`, D201 D202 D213 D214 |
| 6 Proofs Over the Semantics | drafted; the six proof sizes are cited to the manifest (D217), and since D234 the label counts and the fitted law too. *This cell read "the label counts and the fitted law are not" until 2026-09-13 (D235).* | `docs/P2-PROOF-INTERFACE.md`, `X86/Program.lean`, `Tests/Program.lean` |
| 7 Related Work | drafted; the last placeholder was replaced 2026-09-12 after reading the cited papers (D222, D223). *This cell read "two paragraphs drafted; the frame-discipline and lifted-semantics sentences wait on their reads" until 2026-09-13.* ⚠️ The lifted-semantics sentences rested on ABSTRACTS until 2026-09-14, when both papers were read at the authors' PDFs and three sentences changed (D246). | `docs/TACAS-G1-POSITIONING.md`, `docs/TACAS-G6-RELATED-WORK.md`, D222 D223 D246 |
| 4.1 The Harness · 4.2 Two Origins | drafted | `Main.lean` comparator; `docs/DIFFERENTIAL-P2-BATCH22.md`; `docs/TACAS-G1-POSITIONING.md` 1c.7 |
| Abstract · 1 Introduction · 8 Conclusion | drafted, from the sections; no new figures | the sections they summarise |
| remaining placeholders | none — §7's last was replaced 2026-09-12 (D223). *This cell read "§7's read-dependent sentences" until 2026-09-13 (D235), against the §7 cell above it.* | — |

## arXiv (council 2026-10-02)

The paper is posted to arXiv (cs.SE) as a SaltBench paper, as soon as it has had its reads, ahead of
any TACAS decision. That is inside the window in which the TACAS call asks authors not to post
(two weeks either side of 2026-10-15); the case-study track is not double-blind, and whether the paper
still goes to TACAS, with the preprint declared, was the author's decision. ⚖️ **Decided 2026-10-02:
post the preprint now, and submit to TACAS on 2026-10-15 as well, declaring the preprint** (his words: "I think
we should go ahead and post now" and "we stay with TACAS"), against the call's "we strongly encourage authors to
not put the work on arXiv (or similar repos) around 2 weeks before and after the submission deadline". The arXiv upload is the
`.tex`, the `.bbl` that the build produces, and `llncs.cls`; arXiv compiles with pdflatex, so read its
compiler log before announcing.

## The call (read 2026-09-12, `docs/TACAS-PRICING.md` §3a)

Deadline **2026-10-15**; **18 pp excluding bibliography**, llncs; a **data availability statement is
mandatory** (drafted on the case-study arm; it names acl2@c8897a34, pinned by D218). ⚖️ The category is **ruled: case-study** (not double-blind; council 2026-09-13, `docs/TACAS-PRICING.md` §3a),
so the draft does no anonymization. *(This read "is the Captain's; the draft proceeds on the recommendation" until 2026-09-15.)* No arXiv posting ~2 weeks either side of the deadline.

## Owed before submission

- **The preprint declaration (decided 2026-10-02).** The TACAS submission names the arXiv preprint by its
  identifier, says it was posted inside the call's two-week window by the author's choice, and notes that the
  case-study track is not double-blind, so the preprint reveals nothing a reviewer would not see. The
  identifier goes here once arXiv announces it.

- Every `.bib` entry fetched by DOI from the registrar, never copied from G6 (D214: 3 of G6's 8 rows
  disagreed with their own DOI's record). Done for every DOI entry in the file on 2026-09-12. ✅ The SDM
  entry carries its order number (325462-092US, read on the PDF's cover) and URL since 2026-09-13 (D236); the
  Myreen FMCAD 2012 record was taken from the author's page and bibtex (D222). ✅ **Re-read 2026-09-15 (D249)** against Crossref and
  each paper's own footer: Goel is cited as its EPTCS 249 publication, the two PACMPL entries carry their article numbers
  (Armstrong's "1--31" did not locate the article; libLISA's "333--361" was Crossref issue pagination absent from the PDF), and
  the four repository entries carry sort keys. ✅ **The TACAS 2007 LNCS volume is 4424 (D301)**, read from the Library of Congress MARC record (LCCN 2007922076, field 830), because Crossref carries no volume for the chapter or the book DOI and Springer's page is behind a bot check. *This item read "the TACAS 2007 LNCS volume is still unverified" until 2026-09-25.* *This item read "the SDM entry
  needs its order number and URL; the Myreen FMCAD 2012 record needs a browser" until 2026-09-13.*
- ✅ **CLOSED 2026-09-13 (D237): which Goel work to cite for x86isa's design (D214).** Keep the arXiv note
  (`goel-x86isa`, read; cited since D249 as its EPTCS 249 publication, the same text) + `x86isa-repo`; cite NEITHER the dissertation NOR the Springer chapter, both UNREAD.
  **The question dissolved rather than being decided:** §3's undefined-bit table says *"Each row was read at the
  project's own source"*, and x86isa's row cites `create-undef`, `encapsulate` and the seed counter — source-level
  facts in a BSD-3 repo we hold. §2 merely NAMES the model. So no §2/§3 claim ever rested on a Goel text.
  ⚠️ Reopens only if the draft adds a claim about x86isa's design RATIONALE (why, not what) — source code is
  silent on why. Read routes measured, not assumed: Springer `10.1007/978-3-319-48628-4_8` is paywalled
  (Crossref confirms the record; TDM licence only); the UT dissertation is unreachable because **the whole UT
  Austin estate 403s this box** — a fact about our network, not about the work's availability.
- ✅ **Figures written as words were censused 2026-09-25 (D302):** 195 number words, five measured figures given rows; the rest are
  constants, the text's own structure, or quotations.
- Every number moved into `docs/CLAIMS.tsv` at the submission sha, so artifact evaluation reproduces
  it with one command (G5). §4.3's ceiling and packed-shift figures are there now (pinned `d7dbd58`). *The packed-shift record rows read
  `p2_batch13_*` and cited a different batch's record until 2026-09-15 (D249); the file number and the batch number are two counters.*
- ✅ A number in the `.tex` IS checked against the row its `\src` cites, when it cites one:
  write `docs/CLAIMS.tsv[id, id]` inside the marker, and `scripts/check_claims.py` (in CI) requires
  each cited value in the prose since the previous marker (D216). ⚠️ A number with no such citation
  is NOT checked. Before submission, every number in the paper should carry one. ✅ **Censused 2026-09-25 (D301):** of 122 digit-numbers in the prose, the six measured ones that had no row now have one; the 27 left are constants, versions and quotations. ⚠️ Numbers written as words were not censused.
