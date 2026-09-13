# paper/ — the x86lean semantics paper (draft)

`x86lean-semantics.tex` is the draft of the semantics paper (LNCS format, aimed at the TACAS 2027
regular track). Its framing was ruled on 2026-09-12 and is recorded in `docs/TACAS-PRICING.md` §2.1:
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
| 3 Undefined Behaviour | drafted | `docs/TACAS-G2-SECTION-DRAFT.md`, `docs/DECISIONS.md` D5 D6 D20 D52 D213 |
| 4.3 Where the Reference Model Is Not the Specification | drafted | D91, D108, D115; `docs/P2-ROSTER.md` |
| 5 Gated Claims | drafted; its last sentence waits on the paper-vs-manifest check | `scripts/claimed_forms.py`, `docs/CLAIMS.tsv`, D201 D202 D213 D214 |
| 7 Related Work | two paragraphs drafted; the frame-discipline and lifted-semantics sentences wait on their reads | `docs/TACAS-G1-POSITIONING.md`, `docs/TACAS-G6-RELATED-WORK.md` |
| 4.1 The Harness · 4.2 Two Origins | drafted | `Main.lean` comparator; `docs/DIFFERENTIAL-P2-BATCH22.md`; `docs/TACAS-G1-POSITIONING.md` 1c.7 |
| everything else | placeholder | named in each placeholder |

## Owed before submission

- Every `.bib` entry fetched by DOI from the registrar, never copied from G6 (D214: 3 of G6's 8 rows
  disagreed with their own DOI's record). Done for every DOI entry in the file on 2026-09-12. The SDM
  entry needs its order number and URL; the Myreen FMCAD 2012 record needs a browser.
- Which Goel work to cite for x86isa's design (D214).
- Every number moved into `docs/CLAIMS.tsv` at the submission sha, so artifact evaluation reproduces
  it with one command (G5). §4.3's ceiling and batch-13 figures are there now (pinned `d7dbd58`).
- ⚠️ Nothing yet checks that a number in the `.tex` equals the `CLAIMS.tsv` row its `\src` names: the
  rows are gated against the repository, and the prose is not gated against the rows.
