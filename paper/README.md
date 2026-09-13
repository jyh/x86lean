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
| 4.3 Where the Reference Model Is Not the Specification | two of three paragraphs drafted | D91, D108, D115; `docs/P2-ROSTER.md` |
| 7 Related Work | placeholder | `docs/TACAS-G6-RELATED-WORK.md` |
| everything else | placeholder | named in each placeholder |

## Owed before submission

- Every `.bib` entry re-fetched by DOI from the registrar (D214: a row labelled as fetched carried a
  title its own DOI does not return). The SDM entry needs its order number and URL.
- Which Goel work to cite for x86isa's design (D214).
- Every number moved into `docs/CLAIMS.tsv` at the submission sha, so artifact evaluation reproduces
  it with one command (G5).
