# paper/ — the arXiv package for the semantics paper

This branch carries the paper as submitted to TACAS 2027 (tag `tacas27-submission`, commit `e66e24a`)
packaged for arXiv. The text is unchanged: `x86lean-semantics.tex` and `x86lean-semantics.bib` are
byte-identical to `e66e24a`. The one added build input is `x86lean-semantics.bbl`, because arXiv does not
run BibTeX when a `.bbl` is present.

## What is uploaded

Two files, at the top level of the archive:

```
x86lean-semantics.tex
x86lean-semantics.bbl
```

Build the archive from this directory:

```
tar -czf x86lean-arxiv.tar.gz x86lean-semantics.tex x86lean-semantics.bbl
```

The class (`llncs.cls`), the style that produced the `.bbl` (`splncs04.bst`) and every package the tex
loads (`fontenc`, `lmodern`, `booktabs`, `array`, `amsmath`, `url`, `hyperref`, `microtype`, `alltt`) are
in TeX Live, so none is shipped. The source is 7-bit ASCII and has no `\input`, `\include` or
`\includegraphics`.

## How the `.bbl` was made, and how to check the package

With pdfTeX 3.141592653-2.6-1.40.29 and BibTeX 0.99e (TeX Live 2026):

```
pdflatex x86lean-semantics && bibtex x86lean-semantics && pdflatex x86lean-semantics && pdflatex x86lean-semantics
```

arXiv's build is the same minus BibTeX. Rehearsed in an empty directory holding only the two uploaded
files, three `pdflatex` runs give 0 errors, 0 undefined references, 0 overfull boxes, 0 `[?]` citations,
20 pages, US letter, 15 of 15 fonts embedded. Its text layer is identical to the full build's, and,
with ligatures, hyphenation and running heads normalised, to the PDF built by `tectonic` at `e66e24a`.

## The abstract field

The arXiv form caps the abstract at 1,920 characters and refuses a longer one. The paper's own abstract,
as plain text, is 1,271 characters (extracted from the built PDF). A count over the tex source that
keeps the `\src{}` marker reads 1,342, which is an upper bound.

## When

The TACAS 2027 call strongly encourages authors not to post the work on arXiv around two weeks before
and after the submission deadline of 2026-10-15 (`docs/TACAS-PRICING.md`, the call's own words). Posted
after that window, the paper is outside the request.
