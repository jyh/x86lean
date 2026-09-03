# PROVENANCE — sources, licences, and the reading log

x86lean is built from PUBLIC sources only. This file is the deliverable that says which, under what
licence, and what was actually consulted. Every licence below was read at the canonical repository
file or page on 2026-09-02 (method: the GitHub contents API with `Accept: application/vnd.github.raw`,
or the canonical web page). Nothing here is cited from memory.

## This repository's own licence

**Apache-2.0** (`LICENSE`, verbatim from apache.org, copyright 2026 Jason Hickey), by the
Captain's ruling at the 09/03 council. ⚠️ The choice is not free: this repository CONSULTS
BSD-3 (ACL2 x86isa), NCSA (K) and BSD-2/BSD-3 (Sail) work by EXECUTION and copies none of
it, so nothing here is a derivative of them — but Apache-2.0's patent grant is the reason
it is Apache and not MIT, on a repository whose subject is a patented instruction set.
⛔ **The repository is PRIVATE.** Publication is gated on the Captain's IARC approval; a
licence file is not a publication decision and does not become one.

## Licence table

| Source | Canonical location | Licence | Role here |
|---|---|---|---|
| Intel 64 and IA-32 Architectures Software Developer's Manual | intel.com/…/technical/intel-sdm.html (PDF version 092 as of 2026-08-19) | Intel copyright; no open licence stated for the manuals | READING reference. Cited by volume/section; no text is copied |
| felixcloutier.com/x86 | felixcloutier.com/x86 (derived from the Dec 2023 SDM); tooling github.com/fay59/x86doc | Site text: Intel-derived, no licence stated. Tooling: The Unlicense | Reading mirror under Intel's terms. The Unlicense covers the extraction tool, not the text |
| ACL2 x86isa | github.com/acl2/acl2 `books/projects/x86isa/` | BSD-3-Clause, Copyright (C) 2015 Regents of the University of Texas (top.lisp); per-file headers govern per file | Primary executable oracle for differential testing; its `UNDEF` seeding is the precedent for our undefined-bit oracle |
| K x86-64 semantics | github.com/kframework/X86-64-semantics `LICENSE.md` | University of Illinois/NCSA Open Source License, Copyright (c) 2019 UIUC | Second oracle; coverage target list (3155 variants / 774 mnemonics, Haswell user-level) |
| Sail x86 (from ACL2) | github.com/rems-project/sail-x86-from-acl2 | BSD-2-Clause (tooling); `model/`: BSD-3-Clause AND the ACL2 x86 model's licence | Spike-only third reference (plan P3b). Never the proving model |
| Sail | github.com/rems-project/sail | BSD-2-Clause | The Lean backend (`sail_lean_backend`) for the P3b spike |
| Intel XED | github.com/intelxed/xed | Apache-2.0 | Decoder whose structured output is consumed as the AST (decode trust is named in TRUSTBASE.md). NOTE: `/usr/bin/xed` on macOS is Xcode's editor launcher, not Intel XED |
| Lean 4 · mathlib4 | github.com/leanprover/lean4 · github.com/leanprover-community/mathlib4 | Apache-2.0 | The prover and its library |
| LNSym | github.com/leanprover/LNSym | Apache-2.0 | PRECEDENT only (an Arm ISA in Lean 4 with hardware conformance testing); no code is copied |

## Rules
1. A source enters this table BEFORE any file from it is read for the model.
2. Every file consulted for a semantic rule is logged below with its per-file copyright holder and the
   rule it informed. "Consulted" means read to decide a rule, not copied: this model is written fresh
   in Lean from the SDM's prose and the oracles' BEHAVIOUR, and validated against them by execution.
3. No employer-lane material, of any employer, in any form. Method lessons arrive as ideas in the
   owner's words, never as files or code.
4. Salt tooling (the owner's personal-lane Lean project) may be reused freely.

## Reading log

| when | source | files | licence holder | what it informed |
|---|---|---|---|---|
| 2026-09-02 (P0) | ACL2 x86isa | consulted by EXECUTION only, as the differential oracle | © 2015 Regents of the Univ. of Texas (BSD-3) | No rule was read from its text. Its ANSWERS are recorded as evidence in `docs/DIFFERENTIAL-P0.md`; `scripts/x86isa_driver.lisp` is this project's own code driving it. |
| 2026-09-02 (P1) | K x86-64 semantics, commit `592380aea048` | `semantics/{register,immediate,memory,system}Instructions/*.k` — 3063 files, read MECHANICALLY by `scripts/k_roster.py` | © 2019 Univ. of Illinois at Urbana-Champaign (NCSA) | The P1 ROSTER and its batch partition (`p1/roster.tsv`, `docs/P1-ROSTER.md`): each file yields its mnemonic, operand shapes, which flags it writes, whether it writes a computed value / a constant / `undefMInt`, and which flags it reads. No K rule text is reproduced; what leaves the script is mnemonic names, operand shapes and flag dispositions — facts about x86-64 that the SDM states. |

⚠️ **The second row is a MECHANICAL reading and is logged as one entry, not 3063.** Rule 2 asks for
every file consulted for a semantic rule; these files were consulted for a CLASSIFICATION, by a script
whose source is in this repository and whose output is regenerated in CI. The audit unit is the script,
not the file list — the file list is `semantics/` at the named commit, and `scripts/setup_k_roster.sh`
fetches exactly it.
