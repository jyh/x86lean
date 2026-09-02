# PROVENANCE — sources, licences, and the reading log

x86lean is built from PUBLIC sources only. This file is the deliverable that says which, under what
licence, and what was actually consulted. Every licence below was read at the canonical repository
file or page on 2026-09-02 (method: the GitHub contents API with `Accept: application/vnd.github.raw`,
or the canonical web page). Nothing here is cited from memory.

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
(empty at commit 1)
