# x86lean — PERSONAL LANE (seat "Paris")

Opened 2026-09-02 at the Captain's (JYH's) word (council minute 2026-09-02 §5 / desk EE): an
x86-64 user-level ISA semantics in Lean 4, definitional and executable, from PUBLIC sources only,
differentially validated against public executable models and real hardware, permissively
licensed. Precedence: fourth in the personal lane (saltworks · SaltBench · twin primes · this).

## Lane and provenance (fleet law, ../CLAUDE.md)
- PERSONAL lane. Destined to be PUBLIC: commit hygiene from commit 1 (no `Claude-Session:`
  trailers, no chat URLs; `Co-Authored-By` fine).
  **TWO REMOTES EXIST AND HAVE SINCE 2026-09-03T16:03:49Z**: `origin` =
  `github.com/jyh/x86lean`, **PRIVATE** (measured with `gh`, `isPrivate: true`), and `local` =
  the bare repo on the backup volume. ⛔ **PUSH BOTH AT EVERY LANDING** (the Captain's row-ES
  order of 09/03).
  ⛔ *This bullet read "the scrub gates are ported before the first push to any public remote.
  **No remote exists yet.**" until 2026-09-09 — false for six days, in the first file every
  session in this repo reads.* **AND BOTH HALVES OF IT WERE FALSE TOGETHER, WHICH IS WHY
  NEITHER WAS NOTICED:** the sentence promised a gate CONDITIONAL on a remote it declared
  absent, so a reader who believed the second clause had no reason to check the first. The
  trailer gate had in fact been ported; `check_private_paths.py` had NOT, and on the day it was
  finally ported it found 8 findings in the tree. ⇒ 🔑 **A CONDITIONAL WHOSE ANTECEDENT IS
  FALSELY DENIED IS AN UNGATED CLAIM WEARING A GATE'S CLOTHES.**
- Scrub CI (`.github/workflows/scrub.yml`) runs BOTH gates: `check_commit_trailers.py` over the
  FULL history every push, and `check_private_paths.py` in three arms (delta · tree · messages).
  ⚠️ `--range <root>..HEAD` still reads 7 — historical commits that ADDED paths since repaired
  in the tree. Rewriting that history before publication is the CAPTAIN'S call, not the seat's;
  salt's own precedent (08/30) was ACCEPT AND RECORD, NO REWRITE. Filed in `docs/QUEUE.md`.
- Sources are PUBLIC ONLY, each with its licence in PROVENANCE.md from commit 1: Intel SDM
  (reading), ACL2 x86isa (BSD-3), K x86-64 (NCSA), Sail x86 (BSD), XED (Apache-2.0).
- THIS SEAT NEVER OPENS AN EMPLOYER-LANE TREE (loca, holl, pcc-bios, safe_dav1d, safe_gif).
  Method lessons from anywhere arrive as IDEAS in the Captain's words, never as files or code.
- Salt tooling and lessons (personal lane) are usable freely.

## The plan of record
The seat repo's plan brief for this campaign — `2026-09-02-PLAN-x86lean-personal-DRAFT.md`,
mercutio's draft at the Captain's word, as amended by the helm's rulings in the boot brief: theorems on the three
standard axioms only (bv_decide confined to test executables and a separately labelled tier);
P0's exit = one differential run of 20 scalar forms against x86isa with zero unexplained
disagreements; P1 priced as an executor WAVE; XED decode trust visible in the coverage table.
