# G1 — positioning x86lean against the existing x86 semantics

**Why this file exists:** *"why another x86 semantics?"* is the first referee question, and
`docs/TACAS-PRICING.md` prices answering it at 1–2 days. This is the skeleton with **our column
measured and the others' columns explicitly OWED** — not filled with plausible numbers.

⛔⛔ **THE RULE THIS FILE IS BUILT ON.** Every cell is one of:
* **MEASURED** — derived from this tree today, with the deriving command named;
* **RECORDED** — a figure this repository already carries with a source (`PROVENANCE.md`);
* **OWED** — *not known here*, and it must be read from that project's own documentation before it
  appears in a paper.
**No cell is estimated.** A comparison table is exactly where a plausible number about someone else's
system does the most damage, because it is the one claim a referee can check against the source and we
cannot.

---

## 1. THE TABLE

| | **x86lean** (this work) | **ACL2 x86isa** | **K x86-64** | **Sail-x86-from-acl2** |
|---|---|---|---|---|
| **prover / host** | Lean 4 + mathlib4 — MEASURED | ACL2 — RECORDED (`PROVENANCE.md`) | K framework — RECORDED | Sail → Lean backend — RECORDED |
| **scale** | 158 mnemonics · 1,012 differentially tested forms · 500/525 roster rows · 351/374 distinct machine forms — **MEASURED AND CI-GATED** | **OWED** | 3,155 variants / 774 mnemonics, Haswell user-level — **RECORDED** (K's own coverage target list) | **OWED** (inherits x86isa's scope; the mapping is not recorded here) |
| **executable** | yes — the model runs; `run_differential.sh` drives it — MEASURED | yes — it is our primary executable oracle — MEASURED (by use) | **OWED** — we read its tree mechanically for the roster, never executed it | **OWED** — planned as a P3b spike only |
| **role here** | the proving model | primary differential oracle | roster/coverage source, read mechanically | third reference, spike only — never the proving model |
| **axiom base of theorems** | exactly `[propext, Classical.choice, Quot.sound]`, CI-gated over the library — **MEASURED** | **OWED** | **OWED** (K is not a proof assistant in the same sense; the comparison may not be well-posed) | **OWED** |
| **proof support demonstrated** | 7 machine-checked memory-safety theorems over 4 routines; cost model `19 + ~7.7/label` measured at 2–7 labels — **MEASURED** | **OWED** | **OWED** | **OWED** |
| **undefined-bit treatment** | explicit oracle in the state; `UNDEF`-seeding precedent taken from x86isa — RECORDED | seeds `UNDEF` — RECORDED | **OWED** | **OWED** |
| **decode** | Intel XED consumed as the AST; decode trust named in `TRUSTBASE.md` — MEASURED | **OWED** | **OWED** | **OWED** |

---

## 1b. ⭐ FOUR CELLS FILLED FROM THE SOURCES THEMSELVES, 2026-09-11
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

## 2. WHAT IS STILL OWED, AND WHERE IT MUST COME FROM
```
  x86isa   axiom base · proof support · decode      (scale + validation now RECORDED, §1b)
  K        proof support                            (scale + executability + validation RECORDED, §1b)
  Sail     scale mapping · executability · proof support         sail-x86-from-acl2 repo
```
⚠️ **Five OWED cells** (was nine; four filled at the sources in §1b). Until they are read from the sources, **this table cannot go in a paper** — it
would be a positioning claim resting on our own tree's silence about other people's systems.
📌 **That is a ~1 day reading task and it is the honest remainder of G1**, not a formality: the
pricing's "1–2 days" was for the whole gap, and this skeleton is the half that could be done from
measurement alone.

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
