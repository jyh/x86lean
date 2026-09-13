# G5 — the artifact, scoped: what a reviewer must be able to reproduce, and what stands in the way

**Why this file exists.** `docs/TACAS-PRICING.md` prices G5 at 3–4 days: *"state every denominator, then
run the gates."* The paper is now drafted (`paper/x86lean-semantics.tex`), so the claims an evaluator
must reproduce are no longer hypothetical. This is the SCOPE, taken from the tree on 2026-09-12. **It
is not the artifact.**

⛔ **NOT READ, AND NOT TO BE RECALLED:** the TACAS 2027 artifact-evaluation call — its VM or container
form, its size and time limits, its badge criteria. **Read it at the source before building anything
here.** Every design choice below that depends on it is marked `[CALL]`.

---

## 1. ⛔⛔ THE LARGEST HOLE: THE REFERENCE MODEL'S REVISION IS NEITHER PINNED NOR RECORDED

```
  scripts/setup_oracle.sh      git clone --depth 1 https://github.com/acl2/acl2.git   <- whatever HEAD is today
  docs/ORACLE-SETUP.md         the same recipe; no commit named
  docs/DIFFERENTIAL-*.md       no record names an ACL2 or x86isa commit
                               (searched docs/ scripts/ PROVENANCE.md TRUSTBASE.md for the local sha:
                                0 hits; control: a sha this repo does record, 7bb57ee, is found)
  the only version evidence    "ACL2 Version 8.7+" in DIFFERENTIAL-P1-BATCH1 and -BATCH3 -- the "+" is
                               a DEVELOPMENT snapshot, which names no revision
  the local tree, this machine vendor/acl2 at c8897a34d3efc37eb466d7ee50a2e3861c6e82db,
                               committed 2026-09-01 23:14 -0700, working tree clean;
                               saved_acl2 built 2026-09-02 10:17
```
⇒ **Every differential figure in the paper is agreement with a reference model whose version no record
names.** A reviewer following the recipe today clones a different ACL2. The paper's own §4.3 makes this
concrete: if upstream x86isa has since fixed the packed-shift count (D108), the eight declared
divergences STOP diverging, and the harness — correctly — fails the run. **The evaluator would see a red
run and have no way to know it was a version difference rather than a defect.**
⚠️ **What is NOT known, stated rather than assumed:** that every record was produced against
`c8897a34`. It is the only tree on this machine and it has not moved since P0, but the records do not say
which machine or tree each ran on, and this repository has had a second machine since 2026-09-09.

**Remedy, two parts, both owed:**
1. **Pin** — `setup_oracle.sh` fetches a named commit (`git fetch --depth 1 origin <sha>` then checkout),
   and `ORACLE-SETUP.md` names it.
2. **Record** — every differential record's header carries `git -C vendor/acl2 rev-parse HEAD` as the
   run saw it, and a gate refuses a record without one. **This is a harness change** and it lands before
   the next differential run, not retrofitted onto the existing records, which stay as measured.
⇒ 🔑 ***A DIFFERENTIAL CLAIM IS A CLAIM ABOUT TWO ARTIFACTS, AND THIS REPOSITORY PINNED ONE.***

---

## 2. REPRODUCTION TIERS, AND WHAT EACH PAPER SECTION NEEDS

| tier | what runs | needs | measured cost |
|---|---|---|---|
| **R1 manifest** | `scripts/check_claims.py` — every `CLAIMS.tsv` row at its pinned sha, and the paper's quoted figures against the rows | git, bash, python3; a FULL clone (pinned shas) | **3 s** on this machine, 2026-09-12 |
| **R2 build** | `lake build`, the axiom allowlist gate, the coverage regeneration check | the pinned toolchain `leanprover/lean4:v4.32.0-rc1` + mathlib | CI `build` job **5 m 47 s** on 2026-09-12 (run 34674679895), on a runner that restores caches — a cold build is UNMEASURED here |
| **R3 coverage derivation** | `scripts/claimed_forms.py --check` | clang (the second source assembles every roster row) and objdump | UNMEASURED |
| **R4 differential** | `scripts/run_differential.sh` | SBCL, the ACL2 image, certified x86isa books — **at a pinned revision (§1)** | ACL2 image ~4 min (ORACLE-SETUP.md); x86isa certification "the long pole", UNMEASURED; the run itself "twenty-five-minute" per the script's own comment, not re-measured |

**Which sections need which tier:**
```
  §2 model, §6 proofs         R2   (the theorems are the evidence; the sizes are R1 via proof_lines.py)
  §3 undefined behaviour      R2   (the refusal theorem, the derivation code) + R4 for "confirmed by the run"
  §4.1 harness figures        R1 reads the published record; REPRODUCING the record is R4
  §4.3 the ceiling            R1 reads the roster; reproducing the refuse/execute split is R4 (oracle_availability.py)
  §5 coverage figures         R3
```
⇒ **R1 is nearly free and already exists. R4 is the expensive tier and the one §1 currently makes
unreproducible.** `[CALL]` decides whether R4 must run inside the evaluation budget or may be shipped as
recorded logs with a reduced re-run.

---

## 3. WHAT IS ALREADY IN PLACE
- `docs/CLAIMS.tsv` + `check_claims.py`: 39 rows at 2026-09-12, each with its command, and the paper
  gated against the rows it cites (D216). **The spine of "reproduce every claim" exists.**
- `lean-toolchain` and `lake-manifest.json` pin the Lean side.
- `scripts/setup_oracle.sh`: an idempotent recipe for R4 — **unpinned (§1).**

## 4. OWED, IN ORDER
```
  1  read the TACAS 2027 AE call at its source                                    [CALL]
  2  pin + record the reference model's revision (§1)                             harness change
  3  measure a COLD R2 build and the x86isa certification on a clean machine
  4  cite every remaining number in the paper to the manifest (paper/README.md)
  5  the container or VM, per [CALL]
```
📌 **Price unchanged at 3–4 days** until item 1 is read; §1 is inside that price, not added to it,
because pinning is a few lines and recording is one header field plus a refusing gate.
