# G5 — the artifact, scoped: what a reviewer must be able to reproduce, and what stands in the way

**Why this file exists.** `docs/TACAS-PRICING.md` prices G5 at 3–4 days: *"state every denominator, then
run the gates."* The paper is now drafted (`paper/x86lean-semantics.tex`), so the claims an evaluator
must reproduce are no longer hypothetical. This is the SCOPE, taken from the tree on 2026-09-12. **It
is not the artifact.**

⚖️ **THE CALL WAS READ AT ITS SOURCE THE SAME DAY — `TACAS-PRICING.md` §3a.** Artifact evaluation is
VOLUNTARY for research and case-study papers and due **2027-01-11**, after notification: **G5 is not on
the Oct-15 path.** The submission needs a mandatory data availability statement. ⛔ **STILL NOT READ:** the
AE committee's own page — VM or container form, size and time limits — **because it is not yet published**
(404 on 2026-09-13, §4 item 1). The BADGE CRITERIA are published and read (§4 item 1). Choices depending
on the unpublished page stay marked `[CALL]`.

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

✅ **PART 1 LANDED 2026-09-12 (D218):** pinned in `scripts/oracle_revision.txt`, fetched exactly by
`setup_oracle.sh`, and checked FIRST by `run_differential.sh`, which refuses any other revision and prints
`reference-model: acl2@<sha>`. ⛔ **Part 2's gate on records, and a re-run at the pin that §4.1 can cite,
are still owed.**

**Remedy, two parts, as scoped:**
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
| **R2 build** | `lake build`, the axiom allowlist gate, the coverage regeneration check | the pinned toolchain `leanprover/lean4:v4.32.0-rc1`, and NO package dependency (`lake-manifest.json` lists none; *this cell read "+ mathlib" until 2026-09-13*) | CI `build` job **5 m 47 s** on 2026-09-12 (run 34674679895), on a runner that restores caches. **COLD, measured 2026-09-13:** a fresh `git clone` at `64ded93` (no `.lake`), `lake build X86 X86Native Tests x86lean-diff x86lean-axioms` → **37 s wall, 1 m 39 s user, 45 jobs, rc 0**, on the 14-CPU arm64 development box at load 2.3, with the toolchain ALREADY INSTALLED by elan — a toolchain download is not in that figure, and a reviewer's machine will differ |
| **R3 coverage derivation** | `scripts/claimed_forms.py --check` | clang (the second source assembles every roster row) and objdump, **AND R2's `x86lean-diff` build** (it executes `.lake/build/bin/x86lean-diff`; *this cell omitted that until 2026-09-13*) | **Measured 2026-09-13** at `15a4898`, Apple clang 21.0.0 / LLVM objdump: **5.2 s wall, rc 0** after the build, CLAIMED rows 500 of 525. On a fresh clone WITHOUT the build it refuses **rc 2**, printing the real cause (`could not execute external process '.lake/build/bin/x86lean-diff'`) — run R2 first |
| **R4 differential** | `scripts/run_differential.sh` | SBCL, the ACL2 image, certified x86isa books — **at a pinned revision (§1)** | **COLD SETUP, measured 2026-09-13:** a fresh `git clone` of this repo at `a08e43f` (no `vendor/`), `bash scripts/setup_oracle.sh` as committed (its defaults, `-j2` image, `-j5` books) → **12 m 43 s wall, 34 m 06 s user, 3 m 41 s sys, rc 0**, tree 1.9 GB. Phases, from the run's own timestamped log: fetch of the pinned commit **2 m 03 s** · image **28 s** · ACL2's feature probe **39 s** · certification of `projects/x86isa/top.cert` **9 m 31 s, 1,143 books**. Same 14-CPU arm64 box as R2, SBCL 2.6.8 ALREADY INSTALLED (not in the figure), load1 2.2 at start and 6–9 during certification (the run's own `-j5` is most of it). **COLD RUN, measured 2026-09-13** at `ed312f5` in the same fresh clone, `bash scripts/run_differential.sh` → **10 m 33 s wall (788 s user), rc 0**: gates and the Lean build 1 m 26 s (the `x86lean-diff` build alone 11 s) · oracle and comparison 7 m 02 s · kernel-cost READINGS 2 m 05 s. **All seven counters equal the pin run's** (cases 89,056 · matched 68,524 · explained 29,435 · unexplained 0 · oracle-divergence 171 · leaks 0 · missing 0). Load1 2.7 → 5.6. The script's "twenty-five-minute" comment is not this box's figure. ⛔ **At `a08e43f` this path FAILED in 1 s on a fresh clone** — see §4 item 3 |

**Which sections need which tier:**
```
  §2 model, §6 proofs         R2   (the theorems are the evidence; the sizes are R1 via proof_lines.py)
  §3 undefined behaviour      R2   (the refusal theorem, the derivation code) + R4 for "confirmed by the run"
  §4.1 harness figures        R1 reads the published record; REPRODUCING the record is R4
  §4.3 the ceiling            R1 reads the roster; reproducing the refuse/execute split is R4 (oracle_availability.py)
  §5 coverage figures         R3 derives them; R1 checks the paper's copies against COVERAGE.md at the pin (D231)
```
⇒ **R1 is nearly free and already exists. R4 is the expensive tier: 12 m 43 s of setup and a 10 m 33 s run, cold, on
the development box (§1's pin is in place since D218; *this read "the one §1 currently makes unreproducible" until 2026-09-13*).** `[CALL]` decides whether R4 must run inside the evaluation budget or may be shipped as
recorded logs with a reduced re-run.

---

## 3. WHAT IS ALREADY IN PLACE
- `docs/CLAIMS.tsv` + `check_claims.py`: 75 rows at 2026-09-13 later (69 after item 4, 49 earlier that day, 39 at 2026-09-12), each with its command, and the paper
  gated against the rows it cites (D216). **The spine of "reproduce every claim" exists.**
- `lean-toolchain` and `lake-manifest.json` pin the Lean side.
- `scripts/setup_oracle.sh`: an idempotent recipe for R4, **pinned since D218** and run cold end to end on 2026-09-13 (§2). *(This read "unpinned (§1)" until that day.)*

## 4. OWED, IN ORDER
```
  1  read the TACAS 2027 AE call at its source            ✅ the CFP (PRICING §3a); the AE page itself [CALL]
     ✅ PARTLY, 2026-09-13 (curl + grep of the HTML, not a summariser): the ETAPS-WIDE BADGE CRITERIA are
        published at etaps.org/about/artifact-badges (HTTP 200, linked from the TACAS 2027 page). ⛔ A TACAS 2027
        AE GUIDELINES page is NOT: etaps.org/2027/artifact-evaluation/ and …/conferences/tacas/artifact-evaluation/
        are 404, and the TACAS 2027 page names the AE chairs but has 0 matches for docker · container · virtual
        machine · hours (control: 8 for "artifact" on the same page; the badge page 0 of each, 35 "artifact").
        ⇒ The container format and the evaluation time budget are UNPUBLISHED, not absent; [CALL] stays open
        on them. What IS settled, verbatim:
          Functional   "documented, consistent, complete, exercisable, and include appropriate evidence of
                        verification and validation"
          Reusable     "all the qualities of the 'Functional' badge" + "strictly adhere to norms and standards"
          Available    "made permanently available for retrieval on a publicly accessible archival repository
                        which has a declared plan to enable permanent accessibility and assigns DOIs to its
                        entries. The artifacts' DOIs are referenced in a data-availability statement at the end
                        of the paper."  ETAPS "recommends … Zenodo".
          Validated    "Reproduced" is by others with our artifacts; the page warns a time-limited AE may not
                        reach it. "Replicated" cannot come from a standard AE.
        ⛔⛔ THE PAPER'S DATA AVAILABILITY STATEMENT CITES ONLY github.com/jyh/x86lean — NOT ARCHIVAL, NO DOI —
        so as drafted it cannot earn "Available". See item 6.
  2  pin the reference model's revision (§1)                                     ✅ D218
  2b re-run the differential AT the pin; cite §4.1 to that record   ✅ docs/REFERENCE-PIN-RUN-2026-09-12.md
     (all seven counters equal batch 22's); a gate refusing a NEW record without it   ✅ D219 (in CI since 09-12)
  3  measure a COLD R2 build and the x86isa certification on a clean machine
     ✅ R2 cold on the development box, 37 s (§2); ✅ R4 cold SETUP on the same box, 12 m 43 s, of which the
        x86isa certification is 9 m 31 s (§2, 2026-09-13). ⛔ Neither on a CLEAN machine: both had their
        toolchains preinstalled (elan's Lean; brew's SBCL). ✅ The differential RUN, cold: 10 m 33 s, counters identical
        to the pin run. ⛔⛔ **AND ITS FIRST COLD ATTEMPT FAILED IN ONE SECOND — the finding this item exists for.** The
        oracle-availability gate executes `.lake/build/bin/x86lean-diff`, and `run_differential.sh` built it AFTER that
        gate; the refusal then said *"the residue is stale"*. It had never fired because the development box always
        has the binary. Repaired at `ed312f5` (build first; the emit failure prints what it saw). **A reviewer
        following R4 at any commit before `ed312f5` meets a false diagnosis unless R2 was run first.**
        📌 The "long pole" wording was true in ORDER and misleading in SIZE: certification is ~3/4 of setup and
        still under ten minutes here. A 09-02 cross-check is in the original tree's own files: its 1,143 `.cert`
        mtimes span 9 m 10 s (first to last), against 9 m 30 s by the same reading today — same book count.
  4  cite every remaining number in the paper to the manifest (paper/README.md)
     ⚠️ PARTLY, 2026-09-13: +20 rows (49 → 69), each value DERIVED by its command at 673b64a, never typed, and
        cited where the paper quotes it — K's 3155/774/7,000 and 497 of 3,064; x86isa's 400+, 559, 186 of
        3,192; libLISA's 118,000 and 18–28; the AFP's ~120; Roessle's 1,625; D108's 8 in 78,584; the
        proof rounds 25/12/9.6/7.6. Planted: 497 → 479 in the paper, check_claims FAILs naming the row.
        ⛔ A row gates PAPER == OUR RECORD; an external figure's record carries its source and read date,
        and re-reading the source is still G1's job, not this gate's.
        ⛔ NOT CITED, declared: D52's 82 pre-states / 35 (its record states them in WORDS); the four
        re-check samples 3/9 · 3/8 · 3/7 · 2/3 (no single record line holds them); §7's quoted "118 000"
        (libLISA's own spacing, which the prose arm does not read); the label counts 2, 4, 5, 7 (✅ D234: derived, and corrected to 2, 3, 5, 7; already
        declared in the paper's own marker); Armstrong's 24 of 15,400 (cited to the paper PDF directly).
        Inventory method: every digit run in the printed prose, by segment — 124, of which 75 sat in
        segments citing no row, most of them `x86-64` and `Lean 4`.
     ✅ 2026-09-13 (D231): +6 rows (69 → 75) for the COVERAGE figures, which the paper said CI checked and no gate
        read in the paper (planted 1,012 → 1,021: rc 0 before, rc 1 after). Re-inventoried: 32 uncited digit runs
        remain, every one in the declared set above or a technical constant (66 prefix, low 64 bits, bit 127).
        ⚠️ digit runs only — numbers spelled in words are outside the inventory.
     ✅ 2026-09-13 (D232, D233): numbers in WORDS now citable; the §1/§7 proof concession is corrected and gated
        (6 routines); THREE of the four re-check samples are rows (3/9 D201 · 3/8 D214 · 3/7 D202), checked as
        fractions. STILL DECLARED: the fourth sample 2/3 (D222+D223, no single line), §6's label counts and fit,
        D52's 82/16/35, libLISA's "118 000", Armstrong's 24 of 15,400.
     ✅ 2026-09-13 (D235): libLISA's quoted "118 000" cited (the prose arm reads space-grouped thousands, bounded);
        Armstrong's 24 of 15,400 is a PAIR of rows from D223's record line. ⛔ The fourth sample is WITHDRAWN from the
        rate, not gated: D223's own record counts THREE corrections that evening where the paper counted 2 of 3, and
        a record written now to fit it is what D233 refused. The rate is 3 of 9 · 3 of 8 · 3 of 7, all rows; the
        related-work corrections stay in §5 with no denominator. §6's counts and fit were cited by D234 (this list
        was not updated then). STILL DECLARED: D52's 82/16/35 alone.
  5  the container or VM, per [CALL]     ⛔ still [CALL]: the 2027 AE guidelines are unpublished (item 1)
  6  a DOI for the artifact (the "Available" criterion, item 1): an archival deposit of the submission commit —
     Zenodo is ETAPS's stated recommendation — and its DOI in the Data Availability statement beside the GitHub
     URL. ✅ **RULED DEPOSIT — the Captain, council 2026-09-13, minute B②: "2 yes deposit".** The word this item
     waited on has been given; what remains is mechanism, split across two hands. *(The ⛔ that stood here said
     "NOT TAKEN HERE … it is the Captain's word"; the word arrived. Kept visible because the REASON it was his —
     a DOI cannot be withdrawn — still governs the ORDER of the steps below.)*
     ```
       HIS HAND, ONE ACT     Zenodo profile menu -> GitHub -> "Sync now" -> toggle the slider beside jyh/x86lean.
       (posted to him        Prerequisite: a Zenodo account connected to GitHub.
        2026-09-13)          Source: help.zenodo.org/docs/github/enable-repository/ (slug MEASURED -- two
                             plausible guesses at that URL 404'd first).
       MINE, BEFORE THAT     [DONE] CITATION.cff -- so the record's title, authors and licence are OURS and not
                             GitHub's defaults. A deposited record is cited BY DOI, permanently.
       MINE, AT THE RELEASE  [OWED] set `version:` and `date-released:` in CITATION.cff to the release's own tag
                             and date IN THE RELEASE COMMIT. They are absent today on purpose -- a version field
                             naming a release that does not exist is the stale-literal defect this campaign keeps
                             finding -- and they are recorded HERE, in the recipe, because a free-floating TODO
                             is not read by the hand that cuts the tag.
       THEN                  the DOI goes into the Data Availability statement BESIDE the GitHub URL (not
                             instead of it), which closes line 103's ⛔ and the "Available" criterion.
     ```
     ⛔ **ORDERING IS LOAD-BEARING AND ONLY HALF-SOURCED, SAID PLAINLY.** Zenodo's archive guide opens *"It assumes
     you have already enabled a repository"*, so enabling-first is a **prerequisite it asserts**; the guide does
     **not** say what becomes of releases cut BEFORE enabling, and I did not find a page that does. ⇒ Treated as
     unverified, and obeyed anyway: **the cost of obeying is zero and a minted DOI cannot be withdrawn.**
     ✅ **AND THE MEASUREMENT THAT MAKES THIS RISK-FREE ONCE:** `gh release list` and `git tag` are both EMPTY on
     `jyh/x86lean`. **There is no pre-existing release to be missed or mis-archived** — the first release this repo
     ever cuts is the deposited one. *(That is true TODAY and stops being true the moment anyone cuts a tag.)*
     Priced small (ESTIMATED: a release + one sentence), and the estimate held for my half.
```
📌 **Price unchanged at 3–4 days** until item 1 is read; §1 is inside that price, not added to it,
because pinning is a few lines and recording is one header field plus a refusing gate.
