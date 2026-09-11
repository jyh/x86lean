# x86lean — PERSONAL LANE (seat "Paris")

Opened 2026-09-02 at the Captain's (JYH's) word (council minute 2026-09-02 §5 / desk EE): an
x86-64 user-level ISA semantics in Lean 4, definitional and executable, from PUBLIC sources only,
differentially validated against public executable models and real hardware, permissively
licensed. Precedence: fourth in the personal lane (saltworks · SaltBench · twin primes · this).

## Lane and provenance (fleet law, ../CLAUDE.md)
- PERSONAL lane. Destined to be PUBLIC: commit hygiene from commit 1 (no `Claude-Session:`
  trailers, no chat URLs; `Co-Authored-By` fine).
  **TWO REMOTES EXIST AND HAVE SINCE 2026-09-03T16:03:49Z**: `origin` =
  `github.com/jyh/x86lean`, **PUBLIC since 2026-09-10 09:0x** (measured with `gh`,
  `isPrivate: false`, by paris at boot the same morning), and `local` = the bare repo on the
  backup volume. ⛔ **PUSH BOTH AT EVERY LANDING** (the Captain's row-ES order of 09/03).
  ⛔ *This bullet read "**PRIVATE** (measured with `gh`, `isPrivate: true`)" until 2026-09-10.*
  **THE FLIP IS COUNCIL RULING ⑥ OF 2026-09-10** (desk `JF`), in the Captain's words: *"To go
  public, I want to include this under the umbrella of saltbench... Can we make x86lean public,
  and make it clear in the README that this is developed as part of saltbench?"* — with *"Keep
  paris separate"*: the SEMANTICS is this seat's artifact with its own provenance; the x86 SUITE
  is a SaltBench item under `bench`. See README's **Part of SaltBench** section.
  ⇒ 🔑 ***A STALE VISIBILITY CLAIM IS LOAD-BEARING IN THE PERMISSIVE DIRECTION*** — every other
  staleness in this file costs a re-measurement, but a head that reads "private" here prices
  every hygiene question wrong in the one direction that cannot be taken back after a push.
  ⛔⛔ **AND A LANDING IS NOT ALWAYS A SEAT'S PUSH — MEASURED 2026-09-09.** A pull request merged
  in the GitHub UI lands on `origin` **and on nothing else**: no seat runs a command, so the
  row-ES discipline never fires and the `local` tier silently falls behind. Measured at the object
  that day — `evidence` merged PR #1 at 11:15 and `local` sat one commit behind `origin` until the
  next seat push happened to carry it. ⇒ 🔑 ***A RULE PHRASED AS "DO X AT EVERY LANDING" IS ONLY
  AS GOOD AS THE ASSUMPTION THAT EVERY LANDING PASSES THROUGH A HAND THAT CAN DO X.***
  ⇒ **After any landing you did not perform: `git fetch origin && git push local
  origin/master:master` before trusting the tiers.** Nothing polls this; the divergence is
  invisible until someone compares the two `ls-remote`s, which is how it was found — twice.
  ⛔ **SECOND INSTANCE, 2026-09-10, AND IT WIDENS THE RULE FROM "MERGE" TO "LANDING":** the
  council's own execution acts — `64ecb39` (the PUB-1 history baseline) and `f908ad7` (the public
  flip) — were landed by the HELM at close, so again no seat ran the row-ES command and `local`
  sat **2 commits behind** until paris measured it at boot. **A helm push is not a UI merge**, and
  the 09/09 wording said "merge", so the rule as written did not cover the case that recurred.
  ⇒ 🔑 ***THE TWO COMMITS THE FLEET MOST WANTED DURABLE WERE THE TWO THE DURABLE TIER DID NOT
  HAVE*** — the backup tier is furthest behind exactly when an outside hand acts, which is exactly
  when the landing matters most.
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
  ⛔ *This bullet read "`--range <root>..HEAD` still reads 7 — historical commits that ADDED
  paths since repaired in the tree" until 2026-09-09, when it was measured at the object. **THE
  SENTENCE WAS FALSE IN ITS SUBJECT, NOT ITS NUMBER**, and the number was quoted into a QUEUE
  entry, a fleet-bus post and a Captain's ruling before anyone ran the command again.* `git diff
  A..B` is a **NET DIFFERENCE BETWEEN TWO TREES**, so the file arm of a long `--range` cannot see
  (a) a path added and later repaired inside the range — the repair erases it from the very arm
  meant to record it — or (b) anything in the range's FIRST commit that was never touched again,
  **which for `<root>..HEAD` is the entire root commit.** ⇒ 🔑 ***THE FILE ARM OF `--range
  <root>..HEAD` IS A TREE SCAN WEARING A HISTORY SCAN'S NAME, and it is strictly WEAKER than
  `--tree`.*** The "7" was the TREE RESIDUE of a commit not yet repaired; it read **0** the moment
  the tree was repaired, while every blob stayed in the history a clone receives.
  ✅ **`--history` is the arm that answers the question** (per-commit, diffed against each commit's
  own parent; merges charged only for content no parent carries). It measures **8** findings across
  **4** commits — the seven, plus **the root commit's own CLAUDE.md**, which was structurally
  invisible to the arm that produced the number and was never shown to the Captain.
  ⛔⛔ **THIS PARAGRAPH USED TO EXEMPT THE CI ARMS AND THE EXEMPTION IS FALSE — DRIVEN 2026-09-10.**
  It read: *"CI's delta arm scans one push, where the net difference and 'what this push adds'
  coincide; the tree arm covers what it drops."* **Both halves fail on a MULTI-COMMIT push.** Driven
  in a throwaway repo, two commits pushed together — commit 1 ADDS a private path, commit 2 REMOVES
  it:
  ```
    check_private_paths.py --range BASE..HEAD   rc 0   (the CI delta arm)  — no finding
    check_private_paths.py --tree               rc 0   (the CI tree ratchet) — no finding
    check_private_paths.py --history            FAIL, names the commit and the file
  ```
  ⇒ 🔑 ***THE BLOB IS PUSHED TO A PUBLIC REMOTE AND NO CI ARM SEES IT.*** The path is in neither the
  NET DIFFERENCE nor the TREE — it exists only in an intermediate commit, which is exactly the
  population `--history` was built to read and the one CI does not run.
  ⚠️ **NOT HYPOTHETICAL FOR THIS REPO:** `1304132` was pushed with **three commits at once** the same
  day this was written. Single-commit pushes are safe; this repo does not only make those.
  📌 **The message arm is genuinely unaffected** (`git log` is per-commit), and the TRAILERS gate does
  run a full-history arm (`--range HEAD`). **It is private PATHS that has delta + tree + messages and
  no history arm.**
  ⛔ **AND THE REMEDY IS BLOCKED, WHICH IS PROBABLY WHY IT WAS NEVER WIRED:** `--history` supports
  `--write-baseline`, but writing that baseline IS the PUB-1 recording act, and this file already
  records it as **blocked on the Captain's word about the eighth site**. ⇒ **The gap and the blocker
  are the same item**, and saying so is the correction — the old paragraph instead said there was no
  gap.
  PUB-1 (accept vs rewrite) was ruled **ACCEPT** by the Captain 2026-09-09; salt's own precedent
  (08/30) was the same. The recording act is BLOCKED on his word about the eighth site — filed in
  `docs/QUEUE.md`, on the blocked-on-captain register, and derived in `docs/DECISIONS.md` D182.
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
