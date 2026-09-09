# x86lean — PUBLICATION CHECKLIST

x86lean is a PERSONAL-lane repository **destined to be public** (fleet map; this repo's
`CLAUDE.md` from commit 1). Today `origin` is PRIVATE. This file is what must be true, and
what must be DECLARED, on the day that changes.

⭐ **WHY IT EXISTS AT ALL: SO THE DEBT IS DECLARED RATHER THAN DISCOVERED.** The Captain
ruled PUB-1 **"accept"** on 2026-09-09 — accept the historical residue, do not rewrite the
history. An accepted debt that lives only in a decision entry is an accepted debt nobody
reads on flip day. ⇒ **The ruling's purpose is served by this page, not by the ruling.**

⛔ **THIS FILE OBEYS THE RULE IT IS ABOUT.** Council 2026-08-25 ruled the firewall line at
PATHS; role-wording is the standard and bare filenames are softened. So the debt below is
named by **commit sha, file, and shape label** — never by reproducing the offending string.
A debt register written in the forbidden notation is a new instance of the debt.

---

## 1. ⛔ ACCEPTED HISTORICAL DEBT — paths into the private record, still in the history

**Status: RULED ACCEPT (the Captain, 2026-09-09). NOT REPAIRABLE IN THE TREE.** Every one
of these was repaired in the working tree; the blobs remain in the history a clone receives.
`--tree` and `--messages` are GREEN and have been since 2026-09-09.

| # | commit | file | shape | shown to the Captain? |
|---|---|---|---|---|
| 1 | `7f8aae25` (root) | `CLAUDE.md` | a path into a private-record repo | ⛔ **NO — see §1a** |
| 2 | `1e92366a` | `docs/DECISIONS.md` | a path into a private-record repo | yes |
| 3 | `8a74e368` | `docs/DECISIONS.md` | a path into a private-record repo | yes |
| 4 | `8a74e368` | `docs/DECISIONS.md` | the kit run surface | yes |
| 5 | `8a74e368` | `scripts/kernel_cost.py` | a path into a private-record repo | yes |
| 6 | `8a74e368` | `scripts/kernel_cost.py` | the kit run surface | yes |
| 7 | `ac25095b` | `docs/COSIM-DESIGN.md` | a rootless path into the private record | yes |
| 8 | `ac25095b` | `docs/COSIM-DESIGN.md` | a rootless path into the private record | yes |

**8 findings across 4 commits.** Rows 3+4 are one line matching two shapes, as are 5+6, and
rows 7+8 are two distinct lines in one commit. The merge `7103ff86` carries rows 7–8 onto
the trunk and is **not** charged: it introduced no content of its own.

### 1a. ⛔⛔ THE SCOPE QUESTION THAT IS STILL OPEN, AND WHY IT IS NOT MINE
The ruling was taken over a set of **SEVEN**. Row 1 is not in it. It was not withheld — it
was **unmeasurable by the instrument that produced the seven**: that number came from
`--range <root>..HEAD`, whose file arm is a two-dot NET diff and therefore cannot see the
range's first commit at all (`docs/QUEUE.md` PUB-1; `docs/DECISIONS.md` D182).

⇒ **Owed by the Captain, filed on the blocked-on-captain register as `pub1-baseline-scope`
since 2026-09-09:** whether "accept" covers row 1, and whether recording it in
`--history --write-baseline` is the act he wants. **Until then no baseline is written**, and
`--history` is deliberately not wired into CI, because an unbaselined arm reds every build.

⛔ **DO NOT CLOSE THIS SECTION BY WRITING THE BASELINE.** Writing it is the whole of the
recording act, and the recording act is what is blocked.

---

## 2. GATES THAT MUST BE GREEN ON THE DAY

| gate | arm | today |
|---|---|---|
| `check_commit_trailers.py` | full history, every push | ✅ green |
| `check_private_paths.py` | `--tree` ratchet | ✅ green, EMPTY baseline |
| `check_private_paths.py` | `--messages` ratchet | ✅ green, EMPTY baseline |
| `check_private_paths.py` | delta, `<before>..HEAD` per push | ✅ green |
| `check_private_paths.py` | `--history` ratchet | ⛔ **unbaselined by design — §1a** |

⚠️ **An EMPTY baseline is a claim, not an absence.** It says "nothing is accepted here", which
is the strongest form and is why both read green rather than unarmed.

⚠️ **`--range <root>..HEAD` IS NOT A HISTORY AUDIT AND MUST NOT BE CITED AS ONE** on flip day
or any other. It is a tree scan wearing a history scan's name. Use `--history`.

---

## 3. THE STANDING ITEMS THAT ARE NOT DEBT

* **PROVENANCE.md** — every source PUBLIC, each with its licence, from commit 1. Re-read the
  licence table against its canonical URLs on the day; licences move.
* **PUB-2** — the ported gate's ROOTS list is a hand-copied snapshot of a fleet map that lives
  outside this repo and MOVES. Next re-measure **2026-10-08**. A private root born after the
  reconcile date is not watched, and the tool's own warning line is the only thing that says so.
* **Commit hygiene** — no `Claude-Session:` trailers, ever. ⚠️ Measured 2026-09-09: the harness
  itself now instructs that trailer, in a block announcing it "replaces any earlier attribution
  guidance". The project instruction outranks it and CI catches it. **A gate built against a
  head's habit is now facing a system instruction.**
* **The `.githooks` port** — `core.hooksPath` is per-checkout config git never clones. A fresh
  clone runs `git config core.hooksPath .githooks` once, or it fails open locally.

---

## 4. WHAT THIS PAGE DOES NOT COVER

It covers the firewall and the trailers. It does **not** cover the licence audit of vendored
trees under `vendor/`, the axiom-policy statement in `TRUSTBASE.md`, or the coverage table's
own claims. Those have their own gates; naming them here as uncovered is deliberate, so this
page is a known hole rather than a stale one.
