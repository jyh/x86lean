#!/usr/bin/env python3
"""EVERY COMMENT THAT CITES A DECLARATION BY NAME AND FILE MUST BE TELLING THE TRUTH.

WHY THIS EXISTS.  The comments in this repository carry a great deal of the
reasoning, and they routinely point at the gate that holds a claim:
"`foo_is_checked` in Tests/Coverage.lean is that sentence as a theorem".

⛔ P1 BATCH 16 FOUND ONE THAT WAS NEVER TRUE.  `X86/Syntax.lean` has said since
P1 batch 11 that

    `loop_synonyms_are_one_encoding` in Tests/Coverage.lean is that sentence
    as a theorem over the vector table.

There is no such theorem.  There never was.  It survived five batches, and the
reason it survived is the reason it was written: a citation to a gate READS AS
THE GATE.  Nobody greps for the name of a theorem they have just been told
exists — the sentence answers the question a sceptical reader was about to ask,
which is D15's rule exactly, one level up.

⇒ 🔑 **A CITATION IS ITSELF AN UNGATED CLAIM**, and it is the most persuasive
kind, because it names its own evidence.  The repository gates the coverage
prose (D41), the watch windows (D45) and the README's numbers (D47); until this
gate, nothing checked that the gates those documents NAME are real.

⚠️ And batch 16 nearly reproduced it verbatim: a first draft of the batch's own
`Tests/Vectors.lean` comment cited `rep_synonyms_are_one_encoding` "in
Tests/Coverage.lean", written before the theorem was.  The pattern was copied
together with its defect, which is what a convention does when nothing checks it.

WHAT IT CHECKS.  Any `` `identifier` `` followed by "in <path>", where the path
is a source file in this repository: the identifier must OCCUR in that file.

⚠️ OCCUR, NOT "BE DECLARED", AND THE WEAKER TEST IS THE DELIBERATE ONE.  A first
version demanded a declaration and produced five hits, of which two were prose
it had misread — "the list of `undefBit` call sites in `X86/Semantics.lean`"
and "paired with `Oracle.zero` in `Tests/Nonvacuity.lean`" both cite a file for
a USE, which is a true sentence.  A gate that cries wolf on true sentences gets
switched off, and it would have been narrower than its subject in exactly the
way that makes a gate a chore rather than a check.  Occurrence is what separates
"points at something" from "points at nothing", and pointing at nothing is the
failure that hides.

WHAT IT DOES NOT CHECK: that the thing cited says what the sentence claims — nor
that a citation naming the RIGHT file has the right name within it, beyond its
being present somewhere in that file.

⚠️ AND IT CANNOT TELL A LIVE CITATION FROM A QUOTED DEAD ONE.  Batch 16's own
repair notes quote the phantom sentences they replace, and the gate flagged
them: to it, quoting `foo` "in Tests/Coverage.lean" inside a post-mortem is
indistinguishable from asserting it.  The convention that follows is deliberate
and is the reason those notes read as they do: **a dead citation is never
written in citation form** — name it in prose, not as `` `ident` `` beside its
file.  Weakening the gate to guess at quotation marks would have traded a real
check for a heuristic, on a file whose whole subject is claims nobody verifies.
"""
import collections, os, re, sys, glob, subprocess

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(root)

SOURCES = sorted(glob.glob("X86/*.lean") + glob.glob("Tests/*.lean")
                 + glob.glob("X86Native/*.lean") + ["Main.lean"]
                 + glob.glob("scripts/*.py"))

# `name` ... in <path.lean|.py|.sh>   — the citation form used throughout
CITE = re.compile(
    r'`([A-Za-z_][A-Za-z0-9_\'.]*)`'          # the cited identifier
    r'(?:[^`\n]{0,80}?)'                       # a little connective prose
    r'\bin\s+`?((?:X86|X86Native|Tests|scripts|docs)/[A-Za-z0-9_./-]+'
    r'|Main\.lean)`?')

# The identifier must OCCUR in the cited file: as a declaration, or as a use.
# See the header on why the declaration-only test was the wrong calibration.
def occurs(path, name):
    try:
        body = open(path).read()
    except OSError:
        return False                                 # missing file: reported
    if re.search(rf'(?<![A-Za-z0-9_\']){re.escape(name)}(?![A-Za-z0-9_\'])', body):
        return True
    base = name.split(".")[-1]
    return bool(re.search(rf'(?<![A-Za-z0-9_\']){re.escape(base)}(?![A-Za-z0-9_\'])',
                          body))


def selftest():
    """⭐ THE POSITIVE CONTROL — and it carries BOTH directions.

    A gate that only proves it can go red says nothing about whether it goes
    green for the right reason.  Two arms: a citation that points at NOTHING
    must be caught, and a citation that points at something REAL must not fire
    — the second is what keeps this from being a gate that flags every
    backtick near a path.
    """
    target = "Main.lean"
    saved = open(target).read()
    arms = [
        ("phantom", "\n-- `a_theorem_that_does_not_exist` in `Tests/Coverage.lean`\n", True),
        ("real",    "\n-- `mem_dest_claims_are_backed` in `Tests/Coverage.lean`\n", False),
    ]
    ok = True
    try:
        for label, line, expect_red in arms:
            open(target, "w").write(saved + line)
            r = subprocess.run([sys.executable, __file__], capture_output=True, text=True)
            red = r.returncode != 0
            if red != expect_red:
                print(f"  ✖ {label}: expected {'a failure' if expect_red else 'a pass'}, "
                      f"got rc {r.returncode}")
                ok = False
            else:
                print(f"  ✔ {label}: {'caught' if red else 'correctly not flagged'}")
    finally:
        open(target, "w").write(saved)
    print("✅ check_citations selftest: a phantom citation is caught and a real "
          "one is not" if ok else "⛔ check_citations selftest FAILED")
    sys.exit(0 if ok else 1)


# ══════════════════════════════════════════════════════════════════════════
# ⭐⭐ D130's SECOND INSTANCE: A DECISION NUMBER IS A CITATION TOO.
#
# `docs/DECISIONS.md` is cited by number from source comments and from `ci.yml`
# ("the kernel-time delta gate (D123)"), so a D-number is an identifier with
# inbound references — exactly what the rest of this file exists to protect.
# Nothing checked that a number names ONE decision.
#
# ⛔ IT ALREADY DID NOT.  `D123` heads two different sections: batch 24's VEX-128
# bucket (landed `5c01599`) and the delta gate (landed `ff5b59c`).  Two decisions,
# one number, and every one of the seven inbound references — `ci.yml`,
# `kernel_cost.py`, and five cross-references inside DECISIONS.md itself —
# resolves to the delta gate, so the other section is unreachable BY NUMBER.
#
# ⚠️ WHY IT IS RECORDED AND NOT RENUMBERED.  Renumbering the referenced one would
# break `ci.yml` and `kernel_cost.py`; renumbering the unreferenced one has no
# free in-sequence number to move to, since D124 was taken by the next batch the
# same day.  So the collision stays in the history and is FROZEN here instead:
# the assertion is EXACT, not a tolerance, so a third `D123` or any new duplicate
# fails.  ⛔ Do not add to `KNOWN_DUPLICATE_D`; a second entry means a number was
# reused after this gate existed, which is the thing it is here to stop.
KNOWN_DUPLICATE_D = {"123": 2}

# ⛔⛔ THE PATTERN MUST MATCH EVERY SHAPE THE FILE ACTUALLY USES, AND MUST SAY SO
# WHEN IT DOES NOT.  This read `^## D(\d+) ` — with a trailing SPACE — for its
# whole life, and four real headings (`## D38`, `## D39`, `## D40`, `## D41`) put
# their title on the NEXT line and so end at the digit.  The gate saw 141 of 145
# distinct numbers and printed a count that read like a total, so a second
# `## D38` would have been invisible to the one check this function exists to
# make.  ⇒ 🔑 A GATE THAT CANNOT SEE PART OF ITS SUBJECT REPORTS AGREEMENT ABOUT
# THE PART IT CAN SEE, and its own printed denominator is where that shows.
# The pattern now accepts both shapes, and `check_decision_numbers` REFUSES if any
# line beginning `## D<digits>` is not matched by it — so the next new heading
# shape fails loudly instead of silently leaving the census.
# [[feedback-unobserved-regions-report-agreement]]
D_HEAD = re.compile(r"^## D(\d+)(?=\s|$)")
D_HEAD_LOOSE = re.compile(r"^## D\d+.*$")


# ⛔ AND THE SAME DEFECT MIRRORED: a heading QUOTED INSIDE A FENCE IS NOT A
# HEADING.  D147 documents the bare `## D38` shape by showing it, and the first
# repair of this gate then read that quotation as a second claimant and refused —
# a gate that fails whenever the file explains the gate.  Fences are skipped;
# an ODD number of fence lines is itself a refusal, because "skip what is inside
# a fence" with an unterminated fence silently swallows the rest of the file,
# which is the blindness this whole entry is about, one layer down.
def _outside_fences(text):
    lines, out, inside, fences = text.split("\n"), [], False, 0
    for ln in lines:
        if ln.startswith("```"):
            fences += 1
            inside = not inside
            continue
        if not inside:
            out.append(ln)
    return out, fences


def check_decision_numbers():
    text = open("docs/DECISIONS.md").read()
    body, fences = _outside_fences(text)
    if fences % 2:
        print("⛔ DECISION NUMBERS — docs/DECISIONS.md has %d fence lines, an ODD "
              "number, so a fence is unterminated and every heading after it "
              "would be skipped in silence." % fences)
        return 1
    heads = [m.group(1) for m in (D_HEAD.match(l) for l in body) if m]
    loose = [l for l in body if D_HEAD_LOOSE.match(l)]
    if len(loose) != len(heads):
        seen = set()
        unmatched = [l for l in loose
                     if not D_HEAD.match(l) and not (l in seen or seen.add(l))]
        print("⛔ DECISION NUMBERS — %d lines begin `## D<digits>` but only %d are "
              "matched by the heading pattern, so the distinct-number census "
              "silently omits the rest." % (len(loose), len(heads)))
        for l in unmatched[:8]:
            print("    unmatched: %r" % l)
        return 1
    dups = {n: c for n, c in collections.Counter(heads).items() if c > 1}
    if dups != KNOWN_DUPLICATE_D:
        new = {n: c for n, c in dups.items() if KNOWN_DUPLICATE_D.get(n) != c}
        gone = {n: c for n, c in KNOWN_DUPLICATE_D.items() if dups.get(n) != c}
        print("⛔ DECISION NUMBERS — a number that names two decisions is a "
              "citation that resolves to whichever the reader finds first.")
        if new:
            print("    NEW duplicates: " + ", ".join(
                "D%s heads %d sections" % (n, c) for n, c in sorted(new.items())))
        if gone:
            print("    the known historical duplicate changed or was repaired: "
                  "%s — if it was repaired, delete it from KNOWN_DUPLICATE_D "
                  "rather than widening this gate." % sorted(gone.items()))
        return 1
    print("  \u2714 decision numbers: %d headings, %d distinct; the one known "
          "historical collision (D123) is frozen, not tolerated"
          % (len(heads), len(set(heads))))
    return 0


def selftest_decision_numbers():
    """⭐ RED FIRST, and the arm PLANTS A DUPLICATE IN A COPY OF THE SHIPPED FILE
    rather than in a fixture, so the gate is exercised against the real text it
    reads ([[feedback-a-gate-is-not-exempt-from-its-own-defect]])."""
    target = "docs/DECISIONS.md"
    saved = open(target).read()
    ok = True
    try:
        # arm 1: a NEW duplicate of an existing number
        first = re.search(r"^## D(\d+) .*$", saved, re.M)
        open(target, "w").write(saved + "\n## D%s \u2014 a planted second claimant\n"
                                % first.group(1))
        if check_decision_numbers() == 0:
            print("  \u2716 red arm SILENT: a duplicated D-number was not caught")
            ok = False
        else:
            print("  \u2714 red arm caught: a second section claiming D%s"
                  % first.group(1))
        # arm 2: a THIRD D123 — the known duplicate must not be a blanket pass
        open(target, "w").write(saved + "\n## D123 \u2014 a planted third claimant\n")
        if check_decision_numbers() == 0:
            print("  \u2716 red arm SILENT: the KNOWN duplicate absorbed a third "
                  "claimant, so the exemption is a tolerance and not a freeze")
            ok = False
        else:
            print("  \u2714 red arm caught: a THIRD D123 (the exemption is exact)")
        # ⭐ arm 3: THE SHAPE THAT WAS INVISIBLE.  A duplicate planted in the
        # BARE form (`## D38`, title on the next line) is the exact defect this
        # gate could not see; the arm exists so the repair cannot silently
        # regress. [[feedback-a-gate-is-not-exempt-from-its-own-defect]]
        bare = re.search(r"^## D(\d+)$", saved, re.M)
        if bare is None:
            print("  \u26a0 arm 3 SKIPPED: the shipped file no longer uses the "
                  "bare `## D<n>` heading shape, so this arm has no subject")
        else:
            open(target, "w").write(saved + "\n## D%s\n\na planted second "
                                    "claimant in the BARE heading shape\n"
                                    % bare.group(1))
            if check_decision_numbers() == 0:
                print("  \u2716 red arm SILENT: a duplicate in the BARE heading "
                      "shape was not caught")
                ok = False
            else:
                print("  \u2714 red arm caught: a second bare `## D%s`"
                      % bare.group(1))
        # ⭐ arm 5: a heading QUOTED INSIDE A FENCE is not a claimant.  The
        # control is arm 5b: the identical text OUTSIDE the fence must still be
        # caught, or this arm has merely switched the census off.
        # [[feedback-a-probe-must-create-its-condition]]
        dupn = re.search(r"^## D(\d+)", saved, re.M).group(1)
        open(target, "w").write(saved + "\n```\n## D%s\n```\n" % dupn)
        if check_decision_numbers() != 0:
            print("  \u2716 arm 5: a heading quoted inside a fence was counted as "
                  "a second claimant")
            ok = False
        else:
            print("  \u2714 arm 5: a heading inside a fence is not a claimant")
        open(target, "w").write(saved + "\n## D%s\n" % dupn)
        if check_decision_numbers() == 0:
            print("  \u2716 arm 5b CONTROL SILENT: the same heading OUTSIDE a "
                  "fence was not caught, so the fence rule switched the census off")
            ok = False
        else:
            print("  \u2714 arm 5b control: the same heading outside a fence IS "
                  "caught")
        # ⭐ arm 6: an UNTERMINATED fence must refuse, not swallow the rest.
        open(target, "w").write(saved + "\n```\n")
        if check_decision_numbers() == 0:
            print("  \u2716 arm 6 SILENT: an unterminated fence passed")
            ok = False
        else:
            print("  \u2714 arm 6: an unterminated fence refuses")
        # ⭐ arm 4: a heading shape the pattern does NOT know must REFUSE rather
        # than quietly drop out of the census — the failure mode this repair is
        # about.
        open(target, "w").write(saved + "\n## D9999:a shape with no separator\n")
        if check_decision_numbers() == 0:
            print("  \u2716 red arm SILENT: an unmatched `## D<digits>` line left "
                  "the census without a word")
            ok = False
        else:
            print("  \u2714 red arm caught: an unmatched heading shape refuses")
    finally:
        open(target, "w").write(saved)
    # the control: unplanted, it must pass
    if check_decision_numbers() != 0:
        print("  \u2716 control: the shipped DECISIONS.md fails its own gate")
        ok = False
    else:
        print("  \u2714 control: the shipped file passes unplanted")
    return ok


if "--selftest" in sys.argv:
    if not selftest_decision_numbers():
        sys.exit(1)
    selftest()

if check_decision_numbers():
    sys.exit(1)

bad, checked = [], 0
for src in SOURCES:
    text = open(src).read()
    for m in CITE.finditer(text):
        name, path = m.group(1), m.group(2)
        if not os.path.exists(path):
            continue                    # a path that is not a file we ship
        if src.endswith("check_citations.py"):
            continue                    # this file's own header quotes examples
        if path.startswith("docs/"):
            continue                    # prose documents declare nothing
        checked += 1
        if not occurs(path, name):
            line = text[:m.start()].count("\n") + 1
            bad.append((src, line, name, path))

if bad:
    print("⛔ CITATIONS THAT POINT AT NOTHING — a comment names something "
          "its file does not contain:")
    for src, line, name, path in bad:
        print(f"     {src}:{line}: `{name}` is cited as being in {path}, "
              f"and {path} never mentions it")
    print("   Either write the declaration or correct the sentence. A citation "
          "reads as the gate it names; one that points at nothing is the most "
          "persuasive false claim a comment can make.")
    sys.exit(1)

print(f"citation gate: CLEAN — {checked} named cross-references across "
      f"{len(SOURCES)} files, every one present where it is said to be")
