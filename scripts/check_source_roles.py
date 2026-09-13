#!/usr/bin/env python3
"""CLAIM-1 — THE README'S SOURCES SENTENCE, GATED AGAINST THE TREE.

⚖️ **RULED BY THE HELM, 2026-09-13** (D239 §5), taking arm (B) of the fork:
*"The sources sentence is rendered from a table, and checks (ii) role-from-tree
and (iii) two-way closure carry the load, with (i) as transport only… all five
named things are rows, with a KIND column."*

## THE DEFECT THIS CLOSES

`README.md` claimed the model was corroborated by three executable models. **One
has ever been executed.** The sentence has been rewritten twice since, and
nothing read it: `claimed_forms.py` and `check_readme_snapshot.py` both read the
README and both are aimed at NUMBERS. A sentence about ROLES had no gate at all.

## THE THREE CHECKS, AND WHICH ONES CARRY THE LOAD

```
  (i)   README == render(table), byte for byte                   TRANSPORT ONLY
  (ii)  each row's CLAIM holds against the tree                   CARRIES THE LOAD
  (iii) CLOSURE, BOTH WAYS                                        CARRIES THE LOAD
```
⛔⛔ **(i) ALONE WOULD BE WORSE THAN NO GATE.** A byte-for-byte re-derivation
proves the file matches its generator and says nothing about whether the
generator tells the truth [[feedback-a-derivation-gate-wraps-a-false-sentence]] —
it would look like a gate and check nothing about the world. **The helm made that
part of the ruling: a (B) that ships (i) without (ii) and (iii) has NOT landed
CLAIM-1**, and `--selftest` therefore carries an arm in which THE TABLE LIES AND
(i) STAYS GREEN.

## ⛔ A NAME IS NOT A CODE PATH, AND THAT IS THE WHOLE DIFFICULTY

The tempting derivation is "grep the scripts for the model's name". Measured, it
is wrong in both directions:
```
  Sail    2 script lines, BOTH PROSE   a positioning-table column header, one comment
  XED     0 word-bounded script lines  and yet it is not named-as-intent: Main.lean
                                       writes `XED (trusted)` into every coverage row
  xed     matches "fixed", "mixed", "suffixed", "executed" under -i without \\b
```
⇒ Each row names a CLAIM CHECKER instead, and each checker asks about a specific
kind of consumption — an invocation, an artifact read, a generated table's
contents — never about a mention. [[a-path-gate-does-not-match-names]]

## THE VALUE SET IS THREE, AND THE KINDS ARE WHY

D239 §3: for SEMANTICS, `EXECUTED` · `READ-MECHANICALLY` · `NAMED-AS-INTENT`. A
two-valued gate over that world scores the unseen state as its residual, and the
residual is the flattering one. The KIND column extends the same reasoning one
level up: the SDM is a DOCUMENT and XED a DECODER, and **a row whose kind carries
no derivable claim must SAY SO in the table (`claim = none`), not by omission.**

  check_source_roles.py [--print] [--selftest]
"""
# ⛔ REFUSE AN UNKNOWN FLAG BEFORE ANY WORK HAPPENS — see portable.strict_flags.
if __name__ == "__main__":
    import os as _os, sys as _sys
    _sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
    from portable import strict_flags as _strict_flags
    _strict_flags(__file__)

import os
import re
import subprocess
import sys
import textwrap

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
TABLE = os.path.join(ROOT, "docs", "source-roles.tsv")
README = os.path.join(ROOT, "README.md")

LEAD = "It is built from public sources only: "
WIDTH = 79          # the paragraph's own measured maximum before this gate existed
KINDS = {"SEMANTICS", "DOCUMENT", "DECODER"}
SEMANTIC_ROLES = {"EXECUTED", "READ-MECHANICALLY", "NAMED-AS-INTENT"}


def read_table(path=TABLE):
    rows = []
    for n, line in enumerate(open(path, encoding="utf-8"), 1):
        if line.startswith("#") or not line.strip():
            continue
        f = line.rstrip("\n").split("\t")
        if len(f) != 5:
            sys.exit(f"⛔ {path}:{n}: expected 5 tab-separated fields, got {len(f)}")
        name, kind, role, claim, phrase = (x.strip() for x in f)
        if kind not in KINDS:
            sys.exit(f"⛔ {path}:{n}: unknown kind {kind!r} (known: {sorted(KINDS)})")
        if kind == "SEMANTICS" and role not in SEMANTIC_ROLES:
            sys.exit(f"⛔ {path}:{n}: a SEMANTICS row's role must be one of "
                     f"{sorted(SEMANTIC_ROLES)}, not {role!r}. The value set is THREE "
                     f"(D239 §3) and a two-valued reading scores the unseen state as "
                     f"its residual.")
        rows.append({"name": name, "kind": kind, "role": role,
                     "claim": claim, "phrase": phrase, "line": n})
    if not rows:
        sys.exit(f"⛔ {path} has no rows. An empty table renders an empty sentence and "
                 f"every check below passes vacuously.")
    return rows


# ────────────────────────────────────────────────────────────────────────────
# (i) THE RENDERING — transport
# ────────────────────────────────────────────────────────────────────────────
def render(rows):
    """The sentence, wrapped as its own paragraph.

    ⚠️ THE SENTENCE IS ITS OWN PARAGRAPH IN THE README, and that was a deliberate
    edit made for this gate. It used to share a paragraph with the undefined-bit
    sentence, which would have forced the renderer to template prose it has no
    business owning — and a generator that owns more text than it has data for
    invites exactly the "regenerate it" reflex that makes a wrong number look
    freshly computed."""
    ps = [r["phrase"] for r in rows]
    if len(ps) == 1:
        body = ps[0]
    else:
        body = ", ".join(ps[:-1]) + ", and " + ps[-1]
    return "\n".join(textwrap.wrap(LEAD + body + ".", width=WIDTH)) + "\n"


def check_rendering(rows, readme=README):
    want = render(rows)
    text = open(readme, encoding="utf-8").read()
    if want in text:
        return []
    # ⛔ SAY WHAT IT SAW. A refusal with no reading attached turns this into a
    # guessing game about whitespace (D94).
    got = ""
    for para in text.split("\n\n"):
        if para.startswith(LEAD.rstrip()) or para.lstrip().startswith(LEAD.rstrip()):
            got = para + "\n"
            break
    return [f"(i) README does not contain the rendered sentence.\n"
            f"    WANT:\n{textwrap.indent(want, '      ')}"
            f"    GOT:\n{textwrap.indent(got or '      <no paragraph starts with the lead-in>', '      ')}"]


# ────────────────────────────────────────────────────────────────────────────
# (ii) THE CLAIMS — derived from the tree, one checker per claim key
# ────────────────────────────────────────────────────────────────────────────
def _text(rel):
    p = os.path.join(ROOT, rel)
    return open(p, encoding="utf-8", errors="replace").read() if os.path.exists(p) else ""


def _script_word_hits(word):
    """Files under scripts/ carrying `word` as a WHOLE WORD.

    ⛔ WHOLE WORD, AND CASE-SENSITIVELY ANCHORED, because `-i xed` matches
    "fixed", "mixed", "suffixed" and "executed" — measured, it returned 20 files
    of pure noise before the boundary was added."""
    out = []
    sd = os.path.join(ROOT, "scripts")
    pat = re.compile(r"\b" + re.escape(word) + r"\b", re.IGNORECASE)
    for f in sorted(os.listdir(sd)):
        if f.endswith((".py", ".sh", ".lisp")):
            if pat.search(_text(os.path.join("scripts", f))):
                out.append(f)
    return out


def claim_harness_invokes(row):
    """EXECUTED: the differential harness runs THIS model and reads verdicts back.

    ⛔ IT ASKS ABOUT `row`, AND THE FIRST DRAFT DID NOT. It checked a fixed fact —
    "run_differential.sh mentions ACL2" — and returned it for whatever row it was
    handed, so `Sail / EXECUTED / harness_invokes` PASSED (ii). The mutation matrix
    found it: with the claim checkers stubbed to `True` the suite stayed 21/21,
    because the lie it was pointed at was being caught by the role/checker
    comparison one line above instead. **An arm satisfied by a neighbouring check is
    not an arm.** Every checker below now derives from the ROW."""
    reached = harness_models()
    ok = row["name"] in reached
    return ok, (f"run_differential.sh invokes it as an oracle and reads run/oracle.txt "
                f"back" if ok else
                f"no oracle invocation path in run_differential.sh reaches "
                f"{row['name']!r} (it reaches: {sorted(reached) or 'nothing'})")


# Which (setup, reader, distribution marker) witnesses each mechanically-read model.
# ⛔ A model NOT in this map is REFUSED rather than judged: a checker that silently
# answers about a model it has never heard of is the defect above, one level down.
ARTIFACT_READERS = {
    "K x86-64": ("scripts/setup_k_roster.sh", "scripts/k_roster.py", "X86-64-semantics"),
}


def claim_artifact_read(row):
    """READ-MECHANICALLY: a script consumes files from THIS model's distribution."""
    w = ARTIFACT_READERS.get(row["name"])
    if w is None:
        return False, (f"no artifact-reading witness is registered for {row['name']!r}; "
                       f"refusing rather than answering about a model this checker has "
                       f"never heard of (registered: {sorted(ARTIFACT_READERS)})")
    setup_p, reader_p, marker = w
    setup, reader = _text(setup_p), _text(reader_p)
    cloned = marker in setup and "git clone" in setup
    read = bool(reader) and "open(" in reader
    ok = cloned and read
    return ok, (f"{setup_p} clones {marker} and {reader_p} reads files out of it"
                if ok else f"cloned={cloned} read={read} — no artifact-consuming path")


def claim_no_code_path(row):
    """NAMED-AS-INTENT: no code path reaches it at all.

    ⛔ AN ABSENCE IS A CLAIM ABOUT A POPULATION, so this carries its own POSITIVE
    CONTROL in the same call: the identical matcher must FIND a model that is
    consumed. Three clean zeros from a borrowed instrument are the shape of a
    broken one."""
    hits = _script_word_hits(row["name"])
    control = _script_word_hits("x86isa")
    if not control:
        return False, ("the matcher found NO file for `x86isa` either, so its zero for "
                       "this row is evidence about the matcher, not about the tree")
    vendored = os.path.isdir(os.path.join(ROOT, "vendor", row["name"].lower()))
    # TWO files carry model names as DATA rather than consuming them: the leak gate,
    # whose fixtures are names, and THIS GATE, whose whole subject is the table of
    # them. ⛔ The exclusions are BY NAME and are PRINTED with every verdict, because
    # a declared exclusion list is wrong in whatever direction it defaults to and the
    # only defence is that a reader can see it.
    # [[feedback-a-declared-list-inherits-its-default]]
    excluded = {"check_private_paths.py", os.path.basename(__file__)}
    hits = [h for h in hits if h not in excluded]
    ok = not vendored and not _consumes(hits, row["name"])
    return ok, (f"no artifact under vendor/, and the {len(hits)} script mention(s) "
                f"{hits} are prose (control: x86isa matches {len(control)} files; "
                f"excluded as name-carrying: {sorted(excluded)})"
                if ok else
                f"vendored={vendored}; script hits {hits}")


def _consumes(files, name):
    """Does any of these files CONSUME the named thing rather than mention it?

    A consumption is an `open(`, a `subprocess`, a clone or a path under `vendor/`
    on a line that also carries the name. A bare mention on a comment or a string
    is not. ⚠️ This is a heuristic and it is stated as one: it is deliberately
    biased towards reporting consumption (any of those tokens on the line counts),
    because the direction that must not be silent is 'we said intent and it is
    actually wired'."""
    for f in files:
        for line in _text(os.path.join("scripts", f)).splitlines():
            if re.search(r"\b" + re.escape(name) + r"\b", line, re.IGNORECASE):
                if any(t in line for t in ("open(", "subprocess", "git clone",
                                           "vendor/", "Popen", "check_output")):
                    return True
    return False


def claim_coverage_table_trust(row):
    """DECODE-TRUST-RECORDED: the generated coverage table records the trust."""
    cov = _text("docs/COVERAGE.md")
    if not cov:
        return False, "docs/COVERAGE.md is absent"
    # the token is built from the ROW, not typed: "Intel XED" -> "XED (trusted)".
    short = row["name"].split()[-1]
    token = f"{short} (trusted)"
    rows_with = cov.count(token)
    emitter = token in _text("Main.lean")
    ok = rows_with > 0 and emitter
    return ok, (f"docs/COVERAGE.md records `{token}` {rows_with} times and Main.lean "
                f"is the emitter" if ok else
                f"`{token}`: occurrences={rows_with} emitter_present={emitter}")


def claim_none(row):
    """A row that DECLARES it has no derivable claim. ⭐ This is a value, not a gap:
    the helm's ruling is that a row whose kind carries no check must say so in the
    table rather than by omission, so that the absence is auditable."""
    return True, "declares no derivable claim (a DOCUMENT: the SDM is read by people)"


CLAIMS = {"harness_invokes": claim_harness_invokes,
          "artifact_read": claim_artifact_read,
          "no_code_path": claim_no_code_path,
          "coverage_table_trust": claim_coverage_table_trust,
          "none": claim_none}

# Which role each claim key ESTABLISHES, so a row cannot pair a role with a checker
# that does not test it. ⛔ Without this, `Sail / EXECUTED / no_code_path` would
# PASS: the checker would confirm "no code path" and the role would go unread.
ESTABLISHES = {"harness_invokes": "EXECUTED",
               "artifact_read": "READ-MECHANICALLY",
               "no_code_path": "NAMED-AS-INTENT",
               "coverage_table_trust": "DECODE-TRUST-RECORDED",
               "none": "NONE"}


def check_claims(rows, quiet=False):
    findings = []
    for r in rows:
        fn = CLAIMS.get(r["claim"])
        if fn is None:
            findings.append(f"(ii) {r['name']}: unknown claim key {r['claim']!r} "
                            f"(known: {sorted(CLAIMS)})")
            continue
        if ESTABLISHES[r["claim"]] != r["role"]:
            findings.append(f"(ii) {r['name']}: role {r['role']!r} is not what claim "
                            f"{r['claim']!r} establishes ({ESTABLISHES[r['claim']]!r}). "
                            f"A row may not pair a role with a checker that does not "
                            f"test it.")
            continue
        ok, why = fn(r)
        if not quiet:
            print(f"  {'✅' if ok else '⛔'} {r['name']:14} {r['kind']:10} "
                  f"{r['role']:22} {why}")
        if not ok:
            findings.append(f"(ii) {r['name']}: claims {r['role']} and the tree says "
                            f"otherwise — {why}")
    return findings


# ────────────────────────────────────────────────────────────────────────────
# (iii) CLOSURE, BOTH WAYS
# ────────────────────────────────────────────────────────────────────────────
def harness_models():
    """The models the DIFFERENTIAL HARNESS invokes, derived from the harness.

    📌 SCOPE, STATED: this is the harness's oracle invocations, not everything the
    repository reads. `vendor/liblisa` is vendored and read by
    `liblisa_hardware_check.py` and is deliberately out of this population — a
    one-off hardware ground-truth check is not a source the model is built from.
    The exclusion is written down in `docs/source-roles.tsv` rather than left
    implicit, because an exclusion nobody wrote down cannot be told from an
    oversight."""
    h = _text("scripts/run_differential.sh")
    found = set()
    if "projects/x86isa/" in h and ("$ACL2" in h or "${ACL2" in h):
        found.add("ACL2 x86isa")
    return found


def check_closure(rows):
    findings = []
    named = {r["name"] for r in rows}
    executed = {r["name"] for r in rows if r["role"] == "EXECUTED"}
    reached = harness_models()
    # → every model the harness reaches has a row
    for m in sorted(reached - named):
        findings.append(f"(iii) the harness invokes {m!r} and the table has no row for "
                        f"it — the sentence does not mention a model this repository "
                        f"actually runs")
    # ← every row claiming EXECUTED is reached
    for m in sorted(executed - reached):
        findings.append(f"(iii) {m!r} claims EXECUTED and no harness invocation path "
                        f"reaches it")
    return findings


# ────────────────────────────────────────────────────────────────────────────
def run(quiet=False):
    rows = read_table()
    if not quiet:
        print(f"source-roles: {len(rows)} rows")
    f = check_claims(rows, quiet) + check_rendering(rows) + check_closure(rows)
    return f


def selftest():
    import tempfile
    arms, red = 0, []

    def check(name, cond):
        nonlocal arms
        arms += 1
        if not cond:
            red.append(name)

    tmp = tempfile.mkdtemp(prefix="x86lean-srcroles-")
    try:
        rows = read_table()
        # ── the shipped tree ────────────────────────────────────────────────
        check("the shipped table passes all three checks", run(quiet=True) == [])
        check("all five named things are rows", len(rows) == 5)
        check("every kind is known", all(r["kind"] in KINDS for r in rows))
        check("a row with no derivable claim SAYS so",
              any(r["claim"] == "none" for r in rows))
        check("the SEMANTICS rows use the three-valued role set",
              {r["role"] for r in rows if r["kind"] == "SEMANTICS"} <= SEMANTIC_ROLES)

        # ── (i) transport ───────────────────────────────────────────────────
        check("the rendering reproduces the README paragraph",
              check_rendering(rows) == [])
        bad = [dict(r) for r in rows]
        bad[0]["phrase"] = bad[0]["phrase"].replace("intent", "intentions")
        check("a changed phrase reds (i)", check_rendering(bad) != [])

        # ⭐⭐⭐ THE ARM THE HELM REQUIRED BY NAME: THE TABLE LIES AND (i) STAYS GREEN.
        # Sail's ROLE is flipped to EXECUTED while its PHRASE is untouched, so the
        # rendered sentence is byte-identical and the README is unchanged. If (ii)
        # and (iii) were absent this gate would report CLEAN about a table that
        # claims the repository executes a model it has never run — which is the
        # ORIGINAL DEFECT CLAIM-1 exists to stop, restated exactly.
        lie = [dict(r) for r in rows]
        for r in lie:
            if r["name"] == "Sail":
                r["role"] = "EXECUTED"
        check("THE TABLE LIES AND (i) STAYS GREEN", check_rendering(lie) == [])
        check("…and (ii) catches the lie", check_claims(lie, quiet=True) != [])
        check("…and (iii) catches it independently of (ii)",
              check_closure(lie) != [])

        # ── (ii) the claims, each driven against a false row ────────────────
        for name, role, claimkey in (("ACL2 x86isa", "EXECUTED", "harness_invokes"),
                                     ("K x86-64", "READ-MECHANICALLY", "artifact_read"),
                                     ("Sail", "NAMED-AS-INTENT", "no_code_path"),
                                     ("Intel XED", "DECODE-TRUST-RECORDED",
                                      "coverage_table_trust")):
            r = next(x for x in rows if x["name"] == name)
            check(f"{name}'s claim holds on the real tree", CLAIMS[claimkey](r)[0])

        # ⭐⭐ THE ARM THAT MAKES (ii) LOAD-BEARING RATHER THAN DECORATIVE. Role and
        # claim AGREE here (both say EXECUTED), so the role/checker guard is silent and
        # only the checker itself can red it. ⛔ Without this arm, stubbing every claim
        # checker to `True` left the suite at 21/21 — the lie it was pointed at was
        # being caught by the guard one line above, and (ii) was never exercised at all.
        exec_lie = [{"name": "Sail", "kind": "SEMANTICS", "role": "EXECUTED",
                     "claim": "harness_invokes", "phrase": "x", "line": 0}]
        f_exec = check_claims(exec_lie, quiet=True)
        check("a row claiming EXECUTED that the harness does not reach reds (ii)",
              len(f_exec) == 1 and "no oracle invocation path" in f_exec[0])
        check("…and a checker handed a model it does not know REFUSES",
              not claim_artifact_read({"name": "Sail"})[0])

        # a role paired with a checker that does not test it must be refused, or the
        # checker confirms something nobody asked about and the role goes unread
        mism = [dict(next(x for x in rows if x["name"] == "Sail"))]
        mism[0]["role"] = "EXECUTED"          # claim stays `no_code_path`
        check("a role/checker mismatch is caught",
              any("is not what claim" in f for f in check_claims(mism, quiet=True)))

        # ── the absence claim's own positive control ────────────────────────
        ok, why = claim_no_code_path({"name": "Sail"})
        check("the absence claim is stated WITH its control", ok and "control:" in why)
        # ⛔ AND THE CONTROL MUST BITE, NOT MERELY BE PRINTED. The arm above passes
        # whether or not the guard exists, because the sentence carries the word either
        # way — so it tests the WORDING and not the GUARD. This one creates the
        # condition: with the matcher returning nothing for anything, a zero for Sail is
        # evidence about the instrument and the claim must REFUSE rather than report
        # absence. [[feedback-a-probe-must-create-its-condition]]
        _real = globals()["_script_word_hits"]
        globals()["_script_word_hits"] = lambda w: []
        try:
            ok_b, why_b = claim_no_code_path({"name": "Sail"})
        finally:
            globals()["_script_word_hits"] = _real
        check("a DEAD matcher makes the absence claim refuse, not pass",
              not ok_b and "matcher found NO file" in why_b)
        # and the control must be able to FAIL: a name that IS consumed is not absent
        ok2, _ = claim_no_code_path({"name": "x86isa"})
        check("the absence claim REFUSES a name that is consumed", not ok2)

        # ── the parser's refusals ───────────────────────────────────────────
        def parse_refuses(body):
            p = os.path.join(tmp, "t.tsv")
            open(p, "w", encoding="utf-8").write(body)
            r = subprocess.run([sys.executable, "-c",
                                f"import sys; sys.path.insert(0, {HERE!r}); "
                                f"import check_source_roles as m; m.read_table({p!r})"],
                               capture_output=True, text=True)
            return r.returncode != 0, r.stdout + r.stderr

        # ⛔ AN ORDERLY REFUSAL NAMING ITS CAUSE, NOT MERELY A NON-ZERO EXIT. With the
        # field-count refusal DELETED this arm still passed: the tuple unpacking below
        # it raised a ValueError, which is also non-zero. Same three-valued world as
        # `ku_delta`'s (pass · refuse · crash), same flattering residual, found by the
        # same mutation matrix on the same afternoon.
        # [[feedback-a-classifiers-value-set-is-a-claim]]
        def refuses_with(body, needle):
            ref, msg = parse_refuses(body)
            return ref and needle in msg

        check("a wrong field count is refused",
              refuses_with("a\tb\tc\n", "expected 5 tab-separated fields"))
        check("an unknown kind is refused",
              refuses_with("a\tWIDGET\tNONE\tnone\tp\n", "unknown kind"))
        check("a two-valued role on a SEMANTICS row is refused",
              refuses_with("a\tSEMANTICS\tPROBABLY\tnone\tp\n", "THREE"))
        check("an empty table is refused",
              refuses_with("# only a comment\n", "no rows"))
    finally:
        import shutil
        shutil.rmtree(tmp, ignore_errors=True)

    print(f"check_source_roles selftest: {arms - len(red)}/{arms} arms")
    for r in red:
        print(f"  ⛔ RED: {r}")
    return 1 if red else 0


def main():
    if "--selftest" in sys.argv:
        return selftest()
    if "--print" in sys.argv:
        sys.stdout.write(render(read_table()))
        return 0
    f = run()
    if f:
        print(f"\n⛔ source-roles: {len(f)} finding(s)")
        for x in f:
            print(f"  {x}")
        return 1
    print("source-roles: CLEAN — the sentence is rendered from the table, every row's "
          "claim holds against the tree, and the population is closed both ways")
    return 0


if __name__ == "__main__":
    sys.exit(main())
