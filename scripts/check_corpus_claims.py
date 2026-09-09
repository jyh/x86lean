#!/usr/bin/env python3
"""A PROSE CLAIM THAT NAMES A DATA CORPUS, JOINED TO THE TOOL THAT CONSUMES IT.

WHY THIS EXISTS.  On 2026-09-09 this seat landed `b5d1522` — "QUEUE 4b-LOAD: the
loaded night is a load-~60 night, not a load-~12 one" — and pushed it to both
tiers.  It was FALSE.  The tool it was about, `unfolding_calibration.py`, takes
TWO corpora: `--walk` (a kernel-delta walk) and `--counters` (a deterministic-cost
walk).  "The loaded night" is the `--walk` input; the entry measured the
`--counters` input and reported the answer as if it were the other.  The
arithmetic was correct.  The FILE was wrong.

`ba3f701` retracted it and named the gap in one sentence:

    "the retracted entry passed every gate, because no gate here joins a prose
     claim about a corpus to the tool that consumes it."

⇒ 🔑 **A MEASUREMENT NAMES A FILE; ONLY THE CONSUMER'S CONTRACT SAYS WHETHER IT
IS THE RIGHT FILE.**  [[feedback-only-the-contract-says-which-file]]

⛔⛔ AND THE OBVIOUS DESIGN — "ask the tool, it will refuse the wrong corpus" —
WAS REFUTED BEFORE THIS GATE WAS WRITTEN.  Measured 2026-09-09 at the object:

    delta_repair_price.load_walk("docs/deterministic-cost-history-2026-09-05.jsonl")
      ⇒ ACCEPTED.  Returned a well-formed 12-commit walk.  No error, no warning.
    unfolding_calibration.load_counters("docs/kernel-delta-history-2026-09-04.jsonl", …)
      ⇒ returned ({}, {}) SILENTLY.

Both loaders are duck-typed on `commit`/`t`, which BOTH corpora carry.  So the
consumer could not referee its own contract: feeding it the wrong corpus produces
NUMBERS, not a refusal.  ⇒ 🔑 **A DUCK-TYPED LOADER REPORTS AGREEMENT ABOUT A
ROLE IT NEVER CHECKED** [[feedback-unobserved-regions-report-agreement]].  That is
why this file owns `corpus_role()` and the loaders IMPORT it (D148 §2's law: one
rule, one home — a referee invented beside a shipped rule disagrees in the
flattering direction).

WHAT IT CHECKS, IN THREE ARMS.

  A. EXISTENCE.  Every `docs/….jsonl` path written in citation form (i.e. WITH
     its `docs/` prefix) in gated prose must exist in the tree.  Citations inside
     a `*selftest*` function are FIXTURES, exempt, and every exemption is PRINTED
     with its site [[feedback-a-tool-has-no-concept-of-not-applicable]].

  B. ROLE.  Every committed `docs/*.jsonl` corpus classifies to EXACTLY ONE role
     by its required-key signature.  Zero roles and two roles are both REFUSALS,
     never a default [[feedback-a-classifiers-value-set-is-a-claim]].

  C. THE CLAIM JOIN.  A corpus path cited within `WINDOW` characters after a ROLE
     FLAG (`--walk`, `--counters`, …) is a claim that the corpus fills that role.
     The claim is checked against arm B's measured role.

⛔⛔ WHAT THIS GATE DOES NOT DO, STATED FIRST BECAUSE IT IS THE TEMPTING
OVER-CLAIM: **arm C would NOT have caught `b5d1522`.**  That commit message named
the tool and the corpus in ordinary English, with no role flag beside the path.
A gate that tried to parse "its second source" out of prose would be a heuristic
on a file whose whole subject is claims nobody verifies.  What closes `b5d1522`
is not arm C but the LOADER REFUSAL this file exports: `corpus_role()` is called
by `load_walk` and `load_counters`, so the same mix-up now fails AT THE MOMENT IT
WOULD HAVE PRODUCED NUMBERS, whatever the prose said.  Arm C catches the weaker,
commoner case — an explicit binding that has gone stale.

WHAT IT ALSO DOES NOT CHECK: that a corpus in the right ROLE is the right corpus.
Three kernel-delta walks share one role and one schema; only a figure joins them
(D151's "contended corpus, 14 readings" identifies `USER-CONTENDED` and nothing
else).  Arm A found one stale path today; a figure join is not built here and is
named as absent rather than implied.
"""
import ast, glob, json, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# ⛔ NO os.chdir AT IMPORT TIME. `load_walk` imports this module for `corpus_role`,
# and a module that moves its importer's cwd is a side effect nobody reads for.
# The entry points chdir; the rule does not.

# ── THE ROLES ────────────────────────────────────────────────────────────────
# A role is a REQUIRED-KEY SET that EVERY row must carry.  The sets were checked
# against all twelve committed corpora: each matches exactly one.
#
# ⚠️ `modules` (walk, plural) and `module` (counters, singular) differ by ONE
# CHARACTER, and a prefix match would collapse them.  Membership is exact-key.
# [[feedback-a-column-parser-is-tested-by-its-widest-datum]]
# ⛔⛔ `root` IS NOT IN THE WALK SIGNATURE, AND ITS REMOVAL IS THE FIRST THING THIS
# GATE GOT WRONG.  The first draft required it, because all eight committed walks
# carry it — i.e. the signature was fitted to the set it was validated on.  The
# held-out datum refuted it within the hour: `delta_repair_price._synth()` builds a
# genuine walk (commit/sweep/modules/decls) with no `root`, and `load_walk` REFUSED
# its own selftest fixture.  ⇒ 🔑 **A SIGNATURE MUST BE THE KEYS THE ROLE IS
# DEFINED BY, NOT THE KEYS ITS KNOWN MEMBERS HAPPEN TO CARRY** — `root` is
# provenance the loader never reads.  [[feedback-a-control-can-share-the-blind-spot]]
# The arm below pins it: the signature is checked against a fixture built by
# ANOTHER tool, so the rule and its test have independent origins
# [[feedback-two-readings-are-not-two-witnesses]].
ROLES = {
    "walk":       {"commit", "sweep", "modules", "decls"},
    "counters":   {"commit", "module", "ku", "hb"},
    "repeats":    {"rep", "modules", "decls", "t0", "t1"},
    "threads-ab": {"arm", "round", "threads", "type_checking_ms"},
    "ledger":     {"base", "head", "allowance", "budget_digest"},
}

# ── THE ROLE FLAGS ───────────────────────────────────────────────────────────
# flag -> (role, the site whose code or usage line DEFINES the binding).
# ⛔ The site is not decoration: arm C verifies each flag still occurs in its
# named file, so RENAMING a flag reds this gate instead of silently disarming
# the arm that reads it [[feedback-a-gate-named-by-a-literal-stops-seeing-renamed-work]].
ROLE_FLAGS = {
    "--walk":           ("walk",     "scripts/delta_repair_price.py"),
    "--counters":       ("counters", "scripts/unfolding_calibration.py"),
    "--kernel":         ("walk",     "scripts/deterministic_cost.py"),
    "--readings":       ("walk",     "scripts/user_cost_budget.py"),
    "--baseline":       ("walk",     "scripts/user_cost_budget.py"),
    "--repeat-scaling": ("repeats",  "scripts/delta_repair_price.py"),
}
WINDOW = 80          # chars after a role flag within which a path is its argument

CITE = re.compile(r'docs/[A-Za-z0-9_.-]+\.jsonl')
PROSE = ["docs/*.md", "docs/seals/*.md", "scripts/*.py", "scripts/*.sh",
         "README.md", "TRUSTBASE.md", "PROVENANCE.md"]


def corpus_role(rows):
    """(role, reason).  role is None on a REFUSAL, and the reason says which."""
    if not rows:
        return None, "empty corpus — 0 rows is not a role"
    hits = [r for r, req in ROLES.items() if all(req <= set(x) for x in rows)]
    if len(hits) == 1:
        return hits[0], "ok"
    if not hits:
        per = {r: sum(1 for x in rows if req <= set(x)) for r, req in ROLES.items()}
        near = ", ".join(f"{r} on {n}/{len(rows)} row(s)" for r, n in per.items() if n)
        return None, ("matches NO declared role" +
                      (f" (partial: {near} — a MIXED corpus is not a role)" if near else ""))
    return None, f"matches {len(hits)} roles at once: {sorted(hits)} — ambiguous, not a default"


def role_of_file(path):
    with open(path) as fh:
        rows = [json.loads(l) for l in fh if l.strip()]
    return corpus_role(rows)


def fixture_spans(py_path, text):
    """Line ranges of every function whose name contains 'selftest'."""
    try:
        tree = ast.parse(text)
    except SyntaxError:
        return []
    spans = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and "selftest" in node.name:
            spans.append((node.lineno, getattr(node, "end_lineno", node.lineno), node.name))
    return spans


def scan(files):
    """[(path, file, line, cited, in_fixture_named)] for every corpus citation."""
    out = []
    for f in files:
        if not os.path.exists(f):
            continue
        text = open(f, encoding="utf-8", errors="replace").read()
        spans = fixture_spans(f, text) if f.endswith(".py") else []
        for i, line in enumerate(text.splitlines(), 1):
            for m in CITE.finditer(line):
                fx = next((n for a, b, n in spans if a <= i <= b), None)
                out.append((m.group(0), f, i, line, fx))
    return out


def claim_sites(files):
    """[(flag, role_claimed, path, file, line)] — every explicit role binding."""
    out = []
    for f in files:
        if not os.path.exists(f):
            continue
        for i, line in enumerate(open(f, encoding="utf-8", errors="replace"), 1):
            for flag, (role, _site) in ROLE_FLAGS.items():
                for fm in re.finditer(re.escape(flag) + r'(?![A-Za-z0-9-])', line):
                    tail = line[fm.end():fm.end() + WINDOW]
                    for pm in CITE.finditer(tail):
                        out.append((flag, role, pm.group(0), f, i))
    return out


def run():
    os.chdir(ROOT)
    files = sorted({p for pat in PROSE for p in glob.glob(pat)})
    corpora = sorted(glob.glob("docs/*.jsonl"))
    if not corpora:
        print("⛔ no docs/*.jsonl corpora found. A gate that cannot find its "
              "subject reports a FAILURE, not a pass.")
        return 2
    if not files:
        print("⛔ no prose files found to scan. Absence of a subject is not a pass.")
        return 2

    bad = []
    # ── ARM B first: the roles the other arms are judged against ─────────────
    roles = {}
    for c in corpora:
        role, why = role_of_file(c)
        roles[c] = role
        if role is None:
            bad.append(f"⛔ ARM B  {c}: {why}")
    print(f"corpus roles ({len(corpora)} corpora): " +
          ", ".join(f"{os.path.basename(c)}={roles[c]}" for c in corpora[:3]) + " …")
    for r in sorted(ROLES):
        n = sum(1 for v in roles.values() if v == r)
        print(f"    {r:<11s} {n} corpus/corpora")

    # ── ARM A: existence ─────────────────────────────────────────────────────
    cites = scan(files)
    exempt = [c for c in cites if c[4] is not None and not os.path.exists(c[0])]
    for path, f, i, _line, fx in cites:
        if os.path.exists(path) or fx is not None:
            continue
        bad.append(f"⛔ ARM A  {f}:{i} cites {path}, which does not exist in the tree. "
                   f"A citation to a corpus READS AS the corpus.")
    print(f"arm A: {len(cites)} corpus citation(s) across {len(files)} prose file(s); "
          f"{len(exempt)} exempt as selftest fixture(s)")
    for path, f, i, _l, fx in exempt:
        print(f"    EXEMPT {f}:{i} cites {path} inside {fx}() — a fixture, not a claim")

    # ── ARM C: the claim join, plus the flags' own anchors ───────────────────
    for flag, (role, site) in sorted(ROLE_FLAGS.items()):
        if not os.path.exists(site):
            bad.append(f"⛔ ARM C  {flag}'s defining site {site} is gone; the binding is unanchored.")
        elif flag not in open(site, encoding="utf-8", errors="replace").read():
            bad.append(f"⛔ ARM C  {flag} no longer occurs in {site}. Either it was renamed "
                       f"(and this table is now blind to it) or the binding is dead.")
    claims = claim_sites(files)
    for flag, claimed, path, f, i in claims:
        actual = roles.get(path)
        if actual is None and os.path.exists(path):
            continue                       # already reported by arm B
        if not os.path.exists(path):
            continue                       # already reported by arm A
        if actual != claimed:
            bad.append(f"⛔ ARM C  {f}:{i} binds {path} to {flag}, which takes a "
                       f"{claimed!r} corpus — but that file measures as {actual!r}.")
    print(f"arm C: {len(claims)} explicit role binding(s) checked against "
          f"{len(ROLE_FLAGS)} flag(s), each anchored at its defining site")

    if bad:
        print()
        for b in bad:
            print(b)
        return 1
    print("corpus-claims gate: CLEAN")
    return 0


# ── THE RED ARMS ─────────────────────────────────────────────────────────────
# ⛔ Every arm below must FIRE — a plant nothing catches is a finding about the
# STATE, and an assertion no input reaches is not an arm at all
# [[feedback-probe-silence-has-two-causes]] [[feedback-an-implied-assertion-is-not-a-second-gate]].
_FIRED = set()


def ok(cond, what, plant=None):
    tag = "RED " if plant else "CTRL"
    if plant:
        _FIRED.add(plant)
    print(f"   {'ok  ' if cond else '⛔ FAIL'} [{tag}] {what}"
          + (f"   (plant: {plant})" if plant else ""))
    if not cond:
        selftest.failed = True


WALK_ROW = {"commit": "a", "sweep": 0, "modules": {}, "decls": {}, "root": "/", "t": 1}
CNT_ROW = {"commit": "a", "module": "M", "ku": {}, "hb": {}, "t": 1}


def selftest():
    os.chdir(ROOT)
    import scratch
    selftest.failed = False
    print("check_corpus_claims selftest")

    # ---- the classifier, both directions -----------------------------------
    ok(corpus_role([WALK_ROW, WALK_ROW])[0] == "walk",
       "CONTROL — a real walk row-set classifies as 'walk'")
    ok(corpus_role([CNT_ROW, CNT_ROW])[0] == "counters",
       "CONTROL — a real counters row-set classifies as 'counters'")
    r, why = corpus_role([{"commit": "a", "t": 1}])
    ok(r is None and "NO declared role" in why,
       "a row carrying only the shared keys matches NO role and is REFUSED, "
       "rather than falling to whichever role is listed first",
       plant="no-role")
    r, why = corpus_role([dict(WALK_ROW, **CNT_ROW)])
    ok(r is None and "2 roles" in why,
       "a row satisfying TWO signatures is REFUSED as ambiguous, not resolved by order",
       plant="two-roles")
    r, why = corpus_role([WALK_ROW, CNT_ROW])
    ok(r is None and "MIXED" in why,
       "a MIXED corpus (one walk row, one counters row) is refused, and the "
       "refusal names how many rows matched each — a role is a property of the "
       "CORPUS, not of its first line",
       plant="mixed")
    ok(corpus_role([])[0] is None,
       "an EMPTY corpus is a refusal, not a role", plant="empty")
    # the one-character near-collision the signatures are most likely to lose
    ok(corpus_role([dict(CNT_ROW, sweep=0, decls={}, root="/")])[0] == "counters",
       "a counters row carrying `module` (singular) plus every OTHER walk key is "
       "still 'counters' — `modules` vs `module` is an exact-key test, not a prefix",
       plant="module-vs-modules")

    # ---- the loaders, which are the half that closes b5d1522 ---------------
    sys.path.insert(0, os.path.join(ROOT, "scripts"))
    import delta_repair_price as drp
    import unfolding_calibration as uc
    # the held-out control that refuted the first signature, kept as an arm
    ok(corpus_role(drp._synth(n_commits=2))[0] == "walk",
       "CONTROL — a walk built by ANOTHER tool (delta_repair_price._synth, which "
       "writes no `root`) classifies as 'walk'. The signature and its test have "
       "independent origins; the first draft required `root` and refused this")
    walks = sorted(glob.glob("docs/kernel-delta-history-2026-*.jsonl"))
    cnts = sorted(glob.glob("docs/deterministic-cost-history-*.jsonl"))
    ok(bool(walks) and bool(cnts),
       f"CONTROL — the two real corpora the loader arms need are present "
       f"({len(walks)} walk, {len(cnts)} counters); without them the arms below "
       f"would pass by being unreachable")
    if walks and cnts:
        ok(len(drp.load_walk(walks[0])["order"]) > 0,
           "CONTROL — load_walk still ACCEPTS a real kernel-delta walk")
        try:
            drp.load_walk(cnts[0])
            fired = False
        except SystemExit:
            fired = True
        except ValueError:
            fired = True
        ok(fired,
           "load_walk REFUSES a deterministic-cost corpus. Measured before this "
           "gate existed: it ACCEPTED one and returned a well-formed 12-commit "
           "walk. That silent acceptance is the mechanism of b5d1522.",
           plant="walk-loader-wrong-role")
        ok(len(uc.load_counters(cnts[0], "Tests.Coverage", [])[0]) > 0,
           "CONTROL — load_counters still ACCEPTS a real deterministic-cost corpus")
        try:
            uc.load_counters(walks[0], "Tests.Coverage", [])
            fired = False
        except (SystemExit, ValueError):
            fired = True
        ok(fired,
           "load_counters REFUSES a kernel-delta walk. Measured before this gate: "
           "it returned ({}, {}) SILENTLY — an empty answer, not a refusal "
           "[[feedback-an-unparseable-gate-file-reports-failure-not-absence]]",
           plant="counters-loader-wrong-role")

    # ---- arm A: existence, and its OVER-REFUSAL control --------------------
    d = scratch.mkdtemp("x86lean-corpusclaims-")
    live = os.path.join(d, "live.py")
    open(live, "w").write(
        "# it reads docs/absolutely-not-here.jsonl for the answer\n"
        "def selftest():\n"
        "    # a fixture: docs/also-not-here.jsonl\n"
        "    pass\n")
    hits = [c for c in scan([live]) if not os.path.exists(c[0]) and c[4] is None]
    ok(len(hits) == 1 and hits[0][0] == "docs/absolutely-not-here.jsonl",
       "a citation of an ABSENT corpus in live prose is caught",
       plant="absent-corpus")
    ok(any(c[0] == "docs/also-not-here.jsonl" and c[4] == "selftest" for c in scan([live])),
       "CONTROL — the SAME absent citation inside a selftest() is recognised as a "
       "fixture and exempted, so the gate does not cry wolf on a red arm "
       "[[feedback-under-claims-are-unpoliced]]")

    # ---- arm C: the claim join, both directions ----------------------------
    if walks and cnts:
        mis = os.path.join(d, "mis.md")
        open(mis, "w").write(f"run it with --counters {walks[0]} today\n")
        cl = claim_sites([mis])
        ok(len(cl) == 1 and cl[0][1] == "counters" and roles_probe(cl[0][2]) == "walk",
           "a WALK corpus bound to --counters is detected as a role mismatch",
           plant="claim-role-mismatch")
        good = os.path.join(d, "good.md")
        open(good, "w").write(f"run it with --counters {cnts[0]} today\n")
        cl = claim_sites([good])
        ok(len(cl) == 1 and roles_probe(cl[0][2]) == cl[0][1],
           "CONTROL — the CORRECT binding is not flagged")
        far = os.path.join(d, "far.md")
        open(far, "w").write("--counters " + "x" * (WINDOW + 10) + f" {walks[0]}\n")
        ok(not claim_sites([far]),
           f"CONTROL — a path more than WINDOW={WINDOW} chars from the flag is NOT "
           f"read as its argument")

    n_expected = 9
    ok(len(_FIRED) == n_expected,
       f"CONTROL — {len(_FIRED)} distinct red arms fired of {n_expected} declared. "
       f"A broken harness reds every plant; the count is what says the arms are "
       f"distinct [[feedback-a-plant-probes-control-comes-first]]")
    print("SELFTEST " + ("⛔ FAILED" if selftest.failed else "ok"))
    return 1 if selftest.failed else 0


def roles_probe(path):
    return role_of_file(path)[0] if os.path.exists(path) else None


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        sys.exit(selftest())
    sys.exit(run())
