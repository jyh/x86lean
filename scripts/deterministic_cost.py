#!/usr/bin/env python3
"""THE DETERMINISTIC-COST WALK — which zero-noise quantity, if any, is a proxy
for the noisy one the kernel-delta gate is built on?  (D146)

⭐⭐ WHY THIS EXISTS.  `scripts/kernel_delta.py` gates the CHANGE in kernel
`type checking` time, and D141/D142 measured what that instrument can resolve:
the SAME COMMIT on both sides invented a −2,150 ms delta on a unit with a
1,980 ms budget, and the same base tree read 27,500 and 24,500 ms an hour apart.
A gate cannot be tighter than its instrument, and this one is not.

TWO CANDIDATES ARE MEASURED, in one pass per commit each:

  `hb`  ELABORATOR HEARTBEATS — `IO.getNumHeartbeats`, the counter `maxHeartbeats`
        is checked against.  ⛔ **REFUTED (D146), and kept here only as the
        control that shows what a blind proxy looks like.**  Heartbeats measure
        the SOURCE elaborated, not the DATA reduced: at three data sizes over a
        byte-identical checked module the count is the SAME INTEGER (12,084)
        while kernel `type checking` grows 5.6x.  In the corpus, a batch that
        added thirteen vectors moved it by −12 out of 4.9 million.

  `ku`  KERNEL UNFOLDINGS — the `[kernel] unfolded declarations` counters Lean
        reports under `set_option diagnostics true`.  Exactly linear in the data
        (6,002 / 12,002 / 24,002 on the same three arms), exactly zero on all
        five commits in the corpus that change no `.lean` file, at machine loads
        from 13 to 95.  ⚠️ Machine independence is UNMEASURED and no budget is
        derived; do not gate on it before both.

⛔⛔ AND THE CLAIM A PROXY LIVES OR DIES BY.  Heartbeats are charged in the
ELABORATOR; the gated quantity is the KERNEL's.  `decide` does the work TWICE
— once elaborating
(charged, deterministic) and once in the kernel (timed, uncharged) — and whether
the two track each other ACROSS THE CHANGES THIS GATE EXISTS TO CATCH is the
whole question.  This walk measures it on the twelve real commits already in
`docs/kernel-delta-history-2026-09-04.jsonl`, so the two columns come from the
same commits and can be differenced pair by pair.

## HOW A HEARTBEAT COUNT IS TAKEN

Lean has no per-declaration heartbeat report, so this makes one: it rewrites the
module's source, wrapping every top-level declaration in a `hb_count "<name>" in`
command that reads `IO.getNumHeartbeats` either side of `elabCommand` and logs
the difference.  The rewritten file is elaborated with `lake env lean --json`
against the worktree's own build, and the log messages are read back.

⛔ THE WRAPPER MUST PRECEDE THE WHOLE COMMAND, not the `theorem` line: a doc
comment and a `set_option … in` prefix are PART of the declaration's syntax, and
a wrapper spliced between them does not parse.  The rewriter walks backward over
exactly those shapes and REFUSES rather than guessing.

⛔ THE JOIN BACK IS BY POSITION RANGE, NOT BY MESSAGE ORDER.  Lean elaborates
commands in parallel here (`user` time is ~2x `real`), so emission order is not
evidence of which declaration a profiler message belongs to.  Each `HBCOUNT`
message carries the [pos, endPos] of the whole wrapped command; a message that
lands in no range, or in two, is REPORTED and not silently attributed.

⭐ THE INSTRUMENT'S OWN ZERO IS ASSERTED, NOT ASSUMED.  `--determinism` re-runs
the first commit and requires BOTH metric maps to be IDENTICAL, declaration by
declaration.  Determinism is the entire value of any of these proposals and it
arrived as an inherited sentence about Lean.
[[feedback-inherited-diagnosis-is-a-hypothesis]]

⛔⛔ AND THAT ARM IS NOT SUFFICIENT — IT SHARES THE BLIND SPOT IT IS MEANT TO
EXPOSE.  It repeats the measurement IMMEDIATELY, on a machine in the same state,
which is the one condition under which a scheduling-dependent count cannot
differ.  It passed 103/103 for heartbeats, and two no-op commits later in the
same walk moved the heartbeat count by +20 and −8 on byte-identical Lean input.
⇒ READ THE NO-OP CONTROLS BELOW, NOT THIS ARM: they are separated by other work
and by whatever the box was doing, which is the reproducibility that matters.
[[feedback-a-control-can-share-the-blind-spot]]

⭐⭐ AND THE NEGATIVE CONTROLS ARE ALREADY IN THE CORPUS AND ARE NOT SYNTHETIC.
FIVE commits in the twelve-commit window change zero `.lean` files (`3769ea0`,
`762da1a`, `873a4d9`, `e57c99f`, `5c01599`), so a deterministic instrument must
read EXACTLY zero across each.  ⚠️ `kernel_delta_history.py`'s docstring names
only ONE of them; its code finds all five, and the under-count is in the prose.
`--analyse` finds them by `git diff-tree` rather than by hash, so the set cannot
go stale against the commit list.  The kernel millisecond instrument's readings
of its own zero across those five are −250, +50, +0, +50 and −350 ms.
⇒ A PROBE THAT CANNOT SHOW ITS ZERO HAS NOT SHOWN ITS ONE.

usage:
  deterministic_cost.py --commits c1,c2,…  [--module Tests.Coverage] [--out F]
                        [--determinism]
  deterministic_cost.py --analyse F [--metric ku|hb]
                        [--kernel docs/kernel-delta-history-….jsonl]
  deterministic_cost.py --selftest
"""
import os, re, sys, json, time, shutil, tempfile, subprocess, statistics, platform

# ⛔ REFUSE AN UNKNOWN FLAG BEFORE ANY WORK HAPPENS. This script dispatched on
# `"--x" in sys.argv` and otherwise fell through to its main path, so a mistyped
# flag did not fail — it RAN. Measured 2026-09-09: `threads_ab.py` given a bogus
# flag started `lake env lean -D profiler=true`, saturated a core for 300+ s on a
# shared machine, and orphaned past its caller. See portable.strict_flags.
if __name__ == "__main__":
    import os as _os, sys as _sys
    _sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
    from portable import strict_flags as _strict_flags
    _strict_flags(__file__)

# ⛔⛔ EVERY `open()` IN THIS FILE NAMES ITS ENCODING, AND THE REASON IS A SECOND
# MACHINE. Python's default text encoding is LOCALE-DEPENDENT: UTF-8 on this Mac,
# **cp1252 on Windows**. Lean sources are full of unicode, so on the box the
# Captain allocated for item 4b this file died at `open(src).read()` with
# `UnicodeDecodeError: 'charmap' codec can't decode byte 0x8f`, before taking a
# single reading. ⇒ 🔑 **A LOCALE-DEFAULTED `open()` IS A HIDDEN DEPENDENCY ON THE
# MACHINE, AND A WALK WHOSE WHOLE PURPOSE IS CROSS-MACHINE COMPARISON IS THE LAST
# PLACE IT CAN SURVIVE.** It was invisible for as long as there was one machine —
# the same shape, found the same hour, as the one absolute POSIX path in
# `score_calibration_night.py`. A portability defect is invisible until the second
# machine exists, and then it is the first thing that breaks.
#
# ⛔ AND THE SAME DEFECT HAS TWO DIRECTIONS, WHICH I LEARNED BY FIXING ONLY ONE.
# With every `open()` repaired the walk got FURTHER on Windows and died again --
# this time on `print()`, because the locale default governs stdout too and this
# file prints unicode. ⇒ **NAMING A DEFECT IS NOT FINDING ITS SIBLINGS**: the read
# side and the write side are one defect with one cause, and repairing the half
# that happened to fail first bought exactly one more line of progress.
for _stream in (sys.stdout, sys.stderr):
    try:
        _stream.reconfigure(encoding="utf-8")
    except (AttributeError, ValueError):
        pass

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# ⛔⛔ THE RESOLUTION RULE IS THE SHIPPED GATE'S, IMPORTED, NOT RE-DERIVED (D148).
# This walk's first version invented its own referee — `|Δkernel| > the two
# commits' summed sweep RANGES` — and that rule is LOOSER than the gate the
# repository actually merges on. On this corpus it called RESOLVED a pair whose
# Lean input is byte-identical (Δ −350 ms against 300 ms of range), which the
# gate's own band (K·se = 376 ms) correctly declines. A second rule invented
# beside a shipped one does not merely duplicate it; it disagrees, and it
# disagrees in the direction that manufactures evidence.
# [[feedback-a-duplicate-born-in-agreement]] [[feedback-two-defects-that-cancel]]
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kernel_delta   # noqa: E402  (guarded `main`; importing it runs nothing)


def resolves(bs, hs):
    """Can the kernel reference tell this pair's delta from the box?

    Delegates to the merge gate's own arithmetic: the band is `K_SIGMA` standard
    errors of the difference of medians. Both names are read off the imported
    module at CALL time, so a rename in the gate reaches this walk instead of
    leaving it quietly running yesterday's rule."""
    if len(bs) < 2 or len(hs) < 2:
        return None, float("inf")
    band = kernel_delta.K_SIGMA * kernel_delta.resolution(bs, hs)
    d = statistics.median(hs) - statistics.median(bs)
    return abs(d) > band, band

# The wrapper command and the option block, spliced in after the module's imports.
#
# ⭐⭐ TWO CANDIDATE PROXIES ARE TAKEN IN ONE PASS, and they must be, because the
# second changes the first: `diagnostics true` adds bookkeeping the elaborator is
# charged for, so a heartbeat count taken WITHOUT it is not comparable with one
# taken WITH it.  Measuring them in separate runs would produce two internally
# consistent tables that cannot be put in the same row.
HB_HEADER = '''import Lean
set_option diagnostics true
set_option diagnostics.threshold 1
open Lean Elab Command in
/-- Report the ELABORATOR heartbeats one command consumed.  `IO.getNumHeartbeats`
is Lean core's own counter, the one `maxHeartbeats` is checked against. -/
elab "hb_count " nm:str " in" cmd:command : command => do
  let start ← IO.getNumHeartbeats
  elabCommand cmd
  let stop ← IO.getNumHeartbeats
  logInfo m!"HBCOUNT {nm.getString} {stop - start}"
'''

DECL = re.compile(r'^(?:private |protected |partial |noncomputable )*'
                  r'(theorem|def|abbrev|instance|example|lemma)\s+'
                  r'([A-Za-z_][A-Za-z0-9_\'!?.]*)')
PREFIX = re.compile(r'^(set_option|open|attribute)\b.* in$')


def arg(name, default=None):
    for i, a in enumerate(sys.argv):
        if a == name and i + 1 < len(sys.argv):
            return sys.argv[i + 1]
    return default


def git(*a, cwd=ROOT):
    r = subprocess.run(["git"] + list(a), cwd=cwd, capture_output=True, text=True)
    if r.returncode != 0:
        print(f"⛔ git {' '.join(a)} failed in {cwd}:\n{r.stdout}\n{r.stderr}")
        sys.exit(2)
    return r.stdout.strip()


def code_lines(text):
    """Which lines START outside every comment and string.

    ⛔ THE RULE THIS SUPPLIES IS THE ONE THE REGEX CANNOT HAVE.  `Tests/Coverage.lean`
    carries PROSE beginning with the word `theorem` at column 0 inside two doc
    comments (\"theorem does not compile, which is how it is known to have teeth\",
    \"theorem names NEITHER\").  A rewriter without this scanner wraps them, the
    wrapper lands INSIDE the comment where it is inert, the module still compiles,
    and two declarations silently go unmeasured.  That is not a parse error — it is
    a shorter table that looks complete.  A tool has no concept of \"not applicable\"
    unless it is given one, and it must PRINT what it excluded.
    [[feedback-a-tool-has-no-concept-of-not-applicable]]"""
    out, depth, in_str, in_line = [], 0, False, False
    at_start = True
    i, n = 0, len(text)
    line_ok = (depth == 0 and not in_str)
    while i < n:
        c = text[i]
        if at_start:
            out.append(depth == 0 and not in_str)
            at_start = False
        if c == "\n":
            in_line = False
            at_start = True
            i += 1
            continue
        if in_line:
            i += 1
            continue
        if in_str:
            if c == "\\":
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
            continue
        if depth == 0 and c == '"':
            in_str = True
            i += 1
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth == 0 and text.startswith("--", i):
            in_line = True
            i += 2
            continue
        i += 1
    while len(out) < len(text.split("\n")):
        out.append(depth == 0 and not in_str)
    return out


def instrument(text, report=None):
    """Wrap every top-level declaration; return (instrumented text, [names])."""
    lines = text.split("\n")
    live = code_lines(text)
    sites = []
    for i, ln in enumerate(lines):
        m = DECL.match(ln)
        if not m:
            continue
        if not live[i]:
            if report is not None:
                report.append((i + 1, ln[:60]))
            continue
        j = i
        while j > 0:
            prev = lines[j - 1].rstrip()
            if PREFIX.match(prev) or prev.startswith('@['):
                j -= 1
                continue
            if prev.endswith('-/'):
                k = j - 1
                while k >= 0 and not lines[k].lstrip().startswith('/-'):
                    k -= 1
                if k < 0:
                    raise SystemExit(f"⛔ unterminated comment above line {i+1}")
                if lines[k].startswith('/--'):
                    j = k
                    continue
            break
        sites.append((j, m.group(2)))
    seen = [s for s, _ in sites]
    if len(set(seen)) != len(seen):
        raise SystemExit("⛔ two declarations resolved to one insertion point; "
                         "the rewriter refuses rather than dropping one")
    ins = dict(sites)
    out = []
    for i, ln in enumerate(lines):
        if i in ins:
            out.append(f'hb_count "{ins[i]}" in')
        out.append(ln)
    imports = [i for i, l in enumerate(out) if l.startswith("import ")]
    if not imports:
        raise SystemExit("⛔ the module has no `import` line to splice the header after")
    out.insert(max(imports) + 1, HB_HEADER)
    return "\n".join(out), [n for _s, n in sites]


def _diag_counts(text):
    """(kernel unfoldings, elaborator unfoldings) out of one `[diag]` message.

    ⛔ THE TWO SECTIONS ARE NOT INTERCHANGEABLE AND THE HEADINGS ARE NEARLY THE
    SAME STRING.  `[kernel] unfolded declarations` is the KERNEL's own reduction
    counter — the quantity the delta gate is about — and `[reduction] unfolded
    declarations` is the ELABORATOR's.  A parser that matched `unfolded
    declarations` would silently sum both and read as a working gate.  There is
    also a third heading, `unfolded reducible declarations`, whose entries are a
    SUBSET already counted above; adding it double-counts."""
    k = r = 0
    sec = None
    for ln in text.split("\n"):
        if "[kernel] unfolded declarations" in ln:
            sec = "k"; continue
        if "[reduction] unfolded declarations" in ln:
            sec = "r"; continue
        if "unfolded reducible" in ln or "use `set_option" in ln:
            sec = None; continue
        g = re.search(r'↦ (\d+)', ln)
        if g and sec == "k":
            k += int(g.group(1))
        elif g and sec == "r":
            r += int(g.group(1))
    return k, r


def read_messages(path, expect_names):
    """Parse `lean --json`: per declaration, heartbeats AND kernel unfoldings."""
    hbs, diags, errors = [], [], []
    for l in open(path, encoding="utf-8"):
        l = l.strip()
        if not l:
            continue
        try:
            m = json.loads(l)
        except json.JSONDecodeError:
            errors.append(f"unparseable line: {l[:200]}")
            continue
        if m.get("severity") == "error":
            errors.append(m.get("data", "")[:300])
            continue
        if not m.get("pos"):
            continue
        lo = (m["pos"]["line"], m["pos"]["column"])
        ep = m.get("endPos") or m["pos"]
        hi = (ep["line"], ep["column"])
        d = m.get("data", "")
        h = re.match(r'HBCOUNT (\S+) (\d+)$', d.split("\n")[0])
        if h:
            hbs.append({"name": h.group(1), "hb": int(h.group(2)),
                        "lo": lo, "hi": hi, "ku": 0, "eu": 0})
            continue
        if "[diag]" in d:
            k, r = _diag_counts(d)
            diags.append((k, r, lo))
    if errors:
        raise SystemExit("⛔ the instrumented module did not elaborate cleanly; "
                         "every reading below would be about a tree that does "
                         "not compile:\n  " + "\n  ".join(errors[:5]))
    got = [x["name"] for x in hbs]
    if got != expect_names:
        missing = [n for n in expect_names if n not in got]
        extra = [n for n in got if n not in expect_names]
        raise SystemExit(f"⛔ the rewriter wrapped {len(expect_names)} declarations "
                         f"and {len(got)} reported.  missing={missing[:6]} "
                         f"extra={extra[:6]}")
    # ⛔ THE JOIN IS BY POSITION RANGE, NOT BY MESSAGE ORDER — Lean elaborates in
    # parallel, so emission order is not evidence of ownership.  A diagnostics
    # message owned by no wrapped declaration is COUNTED AND REPORTED, never
    # dropped: an unattributed count is a hole in the module total.
    orphan_k = orphan_n = 0
    for k, r, p in diags:
        own = [x for x in hbs if x["lo"] <= p <= x["hi"]]
        if len(own) != 1:
            orphan_k += k
            orphan_n += 1
            continue
        own[0]["ku"] += k
        own[0]["eu"] += r
    return ({x["name"]: x["hb"] for x in hbs},
            {x["name"]: x["ku"] for x in hbs},
            {"orphan_msgs": orphan_n, "orphan_kernel_unfoldings": orphan_k})


def measure(worktree, module):
    """One heartbeat reading of one tree.  Deterministic, so one pass suffices."""
    src = os.path.join(worktree, module.replace(".", "/") + ".lean")
    if not os.path.exists(src):
        return None, f"{module} does not exist in this tree"
    b = subprocess.run(["lake", "build", "X86", "Tests", "X86Native"],
                       cwd=worktree, capture_output=True, text=True)
    if b.returncode != 0:
        raise SystemExit(f"⛔ `lake build` failed in {worktree}, so every reading "
                         f"below would be about a tree that does not compile.\n"
                         f"{b.stdout[-2000:]}\n{b.stderr[-2000:]}")
    excluded = []
    text, names = instrument(open(src, encoding="utf-8").read(), report=excluded)
    if excluded:
        print(f"  ⚠️ {len(excluded)} line(s) matched the declaration shape INSIDE a "
              f"comment or string and were excluded:")
        for ln, txt in excluded:
            print(f"       {module}:{ln}  {txt}")
    tmp = os.path.join(tempfile.gettempdir(),
                       f"hb-{module.replace('.', '-')}-{os.getpid()}.lean")
    open(tmp, "w", encoding="utf-8").write(text)
    jsn = tmp + ".json"
    with open(jsn, "w", encoding="utf-8") as fh:
        r = subprocess.run(["lake", "env", "lean", "--json", tmp],
                           cwd=worktree, stdout=fh, stderr=subprocess.PIPE, text=True)
    if r.returncode != 0:
        raise SystemExit(f"⛔ the instrumented elaboration failed (rc {r.returncode}):\n"
                         f"{r.stderr[-2000:]}\n(kept: {tmp}, {jsn})")
    hb, ku, orph = read_messages(jsn, names)
    os.remove(tmp); os.remove(jsn)
    return {"hb": hb, "ku": ku, "orphans": orph}, None


def walk():
    commits = [c for c in (arg("--commits") or "").split(",") if c]
    if not commits:
        print(__doc__)
        return 2
    module = arg("--module", "Tests.Coverage")
    out = arg("--out", os.path.join(tempfile.gettempdir(), "heartbeat-history.jsonl"))
    wt = tempfile.mkdtemp(prefix="x86lean-hb-")
    shutil.rmtree(wt)
    git("worktree", "add", "--detach", wt, commits[0])
    fh = open(out, "a", encoding="utf-8")
    try:
        if "--determinism" in sys.argv:
            # ⭐ THE INSTRUMENT'S OWN ZERO, asserted on the real module before any
            # commit-to-commit number is believed.
            git("checkout", "--detach", commits[0], cwd=wt)
            a, _ = measure(wt, module)
            b, _ = measure(wt, module)
            bad = False
            for metric, label in (("hb", "elaborator heartbeats"),
                                  ("ku", "KERNEL unfoldings")):
                x, y = a[metric], b[metric]
                diff = {k: (x[k], y[k]) for k in x if x[k] != y[k]}
                print(f"DETERMINISM at {commits[0][:9]} — {label}: {len(x)} "
                      f"declarations, {len(x) - len(diff)} identical, "
                      f"{len(diff)} differing; totals {sum(x.values()):,} vs "
                      f"{sum(y.values()):,}")
                if diff:
                    bad = True
                    for k, (u, v) in list(diff.items())[:6]:
                        print(f"  ⛔ {k}: {u} vs {v}")
                else:
                    print("  ✅ identical, declaration by declaration.")
            if bad:
                raise SystemExit("⛔ a proposed proxy is NOT deterministic on this "
                                 "box.  Its premise is refuted; the walk is not run.")
        origin = machine_id()          # read ONCE: it cannot change mid-walk
        print(f"  origin: {origin['node']} / {origin['machine']} / {origin['platform']}")
        for c in commits:
            git("checkout", "--detach", c, cwd=wt)
            t0 = time.time()
            hb, err = measure(wt, module)
            la1, la5, la_src = loadavg()
            rec = {"commit": git("rev-parse", c), "module": module,
                   "hb": hb["hb"] if hb else None, "ku": hb["ku"] if hb else None,
                   "orphans": hb["orphans"] if hb else None,
                   "error": err, "load1": la1, "load5": la5,
                   "load_source": la_src, "origin": origin,
                   "secs": round(time.time() - t0, 1), "t": time.time()}
            fh.write(json.dumps(rec) + "\n")
            fh.flush()
            _l = f"{la1:5.2f}" if la1 is not None else " none"
            print(f"{c[:9]}  {rec['secs']:5.1f}s  load1={_l}  "
                  f"decls={len(hb['hb']) if hb else 0:4d}  "
                  f"heartbeats={sum(hb['hb'].values()) if hb else 0:,}  "
                  f"kernel-unfoldings={sum(hb['ku'].values()) if hb else 0:,}"
                  f"  (unattributed {hb['orphans']['orphan_kernel_unfoldings']:,})",
                  flush=True)
    finally:
        fh.close()
        subprocess.run(["git", "worktree", "remove", "--force", wt],
                       cwd=ROOT, capture_output=True, text=True)
    print(f"\nreadings → {out}")
    return analyse(out)


def machine_id():
    """What machine and toolchain produced a reading.

    ⛔⛔ ADDED 2026-09-09, AFTER a cross-machine comparison had already been run
    WITHOUT it. Until today every reading came from one box, so "which machine"
    was context nobody had to write down. The moment a second machine exists, a
    file of readings that does not name its origin makes the ONE check that
    matters impossible: **two readings from the same machine agree because they
    share an origin, and that is exactly the shape of the result a
    machine-independence claim asserts** [[feedback-two-readings-are-not-two-witnesses]].
    A comparison tool cannot refuse a vacuous pairing it cannot detect.
    ⇒ 🔑 **A MEASUREMENT MUST CARRY THE CONDITION ITS CLAIM IS ABOUT.** The claim
    here is about the MACHINE, so the machine is the field that was missing.
    [[feedback-a-measurement-without-its-conditions]]
    """
    try:
        lean = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                              capture_output=True, text=True, timeout=60).stdout.strip()
    except (OSError, subprocess.SubprocessError):
        lean = ""
    return {"node": platform.node(), "platform": platform.platform(),
            "machine": platform.machine(), "python": platform.python_version(),
            "lean": lean}


def loadavg():
    """(1-min, 5-min, source) load average, or (None, None, reason) where the
    platform has no such notion.

    ⛔⛔ **NEVER ZERO ON FAILURE, AND THIS IS THE ONE THAT WOULD HAVE COST
    SOMETHING.** `os.getloadavg()` is POSIX-only and raises `AttributeError` on
    Windows — the platform of the second machine the Captain allocated for item
    4b. The obvious repair, a `try/except` returning `0.0`, would have written
    **"load1": 0.0** into every reading taken there, and `load1` is exactly the
    covariate this campaign's usability rules are argued over: D179's retired
    rule 4 thresholded it, and every night's census prints its median. ⇒ 🔑 **A
    MISSING MEASUREMENT DEFAULTED TO ZERO DOES NOT READ AS MISSING — IT READS AS
    THE MOST FAVOURABLE POSSIBLE OBSERVATION**, a perfectly idle box, on the
    machine chosen precisely because it is quiet. The absence must be recorded
    AS an absence, with its reason, and every consumer must be able to see it.
    [[feedback-a-tool-has-no-concept-of-not-applicable]]
    [[feedback-a-measurement-without-its-conditions]]
    """
    try:
        a, b, _ = os.getloadavg()
        return a, b, "os.getloadavg"
    except (AttributeError, OSError) as e:
        return None, None, f"unavailable on this platform ({type(e).__name__})"


def kernel_readings(path, module):
    """Per-commit MEDIAN kernel `type checking` ms, from the kernel walk's jsonl.

    ⛔ THE SPREAD IS CARRIED BESIDE THE MEDIAN, and it is the whole reason this
    comparison can be misread.  A zero-noise proxy CANNOT be validated against a
    noisy reference by the stability of their ratio: the REFERENCE's noise sets a
    floor on how unstable that ratio can look, and a wide spread would then be a
    fact about the kernel instrument rather than about the proxy.  Each commit's
    own sweeps give that floor, measured on the same box in the same session.
    [[feedback-a-normalisation-needs-its-denominator-to-vary-the-same-way]]"""
    per = {}
    order = []
    for l in open(path, encoding="utf-8"):
        l = l.strip()
        if not l.startswith("{"):
            continue
        r = json.loads(l)
        c = r["commit"]
        if c not in per:
            per[c] = {"mod": [], "decls": {}}
            order.append(c)
        per[c]["mod"].append(r["modules"].get(module, float("nan")))
        for n, v in r.get("decls", {}).get(module, {}).items():
            per[c]["decls"].setdefault(n, []).append(v)
    med = {c: {"mod": statistics.median(per[c]["mod"]),
               "raw": list(per[c]["mod"]),
               "spread": (max(per[c]["mod"]) - min(per[c]["mod"])),
               "n": len(per[c]["mod"]),
               "decls": {n: statistics.median(v) for n, v in per[c]["decls"].items()}}
           for c in per}
    return order, med


# ⛔⛔ A SIGN STATISTIC IS ONLY AS GOOD AS THE REFEREE THAT SIGNS THE OTHER
# COLUMN, AND ONLY AS INFORMATIVE AS THE PROXY'S OWN VARIATION.
#
# The first version of this walk reported "sign agreement over the pairs where
# the proxy MOVED: 6/6" beside a separate note that the kernel reference resolves
# 2 of 11 pairs, and the two facts never met.  They must: of the six live pairs,
# the referee resolves ONE.  The other five agreements are agreements with a
# Δkernel the referee itself cannot tell from the box.
#
# ⛔ AND THE HARDER HALF, WHICH IS ABOUT THE STATISTIC AND NOT THE REFEREE.  The
# proxy's Δ is POSITIVE ON EVERY LIVE PAIR — a corpus of commits that only ever
# add work has no negative to offer — so a proxy that printed a constant `+1`
# scores exactly the same 6/6.  A statistic a null model matches is not evidence
# about the proxy; it is a description of the reference column.  This function
# therefore prints the NULL MODEL'S SCORE beside the proxy's, and says so out
# loud when they are equal.  [[feedback-a-claim-the-vectors-cannot-distinguish]]
# [[feedback-refute-a-proxy-with-a-plant]]
def sign_stats(pairs, resolved_keys):
    live = [p for p in pairs if p[2] != 0]
    agree = sum(1 for _a, _b, dh, dk in live if (dh > 0) == (dk > 0))
    live_res = [p for p in live if (p[0], p[1]) in resolved_keys]
    agree_res = sum(1 for _a, _b, dh, dk in live_res if (dh > 0) == (dk > 0))
    # the best CONSTANT-SIGN proxy on the same pairs
    null = max(sum(1 for _a, _b, _dh, dk in live if dk > 0),
               sum(1 for _a, _b, _dh, dk in live if dk <= 0))
    signs = set((dh > 0) for _a, _b, dh, _dk in live)
    return {"live": len(live), "agree": agree,
            "live_resolved": len(live_res), "agree_resolved": agree_res,
            "null": null, "one_sided": len(signs) <= 1,
            "informative": not (len(signs) <= 1 or agree <= null)}


def analyse(path):
    rows = [json.loads(l) for l in open(path, encoding="utf-8") if l.strip().startswith("{")]
    if not rows:
        print(f"⛔ {path} holds no readings.")
        return 2
    module = rows[0]["module"]
    metric = arg("--metric", "ku")
    label = {"ku": "KERNEL unfoldings", "hb": "elaborator heartbeats"}[metric]
    seq, hb = [], {}
    for r in rows:
        if r["commit"] not in hb:
            seq.append(r["commit"])
        hb[r["commit"]] = r.get(metric) or r.get("hb")
    print(f"{len(rows)} readings over {len(seq)} commits, module {module}")
    print(f"METRIC: {label}  (--metric hb|ku)")
    kpath = arg("--kernel")
    korder, kmed = ([], {})
    if kpath:
        korder, kmed = kernel_readings(kpath, module)

    print()
    print(f"{'commit':<10}{label[:13]:>14}{'Δ':>13}{'decls':>7}"
          + (f"{'kernel ms':>11}{'Δkernel':>10}" if kpath else ""))
    prev = None
    pairs = []
    for c in seq:
        tot = sum(hb[c].values())
        dh = "" if prev is None else f"{tot - prev:+,}"
        line = f"{c[:9]:<10}{tot:>14,}{dh:>13}{len(hb[c]):>7}"
        if kpath and c in kmed:
            k = kmed[c]["mod"]
            dk = ""
            if prev is not None and seq[seq.index(c) - 1] in kmed:
                dk = f"{k - kmed[seq[seq.index(c) - 1]]['mod']:+.0f}"
                pairs.append((seq[seq.index(c) - 1], c,
                              tot - prev, k - kmed[seq[seq.index(c) - 1]]["mod"]))
            line += f"{k:>11.0f}{dk:>10}"
        print(line)
        prev = tot

    # ⭐ THE NO-OP CONTROL, named by what it CHANGED and not by its hash.
    print()
    print("THE NO-OP CONTROL — a commit that touches no .lean file at all")
    found, noop = False, []
    for a, b in zip(seq, seq[1:]):
        n = subprocess.run(["git", "diff-tree", "--no-commit-id", "--name-only",
                            "-r", f"{a}..{b}"], cwd=ROOT,
                           capture_output=True, text=True).stdout.split()
        if any(x.endswith(".lean") for x in n):
            continue
        found = True
        dh = sum(hb[b].values()) - sum(hb[a].values())
        dk = (kmed[b]["mod"] - kmed[a]["mod"]) if (kpath and a in kmed and b in kmed) else float("nan")
        print(f"  {a[:9]} → {b[:9]}   files: {' '.join(n)}")
        # ⛔ THE LABEL NAMES THE METRIC ACTUALLY READ.  This said "Δheartbeats"
        # under `--metric ku` for one run of this tool's life: a printed label is
        # a claim about which quantity a number is, and it is the claim a reader
        # copies into a bank. [[feedback-a-citation-is-an-ungated-claim]]
        print(f"    Δ{label} = {dh:+,}      "
              + (f"Δkernel = {dk:+.0f} ms" if kpath else ""))
        print(f"    {'✅ EXACTLY ZERO' if dh == 0 else '⛔ NON-ZERO on a no-op commit'}"
              f" — the deterministic instrument's own zero")
        if kpath and a in kmed and b in kmed:
            res, band = resolves(kmed[a]["raw"], kmed[b]["raw"])
            noop.append((a, b, dk, band, bool(res)))
            if res:
                print(f"    \u26d4 AND THE REFEREE CALLS THIS PAIR RESOLVED: "
                      f"|{dk:+.0f}| > the gate's band of {band:.0f} ms, on a pair "
                      f"whose Lean input is byte-identical. The truth is ZERO.")
    if not found:
        print("  ⚠️ none in this corpus: the walk has not shown its zero.")
    # ⭐⭐ THE REFEREE'S OWN ERROR RATE, MEASURED WHERE THE TRUTH IS KNOWN.
    # The no-op pairs are the only pairs in this corpus whose true Δkernel is
    # KNOWN, and it is zero. Every one the resolution rule calls "resolved" is a
    # measured FALSE POSITIVE of the rule that decides which evidence counts.
    # A referee whose error rate is unmeasured cannot referee.
    # [[feedback-measure-a-gates-error-rates]]
    if noop:
        bad = [x for x in noop if x[4]]
        print(f"\n  REFEREE ERROR RATE ON THE KNOWN-ZERO PAIRS: {len(bad)} of "
              f"{len(noop)} no-op pairs are called RESOLVED by the merge gate's "
              f"band\n  (K_SIGMA=%g), where the true \u0394 is zero." % kernel_delta.K_SIGMA)
        for a, b, dk, sp, _ in bad:
            print(f"    {a[:9]}\u2192{b[:9]}  \u0394kernel {dk:+.0f} ms vs spread "
                  f"{sp:.0f} ms")
        print("  \u26a0\ufe0f  A false-negative rate is NOT measurable here: no pair in "
              "this corpus has a\n      known non-zero truth. The rule is measured in "
              "one direction only.")

    if pairs:
        print()
        print(f"ADJACENT PAIRS — Δ{label} against Δkernel-ms")
        print(f"  {'pair':<22}{'Δproxy':>14}{'Δkernel ms':>13}{'ms per 1k':>15}")
        for a, b, dh, dk in pairs:
            r = (dk / (dh / 1000.0)) if dh else float("nan")
            print(f"  {a[:9]}→{b[:9]:<12}{dh:>+14,}{dk:>+13.0f}{r:>15.2f}")
        # ⛔ A SIGN STATISTIC MUST EXCLUDE THE PAIRS WHERE THE PROXY SAID NOTHING.
        # `(dh > 0) == (dk > 0)` scores a Δproxy of EXACTLY ZERO as "agreement"
        # whenever Δkernel happens to be <= 0, so five silent pairs contributed
        # three agreements to an 8/11 that read like corroboration.  A pair the
        # proxy cannot speak about is not evidence for it.
        # [[feedback-under-claims-are-unpoliced]]
        print()
        print("  ⚠️ WHICH PAIRS THE KERNEL REFERENCE CAN ACTUALLY RESOLVE")
        print("     (the rule is the MERGE GATE's own band, K_SIGMA=%g standard errors"
              % kernel_delta.K_SIGMA)
        print("      of the difference of medians, imported from kernel_delta.py; a")
        print("      Δkernel inside it is a reading of the box, and a ratio computed")
        print("      from one is noise/ratio. The range is printed beside it as a")
        print("      READING — it is not the test. [[feedback-a-duplicate-born-in-agreement]])")
        print(f"     {'pair':<22}{'Δkernel':>10}{'band K*se':>11}{'range b+h':>11}{'resolved?':>11}")
        resolved = []
        for a, b, dh, dk in pairs:
            res, band = resolves(kmed[a]["raw"], kmed[b]["raw"])
            sp = kmed[a]["spread"] + kmed[b]["spread"]
            if res:
                resolved.append((a, b, dh, dk))
            print(f"     {a[:9]}→{b[:9]:<12}{dk:>+10.0f}{band:>11.0f}{sp:>11.0f}"
                  f"{('yes' if res else 'NO'):>11}")
        print(f"     resolved: {len(resolved)}/{len(pairs)} pairs")
        # ⭐ THE TWO FACTS MEET HERE, and the null model rides with them.
        st = sign_stats(pairs, {(a, b) for a, b, _dh, _dk in resolved})
        print()
        print(f"  sign agreement over the {st['live']} pairs where the proxy MOVED: "
              f"{st['agree']}/{st['live']}   "
              f"(the other {len(pairs) - st['live']} read exactly zero and are excluded)")
        print(f"  ...of which the referee can RESOLVE {st['live_resolved']}: "
              f"{st['agree_resolved']}/{st['live_resolved']} — the rest agree with a "
              f"Δkernel the referee cannot tell from the box")
        print(f"  NULL MODEL — the best CONSTANT-SIGN proxy scores {st['null']}/"
              f"{st['live']} on the same pairs")
        if st["one_sided"]:
            print("  \u26a0\ufe0f THE PROXY MOVED IN ONE DIRECTION ONLY on every live pair, so "
                  "this statistic\n     cannot distinguish it from a constant. It is a "
                  "description of the reference\n     column, not evidence about the proxy.")
        elif not st["informative"]:
            print("  \u26a0\ufe0f the null model scores at least as well; this statistic "
                  "carries no evidence.")
        if resolved:
            rr2 = [dk / (dh / 1000.0) for _a, _b, dh, dk in resolved if dh]
            if rr2:
                print(f"     ms per 1k proxy units over the RESOLVED pairs only: "
                      f"min {min(rr2):.2f}  median {statistics.median(rr2):.2f}  "
                      f"max {max(rr2):.2f}")
        rr = [dk / (dh / 1000.0) for _a, _b, dh, dk in pairs if dh]
        if rr:
            print(f"  ms per 1k proxy units: min {min(rr):.2f}  median "
                  f"{statistics.median(rr):.2f}  max {max(rr):.2f}  "
                  f"spread {max(rr)/min(rr) if min(rr) > 0 else float('inf'):.1f}x"
                  if min(rr) > 0 else
                  f"  ms per 1k proxy units: min {min(rr):.2f}  median "
                  f"{statistics.median(rr):.2f}  max {max(rr):.2f}")
    return 0


def selftest():
    """Arms on the rewriter, which is the part that can silently drop work."""
    n = ok = 0

    def arm(name, cond, saw=""):
        nonlocal n, ok
        n += 1
        if cond:
            ok += 1
            print(f"  ✅ {name}")
        else:
            print(f"  ⛔ {name}   saw: {saw}")

    t, names = instrument("import X86\n\ntheorem a : True := trivial\n")
    arm("a bare theorem is wrapped", names == ["a"], names)
    arm("the header lands after the import",
        t.split("\n").index("import Lean") == 1, t.split("\n")[:3])

    t, names = instrument("import X86\n/-- doc -/\ntheorem b : True := trivial\n")
    ls = t.split("\n")
    i = ls.index('hb_count "b" in')
    arm("the wrapper precedes a DOC COMMENT, not the theorem line",
        ls[i + 1] == "/-- doc -/", ls[i:i + 3])

    t, names = instrument("import X86\nset_option maxHeartbeats 4 in\n"
                          "theorem c : True := trivial\n")
    ls = t.split("\n")
    i = ls.index('hb_count "c" in')
    arm("the wrapper precedes a `set_option … in` prefix",
        ls[i + 1].startswith("set_option"), ls[i:i + 3])

    t, names = instrument("import X86\n/-- doc -/\nset_option foo in\n"
                          "theorem d : True := trivial\n")
    ls = t.split("\n")
    i = ls.index('hb_count "d" in')
    arm("both prefixes at once are stepped over",
        ls[i + 1] == "/-- doc -/", ls[i:i + 4])

    _t, names = instrument("import X86\ndef e := 1\nprivate def f := 2\n"
                           "  def notTopLevel := 3\n")
    arm("`private def` is wrapped and an indented `def` is NOT",
        names == ["e", "f"], names)

    # ⛔⛔ THE ARMS FOR THE RULE A REGEX CANNOT HAVE, driven with the two REAL
    # shapes out of `Tests/Coverage.lean` rather than invented ones — the walk
    # refused on exactly these, which is how the rule got written.
    rep = []
    _t, names = instrument(
        "import X86\n/-- prose\n"
        "theorem does not compile, which is how it is known to have teeth. -/\n"
        "def real := 1\n", report=rep)
    arm("prose beginning `theorem` inside a DOC COMMENT is not wrapped",
        names == ["real"], names)
    arm("and the excluded line is REPORTED, not dropped in silence",
        len(rep) == 1 and rep[0][0] == 3, rep)

    _t, names = instrument("import X86\n/- block\ndef notADecl := 1\n-/\n"
                           "def real := 1\n")
    arm("a `def` inside a BLOCK comment is not wrapped", names == ["real"], names)

    _t, names = instrument("import X86\n/- outer /- inner\ndef hidden := 1\n"
                           "-/ still inner\ndef alsoHidden := 1\n-/\n"
                           "def real := 1\n")
    arm("NESTED block comments are tracked (both hidden defs stay out)",
        names == ["real"], names)

    # ⭐ THE POSITIVE CONTROL FOR THE SAME RULE: the identical text OUTSIDE a
    # comment must still be wrapped, or the scanner is just switched off.
    # [[feedback-a-probe-must-create-its-condition]]
    _t, names = instrument("import X86\ndef does := 1\ndef names := 2\n")
    arm("the SAME names outside a comment are still wrapped",
        names == ["does", "names"], names)

    _t, names = instrument('import X86\ndef s : String := "/- not a comment"\n'
                           'def after := 1\n')
    arm("a `/-` inside a STRING does not open a comment",
        names == ["s", "after"], names)

    # ⛔ A NEGATIVE ARM: a file with no import must be REFUSED, not silently
    # emitted without the header (which would elaborate and report nothing).
    try:
        instrument("theorem g : True := trivial\n")
        arm("a module with no import is refused", False, "it was accepted")
    except SystemExit:
        arm("a module with no import is refused", True)

    # ⛔ AND THE JOIN'S OWN REFUSAL: a name the rewriter wrapped that never
    # reports must be a REFUSAL, not a shorter table.
    import tempfile as _tf
    p = os.path.join(_tf.gettempdir(), f"hb-selftest-{os.getpid()}.json")
    open(p, "w", encoding="utf-8").write(json.dumps({
        "data": "HBCOUNT a 5", "severity": "information",
        "pos": {"line": 1, "column": 0}, "endPos": {"line": 2, "column": 0}}) + "\n")
    try:
        read_messages(p, ["a", "b"])
        arm("a wrapped declaration that never reports is refused", False, "accepted")
    except SystemExit as e:
        arm("a wrapped declaration that never reports is refused",
            "missing=['b']" in str(e), str(e)[:120])
    # and an error message in the stream is a refusal even if every name reports
    open(p, "w", encoding="utf-8").write(
        json.dumps({"data": "HBCOUNT a 5", "severity": "information",
                    "pos": {"line": 1, "column": 0}, "endPos": {"line": 2, "column": 0}}) + "\n"
        + json.dumps({"data": "boom", "severity": "error",
                      "pos": {"line": 9, "column": 0}, "endPos": {"line": 9, "column": 1}}) + "\n")
    try:
        read_messages(p, ["a"])
        arm("an elaboration error refuses the whole reading", False, "accepted")
    except SystemExit as e:
        arm("an elaboration error refuses the whole reading", "boom" in str(e), str(e)[:120])
    # ⛔⛔ THE ARM FOR THE TWO HEADINGS THAT ARE NEARLY THE SAME STRING.  A parser
    # matching `unfolded declarations` sums the KERNEL's counter and the
    # ELABORATOR's into one number and reads as a working gate.
    k, r = _diag_counts(
        "[diag] Diagnostics\n"
        "  [reduction] unfolded declarations (max: 9, num: 1):\n"
        "    [reduction] Bool.rec ↦ 7\n"
        "  [reduction] unfolded reducible declarations (max: 9, num: 1):\n"
        "    [reduction] Bool.casesOn ↦ 5\n"
        "  [kernel] unfolded declarations (max: 9, num: 2):\n"
        "    [kernel] Bool.casesOn ↦ 100\n"
        "    [kernel] List.rec ↦ 11\n"
        "  use `set_option diagnostics.threshold <num>` to control threshold\n")
    arm("the KERNEL counter is read alone (111), not summed with the elaborator's",
        k == 111, k)
    arm("the ELABORATOR counter is read alone (7), and `reducible` is NOT added",
        r == 7, r)

    os.remove(p)

    # ── arms on `sign_stats`, the statistic that reads the corpus ───────────
    # ⭐ THE STATISTIC IS PROBED BOTH WAYS: a one-sided proxy must be REFUSED as
    # uninformative, and a genuinely two-sided one that beats the null must be
    # ACCEPTED, or the refusal is just a gate that never speaks.
    # [[feedback-probe-gates-both-ways]] [[feedback-measure-a-gates-error-rates]]
    P = lambda *t: [("a%d" % i, "b%d" % i, dh, dk) for i, (dh, dk) in enumerate(t)]
    one_sided = P((100, 300), (200, 500), (50, 100), (0, -250))
    st = sign_stats(one_sided, set())
    arm("a Δproxy of exactly ZERO is excluded from the live set",
        st["live"] == 3, st)
    arm("a ONE-SIDED proxy scores what the null model scores",
        st["agree"] == st["null"] == 3, st)
    arm("...and is reported as NOT informative",
        st["one_sided"] and not st["informative"], st)
    two_sided = P((100, 300), (-200, -500), (50, 100), (-10, -20))
    st2 = sign_stats(two_sided, set())
    arm("a TWO-SIDED proxy that beats the null IS informative",
        st2["agree"] == 4 and st2["null"] == 2 and st2["informative"], st2)
    st3 = sign_stats(P((100, 300), (-200, -500), (50, -100), (-10, 20)), set())
    arm("a two-sided proxy that only MATCHES the null is not informative",
        st3["agree"] == 2 and st3["null"] == 2 and not st3["informative"], st3)
    st4 = sign_stats(one_sided, {("a0", "b0")})
    arm("the RESOLVED sub-count counts only pairs the referee resolves",
        st4["live_resolved"] == 1 and st4["agree_resolved"] == 1, st4)

    # ── arms on the REFEREE, which is now the shipped gate's rule ───────────
    # ⭐ THE DELEGATION IS TESTED, NOT THE AGREEMENT. Stubbing the gate's own
    # function and requiring this walk's answer to MOVE is the only arm that can
    # tell delegation from a copy that happens to agree today (D143's pattern).
    _real = kernel_delta.resolution
    try:
        kernel_delta.resolution = lambda bs, hs: 0.0
        res, band = resolves([100.0, 100.0], [220.0, 420.0])
        arm("the referee DELEGATES: stubbing kernel_delta.resolution moves the answer",
            res is True and band == 0.0, (res, band))
    finally:
        kernel_delta.resolution = _real
    # ⭐ AND THE SHAPE OF THE DEFECT THIS REPAIR REMOVED: a pair the summed-RANGE
    # rule calls resolved and the gate's band declines. On the shipped corpus
    # that pair's Lean input was byte-identical, so the range rule's extra
    # "resolution" was a false positive against a known zero.
    bs, hs = [100.0, 100.0], [220.0, 420.0]
    d = statistics.median(hs) - statistics.median(bs)
    rng = (max(bs) - min(bs)) + (max(hs) - min(hs))
    res, band = resolves(bs, hs)
    arm("the band DECLINES a pair the summed-range rule would resolve",
        abs(d) > rng and res is False and band > abs(d),
        (d, rng, band, res))
    arm("a side with fewer than two readings is REFUSED, not resolved",
        resolves([100.0], [220.0, 420.0]) == (None, float("inf")),
        resolves([100.0], [220.0, 420.0]))

    # ⛔⛔ THE LOAD-ABSENCE CONTRACT, DRIVEN BY BREAKING THE PLATFORM CALL.
    #     The tempting repair for a POSIX-only API is `except: return 0.0`, and on
    #     the second machine that writes "load1": 0.0 -- a PERFECTLY IDLE BOX --
    #     into the covariate this campaign's usability rules are argued over. The
    #     arm asserts the absence is recorded AS an absence, with a reason.
    _real = os.getloadavg

    def _boom():
        raise AttributeError("simulated: no getloadavg on this platform")

    try:
        os.getloadavg = _boom
        a, b, srcname = loadavg()
        arm("a platform without getloadavg yields None, never 0.0",
            a is None and b is None, f"got {a!r},{b!r}")
        arm("and it NAMES the reason, so a consumer can see the absence",
            isinstance(srcname, str) and "unavailable" in srcname, f"got {srcname!r}")
    finally:
        os.getloadavg = _real
    a, b, srcname = loadavg()
    arm("CONTROL - with the platform call restored, a real reading returns numbers",
        isinstance(a, float) and isinstance(b, float) and srcname == "os.getloadavg",
        f"got {a!r},{b!r},{srcname!r}")

    mid = machine_id()
    arm("a reading's origin names node, machine and platform, none of them blank",
        all(mid.get(k) for k in ("node", "machine", "platform")), f"got {mid}")

    print(f"\n{ok}/{n} arms pass")
    return 0 if ok == n else 1


def main():
    if "--selftest" in sys.argv:
        return selftest()
    if "--analyse" in sys.argv:
        return analyse(arg("--analyse"))
    return walk()



# ⛔ GUARDED (D151's sweep).  An unguarded `sys.exit(main())` means `import <this
# module>` RUNS the tool and then exits the importer — `kernel_cost.py` cost a
# two-minute profiling pass and a killed probe before this was noticed, and
# `kernel_delta.py` had already been given the same guard by D148.  Two prior
# namings and the siblings were never swept for.
# [[feedback-naming-a-defect-is-not-finding-its-siblings]]
if __name__ == "__main__":
    sys.exit(main())
