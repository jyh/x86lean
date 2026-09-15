#!/usr/bin/env python3
"""ARM A′ — THE DETERMINISTIC KERNEL-WORK GATE, WITH A COMPLEMENT FOR WHAT IT CANNOT SEE.

⚖️ **RULED BY THE HELM, 2026-09-13**, on D229 §3's recommendation: *"ARM A′
ACCEPTED as you recommended: gate Δku for EVERY module, plus an ABSOLUTE,
generous ms ceiling for `X86.Theorems` · `X86.Syntax` · `X86.Basic` (the three
whose ms/ku sits outside the band). Reason: your measurement shows ARM A
under-prices those modules 1.5–3.5×, rising with inductive-change size, and an
absolute ceiling does not inherit the per-run band that made the ms delta gate
UNMEASURABLE. BUILD IT red-first (a plant that ARM A passes and A′ refuses)."*

## THE TWO HALVES, AND WHY NEITHER IS THE GATE ALONE

**Half 1 — Δku, every module.** `ku` is the kernel's `unfolded declarations`
counter. It is EXACT: D187 measured it 0 on all five no-op commits in the corpus
and identical across two machines; D228's control read the same file twice at
Δ 0. So this half needs no repeats, no standard-error band, and has NO
`UNMEASURABLE` verdict — which is the whole reason ARM A was preferred to the ms
delta gate, whose clock could not separate a real commit from a no-op (D187) and
was not reproducible to better than ~25% on one machine in one night (D188).

**Half 2 — an absolute ms ceiling on three modules.** ⛔ **`ku` IS BLIND TO TWO
KINDS OF KERNEL WORK AND ITS BLINDNESS READS AS A MEASURED ZERO** (D228 §3, the
🔑 this gate exists to answer): literal `Nat` arithmetic (K2) and large
no-unfolding terms (K3) cost unbounded kernel time at Δku 0. D229 §1 then
measured how much of this repository is in that shadow: in `X86.Theorems`,
`X86.Syntax` and `X86.Basic` — the three modules a P2 proof or an enum-growing
batch changes — **906 of 1,328 ms (68%) is time the unfolding constant does not
account for.**

⇒ 🔑 ***A GATE WITH NO NOISE HAS NO WAY TO SAY "I DID NOT SEE THAT", SO THE
COMPLEMENT IS NOT A BELT-AND-BRACES — IT IS THE ONLY THING STANDING BETWEEN A
CONFIDENT ZERO AND AN UNBOUNDED REGRESSION.***

## THE CEILING IS ABSOLUTE AND COARSE, AND BOTH WORDS ARE LOAD-BEARING

`kernel_ceilings.txt` is a chronicle of what a TIGHT absolute ceiling becomes: its
own header records `X86.Syntax` passing at **97.6%** and `vectorCoverage` at
**98%**, at which point *"a ceiling whose margin is smaller than the machine's own
spread reports the machine, not the code"*. Those lines are registered at
`measured × 1.6`, a margin chosen when the ceiling was the merge gate and had to
be sensitive.

These are registered at `measured × 3.0` — the SAME rule that file's header states
for its absolute lines, `max(measured × 3.0, 50ms)`, and not a margin invented
here to fit. At 3× the margin is far outside this box's measured 4–8% contention
band, so the ceiling cannot fire on load. **It catches SIZE, which is exactly and
only what it is for: D229 §2's constructor plant shows ku falling behind ms by a
factor that GROWS with the size of an inductive change (1.8× at 128 constructors,
3.6× at 512).**

⛔ **IT IS THEREFORE A TRIPWIRE, NOT A BUDGET.** A change that adds 40% to
`X86.Theorems`'s kernel time passes this half and is caught — if at all — by the
Δku half. That is the division of labour and it is stated so that nobody reads a
green ceiling as "the module did not get more expensive".

## WHY A′ CARRIES ITS OWN REGISTRY

`scripts/ku_delta_budget.txt` holds the ku floor and these three ceilings.
⛔ **They are deliberately NOT added to `kernel_ceilings.txt`, and the reason is
not tidiness.** That file's numbers are per-declaration READINGS at ×1.6 whose
whole history is of numbers re-registered every batch; these are coarse ×3 GATE
ceilings on three whole modules. **Two numbers for one unit in one file, one a
reading and one a verdict, is a file in which each reads as the other** — and
this repository has already paid for a duplicate born in agreement (D148).
✅ **What replaces "one file" is a CHECKED RELATIONSHIP:** `--check-registry`
refuses if an A′ ceiling is BELOW the reading registry's number for the same
unit, so the two cannot silently diverge in the direction that matters.

## THE ku BUDGETS ARE NOT IN THAT FILE, DELIBERATELY

A Δku budget here is `the module's registered RELATIVE ms budget × its base ku`,
read live from `scripts/kernel_delta_budget.txt`. ⭐ **Nothing is copied and no
base reading is stored**, so there is no number here to go stale.

⚠️ **THIS IS A POLICY TRANSFER, DECLARED, AND NOT A MEASUREMENT.** Those
percentages were derived as NOISE allowances for a clock. Applied to a counter
whose noise is exactly zero they are LOOSE — the direction is stated because it
is the unpoliced one. What would tighten them is a Δku walk over real commits per
module, which does not exist: ⛔ **every ku corpus in `docs/` is `Tests.Coverage`
and nothing else** (12 commits × 1 module), which is D229 §4's finding one level
down. That walk is the OPEN ITEM, it is cheap now that a ku reading is seconds
rather than minutes, and it can only tighten these budgets.

  ku_delta.py [--base REV] [--head REV] [--arm a|a-prime] [--json OUT]
  ku_delta.py --check-registry
  ku_delta.py --selftest

VERDICTS: rc 0 CLEAN · rc 1 FAILED · rc 2 REFUSED (a structural problem; never a
verdict about the change). ⛔ There is no rc 3: this gate does not have one,
because neither half is a per-run band.
"""
# ⛔ REFUSE AN UNKNOWN FLAG BEFORE ANY WORK HAPPENS — see portable.strict_flags.
# This gate's default path builds TWO WORKTREES, so a mistyped flag that fell
# through to the main path would start tens of minutes of work nobody asked for.
if __name__ == "__main__":
    import os as _os, sys as _sys
    _sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
    from portable import strict_flags as _strict_flags
    _strict_flags(__file__)

import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)

import deterministic_cost as dc        # noqa: E402  the ku instrument
import kernel_delta as kd              # noqa: E402  base resolution, budgets, ceilings, box stamp

BUDGET_FILE = os.environ.get("X86LEAN_KU_BUDGET",
                             os.path.join(ROOT, "scripts", "ku_delta_budget.txt"))

# The two spellings A′'s registry uses; see `read_registry`. The POPULATION of
# ku-gated modules is not here and is not a list anywhere — see `ku_modules`.
MS_TAG = "@ms"
MACHINE_TAG = "@on"


def refuse(msg):
    """⛔ EXIT 2, THE DOCUMENTED *REFUSED* CODE — never 1, which is this gate's
    VERDICT that the change failed. `sys.exit("...")` exits 1, so every refusal in
    the first draft of this file reported itself as a FAILING CHANGE. The two must
    be distinguishable: a reader who cannot tell "your commit is over budget" from
    "my registry is malformed" will go looking in the wrong place, and CI cannot
    route them differently either."""
    print(msg)
    sys.exit(2)


# ────────────────────────────────────────────────────────────────────────────
# THE REGISTRY
# ────────────────────────────────────────────────────────────────────────────
def ku_modules(*profiles):
    """The modules to gate for Δku: the UNION of what the profiler reports on the
    trees it was given. ⭐ DERIVED FROM THE ARTIFACT, NEVER FROM A DECLARED LIST.

    ⛔ THE FIRST DRAFT OF THIS FUNCTION READ THE ms BUDGET FILE'S MODULE ROWS AND
    IT WAS WRONG BY TWO MODULES ON ITS FIRST RUN: `X86.Program` and `Tests.Program`
    are registered in `kernel_ceilings.txt` and NOT in `kernel_delta_budget.txt`,
    so a population taken from the budget file silently omitted two of the
    twenty-one modules this repository builds — including one of the two the
    (unit, machine) ceiling work was done for. The helm's word is "EVERY module",
    and a declared list is wrong in the direction of whatever it defaults to.
    [[feedback-a-declared-list-inherits-its-default]]

    ⛔ AND IT IS THE PROFILER'S LIST AND NOT A FILESYSTEM WALK. The tree holds 23
    `.lean` files and builds 21 library modules; `Main.lean` and `AxiomGate.lean`
    are executable roots. A walk would have ku-gated two modules the library does
    not contain — the same error in the other direction. The profiler reports what
    the build actually type-checks, which is the population every other kernel
    number in this repository is about."""
    mods = set()
    for p in profiles:
        mods |= set(p["modules"])
    return sorted(mods)


def read_registry(path=None):
    """(floor_ku, {(module, machine): ms}) from A′'s own registry.

    The ms ceilings ride as units whose NAME carries the machine — `X86.Basic @ms
    @on yukon.lan 267` — which `read_budgets` parses natively, because its own
    docstring already promises that "a unit name legitimately contains spaces".
    ⭐ ONE PARSER, NOT A SECOND ONE: the alternative was a bespoke reader for a
    format this repository already has code for, which is the duplicate-born-in-
    agreement shape (D148, and `read_ceilings`'s own note)."""
    path = path or BUDGET_FILE
    default, per, floor = kd.read_budgets(path)
    if default is not None:
        refuse("⛔ ku_delta_budget.txt must not carry @default: the ku budgets come "
                 "from kernel_delta_budget.txt, and a default here would be a second "
                 "answer to a question this file does not ask.")
    if floor is None:
        refuse(f"⛔ no @floor in {path}. Every ku budget is a percentage of a base "
                 f"reading, and a percentage of a module whose base ku is 0 is 0 — "
                 f"a gate that fires on any addition at all.")
    ceilings = {}
    for unit, (kind, val) in per.items():
        p = unit.split()
        mach = None
        if len(p) >= 2 and p[-2] == MACHINE_TAG:
            mach, p = p[-1], p[:-2]
        if len(p) != 2 or p[1] != MS_TAG:
            refuse(f"⛔ unrecognised line in {path}: {unit!r}. This file holds "
                     f"@floor and `<module> {MS_TAG} {MACHINE_TAG} <machine> <ms>` "
                     f"and nothing else — the ku budgets live in "
                     f"kernel_delta_budget.txt and are read from there.")
        if kind != "abs":
            refuse(f"⛔ {unit!r}: an A′ ms ceiling is ABSOLUTE milliseconds. A "
                     f"percentage ceiling is a delta wearing a ceiling's name, and "
                     f"the per-run band is the thing this half exists to avoid.")
        # ⛔ A CEILING WITH NO MACHINE IS ABSENT, NEVER A LOOSE BOUND — the rule the
        # helm ruled for `kernel_ceilings.txt` on D198. The local↔runner factor is
        # per module (measured 1.6×–2.4×) and cannot be divided out of an absolute
        # number, so a number measured elsewhere is not a weak answer here, it is
        # no answer.
        if mach is None:
            refuse(f"⛔ {unit!r} carries no `{MACHINE_TAG} <machine>`. An absolute "
                     f"ms ceiling names the box it was measured on or it is absent.")
        key = (p[0], mach)
        if key in ceilings:
            refuse(f"⛔ DUPLICATE A′ CEILING for {key}: two lines, two numbers, and "
                     f"nothing to choose between them.")
        ceilings[key] = val
    return floor, ceilings


def check_registry(quiet=False):
    """A′'s ceiling for a unit must not sit BELOW the reading registry's.

    ⭐ THIS IS WHAT REPLACES PUTTING BOTH NUMBERS IN ONE FILE. A′'s ceiling is
    coarse (×3) and the reading registry's is tight (×1.6), so A′'s must be the
    larger; if it ever is not, one of the two was re-registered without the other
    and the pair has diverged in the direction where A′ fires before the reading
    it is supposed to be a coarse bound on."""
    floor, ceilings = read_registry()
    readings = kd.read_ceilings()
    bad, rows = [], []
    for (unit, mach), ms in sorted(ceilings.items()):
        # the reading registry keys by (unit, machine) and a machine-unknown line
        # keys as (unit, None); both are compared, because A′ must bound whichever
        # number a reader of that file would find.
        for rkey in ((unit, mach), (unit, None)):
            r = readings.get(rkey)
            if r is None:
                continue
            rows.append((unit, mach, ms, rkey[1], r))
            if ms < r:
                bad.append(f"{unit} on {mach}: A′ ceiling {ms:g} ms is BELOW the "
                           f"reading registry's {r:g} ms"
                           f"{'' if rkey[1] else ' (machine-unknown line)'}")
    if not quiet:
        print(f"A′ registry: floor {floor:g} ku · {len(ceilings)} ms ceiling(s)")
        for unit, mach, ms, rmach, r in rows:
            print(f"  {unit:16} @on {mach:16} A′ {ms:8.0f} ms   reading registry "
                  f"{r:8.0f} ms{'' if rmach else '  (no machine)'}   ratio {ms / r:.2f}x")
        if not rows:
            print("  (no unit is named in both registries — nothing to cross-check)")
    for b in bad:
        print(f"⛔ {b}")
    return 1 if bad else 0


# ────────────────────────────────────────────────────────────────────────────
# THE MEASUREMENT
# ────────────────────────────────────────────────────────────────────────────
def ku_of(worktree, modules):
    """{module: ku} for one tree. ⛔ Exact, so ONE reading a side is the reading —
    there are no repeats here because there is nothing for repeats to average."""
    out = {}
    for m in modules:
        t0 = time.time()
        # ⛔ A MODULE THE OTHER TREE HAS AND THIS ONE DOES NOT IS ZERO, NOT A
        # REFUSAL. The population is the UNION of the two trees precisely so that a
        # change which ADDS a module is gated on the ku it adds; refusing here
        # would make "add a module" the one change this gate cannot judge. The
        # absence is printed, never silently defaulted.
        if not os.path.exists(os.path.join(worktree, m.replace(".", os.sep) + ".lean")):
            out[m] = 0
            print(f"  ku {m:20} {0:>9}   (no such module in this tree)")
            continue
        reading, why = dc.measure(worktree, m)
        if reading is None:
            # ⛔ A GATE THAT REFUSES MUST SAY WHAT IT SAW (D94). A bare "no reading"
            # sends the reader to a local re-run, and a local re-run of a tree that
            # only exists inside this run answers a different question.
            print(f"⛔ no ku reading for {m} in {worktree}: {why}")
            sys.exit(2)
        out[m] = (sum(reading["ku"].values())
                  + reading["orphans"]["orphan_kernel_unfoldings"])
        print(f"  ku {m:20} {out[m]:>9,}   {time.time() - t0:4.1f}s", flush=True)
    return out


def ms_of(worktree):
    """{module: kernel ms} for one tree, through the SAME profiler every other
    gated kernel number in this repository comes from (`kernel_cost.py`)."""
    return kd.profile(worktree, sorted(kd.gated_declarations()))["modules"]


def measure(base_rev, head_rev, keep=None, plant=None):
    """⭐ BOTH ARMS GET THE IDENTICAL MEASUREMENT — the arm switch lives in
    `verdict` alone. That is not an economy, it is what makes the red-first
    demonstration mean anything: a plant that A passes and A′ refuses has to be a
    difference between two DESIGNS, not between two programs that measured
    different things."""
    tmp = keep or tempfile.mkdtemp(prefix="x86lean-kudelta-")
    base_wt, head_wt = os.path.join(tmp, "base"), os.path.join(tmp, "head")
    made = []
    try:
        for wt, rev in ((base_wt, base_rev), (head_wt, head_rev)):
            if not os.path.exists(wt):
                kd.git("worktree", "add", "--detach", wt, rev)
                made.append(wt)
        if plant:
            plant(head_wt)
        print("profiling base …", flush=True)
        base_p = kd.profile(base_wt, sorted(kd.gated_declarations()))
        print("profiling head …", flush=True)
        head_p = kd.profile(head_wt, sorted(kd.gated_declarations()))
        modules = ku_modules(base_p, head_p)
        print(f"{len(modules)} modules, derived from the profiler on both trees")
        print("base tree:")
        base_ku = ku_of(base_wt, modules)
        print("head tree:")
        head_ku = ku_of(head_wt, modules)
        return {"base_rev": kd.git("rev-parse", base_rev),
                "head_rev": kd.git("rev-parse", head_rev),
                "planted": bool(plant), "box": kd.box_stamp(),
                "machine": kd.socket.gethostname(),
                "base_ku": base_ku, "head_ku": head_ku,
                "base_ms": base_p["modules"], "head_ms": head_p["modules"]}
    finally:
        if keep is None:
            for wt in made:
                subprocess.run(["git", "worktree", "remove", "--force", wt],
                               cwd=ROOT, capture_output=True, text=True)
            shutil.rmtree(tmp, ignore_errors=True)


# ────────────────────────────────────────────────────────────────────────────
# THE VERDICT
# ────────────────────────────────────────────────────────────────────────────
def verdict(data, arm, quiet=False):
    """(rc, findings). `arm` is "a" (Δku only) or "a-prime" (Δku + the ceilings).

    ⭐ THE TWO ARMS ARE ONE CODE PATH WITH ONE SWITCH, AND THAT IS THE POINT. The
    red-first arm has to show a plant that A PASSES and A′ REFUSES; if the two
    were separate implementations, the demonstration would be about the difference
    between two programs rather than about the difference between two DESIGNS."""
    default, per, _ = kd.read_budgets(kd.BUDGET_FILE)
    floor, ceilings = read_registry()
    findings, rows = [], []

    for m in sorted(data["base_ku"]):
        base, head = data["base_ku"][m], data["head_ku"][m]
        d = head - base
        budget = per.get(m, default)
        if budget is None:
            # ⛔ NO THIRD CASE — the ms budget file's own rule, and for the same
            # reason: a declared list's gaps all fall the way its default points.
            print(f"⛔ {m} has neither a registered budget nor a @default in "
                  f"{kd.BUDGET_FILE}.")
            sys.exit(2)
        allow = kd.effective(budget, base, floor)
        over = d > allow
        rows.append((m, base, head, d, allow, over))
        if over:
            findings.append(f"Δku {m}: {d:+,} unfoldings against an allowance of "
                            f"{allow:,.0f} ({budget[1]:g}{'%' if budget[0] == 'rel' else ''} "
                            f"of a base of {base:,}, floor {floor:g})")

    if not quiet:
        print(f"\n{'module':22} {'base ku':>10} {'head ku':>10} {'Δku':>10} "
              f"{'allowance':>10}")
        for m, base, head, d, allow, over in rows:
            print(f"{m:22} {base:>10,} {head:>10,} {d:>+10,} {allow:>10,.0f}"
                  f"{'   ⛔ OVER' if over else ''}")

    ms_rows = []
    mach = data["machine"]
    if arm == "a" and not quiet:
        # ⭐ A READING, NEVER A VERDICT — printed under ARM A precisely because ARM
        # A does not judge it. This is how a NEW MACHINE's ceilings get written:
        # the numbers below, times three, are the lines to register, and until they
        # are registered A′ REFUSES on this box rather than passing. It is the same
        # mechanism that produced `X86.Program 792 @on runnervmlun5p` in
        # `kernel_ceilings.txt`, and it is here so that the runner is one commit
        # away from A′ instead of waiting on somebody to think of measuring it.
        # ⛔ A gate whose precondition is that someone remembers is switched off by
        # the first person who forgets.
        # [[feedback-a-gate-whose-precondition-is-a-discipline]]
        want = sorted({u for (u, _) in ceilings})
        missing = [u for u in want if (u, mach) not in ceilings]
        print(f"\nREADINGS on {mach} for the modules A′ gates by ms "
              f"(ARM A does not judge these):")
        for u in want:
            got = data["head_ms"].get(u)
            have = ceilings.get((u, mach))
            print(f"  {u:16} head {got if got is None else f'{got:,.0f}'} ms"
                  f"   registered here: {'—' if have is None else f'{have:,.0f} ms'}"
                  f"{'' if have is not None or got is None else f'   ⇒ would register {max(got * 3.0, 50):,.0f}'}")
        if missing:
            print(f"  ⚠️ {len(missing)} of {len(want)} have NO ceiling on this box, so "
                  f"A′ would REFUSE here. Register them from a WORST-of-four reading, "
                  f"not from this single pass.")
    if arm == "a-prime":
        gated = sorted(u for (u, mm) in ceilings if mm == mach)
        if not gated:
            # ⛔ REFUSE, DO NOT PASS. A′ without its complement is ARM A, and ARM A
            # reports a confident zero on exactly the work the complement exists to
            # catch. A green here would be the blindness reading as a measurement.
            print(f"⛔ this box is {mach!r} and A′'s registry names no ms ceiling for "
                  f"it. A′ WITHOUT ITS ms HALF IS ARM A, and ARM A passes literal "
                  f"arithmetic and large no-unfolding terms AT ANY SIZE with an exact "
                  f"zero (D228). Register a ceiling on this box or run --arm a and "
                  f"say so.")
            sys.exit(2)
        for u in gated:
            ceil = ceilings[(u, mach)]
            got = data["head_ms"].get(u)
            if got is None:
                print(f"⛔ A′ gates {u} on {mach} and the profiler returned no reading "
                      f"for it.")
                sys.exit(2)
            over = got > ceil
            ms_rows.append((u, got, ceil, over))
            if over:
                findings.append(f"ms ceiling {u}: {got:,.0f} ms against an absolute "
                                f"ceiling of {ceil:,.0f} ms on {mach}")
        if not quiet:
            print(f"\n{'module (ms ceiling)':22} {'head ms':>10} {'ceiling':>10} "
                  f"{'of ceiling':>11}")
            for u, got, ceil, over in ms_rows:
                print(f"{u:22} {got:>10,.0f} {ceil:>10,.0f} {100 * got / ceil:>10.0f}%"
                      f"{'   ⛔ OVER' if over else ''}")

    if not quiet:
        print(f"\n{data['box']}")
        print(f"arm {arm} · {data['base_rev'][:9]} → {data['head_rev'][:9]}"
              f"{' · PLANTED' if data['planted'] else ''}")
    return (1 if findings else 0), findings


def report(rc, findings, arm):
    if rc == 0:
        print(f"ku-delta gate ({arm}): CLEAN")
    else:
        print(f"ku-delta gate ({arm}): FAILED — {len(findings)} finding(s)")
        for f in findings:
            print(f"  ⛔ {f}")
    return rc


# ────────────────────────────────────────────────────────────────────────────
# THE SELFTEST
# ────────────────────────────────────────────────────────────────────────────
def _fixture(tmp, body):
    p = os.path.join(tmp, "budget.txt")
    with open(p, "w", encoding="utf-8") as fh:
        fh.write(body)
    return p


def selftest():
    """Pure arms over fixtures. ⛔ Every arm was driven RED against the code before
    the code was written to satisfy it; the mutations are named beside each."""
    arms, red = 0, []

    def check(name, cond):
        nonlocal arms
        arms += 1
        if not cond:
            red.append(name)

    tmp = tempfile.mkdtemp(prefix="x86lean-kudelta-selftest-")
    try:
        # ── the registry parser ────────────────────────────────────────────
        # red-first: with the machine split removed, the unit reads
        # "X86.Basic @ms @on yukon.lan" and no ceiling is ever found.
        floor, ceil = read_registry(_fixture(tmp, "@floor 10\nX86.Basic @ms @on box1 267\n"))
        check("floor is read", floor == 10)
        check("ceiling keyed by (unit, machine)", ceil == {("X86.Basic", "box1"): 267.0})

        # ⛔⛔ AN ORDERLY REFUSAL, NOT MERELY A NON-ZERO EXIT — AND THIS WAS FOUND BY
        # THE MUTATION MATRIX, NOT BY REVIEW. This predicate was `returncode != 0`,
        # and THREE arms below (@floor absent, a wrong unit shape, a machine-less
        # ceiling) then PASSED with the very refusal they name DELETED: with the
        # check gone the parser ran on to a `TypeError` — formatting `None` as a
        # number — and CRASHED, which is also non-zero.
        # ⇒ 🔑 A TWO-VALUED CLASSIFIER OVER A THREE-VALUED WORLD (pass · refuse ·
        # crash) SCORES THE UNSEEN STATE AS WHICHEVER VALUE IS THE RESIDUAL, and
        # here the residual was "refused" — the flattering one.
        # [[feedback-a-classifiers-value-set-is-a-claim]]
        # So: rc must be exactly 2 (this gate's documented REFUSED code, never 1
        # which is a verdict and never 3 which this gate does not have), and the
        # refusal must NAME its cause — the repository's own law that a gate which
        # refuses must say what it saw (D94).
        def refuses(body, needle):
            r = subprocess.run([sys.executable, __file__, "--check-registry"],
                               cwd=ROOT, capture_output=True, text=True,
                               env={**os.environ, "X86LEAN_KU_BUDGET": _fixture(tmp, body)})
            return r.returncode == 2 and needle in (r.stdout + r.stderr)

        # ⛔ EACH OF THESE IS A HOLE A GATE FAILS THROUGH SILENTLY IF IT IS NOT
        # REFUSED, so each is a separate arm rather than one "bad input" arm.
        check("no @floor is refused",
              refuses("X86.Basic @ms @on box1 267\n", "no @floor"))
        check("a machine-less ceiling is refused",
              refuses("@floor 10\nX86.Basic @ms 267\n", "carries no"))
        # ⛔ THE VALUE IS 300%, NOT 30%, AND THE DIFFERENCE IS THE WHOLE ARM. With
        # `30%` this arm PASSED WITH THE REFUSAL IT NAMES DELETED — the mutation
        # applied, and the cross-registry check caught the fixture instead, because
        # 30 parses as 30 ms and 30 < the reading registry's 163. An arm satisfied
        # by a NEIGHBOURING check is not an arm. At 300 the cross-check is content
        # (300 > 163) and only the refusal under test can red it.
        # [[feedback-two-defects-that-cancel]]
        check("a relative ceiling is refused",
              refuses("@floor 10\nX86.Basic @ms @on box1 300%\n", "ABSOLUTE milliseconds"))
        check("a @default is refused",
              refuses("@floor 10\n@default 10%\nX86.Basic @ms @on box1 267\n",
                      "must not carry @default"))
        # ⛔ THE FIXTURE CARRIES A MACHINE, AND THAT IS THE ARM. With `X86.Basic 267`
        # this arm passed with the shape refusal deleted, because the MACHINE check
        # one line down caught it instead — a neighbouring check lending its red.
        # `@xx` has a machine, so only the shape refusal can red it.
        check("an unrecognised unit shape is refused",
              refuses("@floor 10\nX86.Basic @xx @on box1 267\n", "unrecognised line"))
        check("a duplicate (unit, machine) is refused",
              refuses("@floor 10\nX86.Basic @ms @on box1 267\nX86.Basic @ms @on box1 300\n",
                      "DUPLICATE"))

        # ── the module population ──────────────────────────────────────────
        # red-first: with the union replaced by the base tree's list alone, the
        # "a module only the head has" arm reds — which is the change that would
        # make "add a module" the one change this gate cannot judge.
        base_p = {"modules": {"X86.Basic": 83.3, "X86.Syntax": 271.0, "X86.Theorems": 970.0}}
        head_p = {"modules": {"X86.Basic": 83.3, "X86.Syntax": 271.0, "X86.Theorems": 970.0,
                              "X86.Brand.New": 4.0}}
        mods = ku_modules(base_p, head_p)
        check("every ku-gated unit is a bare module", all("@" not in m for m in mods))
        check("a module only the HEAD tree has is in the population",
              "X86.Brand.New" in mods)
        check("the population is the UNION and nothing else",
              set(mods) == set(base_p["modules"]) | set(head_p["modules"]))
        # ⛔ AND THE ARM THAT WOULD HAVE CAUGHT THE FIRST DRAFT'S DEFECT: the
        # population must NOT be the ms budget file's rows. `X86.Program` and
        # `Tests.Program` are registered in `kernel_ceilings.txt` and absent from
        # `kernel_delta_budget.txt`, so a budget-file population omits them.
        _, ms_rows, _ = kd.read_budgets(kd.BUDGET_FILE)
        omitted = {"X86.Program", "Tests.Program"}
        check("the ms budget file really does omit those two (the arm's premise)",
              not (omitted & set(ms_rows)))
        check("and a profiler population still gates them",
              omitted <= set(ku_modules({"modules": {m: 1.0 for m in omitted}})))

        # ── the verdict, on synthetic readings ─────────────────────────────
        # ⭐ THE DISCRIMINATOR ARM THE HELM ASKED FOR, IN ITS PURE FORM: one set of
        # readings, two arms, two verdicts. Δku is 0 (the plant is ku-blind) and the
        # head's ms is over the ceiling. Red-first: with the `arm` switch ignored,
        # both arms return the same rc and this arm and the next cannot both pass.
        reg = _fixture(tmp, "@floor 10\nX86.Basic @ms @on selftestbox 267\n")
        blind = {"base_rev": "a" * 40, "head_rev": "b" * 40, "planted": True,
                 "box": "fixture", "machine": "selftestbox",
                 "base_ku": {"X86.Basic": 15856}, "head_ku": {"X86.Basic": 15856},
                 "head_ms": {"X86.Basic": 474.0}}
        saved, globals()["BUDGET_FILE"] = BUDGET_FILE, reg
        try:
            rc_a, f_a = verdict(blind, "a", quiet=True)
            rc_ap, f_ap = verdict(blind, "a-prime", quiet=True)
            check("ARM A PASSES the ku-blind plant", rc_a == 0 and not f_a)
            check("ARM A′ REFUSES the ku-blind plant", rc_ap == 1 and len(f_ap) == 1)
            check("and it refuses it for the ms ceiling, not for ku",
                  rc_ap == 1 and f_ap[0].startswith("ms ceiling"))

            # the mirror: a ku-VISIBLE regression must be caught by BOTH arms, or the
            # ku half is decorative. Δku +64,240 is D229 §2's N=512 constructor plant.
            seen = dict(blind, base_ku={"X86.Syntax": 23918},
                        head_ku={"X86.Syntax": 88158}, head_ms={"X86.Basic": 80.0})
            rc_a2, f_a2 = verdict(seen, "a", quiet=True)
            check("ARM A catches a ku-VISIBLE regression", rc_a2 == 1 and
                  f_a2[0].startswith("Δku"))

            # a clean pair passes both arms — the control, without which every arm
            # above is satisfied by a gate that refuses everything.
            ok = dict(blind, head_ms={"X86.Basic": 80.0})
            check("a clean pair passes ARM A", verdict(ok, "a", quiet=True)[0] == 0)
            check("a clean pair passes ARM A′", verdict(ok, "a-prime", quiet=True)[0] == 0)

            # ⛔ AND THE ONE THAT MATTERS MOST: A′ on a box with no registered ceiling
            # must REFUSE, not pass. A pass there is ARM A wearing A′'s name.
            r = subprocess.run([sys.executable, "-c",
                                "import sys; sys.path.insert(0, %r); import ku_delta as k; "
                                "k.BUDGET_FILE = %r; "
                                "k.verdict(%r, 'a-prime', quiet=True)"
                                % (HERE, reg, dict(ok, machine="some-other-box"))],
                               cwd=ROOT, capture_output=True, text=True)
            check("A′ on a box with no ceiling REFUSES rather than passing",
                  r.returncode == 2 and "ARM A" in r.stdout)
        finally:
            globals()["BUDGET_FILE"] = saved

        # ── the cross-registry check ───────────────────────────────────────
        # red-first: with the comparison reversed, the shipped registry reds.
        check("the shipped registry cross-checks CLEAN", check_registry(quiet=True) == 0)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    print(f"ku_delta selftest: {arms - len(red)}/{arms} arms")
    for r in red:
        print(f"  ⛔ RED: {r}")
    return 1 if red else 0


# ────────────────────────────────────────────────────────────────────────────
# THE RED-FIRST ARM ON REAL TREES — the one the helm asked for by name
# ────────────────────────────────────────────────────────────────────────────
# ⭐⭐ *"a plant that ARM A passes and A′ refuses"*.
#
# The plant is a K3 term from `ku_kind_plants.py` — an N-deep `And.intro`, one of
# the two kinds D228 MEASURED the unfolding counter to be blind to. It is a REAL
# declaration in a REAL module (`X86.Basic`), not a fixture, and it is the honest
# adversary for this design: it is not a change the counter under-prices, it is a
# change the counter CANNOT SEE AT ALL, so ARM A does not merely pass it — ARM A
# passes it with an exact, confident zero at any budget whatsoever.
#
# ⚠️ N IS 4000 AND IT WAS CHOSEN BY MEASUREMENT BEFORE THIS GATE EXISTED, not
# tuned until the arm went red. Driven on this box 2026-09-13, three profile
# passes a side, `X86.Basic` at HEAD:
#     base                 ku 15,856   ms 88.7 · 95.9 · 89.0   (median 89.0)
#     K3 n=2000            ku 15,856   Δku  +0                  Δms  +96.3
#     K3 n=4000            ku 15,856   Δku  +0                  Δms +385.0
#     K2 n=16,000,000      ku 15,866   Δku +10 (the instrument's own header)
#                                                               Δms  +52.3
# n=4000 is the smallest of these that clears a ×3 ceiling with room to spare; the
# smaller sizes are recorded because a plant that only just clears is a plant that
# will stop clearing on a quieter box.
# ⛔⛔ AND THE QUIETER BOX ARRIVED: THE RUNNER'S FAST VM CLASS (ARMA-1, D244). The runner's ceiling
#   is worst-of-16 x3 = 567 ms on X86.Basic, and D243 measured the VMs `ubuntu-latest` draws under
#   ONE machine name spanning 0.58x-1.1x of the median. Re-measured 2026-09-14 on this box, one file,
#   `import X86.Basic`, kernel `type checking` per declaration:
#       K3 n=4000     365 ms   (D240's +385 reproduced within 5% -- the control)
#       K3 n=8000   1,630 ms   (x4.5: super-linear, as D228 measured)
#   Predicted on the runner from the per-module local<->runner factor (fast class ~1.13x this box,
#   typical ~1.95x): n=4000 reads ~99 + 365x1.13 = ~511 ms on a FAST draw -- UNDER 567, a MISS, so the
#   measured red-first arm would have flaked on which VM the job drew. n=8000 reads ~1,940 (3.4x) fast
#   and ~3,350 (5.9x) typical. ⇒ SIZE THE PLANT TO THE GATE ON ITS FASTEST MACHINE, not to the box it
#   was calibrated on. [[feedback-size-the-plant-to-the-gate-not-the-phenomenon]]
#   ⚠️ The runner figures are PREDICTIONS from a factor measured on module readings; the CI job's
#   own first runs are the measurement, and its summary prints the margin.
K3_N = 8000


def plant_ku_blind(n=K3_N):
    """Append a ku-blind K3 declaration to `X86/Basic.lean` in the head worktree."""
    import ku_kind_plants as kp

    def go(worktree):
        p = os.path.join(worktree, "X86", "Basic.lean")
        s = open(p, encoding="utf-8").read()
        decl = kp.k3(n).replace("theorem plant", f"theorem ku_blind_plant_{n}")
        # `maxRecDepth`: the ELABORATOR needs it for a term this deep. It changes
        # what the elaborator agrees to do, not the kind of work the kernel is
        # handed (D228 §5 makes the same point for K2's exponentiation threshold).
        s2 = s + f"\n\nset_option maxRecDepth 4000000 in\n{decl}\n"
        # ⛔ A PROBE THAT SILENTLY FAILS TO CREATE ITS CONDITION REPORTS THE GATE AS
        # SOUND, and its GREEN is more dangerous than no probe at all.
        # [[feedback-a-probe-must-create-its-condition]]
        if s2 == s or f"ku_blind_plant_{n}" not in s2:
            refuse("⛔ the ku-blind plant did not apply to X86/Basic.lean.")
        open(p, "w", encoding="utf-8").write(s2)
    return go


def selftest_measure():
    """Two arms on real trees, one measurement, two designs.

    ⭐ BOTH ARMS READ THE SAME `data`. The plant is measured ONCE and judged twice,
    so what the arm demonstrates is a difference between ARM A and ARM A′ and not a
    difference between two runs — which on a timing quantity would be no
    demonstration at all.

    ⛔ AND THE NEGATIVE CONTROL RUNS FIRST AND CAN INVALIDATE EVERYTHING: identical
    trees, no plant, both arms must be CLEAN. Δku is exact, so unlike the ms gate's
    control this one has no excuse available to it — a non-zero Δku on identical
    trees is a broken instrument, full stop, and there is no noise to blame."""
    head = kd.arg("--head", "HEAD")
    rc_total, lines = 0, []

    print("── ARM 1 · NEGATIVE CONTROL: identical trees, no plant ──────────────")
    ctl = measure(head, head, keep=None, plant=None)
    moved = {m: ctl["head_ku"][m] - ctl["base_ku"][m]
             for m in ctl["base_ku"] if ctl["head_ku"][m] != ctl["base_ku"][m]}
    if moved:
        print(f"⛔ Δku is NOT ZERO on identical trees: {moved}. This gate's whole "
              f"claim is that the counter is exact; it is not, here, and no verdict "
              f"below can be trusted.")
        return 2
    print(f"✅ Δku is exactly 0 on all {len(ctl['base_ku'])} modules")
    for arm in ("a", "a-prime"):
        rc, f = verdict(ctl, arm, quiet=True)
        lines.append(f"control  arm {arm:8} rc {rc} {'CLEAN' if rc == 0 else f}")
        if rc != 0:
            rc_total = 1

    print(f"\n── ARM 2 · THE ku-BLIND PLANT (K3, n={K3_N}) ────────────────────────")
    pl = measure(head, head, keep=None, plant=plant_ku_blind())
    rc_a, f_a = verdict(pl, "a", quiet=False)
    rc_ap, f_ap = verdict(pl, "a-prime", quiet=True)
    lines.append(f"planted  arm a        rc {rc_a} "
                 f"{'PASSED (as designed)' if rc_a == 0 else f_a}")
    lines.append(f"planted  arm a-prime  rc {rc_ap} "
                 f"{'⛔ MISSED IT' if rc_ap == 0 else f_ap}")
    # THE DISCRIMINATOR. Either half failing means the arm proved nothing: if A
    # also refuses, the plant was not ku-blind and this says nothing about the
    # complement; if A′ passes, the complement does not work.
    if rc_a != 0:
        print(f"\n⛔ ARM A REFUSED the plant, so it is not ku-blind after all and "
              f"this arm demonstrates NOTHING about A′'s complement: {f_a}")
        rc_total = 1
    if rc_ap == 0:
        print(f"\n⛔ ARM A′ PASSED a plant that adds hundreds of milliseconds of "
              f"kernel time. The complement did not fire.")
        rc_total = 1
    if rc_a == 0 and rc_ap != 0 and not all(f.startswith("ms ceiling") for f in f_ap):
        print(f"\n⛔ A′ refused, but not (only) on the ms ceiling: {f_ap}. The arm "
              f"has to show the COMPLEMENT firing, not the ku half.")
        rc_total = 1

    print("\n── VERDICT ──────────────────────────────────────────────────────────")
    for l in lines:
        print(f"  {l}")
    print(f"\nku-delta measured selftest: "
          f"{'PASS — ARM A passes the ku-blind plant, ARM A′ refuses it' if rc_total == 0 else 'FAIL'}")
    return rc_total


# ────────────────────────────────────────────────────────────────────────────
def main():
    if "--selftest" in sys.argv:
        return selftest()
    if "--selftest-measure" in sys.argv:
        return selftest_measure()
    if "--check-registry" in sys.argv:
        return check_registry()

    arm = kd.arg("--arm", "a-prime")
    if arm not in ("a", "a-prime"):
        refuse(f"⛔ --arm is `a` or `a-prime`, not {arm!r}")
    head = kd.arg("--head", "HEAD")
    base = kd.arg("--base") or kd.resolve_base(head)
    print(f"ARM {arm.upper()} · {kd.git('rev-parse', base)[:9]} → "
          f"{kd.git('rev-parse', head)[:9]}")
    data = measure(base, head, keep=kd.arg("--keep"))
    rc, findings = verdict(data, arm)
    out = kd.arg("--json")
    if out:
        with open(out, "w", encoding="utf-8") as fh:
            json.dump({**data, "arm": arm, "rc": rc, "findings": findings}, fh, indent=1)
    return report(rc, findings, arm)


if __name__ == "__main__":
    sys.exit(main())
