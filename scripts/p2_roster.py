#!/usr/bin/env python3
"""⭐⭐ THE P2 ROSTER — K's SIMD/FP forms, PRICED BY THE DEMAND-SIDE CENSUS.

P1's roster answered "what does the coverage target list contain".  That is the
SUPPLY side, and on its own it prices a wave by counting forms — which values a
mnemonic no binary contains exactly as highly as one in every codec kernel.
This roster is the JOIN: K's SIMD/FP variants (the 1,665 `k_roster.py` drops as
P2) against the occurrences the assembly column class actually measured.

⛔ THE JOIN IS PUBLISHED WITH BOTH RESIDUES, because a join reports agreement
where it has looked and says nothing where it has not:

  * SUPPLY WITHOUT DEMAND — a K form the corpus never executes.  Cheap to
    model, worth nothing to model first.
  * DEMAND WITHOUT SUPPLY — a mnemonic the corpus runs that K has no rule for.
    ⚠️ This is the dangerous residue: it cannot be priced from K at all, and a
    roster that silently omitted it would price P2 too low
    ([[feedback-conservative-is-a-direction-not-a-margin]]).

⚠️ K COVERAGE HERE IS A CATALOGUE READING, NOT A MEASUREMENT.  That a `.k` file
exists for a form says the oracle NAMES it; whether the oracle EXECUTES it is a
separate question this repository has already been wrong about once, and the
answer comes from running it, not from reading the tree
([[feedback-cheap-semantics-expensive-state]]).  Every batch below is priced
"runnable pending an oracle-availability run", and that phrase is the gate.

PUBLIC SOURCES.  K x86-64 (NCSA, (c) 2019 UIUC) is READ, never copied: this
script emits counts, mnemonic names and operand shapes -- facts about the
architecture.  The census's corpus is public Debian binaries, counted never
copied.

LANE.  Personal lane, public sources only.

Usage:  p2_roster.py [--out docs/P2-ROSTER.md]
        p2_roster.py --selftest
"""
from __future__ import annotations
import os, re, sys, json, collections, argparse

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
# ⚠️ `k_roster` guards its `main` with `__name__`, so importing it is safe and
# the SIMD predicate is used from its definition rather than restated here.
# ⛔ `demand_census` is NOT importable — it calls `sys.exit(main())` at module
# level, so an import RUNS it and takes this process's argv with it.  Its output
# is consumed through the JSON, which is the artifact anyway.
import k_roster as K
# ⭐ AND the P2 availability table, which is a MEASUREMENT of the oracle rather
# than a reading of it.  This import is only possible because that file's bare
# `sys.exit(main())` was guarded — the first attempt to reuse its runner ran the
# P1 gate and exited this process instead.
import oracle_availability as OA

CENSUS_JSON = os.path.join(root, "docs", "DEMAND-CENSUS.md.json")

# ── the three additions the Captain ordered into P2, IN HIS ORDER ──────────
# ⛔ THESE ARE NOT SIMD, and pricing them inside the vector roster would bury
# them.  Each is a scalar capability the model declined by DESIGN in P0/P1, each
# is a named bucket in the census, so each carries its own measured demand.
ADDITIONS = [
    ("segment base in `Ea`", "segment base %fs:/%gs: (P2 addition 1)",
     "`Ea` has no segment field: segmentation was declared out of scope, so "
     "`mov %fs:0x28, %rax` — the stack-protector load in most compiled "
     "functions — is refused. The addition is a base register on the effective "
     "address, not segmentation: FS/GS are the only two overrides long mode "
     "honours, and their base is an MSR-loaded value the model can carry as "
     "state."),
    ("the LOCK vocabulary", "LOCK prefix (P2 addition 2)",
     "D25 declines `xchg` at memory and the six `bt`-family memory forms "
     "BECAUSE there is no LOCK vocabulary to state their atomicity in. The "
     "addition unblocks those declined rows as a side effect, which is why it "
     "is worth more than its occurrence count says."),
    ("the `movabs` mov form", "mov imm64 / movabs (P2 addition 3)",
     "The 64-bit immediate move is a distinct encoding, not a width of the "
     "existing `mov`: `movabsq $imm64, %r64` is the only form that carries a "
     "full 64-bit immediate, and it is what a compiler emits for any address "
     "or constant that does not fit in 32 bits."),
]


def census():
    try:
        return json.load(open(CENSUS_JSON))
    except OSError:
        print(f"⛔ {CENSUS_JSON} is missing. The P2 roster is priced BY the "
              f"census; without it this tool would rank forms by K's file order, "
              f"which is not a price. Generate the census first.")
        sys.exit(2)


def demand(d):
    """Uncovered occurrences in the ASSEMBLY class, pooled — never with the
    compiler columns, and never with the kernel."""
    cols = [g for g, r in d.items()
            if isinstance(r, dict) and r.get("class") == "asm"]
    m = collections.Counter()
    for g in cols:
        for k, v in d[g]["miss_all"].items():
            m[k] += v
    return m, cols


def k_simd():
    """The variants `k_roster.py` DROPS as SIMD/FP — P2's supply side.

    ⚠️ Derived by the same predicate, in the same file, rather than restated
    here: a second copy of an exclusion rule is a rule that can disagree with
    itself ([[feedback-duplicate-born-in-agreement]])."""
    sem = os.path.join(root, "vendor", "k-x86-64", "semantics")
    if not os.path.isdir(sem):
        print(f"⛔ K's semantics tree is not at {sem}. "
              f"Run scripts/setup_k_roster.sh first.")
        sys.exit(2)
    out, seen = [], set()
    for sub in K.SUBDIRS:
        dp = os.path.join(sem, sub)
        for fn in sorted(os.listdir(dp)):
            if not fn.endswith(".k") or fn in seen:
                continue
            seen.add(fn)
            _prefix, tok, ops = K.parse_name(fn[:-2])
            simd = (tok in K.EXCLUDE_TOKENS
                    or any(tok.startswith(p) for p in K.EXCLUDE_PREFIX)
                    or any(K.VECTOR_OPERAND.match(o) for o in ops))
            if simd:
                out.append((tok, tuple(ops)))
    return out


OUTSCOPE_RE = re.compile(r"^(\S+) \((vector|segment|lock) operand\)$")

def join_key(census_key):
    """(mnemonic, routing) for a census key.

    ⛔ THE THREE OUT-OF-SCOPE KINDS ROUTE DIFFERENTLY, and collapsing them was
    the join's first defect.  A SEGMENT- or LOCK-prefixed instruction is not
    vector work at all — it is P2 addition 1 or 2, already priced in its own
    table — so it must leave the vector join rather than sit in it as
    unexplained demand.  A VECTOR-operand instruction IS vector work, and it
    joins on the mnemonic objdump printed (`movq`), which is the name K's rule
    carries."""
    # ⚠️ `movabs` carries no prefix and no vector operand, so nothing in the
    # census's KIND can route it — it is addition 3 by its identity, and left
    # in the vector pool it reads as SIMD work K forgot to model.
    if census_key in ("movabsq", "movabs", "movabsl"):
        return census_key, "addition"
    m = OUTSCOPE_RE.match(census_key)
    if not m:
        return census_key, "vector"
    return m.group(1), ("vector" if m.group(2) == "vector" else "addition")


def build(d):
    dem, cols = demand(d)
    total_uncovered = sum(dem.values())
    forms = k_simd()
    by_mn = collections.defaultdict(set)
    for tok, ops in forms:
        by_mn[tok].add("".join(K.operand_class(o)[0] for o in ops) or "-")
    k_mnemonics = set(by_mn)

    # ── the join, and both residues ──
    # ⚠️ The demand is re-keyed for the join, and the ADDITIONS' demand is taken
    # OUT of the vector gap rather than left in it as unexplained.
    vec_dem, add_dem = collections.Counter(), collections.Counter()
    for ck, occ in dem.items():
        mn, route = join_key(ck)
        (vec_dem if route == "vector" else add_dem)[mn] += occ
    joined, supply_only, demand_only = [], [], []
    for mn, shapes in sorted(by_mn.items()):
        occ = vec_dem.get(mn, 0)
        (joined if occ else supply_only).append((mn, occ, sorted(shapes)))
    for mn, occ in vec_dem.items():
        if mn not in k_mnemonics:
            demand_only.append((mn, occ))
    joined.sort(key=lambda t: -t[1])
    demand_only.sort(key=lambda t: -t[1])
    return dict(dem=dem, vec_dem=vec_dem, add_dem=add_dem,
                total_uncovered=total_uncovered, cols=cols,
                by_mn=by_mn, joined=joined, supply_only=supply_only,
                demand_only=demand_only, n_variants=len(forms))


def write(d, b, fh):
    fh.write("<!-- GENERATED by `scripts/p2_roster.py`. Do not edit by hand. -->\n\n")
    fh.write("# P2 roster — K's SIMD/FP forms, priced by the demand census\n\n")
    fh.write(f"""P1's roster counted forms. This one counts what runs them.

The supply side is K's own tree: the **{b['n_variants']:,} variants**
`scripts/k_roster.py` drops as SIMD/FP, over **{len(b['by_mn'])} distinct
mnemonics**. The demand side is the assembly column class of
`docs/DEMAND-CENSUS.md` — **{b['total_uncovered']:,} instructions the model does
not cover**, across {len(b['cols'])} codec columns, never pooled with compiler
output or with the kernel.

⚠️ **K coverage below is a CATALOGUE reading.** A `.k` file existing for a form
says the oracle NAMES it, not that the oracle EXECUTES it. Every batch is priced
*runnable pending an oracle-availability run*, and that run — not this table —
is what makes a batch startable.

""")

    # ── the three additions, first, in the Captain's order ──
    fh.write("## The three additions, in the order the Captain gave them\n\n")
    fh.write("⛔ **Not SIMD, and not priced inside the vector roster.** Each is a "
             "scalar capability this model declined by design, and each is a "
             "named row in the census, so each carries a measured demand rather "
             "than an argument.\n\n")
    ext = collections.Counter()
    for g, r in d.items():
        if isinstance(r, dict) and r.get("class") == "asm":
            for e, k in r.get("ext", {}).items():
                ext[e] += k
    fh.write("| # | addition | measured demand (asm class) | share of the gap |\n")
    fh.write("|---|---|---|---|\n")
    for i, (name, key, _why) in enumerate(ADDITIONS, 1):
        k = ext.get(key, 0)
        fh.write(f"| {i} | {name} | {k:,} | "
                 f"{100.0*k/b['total_uncovered']:.2f}% |\n")
    fh.write("\n")
    for i, (name, key, why) in enumerate(ADDITIONS, 1):
        fh.write(f"**{i}. {name}** — {why}\n\n")
    fh.write("""⚠️ **The LOCK vocabulary's occurrence count under-states it by
construction.** Codec kernels are single-threaded inner loops; the count that
matters for LOCK is in the KERNEL column, where the census reads 9,029
lock-prefixed instructions, and in the six rows P1 declined ON RECORD for want
of it. An addition whose value is in what it UNBLOCKS cannot be ranked by its
own frequency, which is why it is listed second by the Captain's order and not
by this table's sort.

""")

    # ── the vector roster, ranked by demand ──
    fh.write("## The vector roster, ranked by measured demand\n\n")
    fh.write("Cumulative share is over the whole uncovered gap "
             f"({b['total_uncovered']:,} instructions), so a row's cumulative "
             "column answers: *if P2 stopped here, what fraction of the "
             "assembly class would the model execute?*\n\n")
    fh.write("| rank | mnemonic | occurrences | share | cumulative | K operand shapes |\n")
    fh.write("|---|---|---|---|---|---|\n")
    cum = 0
    for i, (mn, occ, shapes) in enumerate(b["joined"][:40], 1):
        cum += occ
        fh.write(f"| {i} | `{mn}` | {occ:,} | "
                 f"{100.0*occ/b['total_uncovered']:.2f}% | "
                 f"{100.0*cum/b['total_uncovered']:.1f}% | "
                 f"{', '.join('`'+s+'`' for s in shapes)} |\n")
    joined_total = sum(o for _m, o, _s in b["joined"])
    fh.write(f"\n- The joined set — **{len(b['joined'])} mnemonics K has "
             f"semantics for AND the corpus executes** — accounts for "
             f"**{joined_total:,} instructions "
             f"({100.0*joined_total/b['total_uncovered']:.1f}% of the gap)**.\n")

    # ── both residues, printed ──
    do_total = sum(o for _m, o in b["demand_only"])
    fh.write(f"\n## The two residues\n\n")
    fh.write(f"### ⛔ Demand without supply — {len(b['demand_only'])} mnemonics, "
             f"{do_total:,} instructions ({100.0*do_total/b['total_uncovered']:.1f}% "
             f"of the gap)\n\n")
    fh.write("The corpus executes these and **K has no rule for them**, so they "
             "cannot be priced from the coverage target list at all. A roster "
             "that listed only the join would price P2 this much too low.\n\n")
    fh.write("| rank | mnemonic | occurrences | share |\n|---|---|---|---|\n")
    for i, (mn, occ) in enumerate(b["demand_only"][:25], 1):
        fh.write(f"| {i} | `{mn}` | {occ:,} | "
                 f"{100.0*occ/b['total_uncovered']:.2f}% |\n")
    fh.write(f"\n### Supply without demand — {len(b['supply_only'])} mnemonics\n\n")
    fh.write("K has semantics for these and the corpus never executes one. "
             "Cheap to model; worth nothing to model first.\n\n")
    fh.write("`" + "`, `".join(m for m, _o, _s in b["supply_only"][:60]) + "`\n")
    if len(b["supply_only"]) > 60:
        fh.write(f"\n…and {len(b['supply_only'])-60} more.\n")

    # ── what the oracle can actually answer, MEASURED ──
    dem, _cols = demand(d)
    vec = collections.Counter()
    for ck, occ in dem.items():
        mn, route = join_key(ck)
        if route == "vector":
            vec[mn] += occ
    # ⛔ ONE VERDICT PER MNEMONIC, NOT ONE PER PROBE.  `movq_xmm` and `movq_mmx`
    # are two probes of the same census key (`movq`), and `paddw` is probed at
    # both an xmm and an mm operand — because the CENSUS pools an MMX and an SSE
    # spelling under one mnemonic, which is a real limit of a mnemonic-level
    # count and not something this join can undo.  Counting per probe added
    # `movq`'s 28,019 twice and `paddw`'s once too often, in the direction that
    # makes the oracle look better than it is.
    verdict = {}
    conflict = []
    for label, _asm, _b, _e0, e1 in OA.P2_FORMS:
        if label.startswith(("CONTROL", "ADD")):
            continue
        mn = label.split("_")[0]
        if mn in verdict and verdict[mn] != e1:
            conflict.append(mn)
        verdict[mn] = "refuses" if conflict and mn in conflict else e1
    ex = rf = 0
    ex_names, rf_names = [], []
    for mn, v in sorted(verdict.items()):
        occ = vec.get(mn, 0)
        if v == "executes":
            ex += occ; ex_names.append(mn)
        else:
            rf += occ; rf_names.append(mn)
    probed = ex + rf
    fh.write("\n## What the oracle can answer — measured, not read\n\n")
    fh.write(f"""`scripts/oracle_availability.py --p2` runs every form below on ACL2
x86isa under **two CR4 settings**, with an always-executes control and an
always-refuses control in each arm.

⛔ **The first reading of this said P2 had no oracle at all, and it was a finding
about the PRE-STATES.** Twenty of twenty vector forms refused, both controls
behaving. The oracle's own fault record said `#UD Encountered!` and `CR4` read
**0**: P0 and P1 only ever needed scalar integer instructions, so SSE was never
enabled and x86isa raised #UD exactly as hardware would. Setting
`CR4.OSFXSR|OSXMMEXCPT` makes `movdqa`, `paddd` and `vpaddd` execute.

| | mnemonics | occurrences | share of the gap |
|---|---|---|---|
| the oracle EXECUTES | {len(ex_names)} | {ex:,} | {100.0*ex/b['total_uncovered']:.1f}% |
| the oracle REFUSES | {len(rf_names)} | {rf:,} | {100.0*rf/b['total_uncovered']:.1f}% |
| **probed so far** | {len(ex_names)+len(rf_names)} | **{probed:,}** | **{100.0*probed/b['total_uncovered']:.1f}%** |

So of the demand probed, **{100.0*ex/probed:.0f}% has an oracle** — after a
one-line change to the pre-states, and not before it.

⛔ **A BATCH CANNOT BE PRICED FROM A SAMPLE OF ITS OWN MEMBERS.** Seven SSE forms
were probed and all seven executed; the eighth, `pmaddwd`, refused — and it is
rank 4 in the demand list, 2.31% of the whole gap, refusing in the same run in
which `movdqa` beside it executes. The nine the oracle does not have are
`{'`, `'.join(rf_names)}`.

⚠️ **A mnemonic probed in two register classes gets ONE verdict**, and where the
two disagree the pessimistic one is taken: the census pools an MMX and an SSE
spelling of `paddw` under a single key, so its demand cannot be split between
the batches by mnemonic at all. Conflicts on this run: {conflict or 'none'}.

⛔ **AVX-512 refuses in BOTH arms** — the one batch this oracle cannot answer,
and the only one that needs another (K as an executable oracle, Sail, or the
hardware co-simulation on kenai).

⚠️⚠️ **AND "EXECUTES" IS NOT "DIFFERENTIABLE".** The oracle running a form
without a fault says it can be ASKED. It does not say the harness can SEE the
answer: `x86l-post` reports 16 GPRs, RIP, the flags and two memory windows, and
`X86/State.lean` has no vector register file at all. A P2 differential run today
would execute every vector form on both sides and observe none of their results
— which does not report "unknown", it positively reports agreement. **That is
P2's real harness cost, and this run does not reduce it by one line.**

""")

    # ── the wave, as batches ──
    fh.write("\n## The wave\n\n")
    fh.write("""Batches are cut by ISA bucket, because that is the axis on which
a Lean model pays: a register file is state, and every mnemonic in one width
class shares it. Within a batch the order is by demand.

| batch | bucket | occurrences | share of the gap | cumulative |
|---|---|---|---|---|
""")
    cum = 0
    order = [e for e, _k in ext.most_common()
             if e not in {k for _n, k, _w in ADDITIONS}]
    for i, e in enumerate(order, 1):
        k = ext[e]
        cum += k
        fh.write(f"| {i} | {e} | {k:,} | {100.0*k/b['total_uncovered']:.2f}% | "
                 f"{100.0*cum/b['total_uncovered']:.1f}% |\n")
    add_share = sum(ext.get(k, 0) for _n, k, _w in ADDITIONS)
    fh.write(f"""
⚠️ **This table stops at {100.0*cum/b['total_uncovered']:.1f}%, not at 100%, and the
remainder is not missing.** The three additions are
{add_share:,} instructions ({100.0*add_share/b['total_uncovered']:.1f}% of the gap)
and are priced in their own table above, in the Captain's order rather than by
size. A wave table that silently absorbed them would have ranked a segment base
below MMX.

⚠️ **The first batch is not the cheapest one available.** `SSE-legacy (xmm)` is
{100.0*ext['SSE-legacy (xmm)']/b['total_uncovered']:.0f}% of the gap by itself,
and it is also the widest vocabulary — P1 learned that a wave priced on its
easiest batch is priced wrong, and the price is the whole reason the first batch
is run.

⛔ **Every batch is priced *runnable pending an oracle-availability run*.** P1
measured its oracle by executing it, after a batch was priced from a catalogue
reading and the catalogue was ahead of the tool. Nothing here changes that: the
first act of the first P2 batch is to run the oracle on its forms and report
what it refuses, before any Lean is written.
""")


def selftest():
    """⛔ THE JOIN IS WHERE THIS TOOL WOULD INFLATE OR DEFLATE P2, so it is
    driven on the shapes that would do it."""
    bad = []
    # the SIMD predicate must agree with k_roster's, in both directions
    arms = [
        (("paddb", ("xmm", "xmm")), True),
        (("movdqa", ("xmm", "m128")), True),
        (("cvtsi2sdl", ("xmm", "r32")), True),
        (("vzeroupper", ()), True),
        (("addq", ("r64", "r64")), False),
        (("movq", ("r64", "m64")), False),
        (("cmpxchgq", ("m64", "r64")), False),
    ]
    for (tok, ops), want in arms:
        got = (tok in K.EXCLUDE_TOKENS
               or any(tok.startswith(p) for p in K.EXCLUDE_PREFIX)
               or any(K.VECTOR_OPERAND.match(o) for o in ops))
        ok = got == want
        print(("  ✔ " if ok else "  ⛔ ") +
              f"SIMD? {tok:12s} {str(ops):22s} -> {got}" +
              ("" if ok else f"   EXPECTED {want}"))
        if not ok:
            bad.append(tok)
    # ⛔ THE JOIN KEY, in every shape the census emits.  Getting this wrong put
    # the same 28,019 instructions into BOTH residues at once.
    key_arms = [
        ("movdqa", ("movdqa", "vector")),
        ("movq (vector operand)", ("movq", "vector")),
        ("movq (segment operand)", ("movq", "addition")),
        ("incl (lock operand)", ("incl", "addition")),
        ("movabsq", ("movabsq", "addition")),
        ("endbr64", ("endbr64", "vector")),
    ]
    for ck, want in key_arms:
        got = join_key(ck)
        ok = got == want
        print(("  ✔ " if ok else "  ⛔ ") + f"join key {ck:26s} -> {got}" +
              ("" if ok else f"   EXPECTED {want}"))
        if not ok:
            bad.append("key:" + ck)

    # the census join must not silently read a truncated list
    d = census()
    asm = [g for g, r in d.items()
           if isinstance(r, dict) and r.get("class") == "asm"]
    ok = bool(asm)
    print(("  ✔ " if ok else "  ⛔ ") +
          f"the census JSON declares an assembly class ({len(asm)} columns)")
    bad += [] if ok else ["asm-class"]
    for g in asm:
        has = "miss_all" in d[g]
        print(("  ✔ " if has else "  ⛔ ") +
              f"column `{g}` carries the FULL uncovered map, not the top 40")
        if not has:
            bad.append("miss_all:" + g)
        # ...and the full map must be a superset of the truncated one
        if has:
            top = dict(x for x in d[g]["miss"])
            sup = all(d[g]["miss_all"].get(k) == v for k, v in top.items())
            print(("  ✔ " if sup else "  ⛔ ") +
                  f"  and it agrees with the top-40 list on every entry")
            if not sup:
                bad.append("miss-agree:" + g)
    # the three additions must each name a bucket the census actually emits
    ext = set()
    for g in asm:
        ext |= set(d[g].get("ext", {}))
    for name, key, _w in ADDITIONS:
        ok = key in ext
        print(("  ✔ " if ok else "  ⛔ ") +
              f"addition `{name}` names a bucket the census emits (`{key}`)")
        if not ok:
            bad.append("addition:" + key)
    if bad:
        print(f"p2-roster selftest: FAIL ({len(bad)} arms)")
        return 1
    print(f"p2-roster selftest: PASS ({len(arms)+len(key_arms)+1+2*len(asm)+len(ADDITIONS)} "
          f"arms; the SIMD predicate in both directions, the join's inputs, and "
          f"every addition tied to a bucket the census emits)")
    return 0


def check(out):
    """⛔ THE DOCUMENT IS DERIVED, SO CI RE-DERIVES IT.  Unlike the census —
    which needs a corpus of downloaded binaries and can only be gated for
    staleness — every input to this roster is IN the repository: K's tree (which
    CI already fetches for the P1 roster) and the census's committed JSON.  So
    there is no excuse for gating anything less than the bytes."""
    import io
    d = census()
    b = build(d)
    buf = io.StringIO()
    write(d, b, buf)
    want = buf.getvalue()
    try:
        have = open(os.path.join(root, out)).read()
    except OSError:
        print(f"⛔ {out} does not exist. Generate it: p2_roster.py")
        return 2
    if have == want:
        print(f"p2-roster gate: CLEAN — {out} is byte-identical to what K's "
              f"tree and the census's JSON derive today.")
        return 0
    import difflib
    diff = list(difflib.unified_diff(have.splitlines(), want.splitlines(),
                                     "committed", "derived", lineterm="", n=1))
    print(f"⛔ {out} IS NOT WHAT IT DERIVES. {len(diff)} diff lines; first 30:")
    print("\n".join(diff[:30]))
    return 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="docs/P2-ROSTER.md")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    if args.selftest:
        return selftest()
    if args.check:
        return check(args.out)
    d = census()
    b = build(d)
    with open(os.path.join(root, args.out), "w") as fh:
        write(d, b, fh)
    print(f"wrote {args.out}")
    print(f"  K SIMD/FP variants {b['n_variants']:,} over "
          f"{len(b['by_mn'])} mnemonics")
    print(f"  gap {b['total_uncovered']:,} instructions; joined "
          f"{sum(o for _m,o,_s in b['joined']):,}; "
          f"demand-without-supply {sum(o for _m,o in b['demand_only']):,}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
