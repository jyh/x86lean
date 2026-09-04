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
# ⭐⭐ `demand_census` IS importable as of D98 — its bare `sys.exit(main())` is
# guarded, the third file here to need that.  Its NUMBERS still arrive through
# the JSON, which is the artifact; what is imported is `EXT_SCOPE`, the ruling
# on which ISA buckets the model's state can represent.  A copy of that
# partition in this file would be a second list to keep in step with the roster,
# and D98 is what a second list does when it stops being kept.
import demand_census as DC
import k_roster as K
# ⭐ AND the P2 availability table, which is a MEASUREMENT of the oracle rather
# than a reading of it.  This import is only possible because that file's bare
# `sys.exit(main())` was guarded — the first attempt to reuse its runner ran the
# P1 gate and exited this process instead.
import oracle_availability as OA
# ⭐⭐ P2 ITEM 2: THE DECLINED TABLE, IMPORTED RATHER THAN DESCRIBED.  This
# document used to SAY what the LOCK vocabulary would unblock, and the sentence
# was wrong in the flattering direction — see the note on `DECLINED` in
# `scripts/claimed_forms.py`.  `claimed_forms` guards its `main` with
# `__name__`, so importing it is safe.
import claimed_forms as CF

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
    ("the LOCK vocabulary", "LOCK prefix (P2 addition 2)", None),  # DERIVED, see lock_why()
    ("the `movabs` mov form", "mov imm64 / movabs (P2 addition 3)",
     "The 64-bit immediate move is a distinct encoding, not a width of the "
     "existing `mov`: `movabsq $imm64, %r64` is the only form that carries a "
     "full 64-bit immediate, and it is what a compiler emits for any address "
     "or constant that does not fit in 32 bits."),
]


def mmx_note(n_mmx, occ):
    """The MMX share of one roster row's demand, as the row prints it.

    ⛔ A FUNCTION SO IT CAN BE ARMED.  The three bands are a claim about how much
    of a row's price is demand the row's own shapes cannot close, and a claim
    rendered inline is a claim no arm can drive."""
    f = 100.0 * n_mmx / occ if occ else 0.0
    return ("⛔ **100% — PHANTOM ROW**" if f > 99.5 else
            f"⚠️ {f:.0f}%" if f >= 10.0 else
            f"{f:.0f}%" if n_mmx else "—")


def lock_why():
    """⭐⭐ THE SENTENCE FOR ADDITION 2, DERIVED FROM `claimed_forms`'s TABLES.

    ⛔ IT WAS PROSE, AND THE PROSE WAS FALSE.  It read: *"D25 declines `xchg` at
    memory and the six `bt`-family memory forms BECAUSE there is no LOCK
    vocabulary to state their atomicity in. The addition unblocks those declined
    rows as a side effect."*  Three errors in one sentence, all in the direction
    that flatters the item: there are FOUR `bt`-family rows and not six (six was
    the TOTAL of declined rows); D23 declines them, not D25; and their reason is
    SIGNED BIT-STRING ADDRESSING, which no LOCK vocabulary touches.  The
    addition unblocked **two** rows, not six.

    ⚠️ AND THE DOCUMENT AROUND IT IS GENERATED AND GATED BYTE-FOR-BYTE, which is
    what let the sentence survive: `--check` proves the file matches what this
    script emits, and says nothing about whether the script tells the truth.
    A derivation gate is a wrapper a false sentence can sit inside
    ([[ungated-prose-overclaims]]).

    ⭐ SINCE P2 BATCH 23 THE ADDITION IS DONE, so the sentence is written from
    two tables that are gated in opposite directions: `LOCK_UNBLOCKED` names the
    rows it unblocked and `claimed_forms --check` requires every one of them to
    be CLAIMED; `DECLINED` names what is still declined and why."""
    unblocked = sorted(CF.LOCK_UNBLOCKED)
    still = sorted((r, d) for r, d in CF.DECLINED.items())
    lock_names = ", ".join(f"`{b} {sh}`" for b, sh in unblocked)
    other_names = ", ".join(f"`{b} {sh}`" for (b, sh), _ in still)
    other_decisions = ", ".join(sorted({d for _, d in still}))
    remaining_lock = sum(1 for d in CF.DECLINED.values()
                         if d == CF.LOCK_BLOCKED_DECISION)
    return (
        f"`xchg` at a memory operand asserts the LOCK signal whether or not "
        f"`lock` is written (SDM Vol. 2A, XCHG), and that is an ATOMICITY claim "
        f"a model with no LOCK vocabulary can neither make nor break "
        f"({CF.LOCK_BLOCKED_DECISION}). ⭐ **LANDED in P2 batch 23**: the "
        f"addition unblocked exactly the **{len(unblocked)} row(s)** declined "
        f"for that reason — {lock_names} — which are CLAIMED now, and "
        f"**{remaining_lock} row(s)** remain blocked on atomicity.\n\n"
        f"⛔ **It did NOT unblock the {len(still)} row(s) still declined** "
        f"({other_names}, {other_decisions}), whose reason is signed BIT-STRING "
        f"addressing: the offset may reach far outside the addressed operand and "
        f"the effective address moves with it. That is a different addressing "
        f"mode wearing the same mnemonic, and no LOCK vocabulary touches it. "
        f"⚠️ This paragraph is DERIVED from `claimed_forms`'s tables, each gated "
        f"in its own direction; an earlier hand-written version claimed all "
        f"{len(unblocked) + len(still)} rows for this addition.")


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
    # ⭐⭐ DELIVERED IS DERIVED, AND A ZERO IS NOT A DELIVERY.  All three
    # additions have LANDED, and two of them (the segment base and `movabs`)
    # therefore vanished from the census's uncovered buckets — which reads as
    # "0 instructions of demand", identical to an addition nobody needed.  The
    # state is read from the census's OWN scope partition (`DC.EXT_SCOPE`,
    # imported rather than copied) and the demand from the census's covered
    # buckets, so neither is a sentence anyone has to remember to update.
    covd = collections.Counter()
    for _g, r in d.items():
        if isinstance(r, dict) and r.get("class") == "asm":
            for e, k in (r.get("ext_covered") or {}).items():
                covd[e] += k
    fh.write("| # | addition | state | measured demand (asm class) | "
             "share of the gap |\n")
    fh.write("|---|---|---|---|---|\n")
    for i, (name, key, _why) in enumerate(ADDITIONS, 1):
        k = ext.get(key, 0)
        if DC.EXT_SCOPE[key]:
            fh.write(f"| {i} | {name} | ✅ LANDED — {covd.get(key, 0):,} "
                     f"instructions now COUNTED AS COVERED | — | — |\n")
        else:
            fh.write(f"| {i} | {name} | ⛔ still counted as a gap | {k:,} | "
                     f"{100.0*k/b['total_uncovered']:.2f}% |\n")
    fh.write("\n")
    for i, (name, key, why) in enumerate(ADDITIONS, 1):
        fh.write(f"**{i}. {name}** — {why if why is not None else lock_why()}\n\n")
    n_unblocked = len(CF.LOCK_UNBLOCKED)
    fh.write(f"""⚠️ **The LOCK vocabulary's occurrence count under-states it, but by
less than this document once claimed.** Codec kernels are single-threaded inner
loops; the count that matters for LOCK is in the KERNEL column, where the census
reads 9,029 lock-prefixed instructions, and in the **{n_unblocked} row(s)** it
unblocked. An addition whose value is in what it UNBLOCKS cannot be ranked by
its own frequency, which is why it is listed second by the Captain's order and
not by this table's sort — but the row count is DERIVED now, and it is
{n_unblocked}, not the six this paragraph used to assert.

""")

    # ── the vector roster, ranked by demand ──
    fh.write("## The vector roster, ranked by measured demand\n\n")
    fh.write("Cumulative share is over the whole uncovered gap "
             f"({b['total_uncovered']:,} instructions), so a row's cumulative "
             "column answers: *if P2 stopped here, what fraction of the "
             "assembly class would the model execute?*\n\n")
    # ⛔⛔ THE MMX COLUMN, AND WHY A RANK IS NOT A PRICE WITHOUT IT.  A census
    # residue keyed `movq (vector operand)` erases the REGISTER FILE, so this
    # join priced K's `mx`/`rx`/`xm`/`xr`/`xx` shapes of `movq` with 11,109
    # instructions that are **100% `%mm`** — MMX, which this model has no
    # register file for and which none of those shapes would close.  The demand
    # was real and the supply was real and they were not the same instructions.
    # ⇒ 🔑 A JOIN ON A KEY THAT DROPPED A FIELD PRICES ONE THING WITH ANOTHER'S
    # DEMAND, and it reads as an ordinary row.  The share is printed per row now,
    # from the census's `miss_by_ext`; ⚠️ a row at 100% is a PHANTOM.
    mmx = collections.Counter()
    for _g, r in d.items():
        if isinstance(r, dict) and r.get("class") == "asm":
            for m, per in (r.get("miss_by_ext") or {}).items():
                mmx[m] += per.get("MMX (mm)", 0)
    fh.write("| rank | mnemonic | occurrences | share | cumulative | "
             "of it, MMX | K operand shapes |\n")
    fh.write("|---|---|---|---|---|---|---|\n")
    cum = 0
    for i, (mn, occ, shapes) in enumerate(b["joined"][:40], 1):
        cum += occ
        note = mmx_note(mmx.get(mn, 0), occ)
        fh.write(f"| {i} | `{mn}` | {occ:,} | "
                 f"{100.0*occ/b['total_uncovered']:.2f}% | "
                 f"{100.0*cum/b['total_uncovered']:.1f}% | {note} | "
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
    add_share = sum(ext.get(k, 0) for _n, k, _w in ADDITIONS
                    if not DC.EXT_SCOPE[k])
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
    # ⛔ THE MMX SHARE, IN ALL THREE BANDS AND AT BOTH EDGES.  A row priced
    # entirely by demand its own operand shapes cannot close is a PHANTOM, and
    # the whole value of the column is that it says so out loud.
    for n_mmx, occ, want in ((11109, 11109, "⛔ **100% — PHANTOM ROW**"),
                             (0, 21011, "—"), (454, 21239, "2%"),
                             (5000, 20000, "⚠️ 25%"),
                             (1, 10000, "0%"),          # nonzero but tiny: NOT "—"
                             (0, 0, "—")):              # a row with no demand
        got = mmx_note(n_mmx, occ)
        ok = got == want
        print(("  ✔ " if ok else "  ⛔ ") +
              f"mmx share {n_mmx}/{occ} -> {got}" +
              ("" if ok else f"   EXPECTED {want}"))
        if not ok:
            bad.append(f"mmx:{n_mmx}/{occ}")
    for g in asm:
        has = "miss_by_ext" in d[g]
        print(("  ✔ " if has else "  ⛔ ") +
              f"column `{g}` carries the residue keyed by MNEMONIC AND BUCKET")
        if not has:
            bad.append("miss_by_ext:" + g)
        if has:
            # ⛔ the two keyings are the SAME residue: per-mnemonic bucket totals
            # must not exceed that mnemonic's entry in the flat map.
            for m, per in d[g]["miss_by_ext"].items():
                flat = sum(v for k, v in d[g]["miss_all"].items()
                           if k == m or k.startswith(m + " ("))
                if sum(per.values()) != flat:
                    print(f"  ⛔ `{g}`/`{m}`: {sum(per.values())} by bucket vs "
                          f"{flat} in the flat map")
                    bad.append("miss-keying:" + g + "/" + m)
                    break
            else:
                print(f"  ✔   and it agrees with `miss_all` on every mnemonic")

    # ⛔ GATED IN BOTH DIRECTIONS.  This arm used to say only "the census emits
    # this bucket", which is true exactly while the addition is UNDELIVERED; it
    # went red the moment two of the three landed, and the honest reading is not
    # that the arm broke but that its claim had one direction.  An addition the
    # census now counts as covered must be ABSENT from the uncovered buckets,
    # and one it still refuses must be PRESENT — a delivered item still showing
    # as a gap is exactly the stale-census defect this batch is about.
    for name, key, _w in ADDITIONS:
        landed = DC.EXT_SCOPE[key]
        ok = (key not in ext) if landed else (key in ext)
        print(("  ✔ " if ok else "  ⛔ ") +
              (f"addition `{name}` is in scope for the census and is ABSENT "
               f"from its uncovered buckets (`{key}`)" if landed else
               f"addition `{name}` names a bucket the census emits (`{key}`)"))
        if not ok:
            bad.append("addition:" + key)
    # ⭐⭐ P2 ITEM 2 — THE LOCK CLAIM, DRIVEN IN BOTH DIRECTIONS.
    #
    # ⛔ THIS ARM EXISTS BECAUSE THE SENTENCE IT GUARDS WAS FALSE FOR A WHOLE
    # PHASE, inside a document CI re-derives BYTE-FOR-BYTE.  The derivation gate
    # proves the file matches the script; it says nothing about whether the
    # script tells the truth, and a hand-written paragraph inside a generated
    # document reads as generated ([[ungated-prose-overclaims]]).  So the claim
    # is derived from `claimed_forms.DECLINED`, and here that derivation is
    # required to MOVE when its source moves — and to be right when it does not.
    saved_declined = dict(CF.DECLINED)
    saved_unblocked = set(CF.LOCK_UNBLOCKED)
    lock_arms = []
    try:
        base = lock_why()
        n_unb = len(saved_unblocked)
        n_still = len(saved_declined)
        lock_arms.append(("the shipped sentence names the unblocked rows and the residue",
                          f"**{n_unb} row(s)** declined for that reason" in base
                          and f"the {n_still} row(s) still declined" in base))
        # RED 1: an extra unblocked row must move the count.
        CF.LOCK_UNBLOCKED.add(("xadd", "m,r"))
        lock_arms.append(("an extra UNBLOCKED row moves the derived count",
                          f"**{n_unb + 1} row(s)** declined for that reason" in lock_why()))
        CF.LOCK_UNBLOCKED.clear(); CF.LOCK_UNBLOCKED.update(saved_unblocked)
        # RED 2: a still-declined row re-labelled as atomicity-blocked must be
        # reported as REMAINING, not silently folded into the unblocked claim.
        CF.DECLINED[("bt", "m,r")] = CF.LOCK_BLOCKED_DECISION
        lock_arms.append(("a row re-labelled atomicity-blocked is reported as REMAINING",
                          "**1 row(s)** remain blocked on atomicity" in lock_why()))
        CF.DECLINED.clear(); CF.DECLINED.update(saved_declined)
        # RED 3: with NOTHING unblocked the sentence must say zero rather than
        # fall back on a plausible-looking number.
        CF.LOCK_UNBLOCKED.clear()
        lock_arms.append(("with nothing unblocked the sentence says ZERO",
                          "**0 row(s)** declined for that reason" in lock_why()))
    finally:
        CF.DECLINED.clear(); CF.DECLINED.update(saved_declined)
        CF.LOCK_UNBLOCKED.clear(); CF.LOCK_UNBLOCKED.update(saved_unblocked)
    # ⭐ and the restore is itself checked, because a probe that edits its
    # subject can leave it edited (the P1 seal's rule, and D75's).
    lock_arms.append(("the tables are restored",
                      CF.DECLINED == saved_declined
                      and CF.LOCK_UNBLOCKED == saved_unblocked
                      and lock_why() == base))
    for name, ok in lock_arms:
        print(("  ✔ " if ok else "  ⛔ ") + name)
        if not ok:
            bad.append("lock:" + name)
    if bad:
        print(f"p2-roster selftest: FAIL ({len(bad)} arms)")
        return 1
    print(f"p2-roster selftest: PASS "
          f"({len(arms)+len(key_arms)+1+4*len(asm)+len(ADDITIONS)+len(lock_arms)+6} "
          f"arms; the SIMD predicate in both directions, the join's inputs, "
          f"every addition tied to a bucket the census emits, and the LOCK "
          f"claim derived from `claimed_forms.DECLINED` in both directions)")
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
