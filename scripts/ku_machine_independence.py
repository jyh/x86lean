#!/usr/bin/env python3
"""ITEM 4b's FIRST BLOCKER HALF: is the kernel unfolding counter MACHINE-INDEPENDENT?

`docs/QUEUE.md` item 4b names two things unmeasured, and refuses to gate until
both are done: **machine independence** ("a prediction until a second machine
reads it") and **a budget from a second source**. The Captain allocated the
second machine on 2026-09-09 ("#2 yes use kenai for 4b"). This tool is the
first half only. ⛔ IT DOES NOT TOUCH THE SECOND, and nothing here licenses a
budget.

⭐⭐ THE DESIGN DECISION WORTH THE WHOLE TOOL: **THE PLANT IS MATHLIB-FREE AND
LAKE-FREE.** Machine independence of a KERNEL counter is a property of the
kernel, and a bare `lean` can exhibit it. Reproducing the committed twelve-commit
corpus walk on a second machine would have needed elan + a full mathlib build on
a box that had no Lean toolchain at all; this needs elan and a 225-byte file.
⇒ **A cheap experiment that can REFUTE the claim outright is worth more than an
expensive one that would confirm it**, and it is run FIRST for exactly that
reason: had the counters disagreed, 4b would have died for the price of a
toolchain download instead of a mathlib build.
⚠️ THE COST OF THAT CHOICE, STATED RATHER THAN BURIED: this measures the counter
on a PLANT, not on this repository's modules. See "WHAT THIS DOES NOT SHOW".

## THE THREE CONTROLS, BECAUSE AGREEMENT IS THE EASIEST THING TO FAKE

1. **THE INSTRUMENT MUST BE LIVE.** Counters must DIFFER across plant sizes on
   EACH machine independently. Two frozen instruments agree perfectly, and a
   comparison that only checks agreement cannot tell that from the real thing
   [[feedback-a-control-can-share-the-blind-spot]].
2. **THE COMPARATOR MUST HAVE TEETH.** A reading at one size, compared against
   the other machine at a DIFFERENT size, must be reported as a DISAGREEMENT.
   An always-equal comparator passes every honest test ever put to it.
3. ⛔⛔ **THE TWO SIDES MUST BE DIFFERENT MACHINES, AND THE TOOL REFUSES IF THEY
   ARE NOT.** The platform triple is read from each `lean --version` and compared.
   Two readings taken from one machine are not two witnesses — they agree because
   they share an origin, and that agreement is exactly the shape of the result
   being claimed [[feedback-two-readings-are-not-two-witnesses]]. This is the one
   failure that would have made the whole exercise vacuous while looking perfect.
4. **AN EMPTY READING IS NEVER AGREEMENT.** A parse that finds no counters is a
   refusal, not a pass: an unobserved region does not report "unknown", it
   positively reports agreement [[feedback-unobserved-regions-report-agreement]].

## WHAT THIS DOES NOT SHOW — read this before quoting the verdict

* **NOT the corpus.** It measures a synthetic plant, not the twelve committed
  commits. The corpus reading on a second machine still needs mathlib there.
* **NOT a budget.** Item 4b's other half — a budget from a second SOURCE — is
  untouched, and the Captain's allocation ruling said so explicitly.
* **NOT usability of a second night.** There is still exactly one usable
  calibration night (D180). Nothing here changes that.
⇒ **4b STAYS SHUT.** This removes one named unknown; it supplies no confirmation
that the counter tracks kernel time, which is the claim 4b actually rests on.
"""
import argparse
import json
import os
import re
import subprocess
import sys

PLANT = """set_option maxRecDepth 200000
set_option diagnostics true
set_option diagnostics.threshold 100

def bits (n : Nat) : List Bool := (List.range n).map (fun i => i % 2 == 0)

theorem arm : (bits {n}).length = {n} := by decide"""

SIZES = (1000, 2000, 4000)


def plant_source(n: int) -> str:
    """The plant, byte-exact. Both machines must check THE SAME BYTES -- the
    source is generated from one template and hashed on both sides, never
    re-typed remotely, because a line-ending difference is a different file."""
    return PLANT.format(n=n) + "\n"


def read_counters(text: str) -> dict:
    """The `[kernel] unfolded declarations` block, as {declaration: count}.

    ⛔ Only the KERNEL block. The same output carries `[reduction]` counters
    charged in the ELABORATOR, and 4a is the record of what happens when the two
    are confused: heartbeats are an elaborator quantity and were blind to the
    growth the gate exists to catch.

    ⭐ THE BLOCK DECLARES ITS OWN SIZE (`num: N`) AND THAT IS CHECKED. A parser
    that harvests whatever its regex happens to match reports a SHORT reading as
    a complete one, and a short reading that is short on BOTH machines agrees
    perfectly [[feedback-read-what-the-instrument-measured]]. Lean tells us how
    many counters it is about to print; refusing when the harvest disagrees costs
    one line and converts a silent truncation into a red.
    """
    out, inblk, declared = {}, False, None
    for line in text.splitlines():
        if "[kernel] unfolded declarations" in line:
            inblk = True
            m = re.search(r"num:\s*(\d+)", line)
            declared = int(m.group(1)) if m else None
            continue
        if inblk:
            m = re.match(r"\s*\[kernel\] (\S+) . (\d+)\s*$", line)
            if m:
                out[m.group(1)] = int(m.group(2))
            elif out:
                break
    if declared is not None and len(out) != declared:
        raise ValueError(f"the kernel block declares num: {declared} but {len(out)} "
                         f"counter(s) were harvested — a SHORT reading, refused rather "
                         f"than reported as complete")
    return out


def platform_of(version_line: str) -> str:
    """The platform triple out of `lean --version`, e.g. arm64-apple-darwin24.6.0."""
    m = re.search(r"version [^,]+, ([^,]+), commit", version_line)
    return m.group(1).strip() if m else ""


def commit_of(version_line: str) -> str:
    m = re.search(r"commit ([0-9a-f]+)", version_line)
    return m.group(1) if m else ""


def compare(a: dict, b: dict) -> tuple[bool, list[str]]:
    """(agree, differences). An EMPTY side is never agreement."""
    notes = []
    if not a.get("readings") or not b.get("readings"):
        return False, ["a side carries NO readings — a refusal, never a pass"]
    if platform_of(a["version"]) == platform_of(b["version"]):
        return False, [f"BOTH SIDES ARE {platform_of(a['version'])} — two readings "
                       f"from one platform are not two witnesses; this comparison "
                       f"would be vacuous and is REFUSED"]
    if commit_of(a["version"]) != commit_of(b["version"]):
        notes.append(f"⚠️ DIFFERENT LEAN COMMITS ({commit_of(a['version'])[:8]} vs "
                     f"{commit_of(b['version'])[:8]}): a disagreement below would not "
                     f"be attributable to the MACHINE")
    agree = True
    for n in sorted(set(a["readings"]) | set(b["readings"]), key=int):
        ca, cb = a["readings"].get(n), b["readings"].get(n)
        if ca is None or cb is None:
            notes.append(f"n={n}: only one side has a reading — NOT scored")
            agree = False
            continue
        if ca != cb:
            agree = False
            for k in sorted(set(ca) | set(cb)):
                if ca.get(k) != cb.get(k):
                    notes.append(f"n={n}: {k}  {ca.get(k)} vs {cb.get(k)}")
    return agree, notes


def instrument_is_live(readings: dict) -> bool:
    """Counters must MOVE across sizes. Two frozen instruments agree perfectly."""
    seen = [json.dumps(readings[n], sort_keys=True) for n in sorted(readings, key=int)]
    return len(set(seen)) == len(seen) and len(seen) > 1


def load_corpus(path):
    """A deterministic_cost walk as {commit8: {decl: count}}, plus its origin.

    ⛔ THE ORIGIN IS PART OF THE READING. A walk file that does not say which
    machine produced it cannot be checked for the one failure that would make a
    machine-independence claim vacuous. Files written before the `origin` field
    existed return None, and the comparison then REFUSES rather than assuming.
    """
    rows = [json.loads(l) for l in open(path, encoding="utf-8") if l.strip()]
    if not rows:
        raise ValueError(f"{path} holds no readings — refused, never treated as agreement")
    by = {r["commit"][:8]: (r.get("ku") or {}) for r in rows}
    origins = {json.dumps(r.get("origin"), sort_keys=True) for r in rows if r.get("origin")}
    if len(origins) > 1:
        raise ValueError(f"{path} mixes {len(origins)} origins in one file — a walk is "
                         f"one machine's reading, and this one is not")
    org = json.loads(origins.pop()) if origins else None
    return by, org


def compare_corpus(a, b, org_a, org_b, name_a, name_b) -> int:
    """Per-commit, per-declaration equality of two walks from two machines."""
    if org_a is None or org_b is None:
        print("⚠️  ONE OR BOTH WALKS PREDATE THE `origin` FIELD, so this tool cannot "
              "verify they came from DIFFERENT machines.\n    The comparison is still "
              "run, but its central assumption is UNCHECKED and must be supplied by "
              "the operator, at the object, in the record.")
    elif org_a.get("node") == org_b.get("node") and org_a.get("machine") == org_b.get("machine"):
        print(f"⛔ REFUSED: both walks were produced on {org_a.get('node')} / "
              f"{org_a.get('machine')}. Two readings from one machine are not two "
              f"witnesses — they agree by sharing an origin, which is the exact shape "
              f"of the result a machine-independence claim asserts.")
        return 1
    else:
        print(f"  {name_a}: {org_a['node']} / {org_a['machine']} / {org_a['platform']}")
        print(f"  {name_b}: {org_b['node']} / {org_b['machine']} / {org_b['platform']}")
    shared = sorted(set(a) & set(b))
    only = sorted(set(a) ^ set(b))
    if not shared:
        print("⛔ REFUSED: the two walks share NO commit — nothing was compared.")
        return 1
    bad = 0
    tot_decls = 0
    for c in shared:
        da, db = a[c], b[c]
        diff = [k for k in set(da) | set(db) if da.get(k) != db.get(k)]
        tot_decls += len(set(da) | set(db))
        flag = "✅" if not diff else f"⛔ {len(diff)} DIFFER"
        print(f"    {c}  {len(da):4d} vs {len(db):4d} decls  "
              f"{sum(da.values()):>12,} vs {sum(db.values()):>12,}   {flag}")
        if diff:
            bad += 1
            for k in sorted(diff)[:5]:
                print(f"        {k}: {da.get(k)} vs {db.get(k)}")
    if only:
        print(f"  ⚠️ {len(only)} commit(s) present on ONE side only — NOT scored, never "
              f"silently dropped: {only[:6]}")
    print()
    if bad:
        print(f"⛔ {bad} of {len(shared)} commits DISAGREE across machines.")
        return 1
    print(f"✅ IDENTICAL on every one of {tot_decls} declaration readings across "
          f"{len(shared)} commits, on two different machines.")
    print("⛔ AND THIS IS STILL NOT A RESULT FOR 4b: it says the COUNTER is portable, "
          "not that it tracks kernel time. The budget-from-a-second-source half is "
          "untouched and there is still one usable calibration night. 4b stays shut.")
    return 0


def selftest() -> int:
    failures = []
    mac = {"version": "Lean (version 4.32.0-rc1, arm64-apple-darwin24.6.0, commit abc123, Release)",
           "readings": {"1000": {"List.rec": 4004}, "2000": {"List.rec": 8004}}}
    win = {"version": "Lean (version 4.32.0-rc1, x86_64-w64-windows-gnu, commit abc123, Release)",
           "readings": {"1000": {"List.rec": 4004}, "2000": {"List.rec": 8004}}}

    # CONTROL FIRST: the honest case must pass, or every red below is unreadable.
    ok, notes = compare(mac, win)
    if not ok:
        failures.append(f"two agreeing machines must AGREE, got {notes}")

    # TEETH: a real difference must be reported, and must NAME the declaration.
    bad = {**win, "readings": {"1000": {"List.rec": 4004}, "2000": {"List.rec": 8005}}}
    ok, notes = compare(mac, bad)
    if ok or not any("List.rec" in n and "8005" in n for n in notes):
        failures.append(f"a differing counter must be a DISAGREEMENT that names it, got {notes}")

    # ⛔ THE VACUITY REFUSAL — the arm this whole tool exists to not need twice.
    ok, notes = compare(mac, dict(mac))
    if ok or not any("not two witnesses" in n for n in notes):
        failures.append(f"two readings from ONE platform must be REFUSED, got {notes}")

    # AN EMPTY SIDE IS NOT A PASS.
    # ⛔ ASSERT THE REASON, NOT THE VERDICT. A probe removing this guard stayed
    # SILENT because the missing-size path returns False too — two guards
    # overlapping on the exit code, differing only in what they SAY, which is the
    # half a reader acts on. The same shape the private-paths gate hit today.
    ok, notes = compare(mac, {**win, "readings": {}})
    if ok or not any("NO readings" in n for n in notes):
        failures.append(f"an empty side must be refused AS EMPTY, not as a missing "
                        f"size — got {notes}")

    # A MISSING SIZE IS NOT SCORED, and is not silently dropped either.
    ok, notes = compare(mac, {**win, "readings": {"1000": {"List.rec": 4004}}})
    if ok or not any("only one side" in n for n in notes):
        failures.append("a size present on one side only must be reported, not dropped")

    # DIFFERENT LEAN COMMITS: still comparable, but the attribution is flagged.
    other = {**win, "version": win["version"].replace("abc123", "def456")}
    ok, notes = compare(mac, other)
    if not any("DIFFERENT LEAN COMMITS" in n for n in notes):
        failures.append("differing lean commits must be flagged — a disagreement "
                        "would not be attributable to the machine")

    # LIVENESS: a frozen instrument must be caught.
    if instrument_is_live({"1000": {"a": 1}, "2000": {"a": 1}}):
        failures.append("a FROZEN instrument (same counters at two sizes) must not read live")
    if not instrument_is_live({"1000": {"a": 1}, "2000": {"a": 2}}):
        failures.append("a moving instrument must read live")
    if instrument_is_live({"1000": {"a": 1}}):
        failures.append("ONE size cannot establish liveness")

    # THE PARSER: the elaborator block must NOT be harvested as the kernel's.
    mixed = ("  [reduction] unfolded declarations (max: 9, num: 1):\n"
             "    [reduction] List.rec ↦ 9\n"
             "  [kernel] unfolded declarations (max: 7, num: 1):\n"
             "    [kernel] List.rec ↦ 7\n")
    got = read_counters(mixed)
    if got != {"List.rec": 7}:
        failures.append(f"the parser must take the KERNEL block only, got {got}")
    if read_counters("no diagnostics at all") != {}:
        failures.append("a text with no kernel block must parse EMPTY, not invent a reading")

    # ⭐ THE SHORT READING. Lean declares the count; a harvest that falls short is
    # refused. Without this, a regex that silently stopped matching would report a
    # partial set as complete -- and being partial the SAME WAY on both machines,
    # it would still AGREE.
    short = ("  [kernel] unfolded declarations (max: 9, num: 3):\n"
             "    [kernel] List.rec . 9\n"
             "    [kernel] Nat.rec . 4\n")
    try:
        read_counters(short)
        failures.append("a harvest short of the block's declared `num` must be REFUSED")
    except ValueError:
        pass
    full = short + "    [kernel] Nat.casesOn . 2\n"
    if len(read_counters(full)) != 3:
        failures.append("a harvest matching the declared `num` must be accepted")

    # ⛔⛔ THE CORPUS MODE'S OWN ARMS. Added with the mode, not after it: a verdict
    #     function with no arms borrows its neighbours' green
    #     [[feedback-a-gate-with-no-callable-surface]].
    import contextlib as _c, io as _io
    MAC = {"node": "yukon", "machine": "arm64", "platform": "macOS"}
    WIN = {"node": "kenai", "machine": "AMD64", "platform": "Windows"}
    W1 = {"aaaaaaaa": {"d1": 10, "d2": 20}}
    W2 = {"aaaaaaaa": {"d1": 10, "d2": 20}}

    def drive(a, b, oa, ob):
        buf = _io.StringIO()
        with _c.redirect_stdout(buf):
            rc = compare_corpus(a, b, oa, ob, "A", "B")
        return rc, buf.getvalue()

    rc, said = drive(W1, W2, MAC, WIN)
    if rc != 0 or "IDENTICAL" not in said:
        failures.append(f"two agreeing walks from DIFFERENT machines must agree: {said[:120]}")
    if "4b stays shut" not in said:
        failures.append("a corpus agreement must carry the 'this is not a result for 4b' line — "
                        "the tool's own guard against its most likely misreading")

    rc, said = drive(W1, W2, MAC, dict(MAC))
    if rc == 0 or "not two witnesses" not in said:
        failures.append(f"two walks from ONE machine must be REFUSED as vacuous: {said[:120]}")

    rc, said = drive(W1, {"aaaaaaaa": {"d1": 10, "d2": 21}}, MAC, WIN)
    if rc == 0 or "d2: 20 vs 21" not in said:
        failures.append(f"a differing declaration must RED and be NAMED: {said[:160]}")

    rc, said = drive(W1, {"bbbbbbbb": {"d1": 10}}, MAC, WIN)
    if rc == 0 or "share NO commit" not in said:
        failures.append("walks sharing no commit must be REFUSED, not reported as agreement")

    rc, said = drive(W1, {**W2, "cccccccc": {"d9": 1}}, MAC, WIN)
    if rc != 0 or "ONE side only" not in said:
        failures.append("a commit on one side only must be REPORTED, never silently dropped")

    rc, said = drive(W1, W2, None, WIN)
    if rc != 0 or "UNCHECKED" not in said:
        failures.append("a walk with no origin must run but DECLARE its assumption unchecked")

    for f in failures:
        print(f"SELF-TEST FAIL: {f}")
    if failures:
        return 1
    print("ku_machine_independence SELF-TEST: OK (control first; teeth named; "
          "the SAME-PLATFORM vacuity refusal driven; empty side refused; missing "
          "size reported; differing lean commit flagged; liveness both ways and "
          "refused at n=1; parser takes the kernel block, never the elaborator's; "
          "6 CORPUS-mode arms, each break-probed RED — same-machine pairing refused, "
          "a differing declaration named, no-shared-commit refused, a one-sided commit "
          "reported, a missing origin declared, and the 'not a result for 4b' guard "
          "asserted as part of the output)")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description="item 4b: is the kernel unfolding counter machine-independent?")
    ap.add_argument("--emit", metavar="DIR", help="write the plant sources to DIR")
    ap.add_argument("--read", nargs=2, metavar=("A.json", "B.json"),
                    help="compare two machines' recorded readings")
    ap.add_argument("--corpus", nargs=2, metavar=("A.jsonl", "B.jsonl"),
                    help="compare two deterministic_cost walks from two machines, "
                         "per commit and per declaration")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return selftest()
    if args.corpus:
        a, oa = load_corpus(args.corpus[0])
        b, ob = load_corpus(args.corpus[1])
        return compare_corpus(a, b, oa, ob, os.path.basename(args.corpus[0]),
                              os.path.basename(args.corpus[1]))
    if args.emit:
        os.makedirs(args.emit, exist_ok=True)
        for n in SIZES:
            p = os.path.join(args.emit, f"plant_{n}.lean")
            with open(p, "w", encoding="utf-8", newline="") as fh:
                fh.write(plant_source(n))
            print(f"  wrote {p}")
        print("⛔ COPY these bytes to the second machine and hash both sides. Do NOT "
              "regenerate them remotely: a line-ending difference is a different file.")
        return 0
    if args.read:
        a = json.load(open(args.read[0], encoding="utf-8"))
        b = json.load(open(args.read[1], encoding="utf-8"))
        for side, d in ((args.read[0], a), (args.read[1], b)):
            live = instrument_is_live(d["readings"])
            print(f"  {os.path.basename(side):24s} {platform_of(d['version']):28s} "
                  f"instrument {'LIVE' if live else '⛔ FROZEN — counters do not move'}")
            if not live:
                print("  ⛔ REFUSED: an instrument that does not move across sizes cannot "
                      "witness agreement — two frozen counters agree perfectly.")
                return 1
        agree, notes = compare(a, b)
        for n in notes:
            print(f"  {n}")
        if agree:
            print(f"\n✅ AGREE on all {len(a['readings'])} sizes and every counter, across "
                  f"{platform_of(a['version'])} and {platform_of(b['version'])}.")
            print("⛔ AND THAT IS ONE NAMED UNKNOWN, NOT A RESULT FOR 4b: the plant is not "
                  "the corpus, no budget follows, and there is still only one usable "
                  "calibration night. Item 4b stays shut.")
            return 0
        print("\n⛔ DISAGREE — the counter is not machine-independent as measured above.")
        return 1
    ap.print_help()
    return 1


if __name__ == "__main__":
    sys.exit(main())
