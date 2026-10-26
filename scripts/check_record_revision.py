#!/usr/bin/env python3
"""Refuse a differential record that does not name the reference model's pinned revision.

WHY (D218, D219).  No differential record written before 2026-09-12 names the ACL2 / x86isa commit it
ran against, so every agreement figure in them is agreement with an unnamed model.  The revision is now
pinned (`scripts/oracle_revision.txt`) and `run_differential.sh` prints `reference-model: acl2@<sha>`.
A record is still written by hand from that output, so the line can be left out; this refuses that.

THE RULE.  Every `docs/DIFFERENTIAL-*.md` and `docs/REFERENCE-PIN-RUN-*.md` must carry at least one
`reference-model: acl2@<40 hex>` line, and every such line must equal the pin — EXCEPT the records that
PREDATE THE PIN, which are listed below by explicit bounds rather than by a default, so a new record can
never fall into the exemption by accident.  An exempt record that does carry the line is still checked.
Each listed exempt record must exist, so the list cannot rot silently.

D363: THE PIN MOVES, AND A RECORD IS RIGHT ABOUT THE PIN IT RAN AT. `PRIOR_PINS` names every earlier pin with
the records that ran under it, by explicit list again: a listed record must name THAT pin (and only it); every
record not listed must name the CURRENT pin, so a new record that still quotes the old revision is refused.
Each listed record must exist. Moving the pin therefore costs one table row, written in the same act.

Exit 0 clean; 1 on a finding; 2 when it cannot find its subject.  `--selftest` plants each failure.
"""
import argparse, glob, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LINE = re.compile(r"reference-model:\s+acl2@([0-9a-f]{40})\b")
LOOSE = re.compile(r"reference-model:")

# D363: earlier pins, each with the records that ran under it. Explicit lists, as for the exemption below.
PRIOR_PINS = {
    "c8897a34d3efc37eb466d7ee50a2e3861c6e82db":   # D218, 2026-09-12 .. D363, 2026-10-26
        [f"DIFFERENTIAL-P2-BATCH{n}.md" for n in range(23, 43)]
        + ["DIFFERENTIAL-V3.md", "REFERENCE-PIN-RUN-2026-09-12.md"],
    "babde610ed66311a80073b98e5efda3f03a61795":   # D363 .. D365, 2026-10-26
        ["REFERENCE-PIN-RUN-2026-10-26.md"],
}

# The records that predate the pin (D218). Bounds, not a pattern: P0, P1 batches 1-21, P2 batches 1-22.
PREDATES_PIN = (["DIFFERENTIAL-P0.md"]
                + [f"DIFFERENTIAL-P1-BATCH{n}.md" for n in range(1, 22)]
                + [f"DIFFERENTIAL-P2-BATCH{n}.md" for n in range(1, 23)])


def pin(root=ROOT):
    path = os.path.join(root, "scripts", "oracle_revision.txt")
    vals = [l.strip() for l in open(path, encoding="utf-8") if l.strip() and not l.strip().startswith("#")]
    return vals[0] if vals and re.fullmatch(r"[0-9a-f]{40}", vals[0]) else None


def check(records, want, exempt=PREDATES_PIN, prior=None):
    """records: {basename: text}. Returns findings."""
    prior = PRIOR_PINS if prior is None else prior
    ran_at = {name: sha for sha, names in prior.items() for name in names}
    f = []
    if not want:
        return ["scripts/oracle_revision.txt carries no 40-hex pin -- nothing to check records against"]
    if not records:
        return ["no differential records found -- a gate with no subject refuses"]
    for name in exempt:
        if name not in records:
            f.append(f"exempt record {name} does not exist -- the predates-the-pin list has rotted")
    for name, sha in sorted(ran_at.items()):
        if name not in records:
            f.append(f"prior-pin record {name} does not exist -- the PRIOR_PINS list for acl2@{sha[:12]} has rotted")
        if sha == want:
            f.append(f"PRIOR_PINS lists the CURRENT pin acl2@{sha[:12]} -- a prior pin is a pin that has been replaced")
    for name, text in sorted(records.items()):
        shas = LINE.findall(text)
        if not shas:
            if name in exempt:
                continue
            hint = " (a `reference-model:` line is present but malformed)" if LOOSE.search(text) else ""
            f.append(f"{name}: names no reference-model revision{hint}; quote run_differential.sh's "
                     f"`reference-model: acl2@<sha>` line")
            continue
        expect = ran_at.get(name, want)
        bad = sorted({s for s in shas if s != expect})
        if bad:
            role = "the prior pin it ran at" if name in ran_at else "the pin"
            f.append(f"{name}: reference-model acl2@{bad[0]} is not {role} acl2@{expect}")
    return f


def load(root=ROOT):
    paths = glob.glob(os.path.join(root, "docs", "DIFFERENTIAL-*.md")) + \
            glob.glob(os.path.join(root, "docs", "REFERENCE-PIN-RUN-*.md"))
    return {os.path.basename(p): open(p, encoding="utf-8").read() for p in paths}


def selftest():
    red = 0

    def arm(name, ok, detail=""):
        nonlocal red
        print(("  v " if ok else "  x ") + name + ("" if ok else f"   {detail}"))
        red += 0 if ok else 1

    real, want = load(), pin()
    f = check(real, want)
    arm("control: the real records pass", not f, str(f)[:200])
    arm("control: at least one record carries the line (the rule has a live subject)",
        any(LINE.search(t) for t in real.values()))
    plant = dict(real, **{"DIFFERENTIAL-P2-BATCH99.md": "cases=1 matched=1\n"})
    f = check(plant, want)
    arm("PLANT: a NEW batch record without the line is refused, naming it",
        any("DIFFERENTIAL-P2-BATCH99.md" in x and "names no" in x for x in f), str(f)[:200])
    other = "0" * 39 + "1"
    plant = dict(real, **{"DIFFERENTIAL-P2-BATCH99.md": f"reference-model: acl2@{other}\n"})
    f = check(plant, want)
    arm("PLANT: a record at ANOTHER revision is refused, naming both",
        any(other in x and want in x for x in f), str(f)[:200])
    plant = dict(real, **{"DIFFERENTIAL-P2-BATCH99.md": "reference-model: acl2@c8897a34\n"})
    f = check(plant, want)
    arm("PLANT: a short or malformed line is refused as malformed, not accepted",
        any("malformed" in x for x in f), str(f)[:200])
    plant = {k: v for k, v in real.items() if k != "DIFFERENTIAL-P1-BATCH7.md"}
    f = check(plant, want)
    arm("PLANT: an exempt record that vanished is refused (the list cannot rot)",
        any("DIFFERENTIAL-P1-BATCH7.md" in x and "rotted" in x for x in f), str(f)[:200])
    plant = dict(real, **{"DIFFERENTIAL-P1-BATCH7.md": real["DIFFERENTIAL-P1-BATCH7.md"]
                          + f"\nreference-model: acl2@{other}\n"})
    f = check(plant, want)
    arm("PLANT: an EXEMPT record that carries a wrong line is still refused",
        any("DIFFERENTIAL-P1-BATCH7.md" in x and other in x for x in f), str(f)[:200])
    arm("PLANT: an empty record set refuses", bool(check({}, want)))
    # D363 — the prior-pin table, both directions.
    old = next(iter(PRIOR_PINS))
    plant = dict(real, **{"DIFFERENTIAL-P2-BATCH99.md": f"reference-model: acl2@{old}\n"})
    f = check(plant, want)
    arm("PLANT (D363): a NEW record that still names the OLD pin is refused",
        any("DIFFERENTIAL-P2-BATCH99.md" in x and old in x and want in x for x in f), str(f)[:200])
    plant = dict(real, **{"DIFFERENTIAL-P2-BATCH23.md": f"reference-model: acl2@{want}\n"})
    f = check(plant, want)
    arm("PLANT (D363): a prior-pin record re-labelled with the CURRENT pin is refused",
        any("DIFFERENTIAL-P2-BATCH23.md" in x and "prior pin it ran at" in x for x in f), str(f)[:200])
    plant = {k: v for k, v in real.items() if k != "DIFFERENTIAL-V3.md"}
    f = check(plant, want)
    arm("PLANT (D363): a prior-pin record that vanished is refused (the table cannot rot)",
        any("DIFFERENTIAL-V3.md" in x and "rotted" in x for x in f), str(f)[:200])
    f = check(real, want, prior={want: ["DIFFERENTIAL-V3.md"]})
    arm("PLANT (D363): a table that lists the CURRENT pin as prior is refused",
        any("CURRENT pin" in x for x in f), str(f)[:200])
    print(f"\n  red={red}")
    return 1 if red else 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args(argv)
    if a.selftest:
        return selftest()
    want = pin()
    recs = load()
    if not want or not recs:
        for x in check(recs, want):
            print("⛔ check_record_revision: " + x)
        return 2
    f = check(recs, want)
    if f:
        print(f"⛔ check_record_revision: FAIL — {len(f)} finding(s)")
        for x in f:
            print("   " + x)
        return 1
    named = sum(1 for t in recs.values() if want in LINE.findall(t))
    print(f"check_record_revision: CLEAN — {named} record(s) name acl2@{want[:8]}; "
          f"{len(PREDATES_PIN)} predate the pin and are exempt by explicit bounds; "
          f"{sum(len(v) for v in PRIOR_PINS.values())} ran at {len(PRIOR_PINS)} prior pin(s) and name it")
    return 0


if __name__ == "__main__":
    sys.exit(main())
