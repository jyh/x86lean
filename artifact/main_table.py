#!/usr/bin/env python3
"""Split a differential run down to its MAIN table, the population the paper and docs/COVERAGE.md count.

The method is the one records 41-45 state ("How the main-table line was measured"): the main-table ids are read from
`def vectors` in Tests/Vectors.lean, up to `def vexVectors`; every case whose id is one of them is kept from
run/lean.txt and run/oracle.txt; the pair is then compared by `x86lean-diff compare` (done by the caller).

A record block is a `CASE id=<vector>/<n> …` line and every line after it up to the next CASE line.
Usage: main_table.py RUN_DIR      writes RUN_DIR/main-lean.txt and RUN_DIR/main-oracle.txt, prints the counts.
Refuses (exit 2) on zero ids, a missing file, or a side with no kept case: a split of nothing is not a main table.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def main_ids(path=os.path.join(ROOT, "Tests", "Vectors.lean")):
    src = open(path, encoding="utf-8").read()
    a, b = src.find("\ndef vectors"), src.find("\ndef vexVectors")
    if a < 0 or b < 0 or b < a:
        sys.exit(f"main_table: `def vectors` … `def vexVectors` not found in {path}; refusing")
    return set(re.findall(r'\bid := "([^"]+)"', src[a:b]))


def keep(lines, ids):
    out, on, n = [], False, 0
    for ln in lines:
        if ln.startswith("CASE "):
            m = re.match(r"CASE id=([^/\s]+)/", ln)
            on = bool(m) and m.group(1) in ids
            n += on
        if on:
            out.append(ln)
    return out, n


def main(argv):
    if len(argv) != 2:
        sys.exit(__doc__)
    run = argv[1]
    ids = main_ids()
    if not ids:
        print("main_table: 0 main-table ids; refusing", file=sys.stderr)
        return 2
    counts = {}
    for side in ("lean", "oracle"):
        src = os.path.join(run, f"{side}.txt")
        if not os.path.exists(src):
            print(f"main_table: {src} missing; refusing", file=sys.stderr)
            return 2
        lines = open(src, encoding="utf-8", errors="replace").read().split("\n")
        kept, n = keep(lines, ids)
        if n == 0:
            print(f"main_table: no main-table case kept from {src}; refusing", file=sys.stderr)
            return 2
        open(os.path.join(run, f"main-{side}.txt"), "w", encoding="utf-8").write("\n".join(kept) + "\n")
        counts[side] = n
    print(f"MAIN-TABLE ids={len(ids)} kept lean={counts['lean']} oracle={counts['oracle']}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
