#!/usr/bin/env python3
"""Cross-check every differential vector's `Instr.len` and bytes against a real
assembler.

WHY THIS EXISTS.  `Instr.len` is a DATUM the model takes on trust from the
decoder (X86/Syntax.lean): a wrong length is a wrong RIP on every vector using
that form, and no theorem in the repository can notice, because the model has
nothing to compare its length against.  This script gives it something: clang
assembles the vector's own `asm` string and the disassembly's byte count is the
authority.

It is the decode-trust column of the coverage table, made checkable for the 43
forms the differential run actually executes.
"""
import re, subprocess, sys, os, tempfile

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(root)

def run(cmd, **kw):
    return subprocess.run(cmd, shell=True, capture_output=True, text=True, **kw)

tmp = tempfile.mkdtemp()
asm, exp = os.path.join(tmp, "v.s"), os.path.join(tmp, "exp.txt")
obj = os.path.join(tmp, "v.o")

for mode, out in (("emit-asm", asm), ("expected-lengths", exp)):
    r = run(f"lake env .lake/build/bin/x86lean-diff {mode} {out}")
    if r.returncode != 0:
        print(r.stdout, r.stderr); sys.exit(2)

r = run(f"clang -target x86_64-unknown-linux-gnu -c {asm} -o {obj}")
if r.returncode != 0:
    print("⛔ assembler refused the vector table:\n" + r.stderr); sys.exit(2)

r = run(f"objdump -d {obj}")
if r.returncode != 0:
    print("⛔ objdump failed:\n" + r.stderr); sys.exit(2)

# Map label -> address, and collect instruction addresses in order.
labels, addrs = {}, []
for line in r.stdout.splitlines():
    m = re.match(r'^([0-9a-f]+) <([^>]+)>:', line.strip())
    if m:
        labels[m.group(2)] = int(m.group(1), 16); continue
    m = re.match(r'^\s*([0-9a-f]+):\s+((?:[0-9a-f]{2} )+)', line)
    if m:
        addrs.append((int(m.group(1), 16), m.group(2).split()))

by_addr = {a: b for a, b in addrs}
ordered = sorted(by_addr)

expected = {}
for line in open(exp):
    parts = line.split()
    if len(parts) == 3:
        expected[parts[0]] = (int(parts[1]), parts[2])

bad, checked = [], 0
for vid, (elen, ebytes) in expected.items():
    if vid not in labels:
        bad.append(f"{vid}: no label in the assembled object"); continue
    a = labels[vid]
    if a not in by_addr:
        bad.append(f"{vid}: no instruction at its own label"); continue
    got_bytes = "".join(by_addr[a])
    got_len = len(by_addr[a])
    checked += 1
    if got_len != elen:
        bad.append(f"{vid}: model says len={elen}, assembler says {got_len} ({got_bytes})")
    if got_bytes != ebytes:
        bad.append(f"{vid}: model says bytes={ebytes}, assembler says {got_bytes}")

if bad:
    print(f"⛔ encoding cross-check FAILED ({len(bad)} of {len(expected)} forms):")
    for b in bad: print("   " + b)
    sys.exit(1)
print(f"encoding cross-check: CLEAN — {checked} forms, every `Instr.len` and every "
      f"byte string agrees with the assembler")

# ─────────────────────────────────────────────────────────────────────────────
# THE SYNONYM COLLAPSE, CHECKED AGAINST THE ASSEMBLER (P1 BATCH 16).
#
# `loopSpellings` and `repSpellings` in X86/Syntax.lean each map several ROSTER
# SPELLINGS onto one constructor, and both are documented as "a fact about the
# machine, not a convenience" — `loopz` IS `loope`, `repz` IS `repe`.
#
# ⛔ THAT CLAIM WAS UNGATED FOR FIVE BATCHES, AND WORSE THAN UNGATED.  Batch 11's
# comment named a theorem — loop-synonyms-are-one-encoding — as living in
# Tests/Coverage.lean and holding the claim "over the vector table", and no such
# theorem was ever written.  P1 batch 16's `scripts/check_citations.py` is what
# found it; see docs/DECISIONS.md D48.
#
# ⚠️ AND IT CANNOT BE A THEOREM OVER THE VECTOR TABLE, WHICH IS WHY THE ORIGINAL
# WAS NEVER WRITTEN.  There are no `loopz`/`repz` vectors and there must not be:
# a vector per spelling would be the same instruction differentially tested
# twice, and the vector table is keyed by AST form, which is precisely what the
# collapse says these spellings share.  The claim is about the ASSEMBLER, so the
# check belongs here, where an assembler is already running.
SYNONYMS = [
    ("loope .+18", "loopz .+18"),
    ("loopne .+18", "loopnz .+18"),
    ("repe cmpsq", "repz cmpsq"),
    ("repe scasb", "repz scasb"),
    ("repne cmpsl", "repnz cmpsl"),
    ("repne scasw", "repnz scasw"),
]

sasm, sobj = os.path.join(tmp, "syn.s"), os.path.join(tmp, "syn.o")
with open(sasm, "w") as f:
    f.write("\t.text\n")
    for i, (a, b) in enumerate(SYNONYMS):
        f.write(f"syn{i}a:\t{a}\nsyn{i}b:\t{b}\n")
r = run(f"clang -target x86_64-unknown-linux-gnu -c {sasm} -o {sobj}")
if r.returncode != 0:
    print("⛔ assembler refused a synonym pair — a spelling this model claims is "
          "real does not assemble:\n" + r.stderr)
    sys.exit(2)
r = run(f"objdump -d {sobj}")
if r.returncode != 0:
    print("⛔ objdump failed on the synonym object:\n" + r.stderr); sys.exit(2)

slabels, saddrs = {}, {}
for line in r.stdout.splitlines():
    m = re.match(r'^([0-9a-f]+) <([^>]+)>:', line.strip())
    if m:
        slabels[m.group(2)] = int(m.group(1), 16); continue
    m = re.match(r'^\s*([0-9a-f]+):\s+((?:[0-9a-f]{2} )+)', line)
    if m:
        saddrs[int(m.group(1), 16)] = "".join(m.group(2).split())

sbad = []
for i, (a, b) in enumerate(SYNONYMS):
    la, lb = slabels.get(f"syn{i}a"), slabels.get(f"syn{i}b")
    if la is None or lb is None or la not in saddrs or lb not in saddrs:
        sbad.append(f"`{a}` / `{b}`: no instruction at one of the labels"); continue
    if saddrs[la] != saddrs[lb]:
        sbad.append(f"`{a}` = {saddrs[la]} but `{b}` = {saddrs[lb]} — these are "
                    f"NOT one encoding, and the roster collapse that assumes "
                    f"they are is wrong")

if sbad:
    print(f"⛔ synonym collapse FAILED ({len(sbad)} of {len(SYNONYMS)} pairs):")
    for b in sbad: print("   " + b)
    sys.exit(1)
print(f"synonym collapse: CLEAN — {len(SYNONYMS)} spelling pairs, each assembling "
      f"to identical bytes, so `loopSpellings` and `repSpellings` collapse "
      f"spellings the machine has already collapsed")
