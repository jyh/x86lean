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

segf = os.path.join(tmp, "seg.txt")
for mode, out in (("emit-asm", asm), ("expected-lengths", exp),
                  ("segment-decls", segf)):
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
    # ⛔⛔ P2 ITEM 3 FOUND THIS BY BEING THE LONGEST ENCODING IN THE TABLE.
    # The pattern used to be `(?:[0-9a-f]{2} )+` — each byte followed by a
    # SPACE — which silently DROPPED THE LAST BYTE of any instruction long
    # enough to fill objdump's byte column, because there the final byte abuts
    # the TAB before the mnemonic instead of a space.  `movabsq $imm64, %r64`
    # is ten bytes, the first form in this repository to reach that width, and
    # it read back as NINE.
    # ⇒ 🔑 AND THE DIRECTION IS THE FINDING: the gate would have reported
    # `len=9` for a ten-byte instruction, so a model that claimed 9 would have
    # AGREED WITH IT.  A harness that truncates its own reading cannot see a
    # model that truncates the same way.  Latent since P0; only the longest
    # encoding could expose it.
    m = re.match(r'^\s*([0-9a-f]+):\s+([0-9a-f]{2}(?: [0-9a-f]{2})*)(?:\s|$)', line)
    if m:
        addrs.append((int(m.group(1), 16), m.group(2).split()))

by_addr = {a: b for a, b in addrs}

# ⭐⭐ P2 ITEM 2: THE `lock` PREFIX IS A SEPARATE objdump LINE, AND JOINING IT IS
# NOT COSMETIC.  objdump disassembles `f0 48 01 0b` as TWO lines — `f0  lock`
# then `48 01 0b  addq %rcx,(%rbx)` — so a vector whose encoding begins with the
# prefix would be read here as a ONE-BYTE instruction.  The `Instr.len` check
# would then compare the model's 4 against the assembler's 1 and fail on every
# locked vector, and — worse in the other direction — a model that had SILENTLY
# DROPPED the prefix would have agreed with that 1.
#
# ⇒ A single-byte `f0` line is FOLDED INTO ITS SUCCESSOR: same start address,
# bytes concatenated. That is what the machine does (a prefix is part of the
# instruction, SDM Vol. 2A §2.1.1) and what `Instr.len` means. Anything else
# objdump splits — REX, the operand-size prefix — it already keeps on one line;
# `f0` is the only one this table has met that it does not.
LOCK_PREFIX = "f0"
_folded, _absorbed = {}, set()
for a in sorted(by_addr):
    if a in _absorbed:
        continue
    b = by_addr[a]
    if len(b) == 1 and b[0] == LOCK_PREFIX and (a + 1) in by_addr:
        _folded[a] = b + by_addr[a + 1]
        _absorbed.add(a + 1)
    else:
        _folded[a] = b
by_addr = _folded
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
# ⭐⭐ P2 ITEM 1 — THE SEGMENT OVERRIDE, HELD BY THREE INDEPENDENT SOURCES.
#
# A `%fs:`/`%gs:` operand is visible in three places that no single edit writes
# together: the hand-written AT&T text of the vector, the PREFIX BYTE the
# assembler emits for it (`64` for FS, `65` for GS — SDM Vol. 2A §2.1.1), and
# the `seg` field of the Lean AST. All three must agree, per vector and per
# SEGMENT — not merely "some override is present", because reading GS's base for
# an FS access is exactly one of the four planted defects this batch carries.
#
# ⛔ WHY IT IS HERE AND NOT A THEOREM. It WAS a theorem — an AST walk compared
# against the encoded bytes over all 784 vectors — and it cost 4 200 ms of kernel
# time, the second most expensive declaration in Tests.Coverage. Measured, the
# byte half alone was 7.9 s standalone against 0.4 s for the AST half: the whole
# cost was `String.toList` on 784 literals. The kernel-cost ceiling refused it
# and named this build. The completeness half — "does the AST walk see every
# constructor" — did not move here: it became the ABSENCE of a wildcard arm in
# `X86.opOperands`, which the compiler checks on every build and which also
# covers constructors no vector uses yet.
declared, declared_lock = {}, {}
for line in open(segf):
    parts = line.split()
    if len(parts) == 3:
        declared[parts[0]] = parts[1]
        declared_lock[parts[0]] = parts[2]

asm_text = {}
for line in open(asm):
    m = re.match(r'^(\S+):\t(.*)$', line.rstrip("\n"))
    if m:
        asm_text[m.group(1)] = m.group(2)

PREFIX = {"64": "fs", "65": "gs"}


def seg_findings(declared, asm_text, first_byte):
    """The three-source comparison, as a function so `--selftest` can doctor each
    source in turn.  Returns the list of disagreements."""
    out = []
    for vid, want in declared.items():
        t = asm_text.get(vid, "")
        from_text = "fs" if "%fs:" in t else "gs" if "%gs:" in t else "-"
        from_bytes = PREFIX.get(first_byte.get(vid, ""), "-")
        if not (want == from_text == from_bytes):
            out.append(f"{vid}: AST says {want}, AT&T text says {from_text}, "
                       f"assembler prefix says {from_bytes}")
    return out


first_byte = {}
for vid in declared:
    b = by_addr.get(labels.get(vid, -1), [])
    if b:
        first_byte[vid] = b[0]

# ⭐ RED-FIRST, IN THE SAME RUN AND FOR THE PRICE OF THREE DICT COPIES.  Each of
# the three sources is doctored ALONE and must produce a finding, and the
# undoctored comparison must produce none — because three sources that agree is
# also what a comparison reading none of them would report.
# It runs on EVERY invocation, not behind a flag: three dict copies cost
# microseconds, and a red-first arm nobody remembers to pass a flag for is a
# red-first arm that does not run.
if True:
    import copy as _copy
    arms, sok = [], True
    victim = next((v for v, w in declared.items() if w == "fs"), None)
    other = next((v for v, w in declared.items() if w == "gs"), None)
    if victim is None or other is None:
        print("⛔ segment selftest cannot run: no FS and GS vector to doctor.")
        sys.exit(2)
    d = dict(declared); d[victim] = "gs"
    arms.append(("the AST's segment, swapped fs->gs",
                 bool(seg_findings(d, asm_text, first_byte))))
    a2 = dict(asm_text); a2[victim] = a2[victim].replace("%fs:", "")
    arms.append(("the AT&T text loses its override",
                 bool(seg_findings(declared, a2, first_byte))))
    b2 = dict(first_byte); b2[victim] = "65"
    arms.append(("the assembler's prefix byte, fs->gs",
                 bool(seg_findings(declared, asm_text, b2))))
    arms.append(("control: the shipped three sources agree",
                 not seg_findings(declared, asm_text, first_byte)))
    for name, ok in arms:
        print(("  ✔ " if ok else "  ✖ ") + name)
        sok = sok and ok
    if not sok:
        print("⛔ segment cross-check SELFTEST FAILED — a doctored source was "
              "not caught, or the control did not hold.")
        sys.exit(1)

segbad = seg_findings(declared, asm_text, first_byte)
if segbad:
    print(f"⛔ segment-override cross-check FAILED ({len(segbad)} of "
          f"{len(declared)} forms):")
    for b in segbad: print("   " + b)
    sys.exit(1)
n_seg = sum(1 for v in declared.values() if v != "-")
if n_seg == 0:
    print("⛔ segment-override cross-check found NO segmented vector. A check "
          "whose subject is absent reports a failure here, not a pass.")
    sys.exit(2)
print(f"segment cross-check: CLEAN — {n_seg} segmented form(s) of {len(declared)}; "
      f"the AT&T text, the assembler's prefix byte and the AST agree on the "
      f"SEGMENT, per vector")

# ─────────────────────────────────────────────────────────────────────────────
# ⭐⭐ P2 ITEM 2 — THE LOCK PREFIX, HELD BY THE SAME THREE SOURCES.
#
# ⛔ AND THIS ONE ALSO GATES THE PREFIX FOLD ABOVE.  objdump prints `f0` as its
# OWN instruction line; without the fold a locked vector reads here as a
# ONE-BYTE instruction, and — the direction that matters — a model that had
# silently DROPPED the prefix would have agreed with that one byte. So the arms
# below are not decoration on a solved problem: they are what says the fold is
# still happening and still necessary.
def lock_findings(declared_lock, asm_text, first_byte):
    out = []
    for vid, want in declared_lock.items():
        t = asm_text.get(vid, "")
        from_text = "lock" if re.match(r"^\s*lock\b", t) else "-"
        from_bytes = "lock" if first_byte.get(vid, "") == "f0" else "-"
        if not (want == from_text == from_bytes):
            out.append(f"{vid}: AST says {want}, AT&T text says {from_text}, "
                       f"assembler prefix says {from_bytes}")
    return out


if True:
    lock_arms, lok = [], True
    lvic = next((v for v, w in declared_lock.items() if w == "lock"), None)
    if lvic is None:
        print("⛔ lock cross-check cannot run: no locked vector to doctor.")
        sys.exit(2)
    d = dict(declared_lock); d[lvic] = "-"
    lock_arms.append(("the AST loses its lock flag",
                      bool(lock_findings(d, asm_text, first_byte))))
    a2 = dict(asm_text); a2[lvic] = re.sub(r"^\s*lock\s+", "", a2[lvic])
    lock_arms.append(("the AT&T text loses its `lock` token",
                      bool(lock_findings(declared_lock, a2, first_byte))))
    b2 = dict(first_byte); b2[lvic] = "48"
    lock_arms.append(("the assembler's prefix byte is not f0 (the UNFOLDED read)",
                      bool(lock_findings(declared_lock, asm_text, b2))))
    lock_arms.append(("control: the shipped three sources agree",
                      not lock_findings(declared_lock, asm_text, first_byte)))
    for name, ok in lock_arms:
        print(("  ✔ " if ok else "  ✖ ") + name)
        lok = lok and ok
    if not lok:
        print("⛔ lock cross-check SELFTEST FAILED.")
        sys.exit(1)

lockbad = lock_findings(declared_lock, asm_text, first_byte)
if lockbad:
    print(f"⛔ lock-prefix cross-check FAILED ({len(lockbad)} of "
          f"{len(declared_lock)} forms):")
    for b in lockbad: print("   " + b)
    sys.exit(1)
n_lock = sum(1 for v in declared_lock.values() if v == "lock")
if n_lock == 0:
    print("⛔ lock cross-check found NO locked vector. A check whose subject is "
          "absent reports a failure here, not a pass.")
    sys.exit(2)
print(f"lock cross-check: CLEAN — {n_lock} locked form(s) of {len(declared_lock)}; "
      f"the AT&T text, the assembler's `f0` prefix byte and the AST's `Ea.lock` "
      f"agree, per vector — which is also what says the prefix FOLD is live")

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
    # ⛔⛔ P2 ITEM 3 FOUND THIS BY BEING THE LONGEST ENCODING IN THE TABLE.
    # The pattern used to be `(?:[0-9a-f]{2} )+` — each byte followed by a
    # SPACE — which silently DROPPED THE LAST BYTE of any instruction long
    # enough to fill objdump's byte column, because there the final byte abuts
    # the TAB before the mnemonic instead of a space.  `movabsq $imm64, %r64`
    # is ten bytes, the first form in this repository to reach that width, and
    # it read back as NINE.
    # ⇒ 🔑 AND THE DIRECTION IS THE FINDING: the gate would have reported
    # `len=9` for a ten-byte instruction, so a model that claimed 9 would have
    # AGREED WITH IT.  A harness that truncates its own reading cannot see a
    # model that truncates the same way.  Latent since P0; only the longest
    # encoding could expose it.
    m = re.match(r'^\s*([0-9a-f]+):\s+([0-9a-f]{2}(?: [0-9a-f]{2})*)(?:\s|$)', line)
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
