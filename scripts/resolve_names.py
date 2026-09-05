#!/usr/bin/env python3
r"""RESOLVE a census mnemonic to x86isa's own name for the SAME INSTRUCTION, by
ENCODING — never by string surgery on the name.

WHY THIS EXISTS.  `p2_oracle_support.py` joins the demand census to x86isa's
instruction listing on `(mnemonic, bucket)`.  When the two spell the same
instruction differently the join misses, and the tool reports the pair as
"absent under this name".  Sixteen pairs sat in that pile.  Ten of them were not
name problems at all — they were entries the catalogue READER dropped, repaired
in D138 — and the six that remain really are spelling differences:

    cvtsi2sdq -> cvtsi2sd     the census carries clang's operand-size suffix
    cvtsi2ssq -> cvtsi2ss
    pextrd    -> pextrd/q     the listing names a PAIR of widths in one entry
    pinsrd    -> pinsrd/q
    pinsrq    -> pinsrd/q
    vzeroupper-> vzeroupper   same name, different BUCKET (see below)

⛔⛔ AND THIS IS WHY THE RULE IS "BY ENCODING, NEVER BY NAME".  A suffix-stripping
rule gets `cvtsi2sdq -> cvtsi2sd` right and then invents `pextrd -> pextr`, which
is not an instruction; nothing that edits the STRING `pextrd` produces the string
`pextrd/q`, because the listing's name is not a spelling of one mnemonic at all —
it is two widths sharing an entry.  D100 already paid for the general form of
this: a lossy key published a phantom row.  So the join key here is the thing the
machine actually dispatches on — the opcode map, the opcode byte, the mandatory
prefix, and the VEX fields — recovered from bytes `clang` emitted.

WHAT IS DERIVED AND WHAT IS AN INPUT.  The SPELLING is an input, hand-chosen, the
same class of datum every `P2_FORMS` row already carries.  Everything else is
derived: the bytes come from `clang`, the encoding key from those bytes, and the
listing name and its implemented flag from the entry that key selects.  The
spelling is not taken on trust either — `--check` requires the assembler's own
disassembly to name the instruction we think we wrote.

⚠️ `vzeroupper` RESOLVES BUT REMAINS UNASKABLE, and saying so is the point.  Its
listing entry is found, and x86isa IMPLEMENTS it.  But the census keys it at
`AVX (state)`, which is one of the buckets `oracle_availability.probe_bucket`
cannot express, so no probe can carry that key.  Resolving the name buys the
verdict and buys nothing askable — 1,241 instructions of demand that this route
cannot reach ([[feedback-a-blocked-repair-blocks-a-design]]).
"""
import json, os, re, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LISTING = os.path.join(ROOT, "vendor", "acl2", "books", "projects", "x86isa",
                       "machine", "inst-listing.lisp")

# (census mnemonic, census bucket, a spelling in that bucket).  INPUT, not
# derived — and checked against the disassembler by `--check`.
UNJOINED = [
    ("vzeroupper", "AVX (state)",       "vzeroupper"),
    ("cvtsi2sdq",  "SSE-legacy (xmm)",  "cvtsi2sdq %rax, %xmm0"),
    ("cvtsi2ssq",  "SSE-legacy (xmm)",  "cvtsi2ssq %rax, %xmm0"),
    ("pextrd",     "SSE-legacy (xmm)",  "pextrd $0x1, %xmm0, %eax"),
    ("pinsrd",     "SSE-legacy (xmm)",  "pinsrd $0x1, %eax, %xmm0"),
    ("pinsrq",     "SSE-legacy (xmm)",  "pinsrq $0x1, %rax, %xmm0"),
]


def assemble(spellings):
    """[(bytes, disassembly)] for each spelling, from clang and objdump.

    ⛔ One assembly unit, one disassembly, and the addresses are checked
    CONSECUTIVE before the results are zipped back onto the inputs — zipping two
    lists by position without checking they describe the same instructions is
    how a row gets another row's bytes."""
    d = tempfile.mkdtemp()
    s, o = os.path.join(d, "n.s"), os.path.join(d, "n.o")
    open(s, "w").write(".text\n" + "\n".join(spellings) + "\n")
    r = subprocess.run(f"clang -target x86_64-unknown-linux-gnu -c {s} -o {o}",
                       shell=True, capture_output=True, text=True)
    if r.returncode:
        sys.exit("⛔ the assembler refused a spelling:\n" + r.stderr)
    r = subprocess.run(f"objdump -d {o}", shell=True, capture_output=True,
                       text=True)
    if r.returncode:
        sys.exit("⛔ objdump failed:\n" + r.stderr)
    ins = []
    for line in r.stdout.splitlines():
        m = re.match(r"^\s*([0-9a-f]+):\s+((?:[0-9a-f]{2} )+)\s*(.*)$", line)
        if m:
            ins.append([int(m.group(1), 16), m.group(2).split(),
                        m.group(3).strip().replace("\t", " ")])
    if len(ins) != len(spellings):
        sys.exit("⛔ %d spellings assembled to %d instructions — refusing to zip"
                 % (len(spellings), len(ins)))
    for i in range(len(ins) - 1):
        if ins[i][0] + len(ins[i][1]) != ins[i + 1][0]:
            sys.exit("⛔ address gap at %d — refusing to zip" % i)
    return [("".join(b), t) for _a, b, t in ins]


def encoding_key(hx):
    """The (opcode key, mandatory prefix, is-VEX) triple x86isa dispatches on.

    The listing writes the opcode map INTO the `:OP` literal: `#xF10` is 0F 10,
    `#xF3A15` is 0F 3A 15, a bare `#x90` is a one-byte opcode.  This rebuilds
    that same literal from the instruction's own bytes."""
    b = [int(hx[i:i + 2], 16) for i in range(0, len(hx), 2)]
    i, pfx, vex = 0, None, None
    while i < len(b):
        if b[i] in (0x66, 0xf2, 0xf3):
            pfx = {0x66: ":66", 0xf2: ":F2", 0xf3: ":F3"}[b[i]]; i += 1
        elif 0x40 <= b[i] <= 0x4f:          # REX: width, not identity
            i += 1
        else:
            break
    if b[i] == 0xc5:                        # 2-byte VEX: map is always 0F
        vex = {"map": 0x0f, "pp": b[i + 1] & 3, "L": (b[i + 1] >> 2) & 1}; i += 2
    elif b[i] == 0xc4:                      # 3-byte VEX: map in mmmmm
        vex = {"map": {1: 0x0f, 2: 0x0f38, 3: 0x0f3a}[b[i + 1] & 0x1f],
               "pp": b[i + 2] & 3, "L": (b[i + 2] >> 2) & 1}; i += 3
    if vex:
        mp, op = vex["map"], b[i]
        pfx = {0: None, 1: ":66", 2: ":F3", 3: ":F2"}[vex["pp"]]
    else:
        mp = 0
        if b[i] == 0x0f:
            i += 1
            if b[i] in (0x38, 0x3a):
                mp = 0x0f00 | b[i]; i += 1
            else:
                mp = 0x0f
        op = b[i]
    key = (op if mp == 0 else
           0xf00 | op if mp == 0x0f else
           0xf3800 | op if mp == 0x0f38 else 0xf3a00 | op)
    # ⛔ VEX.L IS PART OF THE IDENTITY, NOT A WIDTH DECORATION.  Dropping it made
    # `vzeroupper` (VEX.128) and `vzeroall` (VEX.256) collide on one key — they
    # share opcode 0F 77 with no prefix and are told apart by this bit alone.
    # The gate REFUSED on the collision rather than picking the first name,
    # which is how the omission was found ([[feedback-a-gate-that-refuses-must-say-what-it-saw]]).
    return key, pfx, (vex["L"] if vex else None)


def listing_entries():
    """(name, key, prefix, VEX.L or None, implemented) for every non-EVEX entry.

    The L column is `None` for a legacy entry, 0 or 1 for a VEX one — the same
    three-valued field `encoding_key` returns, so the join is on equal terms.
    x86isa spells L with six tokens: `:128`/`:LIG`/`:LZ`/`:L0` are L = 0 and
    `:256`/`:L1` are L = 1 (D138)."""
    txt = open(LISTING).read()
    out = []
    for part in re.split(r'\n\s*\(INST\s+"', txt)[1:]:
        name = part.split('"')[0].lower()
        body = part[:part.find("(INST ")] if part.find("(INST ") > 0 else part
        op = re.search(r":OP\s+#x([0-9A-Fa-f]+)", body)
        if not op or re.search(r":EVEX\s+'\(", body):
            continue
        v = re.search(r":VEX\s+'\(([^)]*)\)", body)
        p = re.search(r":PFX\s+(\S+)", body)
        fn = re.search(r"\n\s+'\((x86-[a-z0-9/?\-\.]+)[\s)]", body, re.I)
        if v:
            g = v.group(1)
            pfx = ":66" if ":66" in g else ":F3" if ":F3" in g else \
                  ":F2" if ":F2" in g else None
            if ":256" in g or ":L1" in g:
                lbit = 1
            elif ":128" in g or ":LIG" in g or ":LZ" in g or ":L0" in g:
                lbit = 0
            else:
                lbit = None            # widthless VEX entry: matches neither
        else:
            pfx = None if (p is None or p.group(1) == ":NO-PREFIX") else p.group(1)
            lbit = None
        out.append((name, int(op.group(1), 16), pfx, lbit, bool(fn)))
    return out


def resolve():
    """{(census mnemonic, bucket): (listing name, verdict)} — derived, not typed."""
    ents = listing_entries()
    got, rows = {}, assemble([sp for _m, _b, sp in UNJOINED])
    for (mn, bucket, spelling), (hx, dis) in zip(UNJOINED, rows):
        key, pfx, lbit = encoding_key(hx)
        hits = [e for e in ents if e[1] == key and e[2] == pfx and e[3] == lbit]
        names = sorted({e[0] for e in hits})
        impl = sorted({e[0] for e in hits if e[4]})
        got[(mn, bucket)] = {
            "spelling": spelling, "bytes": hx, "disassembly": dis,
            "key": "#x%X" % key, "pfx": pfx or "-", "vex_L": lbit,
            "listing_names": names, "implemented_names": impl,
            "verdict": "executes" if impl else ("refuses" if names else None),
        }
    return got


def check():
    """⛔ THE SPELLING IS AN INPUT, SO IT IS THE THING THAT MUST BE CHECKED.

    Two arms, and the second is the one with teeth:
      1. every pair resolves to exactly ONE listing name (a key selecting two
         different names is an ambiguity to report, never to pick from);
      2. the assembler's OWN disassembly of the bytes must name the instruction
         we believe we wrote — either the census mnemonic or the listing name it
         resolves to, modulo the operand-size suffix the census carries.  A
         spelling that assembles to something else would resolve confidently and
         wrongly, and nothing downstream could tell."""
    bad, got = [], resolve()
    for (mn, bucket), r in sorted(got.items()):
        if len(r["listing_names"]) != 1:
            bad.append("%s/%s: %d listing names %s — ambiguous, not picked"
                       % (mn, bucket, len(r["listing_names"]), r["listing_names"]))
            continue
        name = r["listing_names"][0]
        head = r["disassembly"].split()[0] if r["disassembly"] else ""
        # ⛔⛔ COMPARE AGAINST THE CENSUS MNEMONIC, NEVER AGAINST THE LISTING
        # NAME.  The first version of this arm accepted `head in (mn, name)`,
        # and `name` is DERIVED FROM THESE VERY BYTES — so it asked whether the
        # disassembly agrees with what the bytes decoded to, which is true by
        # construction and cannot fail.  Planting `addpd` as the spelling for
        # `cvtsi2sdq` resolved it to `addpd` and the gate printed CLEAN.
        # ⇒ 🔑 A CHECK WHOSE EXPECTED VALUE IS COMPUTED FROM ITS SUBJECT IS NOT
        # A CHECK ([[feedback-a-derivation-gate-wraps-a-false-sentence]]).  `mn`
        # is the one datum here that does NOT come from the bytes: it is what
        # the demand census counted.  The only slack allowed is the operand-size
        # suffix, which is the very difference this file exists to resolve.
        ok = bool(head) and (head == mn or mn.startswith(head)
                             or head.startswith(mn))
        if not ok:
            bad.append("%s: spelled %r, assembled to %r — the disassembler "
                       "calls it %r, so the spelling is not this instruction"
                       % (mn, r["spelling"], r["bytes"], r["disassembly"]))
        print("  %s %-11s %-18s %-8s %-14s -> %-11s %s"
              % ("✔" if ok else "⛔", mn, bucket, r["key"], r["bytes"],
                 name, r["verdict"]))
    if bad:
        print("\n⛔ resolve_names: FAIL")
        for b in bad:
            print("    " + b)
        return 1
    print("\nresolve_names: CLEAN — every unjoined census name resolved to exactly "
          "one x86isa entry BY ENCODING, and the assembler's own disassembly "
          "confirms each spelling is the instruction it claims to be.")
    return 0


if __name__ == "__main__":
    if "--json" in sys.argv:
        print(json.dumps({"%s|%s" % k: v for k, v in resolve().items()}, indent=1))
        sys.exit(0)
    sys.exit(check())
