#!/usr/bin/env python3
"""Derive the coverage claim from the vectors and the roster, instead of asserting it.

WHY THIS EXISTS.  Until batch 19 the sentence "covering N of the 525 forms in
`p1/roster.tsv`" was a HAND-MAINTAINED LITERAL.  Its value was a running sum of
eighteen independent `awk` counting rules, each written in a comment in
`Main.lean` at the batch that added it, and **nothing had ever checked that those
eighteen rules partition the roster**.  Batch 18's handover said so plainly: it
could account for only 32 of the 72 rows it believed remained, and the other ~40
carried base names the model already implements.  A number nobody can recompute
is a number nobody can refute.

WHAT THIS DOES.  It computes the claim from two sources that are not derived from
each other, and **their agreement is the gate**:

  SOURCE S (the vector's own text).  Each differential vector's AT&T `asm`
  string -- the string clang assembles and `check_encodings.py` already gates --
  is parsed against the roster's own shape vocabulary into candidate
  (prefix, base, shape) rows.

  SOURCE E (the roster row's own encoding).  Every roster row is synthesised
  into a canonical instance and assembled by clang.  This says what a row's
  machine encoding IS, with no reference to any vector.

  THE GATE.  A vector may only claim a row whose canonical instance has THE SAME
  OPCODE as the vector's own assembled bytes.  A mis-parse does not survive it:
  reading `andb $0x5a,%al` as the generic `r,imm` form offers opcode 0x80 against
  the vector's 0x24, and the candidate dies.  A vector that resolves to NOTHING,
  or to two rows that are not the same encoding, is a FINDING and this script
  exits non-zero.  It never guesses.

⭐ AND SOURCE E IS WHAT FINDS THE ALIASES.  Rows whose canonical instances
assemble to IDENTICAL BYTES are the same machine form under different spellings
-- `jz` and `je`, `setz` and `sete`, `sal` and `shl`, `xchg ax,r` and
`xchg r,ax`.  The model decodes bytes, not spellings, so a vector spelled `je`
exercises the `jz` row exactly as much.  Claiming both is correct; claiming both
SILENTLY is not, so every alias group is printed with the bytes that prove it.

LANE.  Personal lane, public sources only.  clang/LLVM and binutils are tools;
nothing from either is copied.
"""
import sys, os, re, json, subprocess, tempfile, collections, argparse

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)

# ⛔⛔ THE BYTE-COLUMN PARSE IS IMPORTED, NOT REWRITTEN, AND THAT IS THE WHOLE
# REPAIR OF D106.  This file used to carry its OWN copy of the objdump parse —
# `re.match(r'^\s*([0-9a-f]+):\s+((?:[0-9a-f]{2} )+)', line)` — written before
# `check_encodings.parse_objdump` existed and never revisited after it did.
#
# The two agreed at birth.  Then D83 and its Linux follow-up fixed the ORIGINAL
# twice — the final byte abutting the tab, and GNU objdump's SEVEN-BYTE WRAP —
# and the copy here received neither, because nothing held them together.  ⇒ 🔑
# A DUPLICATE BORN IN AGREEMENT DIVERGES ON THE NEXT ORDINARY REPAIR, AND THE
# ONE THAT MATTERS IS THE ONE ON THE PATH THAT REPORTS SUCCESS: the fixed copy
# was in a gate that had been green for weeks, and the stale copy was in the gate
# master CI had never reached (D104).
#
# ⚠️ MEASURED, NOT INFERRED.  With GNU binutils' objdump on PATH this file's own
# copy read `cmp_rip_q` — ELEVEN bytes, the widest non-exempt vector in the
# table — as its first SEVEN, and reported "1 vector(s) resolve to NO roster
# row", which is exactly what the runner said.  With Apple LLVM's objdump the
# same vector resolves, which is why forty-nine commits of local green said
# nothing about it.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_encodings import parse_objdump

# ---------------------------------------------------------------- the roster

def load_roster(path="p1/roster.tsv"):
    rows = []
    for i, line in enumerate(open(path)):
        if i < 2:                      # a comment line and the header
            continue
        f = line.rstrip("\n").split("\t")
        if len(f) >= 6:
            rows.append({"prefix": f[2], "base": f[3], "shape": f[4], "widths": f[5]})
    return rows

# --------------------------------------------------- SOURCE E: assemble rows

# Registers by their ENCODING INDEX, at each width, chosen so that no instance
# ever needs a REX prefix -- a perturbation that changes an encoding's LENGTH
# has changed its form, and would void the reading.  Index 0 (the accumulator)
# is never used, so clang cannot slip into a short accumulator encoding
# underneath a perturbation that was only meant to move a register field.
RIDX = {"b": {1: "%cl", 2: "%dl", 3: "%bl", 4: "%ah", 5: "%ch", 6: "%dh", 7: "%bh"},
        "w": {1: "%cx", 2: "%dx", 3: "%bx", 4: "%sp", 5: "%bp", 6: "%si", 7: "%di"},
        "l": {1: "%ecx", 2: "%edx", 3: "%ebx", 4: "%esp", 5: "%ebp", 6: "%esi",
              7: "%edi"},
        "q": {1: "%rcx", 2: "%rdx", 3: "%rbx", 4: "%rsp", 5: "%rbp", 6: "%rsi",
              7: "%rdi"}}

# ⭐ THE BANKS EXIST TO MOVE EVERY BIT OF EVERY REGISTER FIELD.  A ModRM
# register field is THREE bits, so two samples cannot span it: whichever bits
# happen to agree in both are frozen into the skeleton as if they were part of
# the opcode.  That is not a hypothetical -- it is the defect this table was
# written to fix, and it made `and %ecx,%eax` fail to match the `and r,r` row
# it is an instance of.  Read down each column: every operand position takes a
# set of indices whose pairwise XORs cover 0b111.
BANKS = [(1, 2, 3), (2, 3, 4), (4, 1, 5), (3, 4, 1)]
HELDOUT_BANK = (5, 6, 2)
# Memory bases, likewise spanning all three bits of the r/m field.  Index 4
# (%rsp) would force a SIB byte and index 5 (%rbp) a displacement, either of
# which changes the LENGTH, so neither appears here.
MBASE = [6, 3, 1, 2]
HELDOUT_MBASE = 7

# ⛔⛔ AND THE LINE ABOVE MAKES THIS INSTRUMENT STRUCTURALLY BLIND TO THE ONE
# BASE REGISTER THAT MOVES WITH THE STACK.  Excluding %rsp and %rbp is CORRECT
# — a form skeleton is a fixed-length byte pattern and either base changes the
# length — but the consequence had never been paid because no vector used one.
#
# P1 BATCH 20 is the first batch that needs one.  `popq (%rsp)` is the ONLY
# instance that can make `step`'s claim — that a POP's destination address is
# computed AFTER the stack pointer is incremented — observable at all: any
# other base does not move, so a model with the order reversed is bit-identical.
# The same is true of `pushq (%rsp)` for the mirror claim.  Both vectors exist
# to be caught by an ARM, not to claim a row: the rows they belong to
# (`push m`, `pop m`) are claimed by their RBX-based siblings.
#
# ⇒ Such a vector resolves to NO roster row, and that is the instrument being
# RIGHT.  It must not be reported as a parse failure — and it must not become a
# hole either.
#
# ⭐ SO THE EXEMPTION IS GATED IN BOTH DIRECTIONS.  An id listed here that
# RESOLVES is a finding, not a quiet pass: it means the skeleton grew to cover
# the case and this list has gone stale, which is the failure mode a hand-kept
# exclusion list always has ([[an-unrecorded-rule-cannot-be-audited]]).  An
# unresolved vector NOT listed here is a finding exactly as before.  `--selftest`
# carries an arm for each direction.
# ⭐⭐ P2 ITEM 1 (BATCH 22) TURNED THIS FROM A SET INTO A TABLE WITH A REASON PER
# ENTRY, and the reason is that the batch would otherwise have filed eight
# segment-override vectors under a label that says "base %rsp forces a SIB byte".
# That label was TRUE of both existing entries and is FALSE of the new eight,
# and a printed tag nobody reads against its subject is exactly how a reassuring
# comment outlives the thing it describes ([[ungated-prose-overclaims]],
# [[an-unrecorded-rule-cannot-be-audited]]).  One list, one rule each, and the
# rule is what gets printed.
#
# THE SEGMENT ENTRIES' RULE, stated so it can be argued with: a segment override
# is a PREFIX (`64`/`65`) on an instruction whose roster row is already claimed
# by its unsegmented sibling — `mov r,m`, `mov m,r`, `add m,r` and `lea r,m` are
# all claimed without these vectors, and the claimed-row count does not move
# when they are added (498 before, 498 after).  They exist to make the SEGMENT
# BASE observable, which is a capability the census prices at 29,943
# instructions and the roster does not describe at all — K's tree has no
# separate rule for a prefixed `mov`.  So: no row, on purpose, and both
# directions of the exemption stay gated exactly as batch 20 built them.
# ⭐⭐⭐ AND THE P2 VECTOR ROWS ARE A THIRD RULE, NOT A THIRD EXAMPLE OF THE
# SECOND.  The segment and LOCK entries below say *the row exists and a sibling
# already claims it*.  The SIMD entries say something different and stronger:
# **this roster does not contain the row at all, by its own derivation.**
# `docs/P1-ROSTER.md` is derived from K's tree by `scripts/k_roster.py`, and its
# exclusion table has carried, since P1, the line
#
#     | any operand `xmm`/`ymm`/`zmm`/`mm`/`m128`/`m256`/`m512` | SIMD: plan v1 §5 P2. |
#
# so there is no `paddd` row here to claim and there never was.  The vector work
# is counted against `docs/P2-ROSTER.md`, which exists, ranks these very
# mnemonics by measured demand, and is the correct denominator for it.
#
# ⛔ THE ALTERNATIVE WAS CONSIDERED AND REFUSED: admitting SIMD to the P1 roster
# means editing a DERIVED artifact's exclusion rule, which moves the 525-row
# denominator and therefore every coverage percentage this repository has
# published — in a batch whose subject is semantics.  A denominator change is its
# own batch with its own evidence, not a side effect of the first vector form.
#
# ⚠️ These stay gated in BOTH directions like every entry here: the day the P1
# roster does admit a SIMD row, the exemption stops being true and this gate says
# so rather than quietly under-counting.
CLAIMS_NO_ROW = {
    "movdqa_xx":  "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movdqu_xx":  "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "paddb_xx":   "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "paddw_xx":   "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "paddd_xx":   "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "paddq_xx":   "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psubb_xx":   "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psubw_xx":   "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psubd_xx":   "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psubq_xx":   "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pxor_xx":    "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pand_xx":    "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "por_xx":     "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "paddd_x2x3": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movdqa_x4x5": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movdqu_x4x5": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movdqa_load_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movdqa_store_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movdqu_load_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movdqu_store_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movdqu_load_unal": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movd_to_x": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movq_to_x": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movd_from_x": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movq_from_x": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "punpcklbw_xx": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "punpcklwd_xx": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "punpckldq_xx": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "punpcklqdq_xx": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "punpckhbw_xx": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "punpckhwd_xx": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "punpckhdq_xx": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "punpckhqdq_xx": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    # ⭐ P2 VECTOR WAVE, BATCH 13 — the packed shift group, exempted for the
    # reason every SIMD vector before it is: the P1 roster is DERIVED from K's
    # non-SIMD forms and excludes xmm operands, so a shift vector has no P1 row
    # to resolve to and is counted in the P2 roster instead.  ⚠️ Added in the
    # SAME COMMIT as the vectors: this list is the one D104 found three commits
    # stale, and the gate that reads it had never run on master.
    "psllw_i": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psllw_isat": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psllw_x": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psllw_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pslld_i": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pslld_isat": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pslld_x": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pslld_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psllq_i": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psllq_isat": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psllq_x": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psllq_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psrlw_i": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psrlw_isat": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psrlw_x": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psrlw_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psrld_i": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psrld_isat": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psrld_x": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psrld_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psrlq_i": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psrlq_isat": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psrlq_x": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psrlq_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psraw_i": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psraw_isat": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psraw_x": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psraw_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psrad_i": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psrad_isat": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psrad_x": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psrad_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pslldq_i": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pslldq_isat": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psrldq_i": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psrldq_isat": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psrad_x2x3": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psrld_i_x4": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psraw_m_disp": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movq_xx": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    # ⭐ P2 BATCH 18 (packuswb), same commit as the vectors.
    "packuswb_x": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "packuswb_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    # ⭐ P2 BATCH 17 (the packed compares), same commit as the vectors.
    "pcmpeqb_x": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pcmpeqb_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pcmpeqw_x": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pcmpeqw_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pcmpeqd_x": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pcmpeqd_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pcmpgtb_x": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pcmpgtb_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pcmpgtw_x": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pcmpgtw_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pcmpgtd_x": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pcmpgtd_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pcmpgtb_x2x3": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    # ⭐ P2 BATCH 15 (the packed binary group's MEMORY shape), added in the
    # SAME COMMIT as the vectors — D106's cost, not re-paid.  Twenty-two
    # entries written out rather than matched by a prefix: a pattern would
    # absorb the next such vector silently, and this list's whole value is
    # that adding a vector is a visible line.
    "pand_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "por_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pxor_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "paddb_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "paddw_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "paddd_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "paddq_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psubb_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psubw_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psubd_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "psubq_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "punpcklbw_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "punpcklwd_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "punpckldq_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "punpcklqdq_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "punpckhbw_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "punpckhwd_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "punpckhdq_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "punpckhqdq_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pand_m_unal": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "por_m_unal": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pxor_m_unal": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    # ⭐ P2 BATCH 14 (the permute group) — ADDED IN THE SAME COMMIT AS THE
    # VECTORS, which is what D106 cost a first-ever-green master run to
    # learn: this list is the ONLY gate that reads these ids, and a vector
    # landing without its entry is invisible until the gate is reached.
    # ⚠️ Fourteen entries for fourteen vectors, written out rather than
    # matched by a `pshuf` prefix: a pattern here would absorb the next
    # permute vector silently, and this list's whole value is that adding a
    # vector is a visible line.
    "pshufd_x_rev": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pshufd_x_asym": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pshufd_x_id": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pshufd_x2x3": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pshuflw_x_rev": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pshufhw_x_rev": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pshufhw_x_asym": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pshufd_m_rev": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pshufd_mw_rev": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pshuflw_m_rev": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pshuflw_mw_rev": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pshuflw_mw_asym": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pshufhw_mw_rev": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "pshufhw_m_asym": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    # ⛔ P2 BATCH 10 (the move family) LANDED WITHOUT THESE SIXTEEN, and
    # nothing said so for three commits: `claimed_forms.py --check` is the
    # only gate that reads this list, and master CI has never reached it —
    # the K fetch two steps earlier had been failing since the workflow
    # first parsed. A gate nobody has ever seen run is not a gate. (D104.)
    "movaps_xx": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movaps_x4x5": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movups_xx": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movaps_load_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movaps_store_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movups_load_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movups_store_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movups_load_unal": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movss_xx": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movss_x4x5": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movss_load_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movss_store_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movsd_xx": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movsd_x4x5": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movsd_load_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "movsd_store_m": "SIMD: the P1 roster excludes xmm operands by derivation; counted in the P2 roster",
    "push_m_rsp":     "base %rsp forces a SIB byte; claims no row",
    "pop_m_rsp":      "base %rsp forces a SIB byte; claims no row",
    "mov_fs_abs_q":   "a segment override is a prefix on a row already claimed",
    "mov_gs_abs_q":   "a segment override is a prefix on a row already claimed",
    "mov_fs_abs_d":   "a segment override is a prefix on a row already claimed",
    "mov_fs_base_q":  "a segment override is a prefix on a row already claimed",
    "mov_fs_store_q": "a segment override is a prefix on a row already claimed",
    "mov_fs_store_b": "a segment override is a prefix on a row already claimed",
    "add_fs_rmw_q":   "a segment override is a prefix on a row already claimed",
    "lea_fs_abs_q":   "a segment override is a prefix on a row already claimed",
    # ⭐ P2 ITEM 2.  Same rule as the segment overrides one line up, for the same
    # reason: `f0` is a PREFIX, and the rows the eleven locked vectors sit on —
    # `inc m`, `add m,r`, `xadd m,r`, `cmpxchg8b m`, `mov m,r` — are all claimed
    # by their unlocked siblings.  The claimed-row count does not move when they
    # are added (500 before, 500 after); what they test is the well-formedness
    # RULE and the #UD edge, which the roster does not describe.
    "lock_inc_m_d":       "a LOCK prefix is a prefix on a row already claimed",
    "lock_dec_m_d":       "a LOCK prefix is a prefix on a row already claimed",
    "lock_add_m_q":       "a LOCK prefix is a prefix on a row already claimed",
    "lock_or_m_q":        "a LOCK prefix is a prefix on a row already claimed",
    "lock_not_m_q":       "a LOCK prefix is a prefix on a row already claimed",
    "lock_neg_m_q":       "a LOCK prefix is a prefix on a row already claimed",
    "lock_bts_m_q":       "a LOCK prefix is a prefix on a row already claimed",
    "lock_xadd_m_q":      "a LOCK prefix is a prefix on a row already claimed",
    "lock_cmpxchg_m_q":   "a LOCK prefix is a prefix on a row already claimed",
    "lock_cmpxchg8b_m":   "a LOCK prefix is a prefix on a row already claimed",
    "lock_mov_m_q_ud":    "a LOCK prefix is a prefix on a row already claimed",
    "lock_lea_ud":        "a LOCK prefix is a prefix on a row already claimed",
    "lock_shl_m_q_ud":    "a LOCK prefix is a prefix on a row already claimed",
    # ⭐ P2 ITEM 3.  K files `mov r,imm` as ONE row with six variants and `blqw`
    # widths, and `mov_ri` already claims it: `movabs` is a distinct ENCODING of
    # a claimed row, not a row of its own.  The resolver assembles the roster
    # row's canonical form (`48 c7 c0 …`) and these are `48 b8 …`, so they
    # resolve to nothing — which is the instrument being right.
    "movabs_q":           "movabs is a distinct ENCODING of a row already claimed",
    "movabs_lo32_ones":   "movabs is a distinct ENCODING of a row already claimed",
    "movabs_hi32_ones":   "movabs is a distinct ENCODING of a row already claimed",
}

SIB_BASE_EXEMPT = set(CLAIMS_NO_ROW)

# Bases whose SOURCE operand width is fixed by the mnemonic (mixed-width moves).
SRCW = {"movsb": "b", "movzb": "b", "movsw": "w", "movzw": "w", "movslq": "l"}
# Bases taking an indirect operand in AT&T syntax.
STAR = {"jmp", "callq"}
ACCTOK = ("al", "ax", "eax", "rax")

# The immediates of a perturbation are BITWISE COMPLEMENTS of one another at the
# same encoded size, so that every bit -- and therefore every byte -- of the
# immediate field moves.  A pair like 0x11/0x22 moves only some of them, and the
# rest would be read as opcode.
IMMS = {
    "narrow": {w: ("$0x11", "$-18", "$0x2b") for w in "bwlq"},
    "wide": {"b": ("$0x5a", "$-91", "$0x33"),
             "w": ("$0x1234", "$-4661", "$0x5678"),
             "l": ("$0x12345678", "$-305419897", "$0x7edcba98"),
             "q": ("$0x12345678", "$-305419897", "$0x7edcba98")}}
# Memory ADDRESSING MODES.  A roster row's shape says `m`; the machine has
# several encodings of `m`, and a vector may use any of them, so each is its own
# form of the same row.  {B} is the base register, {D} the displacement.
MODES = ["({B})", "{D8}({B})", "{D32}({B})", "{D8}({B},%rcx,4)",
         "{D32}(%rip)"]
# ⛔ THESE PAIRS MUST BE TRUE BITWISE COMPLEMENTS, SIGN BIT INCLUDED.  The first
# version of this table used 0x6dcba987 as the "complement" of 0x12345678 --
# every bit but the TOP one -- so bit 31 of every displacement was frozen into
# the skeleton, and the one vector with a NEGATIVE displacement did not match
# the row it is an instance of.  ⚠️ The held-out control did not catch it,
# because the held-out value 0x7edcba98 is positive too and agreed with the
# perturbations on exactly the bit they missed: A CONTROL THAT SHARES THE BLIND
# SPOT IS SILENT.  The held-out values below are negative for that reason.
MDISP = {"D8": ("0x11", "-0x12", "-0x2b"),
         "D32": ("0x12345678", "-0x12345679", "-0x7edcba98")}


def synth(r, w, suffix, imm="$0x11", bank=0, mode=0, dispv=0, held=False):
    """A canonical AT&T instance of roster row `r` at width `w`.

    `bank`, `imm` and `mode` select a PERTURBATION: a different register set, a
    different immediate of the same size, a different addressing mode.  None of
    them changes the instruction's form -- that is what makes the bits they move
    operand bits rather than opcode bits.  `held=True` selects values held out
    of the perturbation set entirely, used to check the resulting skeleton.
    """
    toks = [] if r["shape"] == "-" else r["shape"].split(",")
    regs = HELDOUT_BANK if held else BANKS[bank]
    mbase = HELDOUT_MBASE if held else MBASE[bank]
    att, ri = [], 0
    sw = SRCW.get(r["base"])
    for pos, t in enumerate(toks):
        if t == "r":
            ww = sw if (sw and pos == 1) else w
            ix = regs[ri]
            if sw and pos == 1 and sw == "b" and w == "q" and ix > 3:
                # ⚠️ `movzbq %dh, %rbp` IS NOT ENCODABLE -- a high-8 register and
                # a REX prefix cannot coexist, and REX.W is what makes this a
                # 64-bit destination.  Only indices 1-3 are available here, so
                # bit 2 of this field is genuinely unspannable and the skeleton
                # under-covers it.  That is honest: the instances it then
                # refuses are instances the assembler refuses too.
                ix = 1 + (ix % 3)
            att.append(RIDX[ww][ix]); ri += 1
        elif t == "m":
            m = MODES[mode]
            d8, d32 = (MDISP["D8"][2], MDISP["D32"][2]) if held else \
                      (MDISP["D8"][dispv], MDISP["D32"][dispv])
            att.append(m.format(B=RIDX["q"][mbase], D8=d8, D32=d32))
        elif t == "imm":
            att.append(imm if isinstance(imm, str) else None)
        elif t == "one":
            pass                                    # AT&T leaves the 1 implicit
        elif t == "cl":
            att.append("%cl")
        elif t in ACCTOK:
            att.append("%" + t)
        elif t in ("label", "rel8"):
            # A lone `label` is a branch target.  A `label` BESIDE another
            # operand is a symbolic IMMEDIATE -- `cmp $L, (%rsi)` is how K's
            # grammar writes `cmp m,imm` with a symbol -- so it is synthesised
            # as the immediate it is.  ⚠️ Writing `$NEAR` here instead left the
            # immediate unperturbed, so its bytes stayed literal zeros and were
            # read as OPCODE; the row then failed to group with the `imm` row it
            # is a restriction of, and the separation check said so.
            att.append("NEAR" if len(toks) == 1 else imm)
        elif t == "rel32":
            att.append("Lfar")
        else:
            return None
    if any(a is None for a in att):
        return None
    att.reverse()                                   # the roster is Intel order
    if r["base"] in STAR and toks and toks[0] in ("r", "m"):
        att = ["*" + a for a in att]
    mn = r["base"] + (w if suffix else "")
    if r["prefix"]:
        mn = r["prefix"] + " " + mn
    return (mn + " " + ", ".join(att)).strip()


# An ADDRESS-SIZE prefix the vector spells out.  The roster has no row for it --
# `addr32 loop` is the same form as `loop` with a 0x67 in front -- so the byte is
# removed before matching.  This is not a guess: the prefix is written in the
# vector's own assembly text, and only then is it stripped.
ADDR32 = "67"


def instance_text(rows, key, bank=0, immv=0, dispv=0, pad=0, held=False):
    """The text of one perturbation of the reading identified by `key` =
    (row, width, immediate class, addressing mode, suffix)."""
    i, w, cls, md, suf = key
    r = rows[i]
    imm = IMMS[cls][w][2 if held else immv]
    return synth(r, w, suf, imm=imm, bank=bank, mode=md, dispv=dispv, held=held)


def row_readings(rows):
    """Every (row, width, immediate class, addressing mode, spelling) candidate.

    ⚠️ AN ACCUMULATOR ROW IS SYNTHESISED WITH A WIDE IMMEDIATE ONLY.  Given
    `and $0x11, %rax` clang emits the generic ModRM encoding, not the short
    `0x25` one -- so a narrow immediate would give the `rax,imm` row the same
    encoding as the `r,imm` row and the two would stop being distinguishable.
    A generic row keeps BOTH classes, because both are genuinely its encodings.
    """
    out = []
    for idx, r in enumerate(rows):
        ws = list(r["widths"]) if r["widths"] != "-" else ["q", "l", "w", "b"]
        toks = [] if r["shape"] == "-" else r["shape"].split(",")
        acc = toks and toks[0] in ACCTOK
        nmodes = len(MODES) if "m" in toks else 1
        for w in ws:
            for cls in (["wide"] if acc else ["narrow", "wide"]):
                sufs = (True, False) if r["widths"] != "-" else (False, True)
                for md in range(nmodes):
                    for suf in sufs:
                        k = (idx, w, cls, md, suf)
                        t = instance_text(rows, k)
                        if t:
                            out.append(k)
    return out


def assemble(items, tag, pads=None):
    """Assemble `items` = [(key, text)], one label each; return {index: bytes}.

    `pads[j]` inserts that many `nop`s between instance `j` and its own NEAR
    target, which is how the branch-target perturbation moves a displacement
    without moving anything else.

    Lines clang refuses are dropped and returned as `dead`: a roster row with NO
    assemblable spelling is a finding about the roster, not a crash here.
    """
    tmp = tempfile.mkdtemp()
    alive = list(range(len(items)))
    dead = []
    for _ in range(8):
        src, line_of = ["\t.text"], {}
        for j in alive:
            src.append(f"{tag}{j}:\t{items[j][1].replace('NEAR', f'N{j}')}")
            line_of[len(src)] = j
            src += ["\tnop"] * (pads[j] if pads else 0)
            # ⛔ THE `nop` IS LOAD-BEARING.  Without it this label and the NEXT
            # instance's label share an address, and objdump prints only ONE
            # symbol per address -- which silently hid 4713 of 4714 encodings
            # and reported them as "rows with no assemblable form".  A lost
            # label must not be able to look like an answer, so this function
            # counts them and refuses rather than returning a short table.
            src.append(f"N{j}:\tnop")        # this instance's own rel8 target
        src += [".fill 200, 1, 0x90", "Lfar:", "\tnop"]
        p = os.path.join(tmp, "a.s")
        open(p, "w").write("\n".join(src) + "\n")
        q = subprocess.run(
            f"clang -target x86_64-unknown-linux-gnu -c {p} -o {tmp}/a.o",
            shell=True, capture_output=True, text=True)
        if q.returncode == 0:
            break
        bad = set()
        for m in re.finditer(r'a\.s:(\d+):\d+: error', q.stderr):
            if int(m.group(1)) in line_of:
                bad.add(line_of[int(m.group(1))])
        if not bad:
            print("⛔ clang failed with no attributable line:\n" + q.stderr[:2000])
            sys.exit(2)
        dead += sorted(bad)
        alive = [j for j in alive if j not in bad]
    else:
        print("⛔ assembly did not converge"); sys.exit(2)

    d = subprocess.run(f"objdump -d {tmp}/a.o", shell=True,
                       capture_output=True, text=True)
    if d.returncode != 0:
        print("⛔ objdump failed:\n" + d.stderr[:2000]); sys.exit(2)
    # ⭐ ONE PARSER FOR BOTH DISASSEMBLERS, and it is the one with the tests.
    # `parse_objdump` folds GNU objdump's wrapped continuation lines under an
    # ADDRESS-ARITHMETIC guard and carries its own always-on selftest over a GNU
    # sample, an LLVM sample and a sample that can only be read by the guard.
    labels, by_addr = parse_objdump(d.stdout)
    got, lost = {}, []
    for j in alive:
        lbl = f"{tag}{j}"
        if lbl in labels and labels[lbl] in by_addr:
            got[j] = "".join(by_addr[labels[lbl]])
        else:
            lost.append(j)
    if lost:
        print(f"⛔ {len(lost)} of {len(alive)} assembled instances have no "
              f"readable label in the disassembly (e.g. {items[lost[0]][1]!r}); "
              f"the encodings would be silently missing")
        sys.exit(2)
    return got, dead
# --------------------------------------------------------- the FORM SKELETON

# The seven perturbations of a reading, and the one held out to check them.
# (bank, immediate index, addressing-mode delta, pad)
PERTURB = [(0, 0, 0, 0),      # v0 -- the reading itself
           (1, 0, 0, 0),      # v1..v3 -- register banks spanning every bit of
           (2, 0, 0, 0),      #          every register field
           (3, 0, 0, 0),
           (0, 1, 0, 0),      # v4 -- the complementary immediate
           (0, 0, 1, 0),      # v5 -- the complementary memory displacement
           (0, 0, 0, 7)]      # v6 -- the branch target, seven bytes further


def skeleton(enc, is_branch, has_imm):
    """The bits of an encoding that do NOT depend on operand values.

    `enc[0]` is the reading; the rest are perturbations that move only operand
    VALUES.  A bit that changes under any of them is an operand bit; what
    survives is the form.

    ⭐ TWO FIELDS GET A TRAILING EXTENSION, and the reason is structural rather
    than empirical.  A relative DISPLACEMENT and an IMMEDIATE are the last field
    of an x86 encoding, so every byte from the first one that moves to the end of
    the instruction belongs to that field.  Without this a `rel32` whose high
    bytes never move -- because no perturbation can put a target 16MB away --
    would have those bytes read as opcode, and only branches to nearby targets
    would ever match.

    Returns (mask, skel), or None if a perturbation changed the LENGTH, which
    means it changed the form and the reading is void.
    """
    if len(set(len(e) for e in enc)) != 1:
        return None
    b = [bytes.fromhex(e) for e in enc]
    n = len(b[0])
    mask = bytearray(n)
    for k in range(1, len(b)):
        for i in range(n):
            mask[i] |= b[0][i] ^ b[k][i]
    if is_branch or has_imm:
        # the displacement perturbation is v6, the immediate's is v4
        for v in ((6,) if is_branch else ()) + ((4,) if has_imm else ()):
            if v >= len(b):
                continue
            moved = [i for i in range(n) if b[0][i] ^ b[v][i]]
            if moved:
                for i in range(moved[0], n):
                    mask[i] = 0xff
    return (bytes(mask), bytes(b[0][i] & ~mask[i] for i in range(n)))


def matches(byts, mask, skel):
    """Do these bytes belong to that form?"""
    v = bytes.fromhex(byts)
    if len(v) != len(skel):
        return False
    return all((v[i] & ~mask[i]) == skel[i] for i in range(len(v)))


# --------------------------------------------- SOURCE S: parse a vector's asm

PREFIXES = {"rep", "repe", "repne", "repnz", "repz"}
SUFFIXES = {"b", "w", "l", "q"}
ACCREG = {"%al": "al", "%ax": "ax", "%eax": "eax", "%rax": "rax"}


def split_ops(s):
    """Split AT&T operands on top-level commas -- `0x10(%rax,%rbx,4)` has its
    own."""
    out, cur, depth = [], "", 0
    for ch in s:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur.strip()); cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def op_tokens(o):
    """Every roster shape token an AT&T operand could be.  Deliberately
    GENEROUS: narrowing is the skeleton gate's job, not the parser's."""
    o = o.strip()
    if o.startswith("*"):
        o = o[1:]
    if o.startswith("$"):
        c = ["imm"]
        try:
            if int(o[1:], 0) == 1:
                c.append("one")
        except ValueError:
            pass
        return c
    if o.startswith("%"):
        c = ["r"]
        if o in ACCREG:
            c.append(ACCREG[o])
        if o == "%cl":
            c.append("cl")
        return c
    if "(" in o:
        return ["m"]
    if re.fullmatch(r'\.[+-]\d+', o) or re.fullmatch(r'[A-Za-z_.][A-Za-z0-9_.]*', o):
        return ["label", "rel8", "rel32"]
    return ["m"]


def base_parses(mnem, bases):
    """(base, width) readings of an AT&T mnemonic against the roster's own
    vocabulary, longest base first."""
    out = []
    for b in bases:
        if mnem == b:
            out.append((b, None))
        elif mnem.startswith(b) and mnem[len(b):] in SUFFIXES:
            out.append((b, mnem[len(b):]))
    if not out:                        # AT&T writes `call`/`ret` for `callq`/`retq`
        for b in bases:
            if b == mnem + "q":
                out.append((b, None))
    return out


def read_vectors(asm_path, len_path):
    lens = {}
    for line in open(len_path):
        p = line.split()
        if len(p) == 3:
            lens[p[0]] = (int(p[1]), p[2])
    vecs = []
    for line in open(asm_path):
        line = line.rstrip("\n")
        if "\t" not in line:
            continue
        vid, asm = line.split("\t", 1)
        vid = vid.rstrip(":")
        if not vid:
            continue
        ln, byts = lens.get(vid, (0, ""))
        vecs.append({"id": vid, "asm": asm, "bytes": byts, "len": ln})
    return vecs


def emit_vectors():
    # A PROBE MUST BE CHEAP OR IT DOES NOT GET RUN.  With these set, the vector
    # table is read from files instead of the built binary, so deleting a vector
    # and re-deriving the claim costs a second rather than a rebuild.
    if os.environ.get("X86LEAN_ASM") and os.environ.get("X86LEAN_LEN"):
        return read_vectors(os.environ["X86LEAN_ASM"], os.environ["X86LEAN_LEN"])
    tmp = tempfile.mkdtemp()
    a, l = os.path.join(tmp, "v.s"), os.path.join(tmp, "v.len")
    for mode, out in (("emit-asm", a), ("expected-lengths", l)):
        q = subprocess.run(f"lake env .lake/build/bin/x86lean-diff {mode} {out}",
                           shell=True, capture_output=True, text=True)
        if q.returncode != 0:
            print("⛔ could not emit the vector table (build it first):\n"
                  + q.stdout + q.stderr)
            sys.exit(2)
    return read_vectors(a, l)


# ----------------------------------------------------------------- the build

def build_forms(rows):
    """Every roster row's FORM SKELETONS, and the alias groups they induce."""
    cand = row_readings(rows)
    got, _ = assemble([(k, instance_text(rows, k)) for k in cand], "E")
    # Phase 1 only asks which SPELLING the assembler accepts; keep the first.
    chosen = {}
    for j in sorted(got):
        k = cand[j]
        chosen.setdefault(k[:4], k)

    # Phase 2: the same spelling under perturbations that move only operand
    # values, plus one held-out reading that must match what they derive.
    keys = sorted(chosen, key=lambda k: (k[0], k[1], k[2], k[3]))
    items, pads = [], []
    for k in keys:
        full = chosen[k]
        for (bank, immv, dispv, pad) in PERTURB:
            # ⚠️ THE ADDRESSING MODE IS HELD FIXED.  A perturbation may move a
            # displacement's VALUE but never the mode that carries it: changing
            # `(%rsi)` to `8(%rsi)` changes the LENGTH, which is a change of
            # form, and every memory row voided itself when this was got wrong.
            t = instance_text(rows, full, bank=bank, immv=immv, dispv=dispv)
            items.append((k, t)); pads.append(pad)
        t = instance_text(rows, full, held=True)
        items.append((k, t)); pads.append(3)
    got2, _ = assemble(items, "P", pads=pads)

    per = len(PERTURB) + 1
    forms = collections.defaultdict(list)
    canon = collections.defaultdict(set)
    voided = []
    for n, k in enumerate(keys):
        enc = [got2.get(per * n + v) for v in range(per)]
        toks = [] if rows[k[0]]["shape"] == "-" else rows[k[0]]["shape"].split(",")
        is_branch = any(t in ("label", "rel8", "rel32") for t in toks)
        has_imm = "imm" in toks
        if any(e is None for e in enc[:len(PERTURB)]):
            voided.append((k, "a perturbation did not assemble")); continue
        sk = skeleton(enc[:len(PERTURB)], is_branch, has_imm)
        if sk is None:
            voided.append((k, "a perturbation changed the LENGTH")); continue
        # ⭐ THE HELD-OUT CONTROL.  The mask above is only as good as the
        # perturbations that produced it, and an UNDER-covered mask does not
        # announce itself -- it silently freezes an operand bit into the form
        # and then refuses instances that differ in it.  So one reading, built
        # from registers, an immediate and a displacement that NO perturbation
        # used, must satisfy the skeleton.  If it does not, the reading is void
        # and said so, rather than quietly claiming less than it should.
        if enc[-1] is None:
            voided.append((k, "the held-out reading did not assemble")); continue
        if not matches(enc[-1], *sk):
            voided.append((k, "the held-out reading does not match the derived "
                              "skeleton -- the perturbations under-cover it"))
            continue
        forms[(k[0], k[1])].append(sk)
        canon[k[0]].add(enc[0])

    # ⭐ A CONTROL ON THE WIDTHS.  clang accepts an UNSUFFIXED spelling and
    # picks a default width for it, so a reading meant to be `btw` can quietly
    # come back as `btl` -- and then the row's `w` and `q` readings hold the `l`
    # encoding and every `w`/`q` vector of that row goes unresolved with nothing
    # to say why.  A row whose roster widths are distinct must have distinct
    # encodings at them; where it does not, the readings are void and named.
    for i, r in enumerate(rows):
        ws = list(r["widths"])
        if len(ws) < 2:
            continue
        seen = {}
        for w in ws:
            f = tuple(sorted(set(forms.get((i, w), ()))))
            if not f:
                continue
            if f in seen:
                voided.append(((i, w), f"its encoding is identical to width "
                                        f"{seen[f]}, so the width did not reach "
                                        f"the assembler"))
                forms.pop((i, w), None)
                forms.pop((i, seen[f]), None)
            else:
                seen[f] = w

    # Alias groups: rows whose form skeletons agree at every width.  clang, not
    # a hand-written synonym list, is what says `jz` and `je` are one form.
    sig = {}
    for i, r in enumerate(rows):
        ws = list(r["widths"]) if r["widths"] != "-" else ["q", "l", "w", "b"]
        key = tuple(tuple(sorted(set(forms.get((i, w), ())))) for w in ws)
        if any(k for k in key):
            sig[i] = (r["widths"], key)
    groups = collections.defaultdict(list)
    for i, k in sig.items():
        groups[k].append(i)
    group_of = {}
    for members in groups.values():
        for i in members:
            group_of[i] = tuple(sorted(members))
    return forms, group_of, voided, sig, canon


# ----------------------------------------------------- the published sentence

PUBLISHED_RE = re.compile(
    r"covering \*\*(\d+) of the (\d+) rows\*\*.*?"
    r"\*\*(\d+) of the (\d+) distinct machine forms\*\*.*?"
    r"(\d+) rows are alias SPELLINGS.*?"
    r"\*\*(\d+) are spelled by a vector\*\*", re.S)


# ⚠️ DECLINED IS A DECISION, NOT A MEASUREMENT, so it is declared here -- with
# the decision that made it, so a reader can check the reason and
# `check_citations.py` can check the reference exists.
#
# ⭐⭐ P2 ITEM 2 HOISTED THIS TO MODULE LEVEL, AND THE REASON IS A FALSE CLAIM IT
# WOULD HAVE PREVENTED.  `docs/P2-ROSTER.md` said the LOCK vocabulary would
# unblock "the six `bt`-family memory forms ... declined for want of it", making
# item 2 look three times more valuable in rows than it is.  THIS TABLE IS THE
# ANSWER: six rows are declined, and they carry TWO DIFFERENT DECISIONS — the two
# `xchg` rows for the implicit LOCK (D25), and the four `bt`-family rows for
# SIGNED BIT-STRING ADDRESSING (D23), which no LOCK vocabulary touches.
# `p2_roster.py` derives its sentence from here now instead of asserting one.
DECLINED = {("bt", "m,r"): "D23", ("bts", "m,r"): "D23",
            ("btr", "m,r"): "D23", ("btc", "m,r"): "D23"}

# The decision that blocks a row on ATOMICITY, i.e. the one a LOCK vocabulary
# answers.  Named rather than spelled at the use site, so the claim "this is
# what item 2 unblocks" is stated once.
LOCK_BLOCKED_DECISION = "D25"

# ⭐⭐ P2 ITEM 2 EMPTIED THE `D25` SIDE OF THAT TABLE, and the emptying is a claim
# that has to be gated or it is just a deletion.  `xchg m,r` and `xchg r,m` were
# declined for their implicit LOCK; `Ea.lock` is the vocabulary they lacked, and
# they are CLAIMED now.  This list is what makes "the addition unblocked them"
# checkable: `--check` requires every row here to be in the claimed set, so
# removing a row from DECLINED without actually modelling it fails LOUD instead
# of quietly shrinking the residue.
#
# ⚠️ The residue's total is unchanged in kind: six rows were declined, four are
# (D23's bit-string shape, which no LOCK vocabulary touches — D76).
LOCK_UNBLOCKED = {("xchg", "m,r"), ("xchg", "r,m")}


def residue_buckets(rows, claimed, noform):
    """The residue, partitioned. Called by BOTH `--remaining` (which prints
    it) and `--check` (which gates the README description against it), so the
    printed partition and the gated one cannot be two different derivations."""
    # ⭐⭐ P1 BATCH 21 -- THE RESIDUE'S THIRD BUCKET, AND WHY IT USED TO BE
    # WRONG.  This split was: no-encoding (DERIVED), oracle-unavailable
    # (a HARD-CODED set of nine mnemonics, DECLARED at batch 18), and
    # AVAILABLE WORK -- everything else, BY DEFAULT.
    #
    # ⇒ 🔑 A DECLARED LIST INHERITS THE DIRECTION OF ITS DEFAULT, and this
    # one's default is *available*, so every gap in it INVENTS work.  D61
    # measured `movnti` UNAVAILABLE at batch 20 and wrote the finding into
    # docs/DECISIONS.md and docs/COVERAGE.md and INTO NEITHER GATE -- so for
    # a whole batch the prose said the list had been corrected while this
    # function went on printing `movnti` under AVAILABLE WORK.
    # ⇒ 🔑 A CITATION IS AN UNGATED CLAIM.
    #
    # Both hand-maintained sets are now IMPORTED from the artifacts that own
    # them, and both are gated:
    #   * `scripts/oracle_availability.py` MEASURES the unavailable set by
    #     executing one form per mnemonic on the oracle over the real
    #     pre-states, with two positive controls, checked in BOTH directions
    #     and driven red first;
    #   * DECLINED names a recorded DECISION per row (a decision cannot be
    #     measured), and `check_citations.py` already requires the named
    #     decision to exist.
    # A row in neither, and still unclaimed, is AVAILABLE WORK -- and that
    # bucket is now empty, which is the statement worth gating.
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import importlib.util as _ilu
    _sp = _ilu.spec_from_loader("_oa", loader=None)
    _oa = {}
    _src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                             "oracle_availability.py")).read()
    _m = re.search(r"^FORMS = \[(.*?)^\]", _src, re.S | re.M)
    if not _m:
        print("⛔ could not read FORMS from scripts/oracle_availability.py. "
              "An unavailable-set this file GUESSED at is the defect D61 is "
              "about.")
        sys.exit(2)
    UNAVAILABLE = {mn for mn, exp in
                   re.findall(r'\(\s*"([^"]+)"\s*,\s*"[^"]*"\s*,\s*"[^"]*"\s*,\s*"(\w+)"\s*\)',
                              _m.group(1))
                   if exp == "refuses" and not mn.startswith("CONTROL")}
    unc = [i for i in range(len(rows)) if i not in set(claimed)]
    nof = [i for i in unc if i in noform]
    bmi = [i for i in unc if rows[i]["base"] in UNAVAILABLE and i not in nof]
    dec = [i for i in unc if (rows[i]["base"], rows[i]["shape"]) in DECLINED
           and i not in set(nof) | set(bmi)]
    work = [i for i in unc if i not in set(nof) | set(bmi) | set(dec)]
    return unc, nof, bmi, dec, work, DECLINED


def read_published(path="docs/COVERAGE.md"):
    """The six numbers the GENERATED coverage document publishes.

    ⚠️ This reads the document, not `Main.lean`, on purpose: the document is
    what a reader sees, and CI already fails if it is stale with respect to the
    generator.  A gate that read the generator's own source would be comparing
    the claim to itself.
    """
    try:
        text = open(path).read()
    except OSError:
        print(f"⛔ {path} is missing; nothing to check the derivation against")
        sys.exit(2)
    m = PUBLISHED_RE.search(text)
    if not m:
        print(f"⛔ {path} does not carry the six coverage numbers in the "
              f"expected form; the gate cannot read what it is meant to check")
        sys.exit(2)
    return tuple(int(g) for g in m.groups())


def selftest():
    """Drive this gate RED before believing it green.

    ⛔ THE POINT OF EACH ARM.  A gate is only evidence if it can be seen to
    fail, and this one has two independent halves that can each be silently
    broken: the RESOLVER (which vectors claim which rows) and the COMPARISON
    (whether the published numbers match).  So each half is broken alone, and
    each must go red on its own.
    """
    import shutil
    tmp = tempfile.mkdtemp()
    a, l = os.path.join(tmp, "v.s"), os.path.join(tmp, "v.len")
    for mode, out in (("emit-asm", a), ("expected-lengths", l)):
        q = subprocess.run(f"lake env .lake/build/bin/x86lean-diff {mode} {out}",
                           shell=True, capture_output=True, text=True)
        if q.returncode != 0:
            print("⛔ selftest cannot run: build the vector table first")
            sys.exit(2)

    def run(asm, lens, extra=""):
        env = dict(os.environ, X86LEAN_ASM=asm, X86LEAN_LEN=lens)
        return subprocess.run(
            f"python3 {os.path.abspath(__file__)} --quiet {extra}",
            shell=True, capture_output=True, text=True, env=env)

    arms, bad = [], []

    # ARM 0 -- the positive control.  Untouched, the gate must be GREEN; an arm
    # set that only ever goes red proves the gate is stuck, not that it works.
    r = run(a, l, "--check")
    arms.append(("control: the repository as it stands", r.returncode == 0, r))

    # ARM 1 -- break the RESOLVER: a vector whose bytes are no form at all.
    lines = open(l).read().splitlines()
    b1 = os.path.join(tmp, "b1.len")
    open(b1, "w").write("\n".join(
        [lines[0].rsplit(" ", 1)[0] + " 9090"] + lines[1:]) + "\n")
    r = run(a, b1)
    arms.append(("a vector whose bytes match no roster row", r.returncode != 0, r))

    # ARM 2 -- break the RESOLVER the other way: text and bytes disagree.
    src = open(a).read().replace("movl %ecx, %eax", "xorl %ecx, %eax", 1)
    b2 = os.path.join(tmp, "b2.s")
    open(b2, "w").write(src)
    r = run(b2, l)
    arms.append(("a vector whose text and bytes disagree", r.returncode != 0, r))

    # ARM 3 -- make a claim rest on the ABSTRACTION instead of on evidence.
    # `0x90` is both `nop` and `xchg eax,eax`; the roster carries both rows and
    # no byte-level rule separates them.  Normally `xchg eax,r` is supported by
    # its own vector (`xchg %ecx,%eax`, bytes `91`).  Delete that vector and the
    # row is left claimed ONLY through the colliding `90`, which is exactly the
    # condition the separation check exists to name.
    #
    # ⛔ THE ARM IS BUILT FROM DATA, NOT FROM A CODE HOOK, ON PURPOSE.  The first
    # version of it set an env var that made every mask total -- and that went
    # red by tripping the WIDTH control instead, i.e. for a reason other than
    # the one the arm was named after.  A red light in the wrong lamp is not a
    # test of this gate.
    sp_s, sp_l = os.path.join(tmp, "sp.s"), os.path.join(tmp, "sp.len")
    open(sp_s, "w").write("".join(
        ln for ln in open(a) if not ln.startswith("xchg_rr_l:")))
    open(sp_l, "w").write("".join(
        ln for ln in open(l) if not ln.startswith("xchg_rr_l ")))
    r = run(sp_s, sp_l)
    named = "claimed ONLY through an encoding" in (r.stdout + r.stderr)
    arms.append(("a row left claimed only through a colliding encoding",
                 r.returncode != 0 and named, r))

    # ARM 4/5 -- break the COMPARISON, in BOTH directions.  An over-claim and an
    # under-claim must both fail; the defect this tool was written for was an
    # under-claim, which is the direction nobody polices.
    doc = open("docs/COVERAGE.md").read()
    pub = read_published()
    for delta, name in ((+1, "an OVER-claim of one row"),
                        (-1, "an UNDER-claim of one row")):
        d = os.path.join(tmp, f"cov{delta}.md")
        open(d, "w").write(doc.replace(
            f"**{pub[0]} of the {pub[1]} rows**",
            f"**{pub[0] + delta} of the {pub[1]} rows**", 1))
        shutil.copy("docs/COVERAGE.md", os.path.join(tmp, "keep.md"))
        shutil.copy(d, "docs/COVERAGE.md")
        try:
            r = run(a, l, "--check")
        finally:
            shutil.copy(os.path.join(tmp, "keep.md"), "docs/COVERAGE.md")
        arms.append((f"the published number carries {name}",
                     r.returncode != 0, r))

    # ARM 6/7 -- P1 BATCH 20: the SIB-BASE EXEMPTION, broken in BOTH directions.
    # A hand-kept exclusion list is the classic place for a gate to go quietly
    # slack, so neither direction is left to a reader's care.
    #
    #  * DROP an id from the list and the vector it covered must come back as an
    #    unresolved finding -- i.e. the exemption is really suppressing
    #    something, and is not decoration over a resolver that never fired.
    #  * ADD an id that RESOLVES and the list must be reported STALE -- i.e. the
    #    day the skeleton grows to cover SIB bases, the exemption cannot sit
    #    there silently widening the gate.
    r = run(a, l, "--check")
    dropped = ",".join(sorted(SIB_BASE_EXEMPT)[1:])
    r6 = subprocess.run(
        f"python3 {os.path.abspath(__file__)} --quiet --check",
        shell=True, capture_output=True, text=True,
        env=dict(os.environ, X86LEAN_ASM=a, X86LEAN_LEN=l,
                 X86LEAN_SIB_EXEMPT_OVERRIDE=dropped))
    arms.append(("an exempted vector, un-exempted, is an unresolved finding",
                 r6.returncode != 0
                 and "resolve to NO roster row" in (r6.stdout + r6.stderr), r6))
    r7 = subprocess.run(
        f"python3 {os.path.abspath(__file__)} --quiet --check",
        shell=True, capture_output=True, text=True,
        env=dict(os.environ, X86LEAN_ASM=a, X86LEAN_LEN=l,
                 X86LEAN_SIB_EXEMPT_OVERRIDE=",".join(
                     sorted(SIB_BASE_EXEMPT) + ["mov_d"])))
    arms.append(("an exemption for a vector that RESOLVES is reported stale",
                 r7.returncode != 0
                 and "exemption is stale" in (r7.stdout + r7.stderr), r7))

    # ⭐⭐ ARMS 8-12 -- THE README'S READER DESCRIPTION.  P1 batch 21 landed the
    # description the Captain asked for at the top of README.md, and it states
    # the residue in prose: "27 of 525", "19 ... 2 ... 6 ... 0 rows of available
    # work", "84 mnemonics in 776 ... forms". Every one is a number this script
    # DERIVES, and the pairing of a prose number with a script that derives it
    # is exactly what was ELEVEN LOW for eighteen batches (D56).
    #
    # ⛔ THE ZERO IS THE ARM THAT MATTERS. "0 rows of available work" is the
    # strongest sentence in the document and the one that silently becomes false
    # the day the roster grows -- an over-claim that reads as a milestone.
    #
    # ⚠️ AND A DELETED PARAGRAPH IS ITS OWN ARM, because a gate that reads a
    # number cannot tell "the number is right" from "the sentence is gone".
    rd_saved = open("README.md").read()

    def _num_anchor(txt, pat):
        """The shipped phrase matching `pat` (one capture group: the number),
        read rather than typed.  Empty when the sentence is gone, so the arm
        reports ANCHOR MISSING instead of silently matching."""
        m = re.search(pat, txt)
        return m.group(0) if m else ""

    def _num_perturbed(txt, pat):
        m = re.search(pat, txt)
        if not m:
            return ""
        return m.group(0).replace(m.group(1), str(int(m.group(1)) + 1), 1)

    def _mnem_anchor(txt):
        """The shipped `N mnemonics in M differentially tested forms` phrase,
        read rather than typed.  An empty string when the sentence is gone, so
        the arm reports ANCHOR MISSING instead of silently matching."""
        m = re.search(r'(\d+) mnemonics in (\d+)', txt)
        return m.group(0) if m else ""

    def _mnem_perturbed(txt):
        m = re.search(r'(\d+) mnemonics in (\d+)', txt)
        return f"{int(m.group(1)) - 1} mnemonics in {m.group(2)}" if m else ""

    plants = [
        ("the description's AVAILABLE-WORK zero, made one",
         "- 0 rows of available work", "- 1 rows of available work", None),
        # ⛔⛔ THESE TWO WERE LITERALS AS WELL, AND P2 BATCH 23 FOUND THEM THE
        # SAME WAY D74 FOUND THE THIRD: the batch moved the numbers (6 declined
        # rows -> 4, a residue of 27 -> 25) and both arms reported ANCHOR
        # MISSING.  D74 derived ONE plant and left its two neighbours alone —
        # which is the shape of an incomplete repair: the defect was named, the
        # instance was fixed, and the identical instances beside it were not
        # looked for.  ⇒ EVERY plant in this table is derived from the shipped
        # sentence now, so the table has no literal left to go stale.
        ("the description's DECLINED count, off by one",
         _num_anchor(rd_saved, r'- (\d+) rows declined on record'),
         _num_perturbed(rd_saved, r'- (\d+) rows declined on record'), None),
        ("the description's RESIDUE total, off by one",
         _num_anchor(rd_saved, r'reason\*\* — (\d+) of 525'),
         _num_perturbed(rd_saved, r'reason\*\* — (\d+) of 525'), None),
        # ⛔⛔ THIS PLANT IS DERIVED FROM THE README, AND IT USED TO BE THE
        # LITERAL `"84 mnemonics in 776"`.  P2 batch 1 took the form count from
        # 776 to 784 and this arm reported ANCHOR MISSING — the selftest of the
        # gate whose whole purpose is to stop a hand-maintained number going
        # stale had a hand-maintained number in it, and it went stale on the
        # first batch that moved the figure.  ⇒ A GATE IS NOT EXEMPT FROM THE
        # DEFECT IT POLICES, and the exemption is usually granted by nobody
        # having looked at the gate's own body.  The plant now reads the shipped
        # sentence and perturbs the count it finds there, so it cannot go stale
        # again; a README that stops carrying the sentence still reports ANCHOR
        # MISSING, which is the honest answer.
        ("the description's MNEMONIC count, off by one",
         _mnem_anchor(rd_saved), _mnem_perturbed(rd_saved), None),
        ("the description's residue paragraph, DELETED",
         "- 0 rows of available work", "", "does not state"),
    ]
    try:
        for name, a_, b_, want in plants:
            if a_ not in rd_saved:
                arms.append((name + " [ANCHOR MISSING]", False,
                             subprocess.CompletedProcess([], 0, "", "")))
                continue
            open("README.md", "w").write(rd_saved.replace(a_, b_, 1))
            r = run(a, l, "--check")
            out = r.stdout + r.stderr
            ok = r.returncode != 0 and (
                ("README.md's description" in out) if want is None
                else (want in out))
            arms.append((name, ok, r))
    finally:
        open("README.md", "w").write(rd_saved)

    for name, ok, r in arms:
        print(("  ✔ " if ok else "  ⛔ ") + name)
        if not ok:
            bad.append(name)
            print("      " + (r.stdout + r.stderr).strip()[:400].replace(
                "\n", "\n      "))
    if bad:
        print(f"claimed-forms selftest: FAIL ({len(bad)} of {len(arms)} arms)")
        return 1
    print(f"claimed-forms selftest: PASS ({len(arms)} arms, "
          f"control + resolver x2 + separation + comparison in both "
          f"directions + the SIB-base exemption in both directions)")
    return 0



def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", help="write the derived table here")
    ap.add_argument("--expect", type=int,
                    help="the row count the coverage table publishes; "
                         "disagreement is a finding")
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--aliases", action="store_true",
                    help="print every alias group with the evidence")
    ap.add_argument("--remaining", action="store_true",
                    help="print the unclaimed rows, grouped, as a scope for the "
                         "next batch")
    ap.add_argument("--check", action="store_true",
                    help="gate the numbers PUBLISHED in docs/COVERAGE.md "
                         "against the derivation")
    ap.add_argument("--selftest", action="store_true",
                    help="drive the gate RED in both directions before "
                         "believing it green")
    args = ap.parse_args()
    if args.selftest:
        return selftest()

    rows = load_roster()
    bases = sorted({r["base"] for r in rows}, key=len, reverse=True)
    forms, group_of, voided, sig, canon = build_forms(rows)
    byrow = {}
    for i, r in enumerate(rows):
        byrow.setdefault((r["prefix"], r["base"], r["shape"]), []).append(i)

    vecs = emit_vectors()

    direct = collections.defaultdict(list)    # row -> vector ids that SPELL it
    unresolved, split = [], []
    for v in vecs:
        words = v["asm"].split(None, 1)
        prefix = ""
        vbytes = v["bytes"]
        if words[0] == "addr32":
            words = words[1].split(None, 1)
            if vbytes[:2] == ADDR32:
                vbytes = vbytes[2:]
                v["nopfx"] = vbytes
        if words[0] in PREFIXES:
            prefix = words[0]
            words = words[1].split(None, 1) if len(words) > 1 else [""]
        mnem = words[0]
        ops = split_ops(words[1]) if len(words) > 1 else []

        cands = set()
        for base, width in base_parses(mnem, bases):
            tokss = [op_tokens(o) for o in ops]
            # AT&T leaves the implicit 1 of a shift-by-one form unwritten.
            variants = [tokss] + ([[["one"]] + tokss] if len(ops) == 1 else [])
            for tk in variants:
                combos = [[]]
                for ts in tk:
                    combos = [c + [t] for c in combos for t in ts]
                for combo in combos:
                    shape = ",".join(reversed(combo)) if combo else "-"
                    for i in byrow.get((prefix, base, shape), []):
                        ws = ([width] if width else
                              (list(rows[i]["widths"]) if rows[i]["widths"] != "-"
                               else ["q", "l", "w", "b"]))
                        for w in ws:
                            # ⭐ THE GATE.  The parse only proposes; the row's own
                            # form skeleton disposes.  A mis-parse offers an
                            # encoding the assembler never produced for this
                            # vector, and dies here.
                            if any(matches(vbytes, m, s)
                                   for (m, s) in forms.get((i, w), ())):
                                cands.add(i)
        if not cands:
            unresolved.append(v); continue
        gs = {group_of.get(i, (i,)) for i in cands}
        if len(gs) > 1:
            split.append((v, sorted(cands))); continue
        for i in cands:
            direct[i].append(v["id"])

    # ⭐ THE CLAIM: a row is claimed iff some vector's bytes ARE an instance of
    # one of that row's own encodings.  No spelling is consulted, because the
    # model decodes bytes and not spellings -- which is what makes a vector
    # written `je` a test of the `jz` row.
    #
    # ⛔ THIS REPLACED AN ALIAS-GROUP RULE THAT UNDER-CLAIMED BY ONE.  The first
    # version grouped rows whose skeletons agreed AT EVERY WIDTH and required
    # their roster `widths` to be equal, so `stos m` (widths `bw`) never joined
    # `stos -` (widths `blqw`) even though `stos m` at byte width IS the byte
    # `0xaa` that vector `stos_b` assembles to.  ⇒ Caught by cross-checking the
    # two rules against each other, in a batch whose whole subject is an
    # under-claim nothing was reading. A rule that is CONSERVATIVE is still
    # wrong, and it is wrong in the direction that does not announce itself.
    claimed_of = collections.defaultdict(list)
    for v in vecs:
        for cand in (v["bytes"], v.get("nopfx")):
            if not cand:
                continue
            for (i, w), fs in forms.items():
                if any(matches(cand, m, sk) for (m, sk) in fs):
                    claimed_of[i].append(v["id"])
    claimed = sorted(claimed_of)

    # ⭐ AND THE PARSE IS THE CHECK ON IT.  Source S identified, independently of
    # the byte match, which row each vector spells.  Two things must hold, and
    # both are gated: every row the parse identifies must also be claimed by the
    # bytes; and every row claimed by the bytes that the parse did NOT identify
    # must share an encoding with one it did -- otherwise the skeleton has
    # over-masked and is matching rows that are not the same instruction.
    parsed = sorted(direct)
    unexplained_claim = []
    parsed_skels = set()
    for i in parsed:
        for w in (list(rows[i]["widths"]) if rows[i]["widths"] != "-"
                  else ["q", "l", "w", "b"]):
            parsed_skels |= set(forms.get((i, w), ()))
    for i in claimed:
        if i in direct:
            continue
        mine = set()
        for w in (list(rows[i]["widths"]) if rows[i]["widths"] != "-"
                  else ["q", "l", "w", "b"]):
            mine |= set(forms.get((i, w), ()))
        if not (mine & parsed_skels):
            unexplained_claim.append(i)

    alias_only = [i for i in claimed if i not in direct]

    _sk_cache = {}

    def related(i, j):
        """Do these two rows describe the same instruction?

        ⚠️ NOT EQUALITY OF ENCODING SETS.  K's grammar writes some rows as a
        RESTRICTION of another: `cmp m,label` is `cmp m,imm` with a symbolic
        immediate and only the `q` width, `stos m` is `stos -` at `b` and `w`.
        Its encodings are a strict SUBSET, not a different instruction -- and
        requiring equality here is the same mistake that made the first claim
        rule miss `stos m` entirely.
        """
        a, b = skels_of_cache(i), skels_of_cache(j)
        return bool(a) and bool(b) and (a <= b or b <= a)

    def skels_of_cache(i):
        if i not in _sk_cache:
            ws = (list(rows[i]["widths"]) if rows[i]["widths"] != "-"
                  else ["q", "l", "w", "b"])
            out = set()
            for w in ws:
                out |= set(forms.get((i, w), ()))
            _sk_cache[i] = frozenset(out)
        return _sk_cache[i]

    # ⭐ THE SEPARATION CHECK — the one that catches an OVER-masked skeleton.
    #
    # ⛔ THE GATE ABOVE CANNOT DO IT, and finding that out is why this exists.
    # "Every byte-claimed row shares an encoding with a parse-identified row"
    # passes trivially when a skeleton masks so much that two DIFFERENT rows
    # collide: the wrongly-claimed row then shares its (wrong) encoding with the
    # parsed one, and the gate applauds. Under-masking announces itself -- the
    # held-out reading stops matching -- but over-masking is silent, because
    # matching MORE never makes anything fail.
    #
    # So: a row's skeleton may not match a canonical instance of a row it is not
    # an alias of. Two rows are aliases exactly when their encoding sets agree;
    # anything else the skeleton swallows is a form distinction it has lost.
    by_len = collections.defaultdict(list)
    for i, encs in canon.items():
        for e in encs:
            by_len[len(e)].append((i, e))
    collisions = []
    for (i, w), fs in forms.items():
        for (m, sk) in fs:
            for (j, e) in by_len.get(len(sk) * 2, ()):
                if j == i or related(i, j):
                    continue
                if matches(e, m, sk):
                    collisions.append((i, j, e))
                    break
            else:
                continue
            break

    # ⚠️ A COLLISION IS NOT AUTOMATICALLY A WRONG CLAIM, and the difference is
    # worth keeping: `0x90` genuinely IS both `nop` and `xchg eax,eax`, and the
    # SDM defines that byte as NOP precisely so that it does NOT zero-extend
    # RAX. The roster carries both rows and no byte-level rule can separate
    # them. So a collision is REPORTED; it becomes a FINDING only when the
    # claimed row has no vector supporting it other than the colliding
    # encoding -- which is the case where the claim really does rest on the
    # abstraction rather than on evidence.
    spurious = []
    for (i, j, e) in collisions:
        if i not in claimed_of:
            continue
        support = [vid for vid in claimed_of[i]
                   if next((v for v in vecs if v["id"] == vid), {}).get("bytes")
                   != e]
        if not support:
            spurious.append((i, j))

    # A "machine form" is a row's SET OF ENCODINGS, and rows sharing one are the
    # same instruction under different spellings.  Counting rows instead
    # double-counts every alias, which is exactly why eighteen batches of
    # base-name arithmetic could not partition this roster.
    #
    # ⚠️ THE RELATION IS NOT ALWAYS EQUALITY.  `stos m` (roster widths `bw`) has
    # a STRICT SUBSET of `stos -`'s encodings (`blqw`) -- one such pair in the
    # whole roster, and requiring equality is what made the first version of the
    # claim rule miss it.  Grouping is by equality; the claim above is not.
    def skels_of(i):
        ws = (list(rows[i]["widths"]) if rows[i]["widths"] != "-"
              else ["q", "l", "w", "b"])
        out = set()
        for w in ws:
            out |= set(forms.get((i, w), ()))
        return frozenset(out)

    # Group by CONTAINMENT: a row whose encodings are a subset of another's is
    # the same instruction described more narrowly, not a second one.
    live = [i for i in range(len(rows)) if skels_of(i)]
    parent = {i: i for i in live}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x

    for a in range(len(live)):
        for b in range(a + 1, len(live)):
            i, j = live[a], live[b]
            si, sj = skels_of(i), skels_of(j)
            if si <= sj or sj <= si:
                parent[find(i)] = find(j)
    groups = collections.defaultdict(list)
    for i in live:
        groups[find(i)].append(i)
    n_groups = len(groups)
    noform = [i for i in range(len(rows)) if not skels_of(i)]
    claimed_groups = len({find(i) for i in claimed if skels_of(i)})

    findings = []
    published = read_published() if args.check else None
    if published is not None:
        # ⭐ GATED IN BOTH DIRECTIONS, AND ON EVERY NUMBER.  A gate that read
        # only the claimed-row count would pass an under-claim in any of the
        # other five -- which is the exact shape of the defect that kept eleven
        # rows out of sight for eighteen batches.
        for name, got, want in (("claimed rows", len(claimed), published[0]),
                                ("roster rows", len(rows), published[1]),
                                ("claimed machine forms", claimed_groups,
                                 published[2]),
                                ("machine forms", n_groups, published[3]),
                                ("alias rows",
                                 len(rows) - n_groups - len(noform),
                                 published[4]),
                                ("rows spelled by a vector", len(direct),
                                 published[5])):
            if got != want:
                findings.append(f"docs/COVERAGE.md publishes {want} for "
                                f"'{name}'; the derivation gives {got}")

    # ⭐⭐ P1 BATCH 21 — THE README'S READER DESCRIPTION CARRIES THE RESIDUE, SO
    # THIS TOOL OWNS THOSE NUMBERS TOO.  The description the Captain asked for
    # states "27 of 525 ... 19 ... 2 ... 6 ... 0 rows of available work" in the
    # most-read file in the repository, and every one of those is a claim this
    # script DERIVES.  A number published in prose and derived in a script is
    # exactly the pairing that was ELEVEN LOW for eighteen batches (D56).
    #
    # ⚠️ Gated in BOTH directions like the six above, and the AVAILABLE-WORK
    # zero is gated with them: "0 rows of available work" is the strongest claim
    # in that paragraph and the one that silently becomes false the day the
    # roster grows.
    if args.check:
        unc_r, nof_r, bmi_r, dec_r, work_r, _dcl = residue_buckets(rows, claimed, noform)
        # ⚠️ THE MNEMONIC COUNT IS NOT DERIVABLE HERE, AND SAYING SO IS THE POINT.
        # This file knows the ROSTER's base names (184 of them over 525 rows);
        # the number the description states is how many mnemonics the MODEL
        # implements, which is `rosterSize` and lives in the AST. A first version
        # of this gate counted the roster's bases and reported 184 against the
        # README's 84 -- it would have been "fixed" by writing 184 into the
        # README, which is a gate teaching a document to lie.
        # ⇒ It is read from the GENERATED coverage document, which is emitted
        # from the model and which CI already fails on if it is stale.
        mm = re.search(r"Roster: (\d+) mnemonics in (\d+) differentially tested",
                       open("docs/COVERAGE.md").read())
        if not mm:
            print("⛔ docs/COVERAGE.md does not carry the 'Roster: N mnemonics in "
                  "M ... forms' line; the description's mnemonic count has no "
                  "source to be checked against")
            sys.exit(2)
        n_mnemonics, n_forms_cov = int(mm.group(1)), int(mm.group(2))
        try:
            rdme = open("README.md").read()
        except OSError:
            print("⛔ README.md is missing; the description's numbers cannot be "
                  "checked against the derivation")
            sys.exit(2)
        pats = [
            ("residual rows", r'\*\*Rows of the roster not modelled, with the reason\*\* — (\d+) of (\d+)',
             (len(unc_r), len(rows))),
            ("oracle-unavailable rows", r'\n\s*- (\d+) rows the oracle does not implement', (len(bmi_r),)),
            ("no-encoding rows", r'\n\s*- (\d+) rows that describe no encoding at all', (len(nof_r),)),
            ("declined rows", r'\n\s*- (\d+) rows declined on record', (len(dec_r),)),
            ("available work", r'\n\s*- (\d+) rows of available work', (len(work_r),)),
            ("mnemonics and forms", r'\*\*Instructions\.\*\* (\d+) mnemonics in (\d+) differentially tested',
             (n_mnemonics, n_forms_cov)),
            ("rows covered", r'covering\n?\s*(\d+) of the (\d+) rows of the P1 roster',
             (len(claimed), len(rows))),
            ("alias rows", r'and (\d+) of them are alias spellings', (len(rows) - n_groups - len(noform),)),
            ("differential cases", r'ACL2 x86isa on (\d+) generated cases', (None,)),
        ]
        for name, pat, want in pats:
            m = re.search(pat, rdme)
            if not m:
                findings.append(f"README.md's description does not state "
                                f"'{name}' in the form this gate reads; a number "
                                f"it cannot find is a number nothing checks")
                continue
            got = tuple(int(g) for g in m.groups())
            if want[0] is None:
                continue          # owned by check_readme_snapshot.py, not here
            if got != want:
                findings.append(f"README.md's description publishes {got} for "
                                f"'{name}'; the derivation gives {want}")

    exempt_ids = set(os.environ.get("X86LEAN_SIB_EXEMPT_OVERRIDE",
                                    ",".join(sorted(SIB_BASE_EXEMPT))).split(","))
    exempt_ids = {e for e in exempt_ids if e}
    unres_real = [v for v in unresolved if v["id"] not in exempt_ids]
    stale_exempt = sorted(exempt_ids - {v["id"] for v in unresolved}
                          - {v["id"] for v in vecs if False})
    stale_exempt = [e for e in stale_exempt if any(v["id"] == e for v in vecs)]
    # ⭐⭐ P2 ITEM 2: THE UNBLOCKED ROWS MUST ACTUALLY BE CLAIMED.  Taking a row
    # out of DECLINED shrinks the residue; without this, the shrink would be a
    # deletion nobody checked, and "the LOCK vocabulary unblocked `xchg` at
    # memory" would be prose in a document that derives everything else.
    claimed_pairs = {(rows[i]["base"], rows[i]["shape"]) for i in set(claimed)}
    lock_unclaimed = sorted(LOCK_UNBLOCKED - claimed_pairs)
    if lock_unclaimed:
        findings.append(
            f"{len(lock_unclaimed)} row(s) recorded as UNBLOCKED by the LOCK "
            f"vocabulary are not claimed: " +
            ", ".join(f"{b} {sh}" for b, sh in lock_unclaimed))
    still_declined = sorted(LOCK_UNBLOCKED & set(globals()['DECLINED']))
    if still_declined:
        findings.append(
            f"{len(still_declined)} row(s) are recorded as both DECLINED and "
            f"UNBLOCKED: " + ", ".join(f"{b} {sh}" for b, sh in still_declined))
    if unres_real:
        # ⛔⛔ IT NAMES THEM NOW, AND THE COUNT ALONE COST A DIAGNOSIS.  Every
        # other finding in this list names its subjects; this one printed a bare
        # `1 vector(s)` — and when master CI finally reached this gate (D104
        # cleared the step that had hidden it for 36 runs) the failure was a
        # LINUX-ONLY one, so the seat could not reproduce it and had nothing but
        # a number to go on.  ⇒ 🔑 A GATE THAT REFUSES MUST SAY WHAT IT SAW: a
        # remote red that names nothing turns into a local re-run that measures a
        # different machine.  The BYTES are printed beside the id because the
        # suspected cause is a byte-column parse, and a length that disagrees
        # with the vector's own is the whole evidence.
        findings.append(
            f"{len(unres_real)} vector(s) resolve to NO roster row: " +
            ", ".join(f"{v['id']} ({v['bytes']}, {len(v['bytes']) // 2} bytes)"
                      for v in sorted(unres_real, key=lambda v: v["id"])[:10]))
    if stale_exempt:
        findings.append(
            f"{len(stale_exempt)} claims-no-row vector(s) now RESOLVE, so the "
            f"exemption is stale: " + ", ".join(stale_exempt))
    if spurious:
        findings.append(
            f"{len(spurious)} row(s) are claimed ONLY through an encoding that "
            f"also belongs to a row they are not an alias of: " + ", ".join(
                f"{rows[i]['base']} {rows[i]['shape']} ~ {rows[j]['base']} "
                f"{rows[j]['shape']}" for i, j in spurious[:5]))
    if unexplained_claim:
        findings.append(
            f"{len(unexplained_claim)} row(s) matched by BYTES share no encoding "
            f"with any row the parse identified: " + ", ".join(
                f"{rows[i]['base']} {rows[i]['shape']}"
                for i in unexplained_claim[:6]))
    if split:
        findings.append(f"{len(split)} vector(s) resolve to rows that are NOT "
                        f"the same machine form")
    if args.expect is not None and args.expect != len(claimed):
        findings.append(f"the coverage table publishes {args.expect} rows; "
                        f"the vectors and the roster derive {len(claimed)}")

    if not args.quiet:
        print(f"roster rows                      {len(rows)}")
        print(f"  distinct machine forms         {n_groups}"
              f"   ({len(rows) - n_groups - len(noform)} rows are alias "
              f"spellings, {len(noform)} have no encoding at all)")
        print(f"  rows with NO assemblable form  {len(noform)}")
        print(f"  (row,width) readings voided    {len(voided)}")
        print(f"vectors                          {len(vecs)}")
        print(f"  unresolved                     {len(unresolved)}")
        print(f"  split across forms             {len(split)}")
        print(f"CLAIMED rows                     {len(claimed)} of {len(rows)}")
        print(f"  spelled by a vector            {len(direct)}")
        print(f"  same encoding as one that is   {len(alias_only)}")
        print(f"CLAIMED machine forms            {claimed_groups} of {n_groups}")
        for i in noform:
            print(f"  ⚠️  no assemblable form: {rows[i]['base']} {rows[i]['shape']}")
        for (i, j, e) in collisions:
            print(f"  ⚠️  byte-level collision (reported, not a mis-claim): "
                  f"{rows[i]['base']} {rows[i]['shape']} shares encoding {e} "
                  f"with {rows[j]['base']} {rows[j]['shape']}")
        for v in unresolved:
            tag = (f"exempt ({CLAIMS_NO_ROW.get(v['id'], 'no rule recorded')})"
                   if v["id"] in exempt_ids else "unresolved")
            mark = "  ⚠️  " if v["id"] in exempt_ids else "  ⛔ "
            print(f"{mark}{tag}: {v['id']:24s} {v['asm']:34s} {v['bytes']}")
        for v, c in split:
            print(f"  ⛔ split: {v['id']:22s} {v['asm']:30s} -> " +
                  ", ".join(f"{rows[i]['base']} {rows[i]['shape']}" for i in c))
        for k, why in voided:
            print(f"  ⚠️  voided {rows[k[0]]['base']} {rows[k[0]]['shape']} "
                  f"@{'/'.join(str(x) for x in k[1:])}: {why}")

    if args.remaining:
        unc, nof, bmi, dec, work, DECLINED = residue_buckets(rows, claimed, noform)
        print(f"\nREMAINING {len(unc)} of {len(rows)} rows")
        print(f"  NO ENCODING EXISTS (derived here)          {len(nof):3d}")
        for i in nof:
            print(f"      {rows[i]['base']} {rows[i]['shape']}")
        print(f"  oracle UNAVAILABLE (MEASURED, batch 21)    {len(bmi):3d}"
              f"   {' '.join(sorted({rows[i]['base'] for i in bmi}))}")
        print(f"      re-measure: scripts/oracle_availability.py "
              f"(gated both ways, red-first, ~6 s)")
        print(f"  DECLINED by a recorded decision            {len(dec):3d}")
        for i in dec:
            print(f"      {rows[i]['base']:11s} {rows[i]['shape']:12s} "
                  f"{DECLINED[(rows[i]['base'], rows[i]['shape'])]}")
        print(f"  AVAILABLE WORK                             {len(work):3d}")
        for b in sorted({rows[i]["base"] for i in work}):
            shapes = [f"{rows[i]['shape']}({rows[i]['widths']})"
                      for i in work if rows[i]["base"] == b]
            print(f"      {b:11s} {len(shapes):2d}  " + " · ".join(shapes))
        # ⭐ AND THE PARTITION IS CHECKED, because four buckets that do not sum
        # to the residue is the arithmetic the batch-20 handover got wrong in
        # three of its four terms and in its total.
        if len(nof) + len(bmi) + len(dec) + len(work) != len(unc):
            print("⛔ the residue's buckets do not partition it.")
            sys.exit(2)
        # ⚠️ A DECLINED ENTRY THAT NO LONGER NAMES A ROW is the mirror finding --
        # the roster changed under a hand-written list -- and it is reported
        # because a stale exemption is exactly how a claim goes unpoliced.
        live = {(rows[i]["base"], rows[i]["shape"]) for i in range(len(rows))}
        for k in sorted(DECLINED):
            if k not in live:
                findings.append(f"DECLINED names {k[0]} {k[1]}, which is no "
                                f"longer a roster row")
            elif k not in {(rows[i]["base"], rows[i]["shape"]) for i in unc}:
                findings.append(f"DECLINED names {k[0]} {k[1]}, which is now "
                                f"CLAIMED — the decline is stale ({DECLINED[k]})")

    if args.aliases:
        seen = set()
        print("\n--- alias groups (clang: identical form skeletons) ---")
        for i in range(len(rows)):
            g = group_of.get(i, (i,))
            if len(g) < 2 or g in seen:
                continue
            seen.add(g)
            hit = "✔" if any(x in direct for x in g) else " "
            print(f" {hit} " + " = ".join(
                f"{rows[x]['prefix'] + '/' if rows[x]['prefix'] else ''}"
                f"{rows[x]['base']} {rows[x]['shape']}" for x in g))

    if args.json:
        json.dump({"rows": rows, "claimed": claimed,
                   "direct": sorted(direct), "alias_only": alias_only,
                   "groups": [list(g) for g in
                              sorted({group_of.get(i, (i,)) for i in range(len(rows))})],
                   "noform": noform, "n_groups": n_groups,
                   "claimed_groups": claimed_groups,
                   "by_vector": {str(i): direct[i] for i in sorted(direct)}},
                  open(args.json, "w"), indent=1)

    for f in findings:
        print(f"⛔ {f}")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
