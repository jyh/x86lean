#!/usr/bin/env python3
"""THE PRIMITIVE CENSUS — which public, reference-carrying scalar primitives
execute ONLY instruction forms this model has differential evidence for.

WHAT THIS ANSWERS.  A task in a benchmark built on this model is a function
whose machine code must be reasoned about one instruction at a time, so a
function is a usable task only if EVERY instruction form it executes is one of
the forms the differential vectors test.  `demand_census.py` answers a
neighbouring question at MNEMONIC granularity over whole binaries; this tool
answers it at FORM granularity over named functions, because a mnemonic can be
covered while the form a function uses is not (the CRC-32 routine had four such
forms when it was first measured: `movl $imm,%r32`, `notl %r32`, a memory
operand with an index and no base, and a positive rip-relative displacement).

HOW.  Both sides go through ONE instrument, so neither is compared against a
restatement of the other:

  THE MODEL SIDE.  The vector table's own AT&T text (`x86lean-diff emit-asm`,
  the same table `claimed_forms.py` gates) is assembled by clang and
  disassembled by objdump.
  THE CANDIDATE SIDE.  Each candidate is compiled (C) or assembled (.S) by the
  same clang for the same target and disassembled by the same objdump.

  An instruction's FORM is its printed mnemonic (width suffix, condition code
  and prefixes included) and the CLASS of each operand: `imm`, a register
  class (`r8 r8h r16 r32 r64 xmm ymm …`), `m` for memory, `rel` for a branch
  target, `*` for an indirect one.  A candidate form is COVERED iff some vector
  has the identical form.

⚠️ ONE DIMENSION IS COLLAPSED, AND THE COLLAPSE IS CHECKED, NOT ASSUMED.  A
memory operand's ADDRESSING MODE (base · base+index·scale · index·scale with no
base · rip-relative · absolute · fs/gs-segment) is NOT part of the form,
because the model computes every effective address in ONE function
(`Ea.offset`, X86/Semantics.lean) that no instruction's semantics sees.  What
the collapse would hide is a mode no vector exercises at all, so every mode a
candidate uses is checked against the set of modes the vectors use, and a mode
outside that set is reported beside the verdict as NOT COVERED.  The strict
count (mode kept in the form) is printed as a second column so a reader who
does not accept the collapse can read the table without it.

⛔ WHAT THIS DOES NOT DECIDE, printed with every table:
  - that a covered function can be PROVED at an acceptable price — coverage is
    a precondition for a task, not a price (`kernel_cost.py` prices);
  - the DECODER: "these bytes are this instruction" is trusted to XED
    (TRUSTBASE.md), so an encoding difference that keeps the form (imm8 vs
    imm32, a REX byte) is not a coverage difference here;
  - a function's CALLS that leave its object: they are listed per candidate,
    and a candidate that calls out is marked, never counted as covered silently;
  - one compiler, one version, one target, one set of flags — printed in the
    output's header.  A different compiler emits different forms.

LANE.  Personal lane, public sources only.  The candidate sources are fetched
at the pinned commits below and never vendored; their code is COUNTED, never
copied, and nothing from them enters this repository.

Usage:  primitive_census.py --src DIR [--fetch] [--out docs/PRIMITIVE-CENSUS.md]
        primitive_census.py --selftest
"""
import os, re, sys, json, shutil, argparse, itertools, subprocess, collections

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# ── the pinned public sources (fetched, never vendored) ─────────────────────
REPOS = {
    "s2n-bignum": ("https://github.com/awslabs/s2n-bignum.git",
                   "4d1356a7470663c752660a59375dc3a9ef548428"),
    "hacl-star":  ("https://github.com/hacl-star/hacl-star.git",
                   "504c2987452f87fe44bce9b9f12e19d6e051761f"),
    "zlib":       ("https://github.com/madler/zlib.git",
                   "767c4c947852e143f582c85f14cf573411df1b35"),
    "xxHash":     ("https://github.com/Cyan4973/xxHash.git",
                   "680bf463fa1ca0461b9a7c2dab7556e1f54cf4cf"),
    "SipHash":    ("https://github.com/veorq/SipHash.git",
                   "32d067603b93b47828700880649198e0bfbbcffa"),
    "smhasher":   ("https://github.com/aappleby/smhasher.git",
                   "07bb4de10a63e8cc2e1724865454eba635742383"),
}

# The reference column says what a task's WITHHELD reference could be built
# from, and it is not uniform: a formally verified implementation exists for
# the HACL*, Vale and s2n-bignum rows; the checksum rows carry a published
# specification and test vectors, and NO machine-checked reference was found.
REF = {
    "s2n":  "s2n-bignum: HOL Light proof of this x86 code, hardware-validated model",
    "hacl": "HACL*: F*-verified C (this compiled object is NOT the verified artifact)",
    "vale": "Vale: F*-verified x64 assembly (this is the verified artifact)",
    "spec": "published spec + test vectors; NO machine-checked reference found",
    "poc":  "x86lean's own CRC-32 routine — the POSITIVE CONTROL",
}

# (id, family, ref, kind, path-in-src, symbols, extra-flags)
#   kind: "S" = assembled as-is · "c"/"cpp" = compiled · "inline" = the text is
#   `path` itself.  `symbols` are the entry points; their in-object callees and
#   tail-jump targets are followed and counted with them.
CRC_POC = """    .intel_syntax noprefix
    .text
    .globl _crc32_ieee
_crc32_ieee:
    mov   eax, 0xFFFFFFFF
    test  rsi, rsi
    je    .Ldone
.Lloop:
    movzx ecx, byte ptr [rdi]
    xor   cl, al
    shr   eax, 8
    xor   eax, dword ptr [rcx*4 + 0x3000]
    inc   rdi
    dec   rsi
    jne   .Lloop
.Ldone:
    not   eax
    ret
"""
S2N = "s2n-bignum/x86/"
HS = "hacl-star/dist/gcc-compatible/"
VALE = "hacl-star/dist/vale/"
CANDIDATES = [
    ("crc32-poc", "checksum", "poc", "inline", CRC_POC, ["crc32_ieee"], []),
    ("zlib-crc32", "checksum", "spec", "c", "zlib/crc32.c", ["crc32_z"], []),
    ("zlib-adler32", "checksum", "spec", "c", "zlib/adler32.c", ["adler32_z"], []),
    ("xxh32", "hash (non-crypto)", "spec", "c", "xxHash/xxhash.c", ["XXH32"], ["-DXXH_VECTOR=0"]),
    ("xxh64", "hash (non-crypto)", "spec", "c", "xxHash/xxhash.c", ["XXH64"], ["-DXXH_VECTOR=0"]),
    ("xxh3-64", "hash (non-crypto)", "spec", "c", "xxHash/xxhash.c", ["XXH3_64bits"], ["-DXXH_VECTOR=0"]),
    ("murmur3-x86-32", "hash (non-crypto)", "spec", "cpp", "smhasher/src/MurmurHash3.cpp", ["__Z18MurmurHash3_x86_32PKvijPv"], []),
    ("murmur3-x64-128", "hash (non-crypto)", "spec", "cpp", "smhasher/src/MurmurHash3.cpp", ["__Z19MurmurHash3_x64_128PKvijPv"], []),
    ("lookup3", "hash (non-crypto)", "spec", "cpp", "smhasher/src/lookup3.cpp", ["__Z7lookup3PKvij"], []),
    ("siphash-2-4", "hash (keyed)", "spec", "c", "SipHash/siphash.c", ["siphash"], []),
    ("halfsiphash", "hash (keyed)", "spec", "c", "SipHash/halfsiphash.c", ["halfsiphash"], []),
    ("hacl-sha256", "hash compression", "hacl", "c", HS + "Hacl_Hash_SHA2.c", ["Hacl_Hash_SHA2_update_256"], []),
    ("hacl-sha512", "hash compression", "hacl", "c", HS + "Hacl_Hash_SHA2.c", ["Hacl_Hash_SHA2_update_512"], []),
    ("hacl-sha1", "hash compression", "hacl", "c", HS + "Hacl_Hash_SHA1.c", ["Hacl_Hash_SHA1_update"], []),
    ("hacl-md5", "hash compression", "hacl", "c", HS + "Hacl_Hash_MD5.c", ["Hacl_Hash_MD5_update"], []),
    ("hacl-sha3", "hash compression", "hacl", "c", HS + "Hacl_Hash_SHA3.c", ["Hacl_Hash_SHA3_update_multi_sha3"], []),
    ("hacl-blake2s", "hash compression", "hacl", "c", HS + "Hacl_Hash_Blake2s.c", ["Hacl_Hash_Blake2s_update_multi"], []),
    ("hacl-blake2b", "hash compression", "hacl", "c", HS + "Hacl_Hash_Blake2b.c", ["Hacl_Hash_Blake2b_update_multi"], []),
    ("hacl-chacha20", "stream cipher", "hacl", "c", HS + "Hacl_Chacha20.c", ["Hacl_Chacha20_chacha20_encrypt"], []),
    ("hacl-salsa20", "stream cipher", "hacl", "c", HS + "Hacl_Salsa20.c", ["Hacl_Salsa20_salsa20_encrypt"], []),
    ("hacl-poly1305", "MAC", "hacl", "c", HS + "Hacl_MAC_Poly1305.c", ["Hacl_MAC_Poly1305_update"], []),
    ("vale-poly1305", "MAC", "vale", "S", VALE + "poly1305-x86_64-darwin.S", ["x64_poly1305"], []),
    ("vale-fadd", "field arithmetic", "vale", "S", VALE + "curve25519-x86_64-darwin.S", ["fadd_e"], []),
    ("vale-fsub", "field arithmetic", "vale", "S", VALE + "curve25519-x86_64-darwin.S", ["fsub_e"], []),
    ("vale-fmul", "field arithmetic", "vale", "S", VALE + "curve25519-x86_64-darwin.S", ["fmul_e"], []),
    ("vale-cswap2", "field arithmetic", "vale", "S", VALE + "curve25519-x86_64-darwin.S", ["cswap2_e"], []),
    ("vale-sha256", "hash compression", "vale", "S", VALE + "sha256-x86_64-darwin.S", ["sha256_update"], []),
    ("vale-aesgcm", "AEAD", "vale", "S", VALE + "aesgcm-x86_64-darwin.S", ["gcm128_encrypt_opt"], []),
]
S2N_PICK = [
    ("generic", ["bignum_add", "bignum_sub", "bignum_cmadd", "bignum_mul", "bignum_sqr",
                 "bignum_montmul", "bignum_mux", "bignum_eq", "bignum_ctz", "bignum_bitsize",
                 "word_clz", "word_popcount", "word_bytereverse", "bignum_shl_small",
                 "bignum_cmul", "bignum_modadd", "bignum_demont", "word_negmodinv"]),
    ("p256", ["bignum_add_p256", "bignum_neg_p256", "bignum_mod_n256_alt",
              "bignum_montmul_p256_alt", "bignum_montmul_p256"]),
    ("curve25519", ["bignum_add_p25519", "bignum_mul_p25519_alt", "bignum_mul_p25519"]),
    ("fastmul", ["bignum_mul_4_8_alt", "bignum_sqr_4_8_alt", "bignum_mul_4_8"]),
]
for sub, names in S2N_PICK:
    for n in names:
        CANDIDATES.append(("s2n-" + n, "bignum limb", "s2n", "S",
                           S2N + sub + "/" + n + ".S", [n], []))

# NOT MEASURED, and said so rather than silently left out of the population.
NOT_MEASURED = [
    ("libjade (Jasmin)", "the repository ships `.jazz` sources and no generated "
     "assembly, and `jasminc` is not on this box; its amd64/ref primitives "
     "(ChaCha20, Poly1305, SHA-256, Keccak, X25519) are the next rows to add"),
]

TARGET = "x86_64-apple-macos13"
CFLAGS = ["-O2", "-fno-stack-protector", "-fcf-protection=none",
          "-fno-asynchronous-unwind-tables", "-fno-jump-tables", "-DNDEBUG", "-w"]
# ⛔ `-fno-jump-tables` IS NOT A PREFERENCE.  On this target clang places a
# switch's jump table INSIDE `__text`, and objdump decodes the table as code:
# the first run of this census reported `lcalll *m`, `enter imm,imm`, `xlatb`
# and `<unknown>` as forms MurmurHash3 and SipHash execute.  They execute none
# of them.  Without tables the switch is a compare chain, which is code the
# function really runs.  And `<unknown>` anywhere still refuses the row.
# `-DNDEBUG` removes `assert`'s call out of the object.  s2n-bignum is built
# with its own `-DNO_IBT` option, which drops the `endbr64` at each entry (a
# hint NOP on every pre-CET processor, its header says).
# The second configuration a C candidate is compiled under, because the first
# lets clang auto-vectorise into SSE and a task author can forbid that.
SCALAR = ["-fno-vectorize", "-fno-slp-vectorize"]

# ── operand classes ─────────────────────────────────────────────────────────
GPR = {}
for i, n in enumerate("ax bx cx dx si di bp sp".split()):
    GPR["r" + n] = "r64"; GPR["e" + n] = "r32"; GPR[n] = "r16"
for n in "al bl cl dl sil dil bpl spl".split():
    GPR[n] = "r8"
for n in "ah bh ch dh".split():
    GPR[n] = "r8h"
for k in range(8, 16):
    GPR[f"r{k}"] = "r64"; GPR[f"r{k}d"] = "r32"
    GPR[f"r{k}w"] = "r16"; GPR[f"r{k}b"] = "r8"
SREG = {"es", "cs", "ss", "ds", "fs", "gs"}
PREFIX = {"lock", "rep", "repe", "repne", "repz", "repnz", "notrack", "data16"}
BRANCHY = re.compile(r'^(j[a-z]+|call[a-z]?|loop[a-z]*|jmp[a-z]?)$')


def split_ops(s):
    out, cur, depth = [], "", 0
    for ch in s:
        depth += (ch == "(") - (ch == ")")
        if ch == "," and depth == 0:
            out.append(cur.strip()); cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def reg_class(r):
    r = r.lstrip("%")
    if r in GPR:
        return GPR[r]
    for pre, cls in (("xmm", "xmm"), ("ymm", "ymm"), ("zmm", "zmm"), ("mm", "mmx"),
                     ("st", "x87"), ("k", "kmask"), ("cr", "creg"), ("dr", "dreg")):
        if r.startswith(pre) and r[len(pre):].strip("()").isdigit():
            return cls
    if r == "st":
        return "x87"
    if r in SREG:
        return "sreg"
    if r == "rip":
        return "rip"
    return "reg?" + r


def mem_mode(o):
    """The addressing mode of a memory operand, from its printed text."""
    seg = ""
    m = re.match(r'^%([a-z]s):(.*)$', o)
    if m:
        seg, o = m.group(1), m.group(2)
    if seg in ("fs", "gs"):
        pre = seg + ":"
    else:
        pre = ""                   # es/ds/cs/ss have no base in 64-bit mode
    if "(" not in o:
        return pre + "abs"
    inner = o[o.index("(") + 1:o.rindex(")")]
    parts = [p.strip() for p in inner.split(",")]
    base = parts[0] if parts else ""
    if base == "%rip":
        return pre + "rip"
    idx = len(parts) > 1 and parts[1] != ""
    if base and idx:
        return pre + "base+index"
    if base:
        return pre + "base"
    return pre + "index"


def form_of(text):
    """(form, modes) for one objdump instruction text, or None for padding.
    `form` is a hashable (mnemonic, operand classes); `modes` the addressing
    modes of its memory operands."""
    text = text.split("#", 1)[0].strip()
    if not text:
        return None
    toks = text.split(None, 1)
    mn, rest = toks[0], (toks[1] if len(toks) > 1 else "")
    pre = []
    while mn in PREFIX and rest:
        pre.append(mn)
        t2 = rest.split(None, 1)
        mn, rest = t2[0], (t2[1] if len(t2) > 1 else "")
    mnem = " ".join(pre + [mn])
    ops, modes = [], []
    branch = bool(BRANCHY.match(mn))
    for o in split_ops(rest):
        o = re.sub(r'\s*<[^>]*>$', '', o).strip()
        ind = o.startswith("*")
        if ind:
            o = o[1:]
        if o.startswith("$"):
            c = "imm"
        elif o.startswith("%") and ":" not in o and "(" not in o:
            c = reg_class(o)
        elif branch and not ind and re.fullmatch(r'(0x)?[0-9a-f]+', o):
            c = "rel"
        else:
            c = "m"
            modes.append(mem_mode(o))
        ops.append(("*" if ind else "") + c)
    return (mnem, tuple(ops)), tuple(modes)


def fmt_form(f):
    mn, ops = f
    return mn + (" " + ",".join(ops) if ops else "")


# ── the one instrument both sides go through ────────────────────────────────
LINE = re.compile(r'^\s*([0-9a-f]+):\s+(.*)$')
LABEL = re.compile(r'^([0-9a-f]+) <(.+)>:$')
RELOC = re.compile(r'^\s*([0-9a-f]+):?\s+X86_64_RELOC_\w+\s+(\S+)')
TARGET_SYM = re.compile(r'<([^>+]+)(\+0x[0-9a-f]+)?>\s*$')


def disassemble(obj):
    q = subprocess.run(["objdump", "-d", "-r", "--no-show-raw-insn", obj],
                       capture_output=True, text=True)
    if q.returncode != 0:
        raise RuntimeError("objdump failed on " + obj + ":\n" + q.stderr)
    funcs, cur = collections.OrderedDict(), None
    for line in q.stdout.splitlines():
        m = LABEL.match(line.strip())
        if m:
            cur = m.group(2)
            funcs[cur] = []
            continue
        if cur is None:
            continue
        r = RELOC.match(line)
        if r:
            if funcs[cur]:
                funcs[cur][-1]["reloc"] = r.group(2)
            continue
        m = LINE.match(line)
        if m and m.group(2).strip():
            funcs[cur].append({"addr": int(m.group(1), 16), "text": m.group(2).strip()})
    return funcs


def strip_us(s):
    return s[1:] if s.startswith("_") else s


ENDS = {"retq", "ret", "jmp", "jmpq", "ud2", "hlt"}


def closure(funcs, entries, fallthrough):
    """The entry functions plus every block in the SAME object they call,
    branch to, or FALL THROUGH into, transitively; and the calls that leave the
    object.

    ⛔ FALL-THROUGH IS NOT OPTIONAL.  On this target a local label such as
    `.Lloop:` is kept as a symbol, so objdump splits one routine into several
    blocks, and the loop body is entered by falling off the end of the block
    before it — no branch names it.  The first version of this walk followed
    branches only and counted the CRC-32 PoC at 5 of its 12 instructions: its
    `xorl 0x3000(,%rcx,4)` was never seen, and the census reported the PoC
    covered while blind to the one addressing mode S1 had to add a vector for.
    A mutant that deleted that vector is what showed it.

    ⚠️ AND IT IS FOR ASSEMBLY ONLY.  In a COMPILED object clang's own labels are
    temporaries (`LBB0_3`) and never reach the symbol table, so every block
    objdump prints IS a function, and falling off one (after a call that does
    not return) walks into an unrelated function: the fall-through walk applied
    to C counted XXH32 at 8,992 instructions."""
    names = {strip_us(k): k for k in funcs}
    order = list(funcs)
    todo = [names[e] if e in names else e for e in entries]
    seen, external = [], collections.Counter()
    while todo:
        f = todo.pop()
        if f in seen:
            continue
        seen.append(f)
        body = funcs[f]
        last = body[-1]["text"].split(None, 1)[0] if body else ""
        k = order.index(f)
        if fallthrough and last not in ENDS and k + 1 < len(order):
            todo.append(order[k + 1])
        for ins in body:
            mn = ins["text"].split(None, 1)[0]
            if not BRANCHY.match(mn):
                continue
            tgt = ins.get("reloc")
            if tgt is None:
                m = TARGET_SYM.search(ins["text"])
                tgt = m.group(1) if m else None
            if tgt is None or tgt == f or tgt.startswith("L") or tgt.startswith("ltmp"):
                continue
            if tgt in funcs:
                todo.append(tgt)
            elif strip_us(tgt) in names:
                todo.append(names[strip_us(tgt)])
            elif mn.startswith("call") or ins.get("reloc"):
                external[strip_us(tgt)] += 1
    return seen, external


def clang(args, cwd=None):
    q = subprocess.run(["clang", "-target", TARGET] + args,
                       capture_output=True, text=True, cwd=cwd)
    return q.returncode, q.stdout + q.stderr


# ── the model side ──────────────────────────────────────────────────────────
def model_forms(work):
    asm = os.environ.get("X86LEAN_ASM")
    if not asm:
        asm = os.path.join(work, "vectors.s")
        q = subprocess.run(["lake", "env", ".lake/build/bin/x86lean-diff",
                            "emit-asm", asm], cwd=ROOT, capture_output=True, text=True)
        if q.returncode != 0:
            print("⛔ could not emit the vector table (build x86lean-diff first):\n"
                  + q.stdout + q.stderr)
            sys.exit(2)
    obj = os.path.join(work, "vectors.o")
    rc, out = clang(["-c", asm, "-o", obj])
    if rc != 0:
        print("⛔ the vector table does not assemble:\n" + out)
        sys.exit(2)
    funcs = disassemble(obj)
    forms, strict, modes = collections.defaultdict(list), set(), set()
    nvec = 0
    for vid, ins in funcs.items():
        nvec += 1
        for i in ins:
            r = form_of(i["text"])
            if r is None:
                continue
            forms[r[0]].append(vid)
            strict.add((r[0], r[1]))
            modes.update(r[1])
    return nvec, forms, strict, modes


# ── the candidate side ──────────────────────────────────────────────────────
def build_candidate(c, src, work, scalar):
    cid, fam, ref, kind, path, syms, extra = c
    obj = os.path.join(work, cid + ("-scalar" if scalar else "") + ".o")
    if kind == "inline":
        s = os.path.join(work, cid + ".s")
        open(s, "w", encoding="utf-8").write(path)
        rc, out = clang(["-c", s, "-o", obj])
    elif kind == "S":
        inc = ["-I", os.path.join(src, "s2n-bignum", "include"), "-DNO_IBT"]
        rc, out = clang(["-c", os.path.join(src, path), "-o", obj] + inc)
    else:
        lang = ["-x", "c++", "-std=c++11"] if kind == "cpp" else ["-std=c11"]
        inc = ["-I", os.path.join(src, os.path.dirname(path))]
        if path.startswith("hacl-star"):
            inc += ["-I", os.path.join(src, "hacl-star/dist/karamel/include"),
                    "-I", os.path.join(src, "hacl-star/dist/karamel/krmllib/dist/minimal")]
        rc, out = clang(lang + CFLAGS + (SCALAR if scalar else []) + extra + inc
                        + ["-c", os.path.join(src, path), "-o", obj])
    if rc != 0:
        return {"error": "build failed: " + out.strip().splitlines()[-1][:200]
                if out.strip() else "build failed"}
    funcs = disassemble(obj)
    missing = [s for s in syms if s not in funcs and "_" + s not in funcs]
    if missing:
        return {"error": "entry symbol(s) not in the object: " + ", ".join(missing)}
    seen, external = closure(funcs, syms, kind in ("S", "inline"))
    # the haystack's size, beside the verdict: code in the object the walk
    # never reached (for a one-routine .S file this must be 0)
    unreached = sum(1 for f in funcs if f not in seen for i in funcs[f]
                    if i["text"].split(None, 1)[0] not in ("int3", "nop", "nopw", "nopl"))
    counts, modes, n, pad = collections.Counter(), collections.Counter(), 0, 0
    for f in seen:
        for i in funcs[f]:
            mn = i["text"].split(None, 1)[0]
            if mn == "int3":            # inter-function padding, never executed
                pad += 1
                continue
            if mn.startswith("<unknown>") or mn.startswith("(bad)"):
                return {"error": f"objdump decoded non-code in `{strip_us(f)}` "
                                 "(data in text?) — refused, not guessed"}
            r = form_of(i["text"])
            if r is None:
                continue
            n += 1
            counts[r[0]] += 1
            for md in r[1]:
                modes[md] += 1
    return {"funcs": [strip_us(f) for f in seen], "external": dict(external),
            "unreached": unreached,
            "n": n, "pad": pad, "forms": counts, "modes": modes}


# ISA-extension tags for the not-covered list, so a reader sees WHY a form is
# out of reach before reading the mnemonic.
EXT = [
    (re.compile(r'^(mulx|adcx|adox|rorx|sarx|shlx|shrx|andn|bextr|blsi|blsr|blsmsk|bzhi|pdep|pext)[lq]?$'), "BMI/ADX"),
    (re.compile(r'^(pinsr|pextr|pshufb|palignr|pmins|pmaxs|pminu|pmaxu|ptest|pblend|pmulld)'), "SSSE3/SSE4"),
    (re.compile(r'^(aes|pclmul)'), "AES-NI/CLMUL"),
    (re.compile(r'^sha(1|256)'), "SHA-NI"),
    (re.compile(r'^v'), "AVX/VEX"),
    (re.compile(r'^lock'), "lock (no memory ordering)"),
]


def ext_tag(form):
    mn, ops = form
    for rx, tag in EXT:
        if rx.match(mn):
            return tag
    if any(o.lstrip("*") in ("ymm", "zmm") for o in ops):
        return "AVX/VEX"
    return ""


WIDTH = re.compile(r'^(.*?)([bwlq])$')


def widthless(form):
    """The form with its width erased: the suffix off the mnemonic, the width
    off each register class.  Two forms that agree here differ ONLY in operand
    width."""
    mn, ops = form
    # a condition code is not a width: `jb`/`jl`, `setb`/`setl` stay apart
    m = None if (BRANCHY.match(mn) or mn.startswith("set")) else WIDTH.match(mn)
    base = m.group(1) if m else mn
    return base, tuple(re.sub(r'^(\*?)r(8h|8|16|32|64)$', r'\1r', o) for o in ops)


def score(res, forms, modes_ok, mnems):
    cov = {f: k for f, k in res["forms"].items() if f in forms}
    miss = {f: k for f, k in res["forms"].items() if f not in forms}
    badmodes = {m: k for m, k in res["modes"].items() if m not in modes_ok}
    wl = {widthless(f) for f in forms}
    res["sibling"] = {f for f in miss if widthless(f) in wl}
    res.update({"covered": cov, "missing": miss, "badmodes": badmodes,
                "all": not miss and not badmodes})
    return res


def needs(r):
    return frozenset(r["missing"]) | frozenset(("mode", m) for m in r["badmodes"])


def ladder(rows):
    """Greedy: at each step add the one form that completes the most rows (ties
    by how many rows need it).  Printed as a ladder so a reader sees the price
    of each next increment, not only one answer."""
    pool = [(r["id"], needs(r)) for r in rows]
    have, steps = frozenset(), []
    while True:
        left = [(i, n - have) for i, n in pool if n - have]
        if not left:
            break
        cand = collections.Counter(f for _, n in left for f in n)
        def gain(f):
            return (sum(1 for _, n in left if n == {f}), cand[f])
        f = max(cand, key=lambda f: (gain(f), str(f)))
        if gain(f)[0] == 0:
            # nothing completes with one form: take the cheapest whole row
            i, n = min(left, key=lambda t: (len(t[1]), t[0]))
            have |= n
            steps.append((sorted(n, key=str), [i]))
            continue
        have |= {f}
        done = [i for i, n in left if not (n - have)]
        steps.append(([f], done))
    return steps


def best_unlock(rows, k):
    """The smallest union of missing forms that fully covers k more rows.
    Exact when the search is small, greedy (and SAID SO) when it is not."""
    need = [(r["id"], needs(r)) for r in rows if not r["all"] and "error" not in r]
    need.sort(key=lambda t: len(t[1]))
    if len(need) <= k:
        u = frozenset().union(*[s for _, s in need]) if need else frozenset()
        return [i for i, _ in need], u, "all incomplete rows"
    from math import comb
    # prune: only the rows whose OWN need is small can be in a cheap answer
    cand = need[:22]
    if comb(len(cand), k) <= 800000:
        best = None
        for combo in itertools.combinations(cand, k):
            u = frozenset().union(*[s for _, s in combo])
            if best is None or len(u) < len(best[1]):
                best = ([i for i, _ in combo], u)
        return best[0], best[1], f"exact over the {len(cand)} rows with the smallest needs"
    chosen, u = [], frozenset()
    pool = list(need)
    while len(chosen) < k:
        pool.sort(key=lambda t: len(t[1] - u))
        i, s = pool.pop(0)
        chosen.append(i); u |= s
    return chosen, u, "GREEDY (not proved minimal)"


# ── report ──────────────────────────────────────────────────────────────────
SSE3 = {"movddup", "movshdup", "movsldup", "haddps", "haddpd", "hsubps", "hsubpd",
        "addsubps", "addsubpd", "lddqu", "fisttp"}


def simd_content(forms):
    """How many VECTORS touch each SIMD/FP class — derived from the vectors, so
    the README's scope line can point here instead of carrying a number."""
    cls = collections.defaultdict(set)
    for f, vids in forms.items():
        mn, ops = f
        o = {x.lstrip("*") for x in ops}
        tags = set()
        if "xmm" in o: tags.add("XMM operand")
        if "ymm" in o: tags.add("YMM operand")
        if "zmm" in o: tags.add("ZMM operand")
        if "x87" in o or mn.startswith("f"): tags.add("x87")
        if "mmx" in o: tags.add("MMX register")
        if mn.startswith("v") and o & {"xmm", "ymm", "zmm"}: tags.add("VEX/EVEX-encoded")
        if ext_tag(f) == "SSSE3/SSE4": tags.add("SSSE3/SSE4")
        if mn in SSE3: tags.add("SSE3")
        for t in tags:
            cls[t].update(vids)
    return {t: len(cls.get(t, ())) for t in ("XMM operand", "SSE3", "SSSE3/SSE4",
            "VEX/EVEX-encoded", "YMM operand", "ZMM operand", "x87", "MMX register")}


def render(meta, nvec, nforms, modes_ok, rows, unlock, strict_ok, all_s2n, simd=None):
    L = []
    sib_all = set().union(*[r["sibling"] for r in rows if "error" not in r])
    w = L.append
    w("# THE PRIMITIVE CENSUS — which public scalar primitives use only tested forms\n")
    w("*Generated by `scripts/primitive_census.py`. Do not edit.* Rebuild: "
      "`python3 scripts/primitive_census.py --src <dir> --fetch --out "
      "docs/PRIMITIVE-CENSUS.md` (needs `x86lean-diff` built, clang and network; the "
      "sources are cloned into `<dir>` at the commits below).\n")
    w(f"<!-- census-model: vectors={nvec} forms={nforms} -->\n")
    w("## What this measures, and what it does not\n")
    w(f"A **form** is a printed mnemonic (width suffix, condition code and prefixes "
      f"included) plus the class of each operand. The model side is the **{nvec}** "
      f"differential vectors, which execute **{nforms}** distinct forms. A candidate "
      f"is **ALL COVERED** when every form its code executes is one of them and every "
      f"addressing mode it uses is one some vector uses.\n")
    w("- **Addressing modes are checked separately, not ignored.** The model computes "
      "every effective address in one function (`Ea.offset`), so the mode is not part "
      "of the form; the modes the vectors exercise are "
      + ", ".join(f"`{m}`" for m in sorted(modes_ok))
      + ", and a candidate mode outside that set is NOT COVERED. The `strict` column "
        "keeps the mode in the form, for a reader who does not accept the collapse.")
    w("- **Coverage is a precondition for a task, not a price.** Nothing here says a "
      "covered function can be proved at an acceptable cost.")
    w("- **The decoder is trusted to XED** (TRUSTBASE.md): an encoding difference that "
      "keeps the form is not a coverage difference here.")
    w("- **One compiler, one target, one set of flags:** " + meta["toolchain"]
      + ". C candidates are built twice: the default (`-O2`, clang may vectorise into "
        "SSE) and `scalar` (`-O2 -fno-vectorize -fno-slp-vectorize`). A different "
        "compiler emits different forms.")
    w("- **Calls that leave the object** are listed and mark the row; a candidate that "
      "calls out is never counted as covered. Calls and tail jumps inside the object "
      "are followed and counted with the entry.")
    w("- **The reference column is not uniform.** Only the s2n-bignum and Vale rows "
      "measure the verified artifact itself; a HACL* row measures clang's compilation "
      "of verified C; the checksum rows have a specification and test vectors and no "
      "machine-checked reference was found.\n")
    if simd:
        w("## The vectors' SIMD and floating-point content (derived)\n")
        w("The README's scope lines name these classes and point here for the counts.\n")
        w("| class | vectors |\n|---|---:|")
        for k, v in simd.items():
            w(f"| {k} | {v} |")
        w("")
    w("## The sources (fetched at these commits, never vendored)\n")
    w("| source | commit |\n|---|---|")
    for k, (url, sha) in REPOS.items():
        w(f"| [{k}]({url[:-4]}) | `{sha[:12]}` |")
    for name, why in NOT_MEASURED:
        w(f"| {name} | **NOT MEASURED** — {why} |")
    w("")
    # ⛔ A ROW THAT CALLS OUT IS NEVER COVERED (this file's own rule), and this
    # heading counted it anyway until 2026-09-30: at 1158 vectors it read 41 while
    # stdout and the by-family line read 40, the extra being HACL* Salsa20, whose
    # forms are all covered and which calls `memcpy`.  `run()` now refuses a
    # document whose heading disagrees with the count it prints.
    ok = [r for r in rows if r.get("all") and not r.get("external")]
    w(f"## The verdict: {len(ok)} of {len(rows)} candidates are ALL COVERED\n")
    fam = collections.Counter(r["family"] for r in ok if not r.get("external"))
    w("By family: " + " · ".join(f"{k} **{v}**" for k, v in sorted(fam.items())) + ".\n")
    w("`instrs` counts the instructions the walk reached from the entry (calls and "
      "branches inside the object, and fall-through between an assembly file's "
      "labels); `unreached` is the rest of the object's code — for a one-routine "
      "`.S` file it must be 0, for a compiled file it is the file's other "
      "functions — printed so a short walk cannot pass as a small function. "
      "`strict` counts not-covered forms with the addressing mode kept in the "
      "form. **Same-register operands are not a dimension here** (`xorq %r8,%r8` "
      "is the form `xorq r64,r64`), and neither is which register is used.\n")
    w("| candidate | family | reference | instrs | unreached | forms | not covered | strict | verdict |")
    w("|---|---|---|---:|---:|---:|---|---:|---|")
    for r in rows:
        if "error" in r:
            w(f"| `{r['id']}` | {r['family']} | {r['ref']} | — | — | — | **{r['error']}** | — | NOT MEASURED |")
            continue
        miss = ", ".join(f"`{fmt_form(f)}`×{k}" + ("†" if f in r["sibling"] else "")
                         + (f" ({ext_tag(f)})" if ext_tag(f) else "")
                         for f, k in sorted(r["missing"].items(), key=lambda t: -t[1]))
        bm = ", ".join(f"mode `{m}`×{k}" for m, k in r["badmodes"].items())
        miss = "; ".join(x for x in (miss, bm) if x) or "—"
        ext = r["external"]
        if ext:
            miss += "; **calls out:** " + ", ".join(f"`{k}`" for k in sorted(ext))
        verdict = "**ALL COVERED**" if r["all"] and not ext else (
            "covered, calls out" if r["all"] else f"{len(r['missing']) + len(r['badmodes'])} missing")
        sc = "" if r.get("scalar_all") is None else (
            " · scalar build: " + ("ALL COVERED" if r["scalar_all"] else
                                   f"{r['scalar_missing']} missing" if r["scalar_missing"]
                                   else "covered, calls out"))
        w(f"| `{r['id']}` | {r['family']} | {r['ref']} | {r['n']} | {r['unreached']} | {len(r['forms'])} "
          f"| {miss} | {r['strict_missing']} | {verdict}{sc} |")
    w("")
    ids, u, how, alsodone, steps = unlock
    w(f"## The shortest list of new forms that would unlock the next {len(ids)}\n")
    w(f"Search: {how}, over the rows that do not call out of their object. Adding "
      f"these **{len(u)}** forms (or modes) makes {len(alsodone)} more candidates ALL "
      f"COVERED: " + ", ".join(f"`{i}`" for i in alsodone) + ".\n")
    for f in sorted(u, key=lambda f: str(f)):
        if f[0] == "mode":
            w(f"- addressing mode `{f[1]}`")
        else:
            t = ext_tag(f)
            w(f"- `{fmt_form(f)}`" + (f" — {t}" if t else ""))
    w("")
    w("### The ladder: each next form, and what it completes (greedy)\n")
    w("| step | form(s) added | extension | completes | cumulative ALL COVERED |")
    w("|---:|---|---|---|---:|")
    base = sum(1 for r in rows if r.get("all") and not r.get("external"))
    tot = base
    for n, (fs, done) in enumerate(steps, 1):
        tot += len(done)
        names = ", ".join(("mode " + f[1]) if f[0] == "mode" else f"`{fmt_form(f)}`"
                          for f in fs)
        tags = ", ".join(sorted({ext_tag(f) or ("† width sibling" if f in sib_all else "base ISA")
                                 for f in fs if f[0] != "mode"})) or "—"
        w(f"| {n} | {names} | {tags} | " + ", ".join(f"`{i}`" for i in done)
          + f" | {tot} |")
    w("")
    freq = collections.Counter()
    for r in rows:
        if "error" not in r:
            for f in r["missing"]:
                freq[f] += 1
    w("## Every not-covered form, by how many candidates need it\n")
    w("† = the same mnemonic and operand shape IS tested at another width, so the "
      "form needs a vector, not new semantics (S1's five were this kind).\n")
    w("| form | candidates | tested at another width | extension |\n|---|---:|---|---|")
    sib = set().union(*[r["sibling"] for r in rows if "error" not in r])
    for f, k in freq.most_common():
        w(f"| `{fmt_form(f)}` | {k} | {'† yes' if f in sib else 'no'} | {ext_tag(f) or '—'} |")
    w("")
    if all_s2n:
        tot, okn, byext = all_s2n
        w(f"## Appendix: every s2n-bignum x86 function\n")
        w(f"Of **{tot}** functions in `s2n-bignum/x86/` (every `.S`, each its own entry), "
          f"**{okn}** are ALL COVERED. The not-covered ones, by the extension of the forms "
          f"they miss (a function can count under more than one):\n")
        w("| missing class | functions |\n|---|---:|")
        for k, v in byext.most_common():
            w(f"| {k} | {v} |")
        w("")
    return "\n".join(L) + "\n"


def fetch(src):
    os.makedirs(src, exist_ok=True)
    for name, (url, sha) in REPOS.items():
        d = os.path.join(src, name)
        if not os.path.isdir(d):
            subprocess.run(["git", "clone", "-q", "--filter=blob:none", url, d], check=True)
        subprocess.run(["git", "-C", d, "checkout", "-q", sha], check=True)


def check_pins(src):
    bad = []
    for name, (url, sha) in REPOS.items():
        q = subprocess.run(["git", "-C", os.path.join(src, name), "rev-parse", "HEAD"],
                           capture_output=True, text=True)
        if q.stdout.strip() != sha:
            bad.append(f"{name}: {q.stdout.strip() or 'absent'} != pinned {sha[:12]}")
    if bad:
        print("⛔ the sources are not at the pinned commits (run with --fetch):\n  "
              + "\n  ".join(bad))
        sys.exit(2)


def run(src, work, out):
    check_pins(src)
    os.makedirs(work, exist_ok=True)
    nvec, forms, strict_ok, modes_ok = model_forms(work)
    mnems = {f[0] for f in forms}
    rows = []
    for c in CANDIDATES:
        res = build_candidate(c, src, work, False)
        res.update({"id": c[0], "family": c[1], "ref": c[2]})
        if "error" not in res:
            score(res, forms, modes_ok, mnems)
            res["strict_missing"] = sum(1 for f in res["forms"] if f not in forms) + len(res["badmodes"])
            res["scalar_all"] = None
            if c[3] in ("c", "cpp"):
                s = build_candidate(c, src, work, True)
                if "error" not in s:
                    score(s, forms, modes_ok, mnems)
                    res["scalar_all"] = s["all"] and not s["external"]
                    res["scalar_missing"] = len(s["missing"]) + len(s["badmodes"])
        rows.append(res)
    # ⛔ THE CONTROLS, CHECKED BEFORE ANYTHING IS WRITTEN.  The PoC must read
    # ALL COVERED (S1 added its five forms); a SHA-NI routine must NOT, and must
    # name a sha256 form — otherwise the instrument, not the model, is speaking.
    byid = {r["id"]: r for r in rows}
    poc, neg = byid["crc32-poc"], byid["vale-sha256"]
    # the PoC's size is DERIVED from its own text, not typed: every line that is
    # neither a directive, a label nor a comment is one instruction
    want = sum(1 for l in CRC_POC.splitlines()
               if l.strip() and not l.strip().startswith((".", "#")) and not l.strip().endswith(":"))
    if "error" in poc or poc["n"] != want:
        print(f"⛔ POSITIVE CONTROL FAILED: the census walked {poc.get('n')} of the PoC's "
              f"{want} instructions — the walk, not the model, is the subject")
        sys.exit(3)
    if "error" in poc or not poc["all"]:
        print("⛔ POSITIVE CONTROL FAILED: the CRC-32 PoC does not read ALL COVERED:",
              poc.get("error") or [fmt_form(f) for f in poc["missing"]], poc.get("badmodes"))
        sys.exit(3)
    if "error" in neg or neg["all"] or not any(f[0].startswith("sha256") for f in neg["missing"]):
        print("⛔ NEGATIVE CONTROL FAILED: the SHA-NI routine is not reported missing sha256rnds2")
        sys.exit(3)
    errs = [r for r in rows if "error" in r]
    # the appendix: every s2n-bignum x86 function
    tot, okn, byext = 0, 0, collections.Counter()
    for sub in sorted(os.listdir(os.path.join(src, S2N))):
        d = os.path.join(src, S2N, sub)
        if not os.path.isdir(d):
            continue
        for fn in sorted(os.listdir(d)):
            if not fn.endswith(".S"):
                continue
            nm = fn[:-2]
            r = build_candidate((nm, "", "", "S", S2N + sub + "/" + fn, [nm], []), src, work, False)
            if "error" in r:
                continue
            tot += 1
            score(r, forms, modes_ok, mnems)
            if r["all"] and not r["external"]:
                okn += 1
            else:
                tags = {ext_tag(f) or "base-ISA form untested" for f in r["missing"]}
                if r["badmodes"]:
                    tags.add("addressing mode")
                if r["external"]:
                    tags.add("calls out")
                for t in tags:
                    byext[t] += 1
    # a row that calls out of its object is not unlocked by any form, so it is
    # outside the search (and named in its own row as calling out)
    open_rows = [r for r in rows if "error" not in r and not r["all"]
                 and not r["external"]]
    ids, u, how = best_unlock(open_rows, 10)
    alsodone = [r["id"] for r in open_rows if needs(r) <= u]
    unlock = (ids, u, how, alsodone, ladder(open_rows))
    q = subprocess.run(["clang", "--version"], capture_output=True, text=True)
    meta = {"toolchain": f"`{q.stdout.splitlines()[0]}`, `-target {TARGET}`, "
                         f"`{' '.join(CFLAGS)}`, disassembled by `objdump` (LLVM)"}
    text = render(meta, nvec, len(forms), modes_ok, rows, unlock, strict_ok, (tot, okn, byext),
                  simd_content(forms))
    ok = [r["id"] for r in rows if r.get("all") and not r.get("external")]
    m = re.search(r"^## The verdict: (\d+) of (\d+) candidates", text, re.M)
    if not m or int(m.group(1)) != len(ok) or int(m.group(2)) != len(rows):
        print(f"⛔ the document's verdict heading ({m.group(0) if m else 'absent'}) "
              f"disagrees with the count this run prints ({len(ok)} of {len(rows)})")
        sys.exit(3)
    if out:
        open(out, "w", encoding="utf-8").write(text)
    print(f"primitive-census: vectors={nvec} forms={len(forms)} modes={sorted(modes_ok)}")
    print(f"primitive-census: {len(ok)} of {len(rows)} ALL COVERED ({len(errs)} not measured): "
          + " ".join(ok))
    print(f"primitive-census: {len(unlock[1])} form(s) unlock {len(unlock[3])} more ({unlock[2]}); "
          f"ladder {len(unlock[4])} steps")
    print(f"primitive-census: s2n-bignum appendix {okn}/{tot} ALL COVERED")
    print("primitive-census: controls OK (CRC-32 PoC covered; SHA-NI routine refused)")
    return 0


# ── selftest: the classifier, on shapes, both directions ────────────────────
def selftest():
    cases = [
        ("movl\t%ecx, %eax", (("movl", ("r32", "r32")), ())),
        ("movl\t$0xffffffff, %eax", (("movl", ("imm", "r32")), ())),
        ("xorl\t0x3000(,%rcx,4), %eax", (("xorl", ("m", "r32")), ("index",))),
        ("movzbl\t(%rdi), %ecx", (("movzbl", ("m", "r32")), ("base",))),
        ("leaq\t0x1234(%rip), %rax      # 0x22f2 <x>", (("leaq", ("m", "r64")), ("rip",))),
        ("movq\t%fs:0x28, %rax", (("movq", ("m", "r64")), ("fs:abs",))),
        ("addq\t(%rbx,%rcx,8), %rax", (("addq", ("m", "r64")), ("base+index",))),
        ("jne\t0x100a <crc+0xa>", (("jne", ("rel",)), ())),
        ("callq\t*%rax", (("callq", ("*r64",)), ())),
        ("jmpq\t*0x8(%rax)", (("jmpq", ("*m",)), ("base",))),
        ("rep\t\tstosq\t%rax, %es:(%rdi)", (("rep stosq", ("r64", "m")), ("base",))),
        ("lock\t\txaddl\t%eax, (%rdi)", (("lock xaddl", ("r32", "m")), ("base",))),
        ("shrl\t$0x8, %eax", (("shrl", ("imm", "r32")), ())),
        ("shrl\t%cl, %eax", (("shrl", ("r8", "r32")), ())),
        ("mulxq\t%rcx, %rax, %rdx", (("mulxq", ("r64", "r64", "r64")), ())),
        ("pxor\t%xmm1, %xmm0", (("pxor", ("xmm", "xmm")), ())),
        ("movb\t%ah, %al", (("movb", ("r8h", "r8")), ())),
        ("retq", (("retq", ()), ())),
    ]
    bad = 0
    for text, want in cases:
        got = form_of(text)
        if got != want:
            print(f"⛔ form_of({text!r}) = {got}, want {want}"); bad += 1
    # the two directions a classifier can fail: a merge and a split
    if form_of("movl\t%ecx, %eax")[0] == form_of("movq\t%rcx, %rax")[0]:
        print("⛔ widths merged"); bad += 1
    if form_of("movq\t(%rbx), %rax")[0] != form_of("movq\t0x10(%rbx,%rcx,4), %rax")[0]:
        print("⛔ addressing modes split the form"); bad += 1
    if form_of("movq\t(%rbx), %rax")[1] == form_of("movq\t0x10(%rbx,%rcx,4), %rax")[1]:
        print("⛔ addressing modes not distinguished in the mode check"); bad += 1
    # unlock: a plant where the answer is known
    rows = [{"id": "a", "all": False, "missing": {("x", ()): 1}, "badmodes": {}},
            {"id": "b", "all": False, "missing": {("x", ()): 1, ("y", ()): 1}, "badmodes": {}},
            {"id": "c", "all": False, "missing": {("z", ()): 1, ("w", ()): 1, ("v", ()): 1}, "badmodes": {}}]
    ids, u, _ = best_unlock(rows, 2)
    if sorted(ids) != ["a", "b"] or len(u) != 2:
        print(f"⛔ best_unlock picked {ids} with {len(u)} forms; want a,b with 2"); bad += 1
    # the ladder: `x` completes a AND is half of b, so it must come first
    st = ladder(rows)
    if not st or st[0][0] != [("x", ())] or st[0][1] != ["a"]:
        print(f"⛔ ladder's first step is {st[:1]}; want x completing a"); bad += 1
    # a width sibling is found, and a condition code is NOT a width
    if widthless(("addl", ("r32", "r32"))) != widthless(("addq", ("r64", "r64"))):
        print("⛔ addl/addq not width siblings"); bad += 1
    if widthless(("jb", ("rel",))) == widthless(("jl", ("rel",))):
        print("⛔ jb/jl read as width siblings"); bad += 1
    print("primitive-census selftest:", "FAIL" if bad else f"OK ({len(cases)} shapes + 7 arms)")
    return 1 if bad else 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--src")
    ap.add_argument("--work")
    ap.add_argument("--out")
    ap.add_argument("--fetch", action="store_true")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    if not a.src:
        ap.error("--src DIR is required (the directory the pinned sources are cloned into)")
    if a.fetch:
        fetch(a.src)
    work = a.work or os.path.join(a.src, "_census_work")
    return run(a.src, work, a.out)


if __name__ == "__main__":
    sys.exit(main())
