#!/usr/bin/env python3
"""B2 — the asm -> x86lean front end for the DECLARED 29-mnemonic core.

WHAT IT IS FOR.  The x86 SaltBench cell (desk PE, proposal v1 §3.5) hands a
model's assembly to a referee that must run it under x86lean.  x86lean has no
decoder: decode is TRUSTED (TRUSTBASE.md), and until now every `Program` was
translated by hand from an objdump listing.  This script is that translation,
made mechanical and self-tested:

    clang -> a linked x86-64 ELF -> objdump -d (AT&T) -> THIS -> a Lean module
                                                                 (`prog : X86.Program`,
                                                                  `image : X86.Image`)

The instruction BYTES are the disassembler's and the LENGTH is the byte count
it printed, so this script adds no decode of its own: it maps the text a
disassembler prints onto x86lean's AST.  That mapping is what the selftest
checks.

⛔ THE CORE IS AN ALLOWLIST, NOT "WHAT x86lean COVERS".  v1 §3.5 declares 29
mnemonics; anything else is REFUSED, by name, and a refusal is a distinct
non-scoring outcome in the referee (REFUSED-TRANSLATE), never a translation
failure to be worked around.  An instruction x86lean models but the core omits
(adc, xchg, bt, ...) is refused too — widening the core is a decision, and it
is made in CORE below and nowhere else.

⭐ THE SELFTEST RUNS THE REAL PATH, ON BOTH DISASSEMBLERS.  `--selftest`
assembles EVERY differential vector's own `asm` string with clang, disassembles
it, translates each vector's listing, and asks Lean to compare the result with
the vector's hand-written `instr` by `==`:

    a CORE vector       must translate, and be EQUAL to its `instr`
    any other vector    must be REFUSED

It runs once per disassembler found — LLVM `objdump` (macOS, and `llvm-objdump`
on Linux) and GNU binutils — because they print different text for the same
bytes (GNU drops the size suffix when a register fixes it, prints negative
immediates as their unsigned width, and wraps its byte column at seven bytes;
LLVM prints `lock` as a line of its own).  A parser validated on one is a
parser validated on one (check_encodings.py's D89 note).

THE CONVENTIONS IT REPRODUCES, each read from the corpus rather than chosen:
  - an immediate is its value MODULO THE OPERAND WIDTH (`movl $0xffffffff` is
    0x00000000ffffffff; `andq $-1` is all ones);
  - a displacement is sign-extended to 64 bits;
  - a relative branch's `d` is target - (address + length), modulo 2^64;
  - a shift or rotate with no count operand counts 1 (`imm8 1`);
  - `lock` is carried on the memory operand's `Ea`, never on the instruction.

Usage:
    asm_front.py translate <linked-elf> [--out FILE] [--namespace NS]
    asm_front.py --selftest
Exit codes: 0 ok · 1 selftest red · 2 refused to run (a tool or input is
missing) · 3 REFUSED-TRANSLATE (a form outside the core; each is printed).
"""
import os, re, shutil, struct, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
GNU_OBJDUMP = "/opt/homebrew/opt/binutils/bin/objdump"

# ── THE DECLARED CORE (proposal v1 §3.5).  One line per mnemonic class. ──────
CORE = ("mov movzx movsx add sub and or xor cmp test shl shr sar inc dec neg "
        "not lea push pop jmp jcc call ret cmovcc setcc imul rol ror").split()
# The corpus's `Vec.mnemonic` for ret is `retq`; every other class is spelled
# the same in both places.
CORE_VEC_MNEMONICS = [("retq" if m == "ret" else m) for m in CORE]

BIN = {"add", "sub", "and", "or", "xor", "cmp", "test"}
UN = {"inc", "dec", "neg", "not"}
SHIFT = {"shl", "shr", "sar"}
ROT = {"rol", "ror"}
SUFFIX = {"b": "b", "w": "w", "l": "d", "q": "q"}
WIDTH = {"b": 8, "w": 16, "d": 32, "q": 64}

CC = {"o": "o", "no": "no", "b": "b", "c": "b", "nae": "b",
      "ae": "ae", "nb": "ae", "nc": "ae", "e": "e", "z": "e",
      "ne": "ne", "nz": "ne", "be": "be", "na": "be", "a": "a", "nbe": "a",
      "s": "s", "ns": "ns", "p": "p", "pe": "p", "np": "np", "po": "np",
      "l": "l", "nge": "l", "ge": "ge", "nl": "ge", "le": "le", "ng": "le",
      "g": "g", "nle": "g"}

_R64 = "rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15".split()
REGS = {}
for i, r in enumerate(_R64):
    REGS[r] = (r, "q", False)
    if i < 8:
        e = r[1:]                                   # ax cx dx bx sp bp si di
        REGS["e" + e] = (r, "d", False)
        REGS[e] = (r, "w", False)
        REGS[{"ax": "al", "cx": "cl", "dx": "dl", "bx": "bl"}.get(e, e + "l")] = (r, "b", False)
    else:
        REGS[r + "d"] = (r, "d", False)
        REGS[r + "w"] = (r, "w", False)
        REGS[r + "b"] = (r, "b", False)
for h, r in (("ah", "rax"), ("ch", "rcx"), ("dh", "rdx"), ("bh", "rbx")):
    REGS[h] = (r, "b", True)


class Refused(Exception):
    """A form outside the declared core, or text this front end cannot read."""


# ── THE LISTING ──────────────────────────────────────────────────────────────
_LABEL = re.compile(r'^([0-9a-f]+) <([^>]+)>:\s*$')
_LINE = re.compile(r'^\s*([0-9a-f]+):\s+((?:[0-9a-f]{2} ?)+?)\s*(?:\t\s*(.*))?$')


def parse_listing(text):
    """`objdump -d` text -> [(label, [(addr, nbytes, asm_text)])], BOTH tools.

    ⛔ Three format facts, each of which silently corrupts a length if missed:
    GNU continues a long encoding on a line with an address and NO mnemonic
    (joined here); LLVM prints a `lock` prefix as its own instruction line
    (joined with the next); and a line's byte column may abut the tab."""
    out, cur = [], None
    for raw in text.splitlines():
        m = _LABEL.match(raw)
        if m:
            cur = (m.group(2), [])
            out.append(cur)
            continue
        m = _LINE.match(raw)
        if not m or cur is None:
            continue
        addr = int(m.group(1), 16)
        nb = len(m.group(2).split())
        asm = (m.group(3) or "").split("#")[0].strip()
        ins = cur[1]
        if not asm:                                  # GNU byte-column continuation
            if not ins:
                raise Refused(f"a byte continuation with no instruction at {addr:#x}")
            a, n, t = ins[-1]
            ins[-1] = (a, n + nb, t)
            continue
        if ins and ins[-1][2] == "lock" and ins[-1][0] + ins[-1][1] == addr:
            a, n, _ = ins[-1]                         # LLVM's own-line prefix
            ins[-1] = (a, n + nb, "lock " + asm)
            continue
        ins.append((addr, nb, asm))
    return out


# ── OPERANDS ─────────────────────────────────────────────────────────────────
def _num(s):
    s = s.strip()
    neg = s.startswith("-")
    v = int(s.lstrip("-"), 16 if "0x" in s else 10)
    return -v if neg else v


def _split_operands(s):
    """Split on commas OUTSIDE parentheses."""
    parts, depth, cur = [], 0, ""
    for ch in s:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        parts.append(cur.strip())
    return parts


def _reg(tok):
    if not tok.startswith("%") or tok[1:] not in REGS:
        raise Refused(f"not a general-purpose register: {tok!r}")
    return REGS[tok[1:]]


_MEM = re.compile(r'^(?:%(fs|gs|ds|ss|es|cs):)?([-0-9a-fx]*)(?:\((%\w+)?(?:,(%\w+)(?:,([1248]))?)?\))?$')


def _ea(tok):
    """An AT&T memory operand -> dict of Ea fields (with the corpus's defaults)."""
    m = _MEM.match(tok.replace(" ", ""))
    if not m or (not m.group(2) and m.group(3) is None and m.group(4) is None):
        raise Refused(f"not a memory operand: {tok!r}")
    seg, disp, base, index, scale = m.groups()
    if "(" not in tok and not disp:
        raise Refused(f"not a memory operand: {tok!r}")
    ea = {"base": None, "index": None, "scale": 1, "disp": 0, "ripRel": False,
          "seg": seg if seg in ("fs", "gs") else None, "lock": False}
    ea["disp"] = (_num(disp) if disp else 0) % (1 << 64)
    if base == "%rip":
        if index:
            raise Refused(f"rip-relative with an index: {tok!r}")
        ea["ripRel"] = True
    elif base:
        r, w, h = _reg(base)
        if w != "q" or h:
            raise Refused(f"a non-64-bit address register: {tok!r}")
        ea["base"] = r
    if index:
        r, w, h = _reg(index)
        if w != "q" or h or r == "rsp":
            raise Refused(f"an index register x86lean does not address with: {tok!r}")
        ea["index"] = r
        ea["scale"] = int(scale or 1)
    return ea


def operand(tok):
    """-> ('reg', gpr, width, high8) | ('imm', int) | ('mem', ea)"""
    tok = tok.strip()
    if tok.startswith("$"):
        return ("imm", _num(tok[1:]))
    if tok.startswith("%") and ":" not in tok and "(" not in tok:
        r, w, h = _reg(tok)
        return ("reg", r, w, h)
    return ("mem", _ea(tok))


# ── LEAN TEXT ────────────────────────────────────────────────────────────────
def bv(v, n=64):
    return f"(0x{v % (1 << n):0{n // 4}x}#{n})"


def lean_ea(ea):
    opt = lambda x, f: f"(some {f(x)})" if x is not None else "none"
    return ("{ base := %s, index := %s, scale := .s%d, disp := %s, ripRel := %s, "
            "seg := %s, lock := %s }" % (
                opt(ea["base"], lambda r: "." + r), opt(ea["index"], lambda r: "." + r),
                ea["scale"], bv(ea["disp"]), str(ea["ripRel"]).lower(),
                opt(ea["seg"], lambda s: "." + s), str(ea["lock"]).lower()))


def lean_operand(o, sz):
    if o[0] == "reg":
        return f"(.reg .{o[1]} {str(o[3]).lower()})"
    if o[0] == "mem":
        return f"(.mem {lean_ea(o[1])})"
    return f"(.imm {bv(o[1] % (1 << WIDTH[sz]))})"


# ── ONE INSTRUCTION ──────────────────────────────────────────────────────────
def _split_suffix(m, bases):
    """(base, size-or-None) for a mnemonic in `bases`, with an optional AT&T suffix."""
    if m in bases:
        return m, None
    if m[:-1] in bases and m[-1] in SUFFIX:
        return m[:-1], SUFFIX[m[-1]]
    return None, None


def _size(explicit, ops, what):
    widths = {o[2] for o in ops if o[0] == "reg"}
    if explicit and widths and widths != {explicit}:
        raise Refused(f"{what}: suffix {explicit} disagrees with registers {sorted(widths)}")
    if explicit:
        return explicit
    if len(widths) == 1:
        return widths.pop()
    raise Refused(f"{what}: operand size is not determined by the text")


def _cc_and_suffix(rest):
    if rest in CC:
        return CC[rest], None
    if rest[:-1] in CC and rest[-1] in SUFFIX:
        return CC[rest[:-1]], SUFFIX[rest[-1]]
    return None, None


def _no_imm_dst(o, what):
    if o[0] == "imm":
        raise Refused(f"{what}: an immediate destination")


def translate(addr, n, text):
    """One listing line -> Lean `Instr` text, or raise Refused naming the form."""
    words = text.split(None, 1)
    lock = False
    if words and words[0] == "lock":
        lock = True
        words = words[1].split(None, 1) if len(words) > 1 else []
    if not words:
        raise Refused("an empty instruction")
    mn = words[0]
    ops = []
    what = f"{addr:#x} `{text}`"

    def mem_lock():
        mems = [o for o in ops if o[0] == "mem"]
        if lock:
            if len(mems) != 1:
                raise Refused(f"{what}: `lock` with no single memory operand")
            mems[0][1]["lock"] = True

    def done(op):
        mem_lock()
        return f"⟨{op()}, {n}⟩"

    if mn in ("ret", "retq") and len(words) == 1:
        return done(lambda: ".ret")

    # branches: a bare hex target, or `*operand` for indirect
    if mn in ("jmp", "jmpq", "call", "callq") or (mn.startswith("j") and mn[1:] in CC):
        if len(words) < 2:
            raise Refused(f"{what}: a branch with no target")
        t = words[1].strip()
        if t.startswith("*"):
            o = operand(t[1:])
            if o[0] == "imm" or (o[0] == "reg" and (o[2] != "q" or o[3])):
                raise Refused(f"{what}: an indirect target that is not a 64-bit operand")
            if not mn.startswith(("jmp", "call")):
                raise Refused(f"{what}: an indirect conditional branch")
            kind = "jmp" if mn.startswith("jmp") else "call"
            ops = [o]
            return done(lambda: f".{kind} (.indirect {lean_operand(o, 'q')})")
        tm = re.match(r'^(?:0x)?([0-9a-f]+)(?:\s+<[^>]*>)?$', t)
        if not tm:
            raise Refused(f"{what}: an unreadable branch target")
        d = (int(tm.group(1), 16) - (addr + n)) % (1 << 64)
        if mn.startswith("jmp"):
            return done(lambda: f".jmp (.rel {bv(d)})")
        if mn.startswith("call"):
            return done(lambda: f".call (.rel {bv(d)})")
        return done(lambda: f".jcc .{CC[mn[1:]]} {bv(d)}")

    # every other form: AT&T operands, source first
    ops = [operand(t) for t in _split_operands(words[1])] if len(words) > 1 else []

    # the mov family
    base, sz = _split_suffix(mn, {"mov", "movabs"})
    if base:
        if len(ops) != 2:
            raise Refused(f"{what}: mov takes two operands")
        src, dst = ops
        _no_imm_dst(dst, what)
        s = _size(sz, ops, what)
        return done(lambda: f".mov .{s} {lean_operand(dst, s)} {lean_operand(src, s)}")
    mx = re.match(r'^mov([zs])([bwl])([wlq])$', mn)
    if mx or mn in ("movzx", "movsx", "movsxd"):
        if len(ops) != 2 or ops[1][0] != "reg" or ops[1][3]:
            raise Refused(f"{what}: movzx/movsx needs a register destination")
        src, dst = ops
        if mx:
            kind = "zero" if mx.group(1) == "z" else "sign"
            ssz, dsz = SUFFIX[mx.group(2)], SUFFIX[mx.group(3)]
        else:
            if src[0] != "reg":
                raise Refused(f"{what}: an unsuffixed movzx/movsx from memory")
            kind = "zero" if mn == "movzx" else "sign"
            ssz, dsz = src[2], dst[2]
        if dst[2] != dsz or (src[0] == "reg" and src[2] != ssz):
            raise Refused(f"{what}: operand widths disagree with the mnemonic")
        if kind == "zero" and ssz == "d":
            raise Refused(f"{what}: movzlq is not an instruction")
        return done(lambda: f".movx .{kind} .{dsz} .{ssz} .{dst[1]} {lean_operand(src, ssz)}")

    base, sz = _split_suffix(mn, BIN)
    if base:
        if len(ops) != 2:
            raise Refused(f"{what}: {base} takes two operands")
        src, dst = ops
        _no_imm_dst(dst, what)
        s = _size(sz, ops, what)
        return done(lambda: f".bin .{base} .{s} {lean_operand(dst, s)} {lean_operand(src, s)}")

    base, sz = _split_suffix(mn, UN)
    if base:
        if len(ops) != 1:
            raise Refused(f"{what}: {base} takes one operand")
        _no_imm_dst(ops[0], what)
        s = _size(sz, ops, what)
        return done(lambda: f".un .{base} .{s} {lean_operand(ops[0], s)}")

    base, sz = _split_suffix(mn, SHIFT | ROT)
    if base:
        if len(ops) == 1:
            amt, dst = "(.imm8 (0x01#8))", ops[0]
        elif len(ops) == 2:
            a, dst = ops
            if a[0] == "imm":
                amt = f"(.imm8 {bv(a[1], 8)})"
            elif a[0] == "reg" and a[1] == "rcx" and a[2] == "b" and not a[3]:
                amt = ".cl"
            else:
                raise Refused(f"{what}: a shift count that is neither an immediate nor %cl")
        else:
            raise Refused(f"{what}: {base} takes one or two operands")
        _no_imm_dst(dst, what)
        s = _size(sz, [dst], what)
        ctor = "rot" if base in ROT else "shift"
        return done(lambda: f".{ctor} .{base} .{s} {lean_operand(dst, s)} {amt}")

    base, sz = _split_suffix(mn, {"lea"})
    if base:
        if len(ops) != 2 or ops[0][0] != "mem" or ops[1][0] != "reg" or ops[1][3]:
            raise Refused(f"{what}: lea needs a memory source and a register destination")
        s = _size(sz, [ops[1]], what)
        mem_lock()
        return f"⟨.lea .{s} .{ops[1][1]} {lean_ea(ops[0][1])}, {n}⟩"

    base, sz = _split_suffix(mn, {"push", "pop"})
    if base:
        if len(ops) != 1:
            raise Refused(f"{what}: {base} takes one operand")
        o = ops[0]
        if base == "pop":
            _no_imm_dst(o, what)
        # 64-bit mode: the default operand size of push/pop is 64 bits.
        s = sz or (o[2] if o[0] == "reg" else "q")
        if o[0] == "reg" and o[2] != s:
            raise Refused(f"{what}: suffix disagrees with the register")
        if s not in ("q", "w"):
            raise Refused(f"{what}: push/pop at a width 64-bit mode cannot encode")
        return done(lambda: f".{base} .{s} {lean_operand(o, s)}")

    if mn.startswith("cmov"):
        cc, sz = _cc_and_suffix(mn[4:])
        if cc:
            if len(ops) != 2 or ops[1][0] != "reg" or ops[1][3]:
                raise Refused(f"{what}: cmov needs a register destination")
            s = _size(sz, ops, what)
            return done(lambda: f".cmov .{cc} .{s} .{ops[1][1]} {lean_operand(ops[0], s)}")

    if mn.startswith("set") and mn[3:] in CC:
        if len(ops) != 1:
            raise Refused(f"{what}: setcc takes one operand")
        _no_imm_dst(ops[0], what)
        if ops[0][0] == "reg" and ops[0][2] != "b":
            raise Refused(f"{what}: setcc writes a byte")
        return done(lambda: f".setcc .{CC[mn[3:]]} {lean_operand(ops[0], 'b')}")

    base, sz = _split_suffix(mn, {"imul"})
    if base:
        if len(ops) == 1:
            _no_imm_dst(ops[0], what)
            s = _size(sz, ops, what)
            return done(lambda: f".muldiv .imul .{s} {lean_operand(ops[0], s)}")
        if len(ops) in (2, 3):
            *rest, dst = ops
            if dst[0] != "reg" or dst[3]:
                raise Refused(f"{what}: imul needs a register destination")
            imm = None
            if len(ops) == 3:
                if rest[0][0] != "imm":
                    raise Refused(f"{what}: three-operand imul needs an immediate")
                imm, rest = rest[0][1], rest[1:]
            src = rest[0]
            s = _size(sz, [src, dst], what)
            if s == "b":
                raise Refused(f"{what}: there is no byte-width two-operand imul")
            im = "none" if imm is None else f"(some {bv(imm % (1 << WIDTH[s]))})"
            return done(lambda: f".imulr .{s} .{dst[1]} {lean_operand(src, s)} {im}")
        raise Refused(f"{what}: imul takes one, two or three operands")

    raise Refused(f"{what}: `{mn}` is outside the declared {len(CORE)}-mnemonic core")


# ── TOOLS ────────────────────────────────────────────────────────────────────
def disassemblers():
    """Every AT&T disassembler on this box: [(name, argv0)]."""
    found = []
    llvm = shutil.which("llvm-objdump")
    if llvm:
        found.append(("LLVM", llvm))
    plain = shutil.which("objdump")
    if plain:
        v = subprocess.run([plain, "--version"], capture_output=True, text=True).stdout
        if "LLVM" in v and not llvm:
            found.append(("LLVM", plain))
        elif "GNU" in v:
            found.append(("GNU", plain))
    if os.path.exists(GNU_OBJDUMP) and not any(n == "GNU" for n, _ in found):
        found.append(("GNU", GNU_OBJDUMP))
    return found


def objdump_text(tool, obj, base=0):
    adj = [f"--adjust-vma={base:#x}"] if base else []
    r = subprocess.run([tool, "-d", "--section=.text", *adj, obj], capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"⛔ {tool} failed on {obj}:\n{r.stderr}")
    return r.stdout


# ── TRANSLATE ────────────────────────────────────────────────────────────────
def elf_sections(path):
    """(e_type, [(name, type, flags, addr, bytes)]) of an ELF64 little-endian file."""
    data = open(path, "rb").read()
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        raise SystemExit(f"⛔ {path} is not a little-endian ELF64 file")
    e_type = struct.unpack_from("<H", data, 16)[0]
    shoff, = struct.unpack_from("<Q", data, 0x28)
    shentsize, shnum, shstrndx = struct.unpack_from("<HHH", data, 0x3A)
    secs = []
    for i in range(shnum):
        name, typ, flags, addr, off, size = struct.unpack_from("<IIQQQQ", data, shoff + i * shentsize)
        secs.append([name, typ, flags, addr, off, size])
    so = secs[shstrndx][4]
    out = []
    for name, typ, flags, addr, off, size in secs:
        nm = data[so + name:data.index(b"\0", so + name)].decode()
        body = b"" if typ == 8 else data[off:off + size]           # SHT_NOBITS
        out.append((nm, typ, flags, addr, body if typ != 8 else bytes(size)))
    return e_type, out


def cmd_translate(argv):
    if not argv:
        raise SystemExit("usage: asm_front.py translate <elf> [--base ADDR] [--out FILE] [--namespace NS]")
    path, out, ns, base = argv[0], None, "Submission", None
    rest = argv[1:]
    while rest:
        if rest[0] == "--out" and len(rest) > 1:
            out, rest = rest[1], rest[2:]
        elif rest[0] == "--namespace" and len(rest) > 1:
            ns, rest = rest[1], rest[2:]
        elif rest[0] == "--base" and len(rest) > 1:
            base, rest = int(rest[1], 0), rest[2:]
        else:
            raise SystemExit(f"⛔ unknown argument {rest[0]!r}")
    e_type, secs = elf_sections(path)
    # ⛔ THE LAYOUT IS THE LINKER'S, NOT THIS SCRIPT'S.  A linked executable
    # (ET_EXEC) carries its addresses and is translated as it stands; `--base`
    # is refused for it.  An UNLINKED object (ET_REL) is accepted only when
    # nothing in it needs a layout decision: NO relocation section (a relocated
    # field reads as 0 in the listing, and translating it would bake in the
    # wrong address) and NO allocated data section (whose address only a link
    # can choose).  Its `.text` is then position-independent as assembled, and
    # `--base` places it.  Anything else: link first.
    if e_type == 2:
        if base is not None:
            raise SystemExit("⛔ --base is for an unlinked object; a linked executable carries its own layout")
        base = 0
    elif e_type == 1:
        relocs = [nm for nm, typ, _f, _a, _b in secs if typ in (4, 9)]      # SHT_RELA, SHT_REL
        data = [nm for nm, _t, fl, _a, body in secs if fl & 2 and not fl & 4 and body]
        if relocs or data or base is None:
            raise SystemExit("⛔ an unlinked object needs a link at the fixed layout first: "
                             f"relocations {relocs or 'none'}, data sections {data or 'none'}, "
                             f"--base {'given' if base is not None else 'NOT given'}")
    else:
        raise SystemExit(f"⛔ ELF type {e_type} is neither an executable nor a relocatable object")
    tools = disassemblers()
    if not tools:
        raise SystemExit("⛔ no objdump on this box")
    listing = parse_listing(objdump_text(tools[0][1], path, base))
    code, refused = [], []
    for _label, ins in listing:
        for a, n, t in ins:
            try:
                code.append((a, translate(a, n, t)))
            except Refused as e:
                refused.append(str(e))
    if refused:
        for r in refused:
            print(f"REFUSED-TRANSLATE {r}")
        return 3
    image = []
    for nm, _typ, flags, addr, body in secs:
        # SHF_ALLOC (2) and NOT SHF_EXECINSTR (4): the data the routine reads.
        if flags & 2 and not flags & 4 and body:
            image.extend((addr + i, b) for i, b in enumerate(body))
    lines = [f"-- Generated by x86lean scripts/asm_front.py from {os.path.basename(path)}"
             f" ({len(code)} instructions, {len(image)} data bytes). Do not edit.",
             "import X86", "open X86", "", f"namespace {ns}", "",
             "set_option maxRecDepth 32768 in",
             "def prog : Program := { code := ["]
    lines += [f"  ({bv(a)}, {i})," for a, i in code]
    if code:
        lines[-1] = lines[-1].rstrip(",")
    lines += ["] }", "", "set_option maxRecDepth 32768 in",
              "def image : Image := { data := ["]
    lines += [f"  ({bv(a)}, {bv(b, 8)})," for a, b in image]
    if image:
        lines[-1] = lines[-1].rstrip(",")
    lines += ["] }", "", f"end {ns}", ""]
    text = "\n".join(lines)
    if out:
        open(out, "w").write(text)
        print(f"asm_front: {len(code)} instructions, {len(image)} data bytes -> {out}")
    else:
        sys.stdout.write(text)
    return 0


# ── SELFTEST ─────────────────────────────────────────────────────────────────
def _vector_mnemonics(tmp):
    """id -> Vec.mnemonic, from the compiled differential binary."""
    lean = os.path.join(tmp, "Mn.lean")
    open(lean, "w").write("import Tests.Vectors\nopen X86.Tests\n"
                          "def row (v : Vec) : String := v.id ++ \"\\t\" ++ v.mnemonic\n"
                          "#eval do\n  for v in vectors do\n    IO.println (row v)\n")
    r = subprocess.run([sys.executable, os.path.join(HERE, "lean_route.py"), "lean", lean],
                       capture_output=True, text=True, cwd=ROOT)
    if r.returncode != 0:
        raise SystemExit(f"⛔ could not read the vector table (rc {r.returncode}):\n{r.stdout}\n{r.stderr}")
    return dict(l.split("\t", 1) for l in r.stdout.splitlines() if "\t" in l)


def selftest_one(name, tool, obj, mnems, tmp):
    listing = dict(parse_listing(objdump_text(tool, obj)))
    last = list(listing)[-1]
    # `emit-asm` closes the table with a sentinel `nop`, which lands in the
    # last vector's block.
    if listing[last] and listing[last][-1][2] == "nop":
        listing[last] = listing[last][:-1]
    entries, pre = [], {"core": 0, "other": 0, "refused_core": [], "accepted_other": []}
    core = set(CORE_VEC_MNEMONICS)
    for vid, mn in mnems.items():
        ins = listing.get(vid)
        if not ins or len(ins) != 1:
            raise SystemExit(f"⛔ [{name}] vector {vid}: expected ONE instruction, found {ins!r}")
        a, n, t = ins[0]
        try:
            term = translate(a, n, t)
        except Refused as e:
            term = None
            if mn in core:
                pre["refused_core"].append(f"{vid}: {e}")
        if mn in core:
            pre["core"] += 1
        else:
            pre["other"] += 1
            if term is not None:
                pre["accepted_other"].append(f"{vid} ({mn}): `{t}`")
        entries.append(f'  ("{vid}", ' + (f"some {term}" if term else "none") + ")")
    lean = os.path.join(tmp, f"B2Self{name}.lean")
    body = ",\n".join(entries)
    core_list = ", ".join(f'"{m}"' for m in CORE_VEC_MNEMONICS)
    open(lean, "w").write(f"""import Tests.Vectors
open X86 X86.Tests

set_option maxRecDepth 32768 in
def b2 : List (String × Option Instr) := [
{body}
]

def core : List String := [{core_list}]

def main' : IO Unit := do
  let mut equal := 0
  let mut refused := 0
  let mut bad : Array String := #[]
  for v in vectors do
    match b2.lookup v.id with
    | none => bad := bad.push s!"MISSING {{v.id}}"
    | some r =>
      if core.contains v.mnemonic then
        match r with
        | some i =>
          if i == v.instr then equal := equal + 1
          else bad := bad.push s!"UNEQUAL {{v.id}}\\n    b2   {{repr i}}\\n    want {{repr v.instr}}"
        | none => bad := bad.push s!"REFUSED-IN-CORE {{v.id}}"
      else
        match r with
        | none => refused := refused + 1
        | some _ => bad := bad.push s!"ACCEPTED-OUTSIDE-CORE {{v.id}} ({{v.mnemonic}})"
  for b in bad do IO.println b
  IO.println s!"B2-SELFTEST {name}: {{equal}} core EQUAL · {{refused}} non-core REFUSED · {{bad.size}} BAD · of {{vectors.length}}"
  if bad.size > 0 then throw (IO.userError "B2 selftest RED")

#eval main'
""")
    r = subprocess.run([sys.executable, os.path.join(HERE, "lean_route.py"), "lean", lean],
                       capture_output=True, text=True, cwd=ROOT)
    for l in r.stdout.splitlines():
        if l.startswith(("B2-SELFTEST", "UNEQUAL", "MISSING", "REFUSED-IN-CORE", "ACCEPTED-", "    ")):
            print(l)
    for msg in pre["refused_core"][:40]:
        print(f"  refusal detail: {msg}")
    if r.returncode != 0 and "B2-SELFTEST" not in r.stdout:
        print(r.stdout[-3000:], r.stderr[-3000:])
    return r.returncode, pre


def translate_arms():
    """Planted inputs, each with its REQUIRED verdict — the parser's own red side.
    A selftest over the corpus can only fail on shapes the corpus contains; these
    are the refusals and parses it cannot show."""
    arms = [
        # (what, addr, n, text, expected: Lean text, or 'REFUSED')
        ("xchg is outside the core", 0, 3, "xchgq %rax, (%rbx)", "REFUSED"),
        ("adc is outside the core, though x86lean models it", 0, 3, "adcq %rcx, %rax", "REFUSED"),
        ("a string move is not movsx", 0, 2, "movsq %ds:(%rsi), %es:(%rdi)", "REFUSED"),
        ("an SSE movq is not mov", 0, 5, "movq %xmm0, %rax", "REFUSED"),
        ("crc32 (SSE4.2) is REFUSED — the TRANSLATE ordering rule's case", 0, 5,
         "crc32b %cl, %eax", "REFUSED"),
        ("a nop is outside the core", 0, 1, "nop", "REFUSED"),
        ("lock with no memory operand", 0, 4, "lock addq %rcx, %rax", "REFUSED"),
        ("suffix vs register disagreement", 0, 3, "addq %ecx, %eax", "REFUSED"),
        ("GNU unsuffixed, size from the register", 0x10, 3, "add    %rcx,%rax",
         "⟨.bin .add .q (.reg .rax false) (.reg .rcx false), 3⟩"),
        ("a d-width negative immediate is taken MODULO 2^32", 0, 3, "andl $-0x1, %ecx",
         "⟨.bin .and .d (.reg .rcx false) (.imm (0x00000000ffffffff#64)), 3⟩"),
        ("a backward jcc", 0x20, 2, "jne 0x10 <loop>",
         "⟨.jcc .ne (0xffffffffffffffee#64), 2⟩"),
        ("a GNU backward jcc (no 0x)", 0x20, 2, "jne    10 <loop>",
         "⟨.jcc .ne (0xffffffffffffffee#64), 2⟩"),
        ("the CRC table read: a base-less scaled index", 0x12, 7,
         "xorl 0x3000(,%rcx,4), %eax",
         "⟨.bin .xor .d (.reg .rax false) (.mem { base := none, index := (some .rcx), scale := .s4, "
         "disp := (0x0000000000003000#64), ripRel := false, seg := none, lock := false }), 7⟩"),
        # ⚠️ ADDED AFTER A MUTANT THAT DROPPED `lock` PASSED EVERY ARM ABOVE (the
        # corpus caught it, 9 of 9; the parser's own arms did not).
        ("LLVM's own-line lock, joined, lands on the Ea", 0, 3, "lock incl (%rbx)",
         "⟨.un .inc .d (.mem { base := (some .rbx), index := none, scale := .s1, "
         "disp := (0x0000000000000000#64), ripRel := false, seg := none, lock := true }), 3⟩"),
        ("a shift by one with no count", 0, 3, "shrq %rax",
         "⟨.shift .shr .q (.reg .rax false) (.imm8 (0x01#8)), 3⟩"),
    ]
    bad = 0
    for what, a, n, t, want in arms:
        try:
            got = translate(a, n, t)
        except Refused:
            got = "REFUSED"
        ok = got == want
        bad += not ok
        print(f"  {'✔' if ok else '✘'} {what}" + ("" if ok else f"\n      got  {got}\n      want {want}"))
    return bad, len(arms)


E2E_ASM = """\t.text
\t.globl f
f:\txorl %eax, %eax
1:\tmovzbl (%rdi), %ecx
\ttestb %cl, %cl
\tje 2f
\taddl %ecx, %eax
\tincq %rdi
\tjmp 1b
2:\tretq
"""


def translate_e2e(tmp):
    """`translate` end to end on a routine that is NOT a benchmark problem: the
    byte sum of a NUL-terminated string.  Assembled, translated at --base, then
    ELABORATED and RUN by x86lean to the value Python computes.  Then the two
    refusals the translate mode owes: a non-core instruction (rc 3) and an
    unlinked object that needs a layout decision (a data section)."""
    bad = 0
    s, o, lean = (os.path.join(tmp, x) for x in ("e2e.s", "e2e.o", "E2E.lean"))
    open(s, "w").write(E2E_ASM)
    subprocess.run(["clang", "-target", "x86_64-unknown-linux-gnu", "-c", s, "-o", o], check=True)
    me = [sys.executable, os.path.abspath(__file__), "translate"]
    r = subprocess.run(me + [o, "--base", "0x1000", "--namespace", "E2E", "--out", lean],
                       capture_output=True, text=True)
    if r.returncode != 0:
        print(f"  ✘ translate refused a core-only routine:\n{r.stdout}{r.stderr}")
        return 1, 3
    msg = b"x86lean"
    want = sum(msg)
    with open(lean, "a") as f:
        f.write(f"""
def putBytes (m : Mem) (a : BitVec 64) : List Nat → Mem
  | [] => m
  | b :: bs => putBytes (m.write a (BitVec.ofNat 8 b)) (a + 1) bs

def e2eStart : Cpu :=
  let m := putBytes {{}} 0x2000 {list(msg) + [0]}
  let m := m.writeN 0x8000 0x9999 8
  let c : Cpu := {{ rip := 0x1000, mem := m }}
  let c := c.setReg .q .rdi 0x2000
  c.setReg .q .rsp 0x8000

#eval let r := runP E2E.prog 200 e2eStart
  s!"E2E rip={{r.rip.toHex}} eax={{(r.getReg .d .rax).toNat}}"
""")
    r = subprocess.run([sys.executable, os.path.join(HERE, "lean_route.py"), "lean", lean],
                       capture_output=True, text=True, cwd=ROOT)
    got = re.search(r'E2E rip=(\w+) eax=(\d+)', r.stdout)
    ok = r.returncode == 0 and got and got.group(1).endswith("9999") and int(got.group(2)) == want
    bad += not ok
    print(f"  {'✔' if ok else '✘'} translate -> elaborate -> run: sum({msg!r}) = "
          f"{got.group(2) if got else '?'} (want {want}), returned to {got.group(1) if got else '?'}")
    if not ok:
        print(r.stdout[-2000:], r.stderr[-2000:])
    open(s, "w").write(E2E_ASM.replace("\taddl %ecx, %eax", "\tadcl %ecx, %eax"))
    subprocess.run(["clang", "-target", "x86_64-unknown-linux-gnu", "-c", s, "-o", o], check=True)
    r = subprocess.run(me + [o, "--base", "0x1000", "--out", os.devnull], capture_output=True, text=True)
    ok = r.returncode == 3 and "REFUSED-TRANSLATE" in r.stdout and "adcl" in r.stdout
    bad += not ok
    print(f"  {'✔' if ok else '✘'} a non-core instruction is REFUSED-TRANSLATE, rc 3, by name (rc {r.returncode})")
    open(s, "w").write(E2E_ASM + "\t.section .rodata\n\t.long 7\n")
    subprocess.run(["clang", "-target", "x86_64-unknown-linux-gnu", "-c", s, "-o", o], check=True)
    r = subprocess.run(me + [o, "--base", "0x1000", "--out", os.devnull], capture_output=True, text=True)
    ok = r.returncode == 1 and "link at the fixed layout first" in r.stderr
    bad += not ok
    print(f"  {'✔' if ok else '✘'} an unlinked object with a data section is refused, rc 1 (rc {r.returncode})")
    return bad, 3


def cmd_selftest():
    tools = disassemblers()
    if not tools:
        print("⛔ no objdump on this box — nothing was tested")
        return 2
    print(f"B2 front end, core = {len(CORE)} mnemonics; disassemblers: "
          + ", ".join(f"{n} ({p})" for n, p in tools))
    print("── the parser's planted arms (red side, no Lean) ──")
    bad, total = translate_arms()
    print(f"  {total - bad}/{total} arms as required")
    rc = 1 if bad else 0
    with tempfile.TemporaryDirectory(prefix="b2self-") as tmp:
        asm, obj = os.path.join(tmp, "v.s"), os.path.join(tmp, "v.o")
        r = subprocess.run(["lake", "env", ".lake/build/bin/x86lean-diff", "emit-asm", asm],
                           capture_output=True, text=True, cwd=ROOT)
        if r.returncode != 0:
            print(f"⛔ emit-asm failed (build first):\n{r.stdout}{r.stderr}")
            return 2
        r = subprocess.run(["clang", "-target", "x86_64-unknown-linux-gnu", "-c", asm, "-o", obj],
                           capture_output=True, text=True)
        if r.returncode != 0:
            print(f"⛔ clang refused the vector table:\n{r.stderr}")
            return 2
        mnems = _vector_mnemonics(tmp)
        ncore = sum(m in CORE_VEC_MNEMONICS for m in mnems.values())
        print(f"── the corpus: {len(mnems)} vectors, {ncore} in the core ──")
        if len(tools) < 2:
            print("  ⚠️ only ONE disassembler here; the other's text format is NOT exercised on this box")
        for name, tool in tools:
            lrc, pre = selftest_one(name, tool, obj, mnems, tmp)
            if lrc != 0:
                rc = 1
        print("── translate, end to end ──")
        ebad, etotal = translate_e2e(tmp)
        print(f"  {etotal - ebad}/{etotal} as required")
        if ebad:
            rc = 1
    print("B2 selftest: " + ("GREEN" if rc == 0 else "RED"))
    return rc


if __name__ == "__main__":
    sys.path.insert(0, HERE)
    a = sys.argv[1:]
    if a == ["--selftest"]:
        sys.exit(cmd_selftest())
    if a and a[0] == "translate":
        sys.exit(cmd_translate(a[1:]))
    print(__doc__.split("Usage:")[1].split("Exit codes")[0].rstrip())
    sys.exit(2)
