# hwprobe — the x86-64 referee for sub-group B's SDM-pinned rows

Some rows of the soft-float commission's sub-group B are pinned in the kernel **against the SDM**, where the
reference model (ACL2 x86isa) disagrees (`docs/DECISIONS.md` D265, D266). This directory runs those rows on a
**processor**, so that "the SDM says" is checked against silicon and not only against a manual.

| file | role |
|---|---|
| `sse_ops.S` | one function per instruction under test, in assembly, so the executed bytes are the declared ones |
| `mk_rows.py` | the rows and their expectations, derived from stated rules; `--plant` / `--plant-op` build the controls |
| `ref_mul.py` | the independent multiply reference (D262), exact rational arithmetic |
| `probe.c` | runs each row with MXCSR loaded from it, and compares the result and the sticky flags |
| `rows_on_x86isa.py` + `run_case_mx.lisp` | the same rows on x86isa, for the comparison column |

The job is `.github/workflows/hwprobe.yml`. It prints the processor it ran on and then runs two controls. A wrong
expectation must fail exactly one row (exit 1), and a wrong instruction byte must refuse the run (exit 2). Only then
does it run the referee.

The packed forms (B5, D281) read all 128 bits: each takes both quadwords of each operand and returns an `unsigned
__int128`, because the scalar load zeroes bits 127:64 and a packed instruction would compute lanes no row declares.
They carry their own two controls (`--plant-packed` flips a bit of a HIGH quadword; `--plant-pop` a packed instruction
byte), since a plant in a scalar row says nothing about the 128-bit comparison.

**The integer path (D330)** is a second program beside the SSE one, sharing nothing with it: `int_ops.S` (one function per
ADCX/ADOX/MULX form; general-purpose registers and RFLAGS in and out), `mk_int_rows.py` (the rows, derived from the SDM's
rules), `int_probe.c` (reads CPUID leaf 7 and refuses without BMI2 and ADX, refuses unless each instruction's bytes at its
`_at` label are the declared ones, then compares the destinations and the six arithmetic flags). It has its own two controls
(`--plant`, `--plant-op`). `mk_int_anchors.py` pins the MULX rows in `Tests/Anchors.lean`: x86isa refuses MULX, so those rows
are the only check of the model's MULX numbers. ADCX/ADOX rows are read here too, and are carried by the differential vectors.

**D334 (W1c)** adds ANDN, BEXTR, BLSMSK, BLSR, BZHI, PDEP, PEXT, RORX and MOVNTI on the same path — x86isa refuses all
nine, so every one of their 888 rows is pinned, generated into a module of its own, `Tests/AnchorsBmi.lean`, so it is metered as its own kernel unit. Three things are new:
the probe also requires BMI1 and SSE2 (CPUID.(7,0):EBX bit 3, CPUID.1:EDX bit 26) and refuses without them; each row
carries a FLAG MASK — the six arithmetic flags less those the SDM leaves undefined for the form (AF/PF, and SF for BEXTR) —
and the probe compares only those while printing all six, so each leg's readings of the undefined bits are on record; and
a third control, `--plant-new`, flips a DEFINED flag (ZF) in a masked row (`andnq_rr_zero`), which must red exactly that
row. MOVNTI's destination is memory: the probe reads the quadword back after SFENCE.

| file | role |
|---|---|
| `int_ops.S` | one function per integer form under test (register conventions in its header) |
| `mk_int_rows.py` | the integer rows and their expectations; `--plant` / `--plant-op` / `--plant-new` build the controls |
| `int_probe.c` | runs each integer row and compares GPRs and RFLAGS |
| `mk_int_anchors.py` | the MULX rows and (D334) the W1c rows as Lean pins, with `--check` / `--selftest` |

**The bit-string path (D333)** is a third program, sharing nothing with the other two: `bitstr_ops.S` (one function per
`bt{,s,r,c}{w,l,q} %{cx,ecx,rcx},(%rbx)` form), `mk_bitstr_rows.py` (2944 rows, derived from the SDM's bit-string rule: the
register offset is signed at the operand size, and the bit is `offset AND 7` of the byte at `EA + (offset SAR 3)`), and
`bitstr_probe.c`, which fills a 16 KiB buffer from the generator's PATTERN, overrides the one addressed byte, runs the row, and
compares CF, ZF and the WHOLE buffer. Beside each row it prints whether the processor also matched ACL2 x86isa's rule (bit
`(mod (abs offset) 8)`), which differs for negative offsets; that column is a reading, not the verdict. Controls: `--plant`
(CF), `--plant-mem` (one row expects x86isa's byte), `--plant-stray` (a write outside the watched byte), `--plant-op`.

| file | role |
|---|---|
| `bitstr_ops.S` | one function per bit-string form (register conventions in its header) |
| `mk_bitstr_rows.py` | the rows, PATTERN and both rules' expectations; `--summary [--rows]` prints the counts and the per-row table |
| `bitstr_probe.c` | runs each row and compares CF, ZF and the whole buffer; prints the x86isa-rule agreement count |

**The shuffle path (D336, V1b)** is a fourth program, sharing nothing with the other three: `shuf_ops.S` (one function per
form and imm8 of PSHUFB, PALIGNR, PINSRD, PINSRQ, PEXTRD and PEXTRQ, legacy SSE), `mk_shuf_rows.py` (220 rows, derived from the
SDM's rules), and `shuf_probe.c`, which reads CPUID.1:ECX and refuses without SSSE3 or SSE4.1, refuses unless each function's bytes
are the declared ones, and compares ALL 128 bits of XMM0, all of RAX and the six arithmetic flags (none is written) on every row.
x86isa refuses all six mnemonics, so every row is pinned in `Tests/AnchorsShuf.lean` (a metered module of its own) by `mk_shuf_anchors.py`. Controls: `--plant`
(bit 64 of row 0's expected XMM0), `--plant-op` (a declared byte), `--plant-zx` (bit 32 of one PEXTRD row's expected RAX: the
zero-extension is compared).

| file | role |
|---|---|
| `shuf_ops.S` | one function per shuffle form and imm8 (register conventions in its header) |
| `mk_shuf_rows.py` | the rows and their expectations; `--plant` / `--plant-op` / `--plant-zx` build the controls |
| `shuf_probe.c` | runs each row and compares XMM0, RAX and RFLAGS |
| `mk_shuf_anchors.py` | the rows as Lean pins, with `--check` / `--selftest` |

**The packed-integer arithmetic path (D335, V1a)** is a fifth program, sharing nothing with the other four:
`simda_ops.S` (one function per form — PMADDWD, PMADDUBSW, PMULLW, PMULHRSW, PMULUDQ, PADDSW, PSUBUSW, PSUBUSB, PMAXSW,
PSADBW, PACKSSDW, each at `%xmm1,%xmm0` and at a 16-byte-aligned `(%rbx),%xmm0`), `mk_simda_rows.py` (396 rows, 18 per
form: edge-lane crosses, uniform extremes and seeded random values, derived from each instruction's SDM Operation), and
`simda_probe.c`, which reads CPUID.1 and refuses without SSE2 or SSSE3, refuses unless the declared bytes are the assembled
ones, and compares ALL 128 bits of %xmm0 plus %xmm1, the m128 source and the six arithmetic flags unchanged. x86isa refuses
all eleven mnemonics, so every row is pinned (`mk_simda_anchors.py`, generated into a module of its own, `Tests/AnchorsSimd.lean`, so it is metered as its own kernel unit).

D373 adds SET B beside it (`mk_simda_rows.py --set-b`: PMINSW, PMULHW, PMULHUW, PAVGB, 144 rows, the rules and the row
construction shared with set A, its own seeds): `simdb_ops.S`, the same `simda_probe.c` compiled against `simdb_rows.h`,
and its pins in `Tests/AnchorsSimdB.lean` (`mk_simda_anchors.py --set-b`). x86isa refuses all four (D373, P1).
Controls: `--plant` (bit 64 of row 0's expectation) and `--plant-op`; `--reach` counts the rows on which one named wrong
rule per mnemonic disagrees with the right one (it must be non-zero).

| file | role |
|---|---|
| `simda_ops.S` | one function per packed-integer form (register conventions in its header) |
| `mk_simda_rows.py` | the rows and their expectations; `--plant` / `--plant-op` build the controls; `--summary`, `--reach` |
| `simda_probe.c` | runs each row and compares all 128 bits of the destination, the sources and RFLAGS |
| `mk_simda_anchors.py` | the rows as Lean pins, with `--check` / `--selftest` |

**The SHA-NI path (D338, V2)** is a sixth program, sharing nothing with the other five: `sha_ops.S` (one function per
form — SHA256MSG1, SHA256MSG2, SHA256RNDS2, each at `%xmm2,%xmm1` and at a 16-byte-aligned `(%rbx),%xmm1`; the
destination is `%xmm1` because `%xmm0` is SHA256RNDS2's implicit operand), `mk_sha_rows.py` (148 rows: per form 16 edge
rows over single bits at every σ/Σ rotate and shift boundary, 6 seeded random rows, and known-answer rows from FIPS
180-4's "abc" and 448-bit examples whose expectations come from a TEXTBOOK SHA-256 — message schedule and 64 rounds,
its K and H0 derived from the prime roots — held to the published digests by `--selftest`, so an operand-order misreading
cannot pass by symmetry), and `sha_probe.c`, which reads CPUID.(EAX=07H,ECX=0):EBX bit 29 and refuses without SHA-NI
with its OWN exit code, 3 (`--cpuid` stops there), refuses unless the declared bytes are the assembled ones, and compares
ALL 128 bits of %xmm1 plus %xmm2, the m128, %xmm0 and the six arithmetic flags unchanged. ⚠️ `macos-15-intel`'s i7-8700B
has no SHA-NI: the workflow accepts exit 3 on that label only, prints it, and runs no SHA control or referee there; a 3
on any other leg fails. x86isa refuses all three mnemonics, so every row is pinned (`mk_sha_anchors.py`, into a module of
its own, `Tests/AnchorsSha.lean`). Controls: `--plant` (bit 64 of row 0's expectation), `--plant-op`, and `--plant-wk`
(one SHA256RNDS2 row's expectation computed with WK from %xmm0's HIGH quadword); `--reach` counts the rows on which one
named wrong rule per mnemonic disagrees with the right one.

| file | role |
|---|---|
| `sha_ops.S` | one function per SHA-NI form (register conventions in its header) |
| `mk_sha_rows.py` | the rows, the textbook SHA-256 and the KAT; `--plant` / `--plant-op` / `--plant-wk`; `--summary`, `--reach`, `--selftest` |
| `sha_probe.c` | runs each row and compares all 128 bits of the destination, the sources, %xmm0 and RFLAGS |
| `mk_sha_anchors.py` | the rows as Lean pins, with `--check` / `--selftest` |

**The AES-NI / CLMUL / VEX path (D342, V4)** is a seventh program, sharing nothing with the other six: `aes_ops.S` (one
function per form and imm8 — AESENC and AESENCLAST at `%xmm2,%xmm1` (legacy SSE), and VAESENC, VAESENCLAST, VPCLMULQDQ,
VPSHUFB, VPALIGNR at `%xmm2,%xmm1,%xmm3` and VPSLLDQ, VPSRLDQ at `%xmm1,%xmm3` (VEX.128); YMM1-3 are loaded WHOLE, every
upper half seeded non-zero, and read back whole), `mk_aes_rows.py` (207 rows: edge, seeded random and known-answer rows —
FIPS-197 Appendix B and C.1 round by round through `aesenc` ×9 + `aesenclast`, and the five PCLMULQDQ test vectors of
Gueron and Kounavis's Intel CLMUL white paper — whose expectations come from a TEXTBOOK AES-128 (its S-box derived from
the GF(2^8) inverse, its own key expansion) and a TEXTBOOK carry-less product, held to the published values by
`--selftest`; `--refuse-wrong` shows `build` refusing MixColumns on the last round, PCLMULQDQ's selectors read as
imm8[1:0], and MixColumns before ShiftRows), and `aes_probe.c`, which reads CPUID.01H:ECX (AES, PCLMULQDQ, AVX, OSXSAVE)
and XCR0 and refuses without them with exit 3 — accepted on NO leg, since D342 predicts every runner has all three —
refuses unless the declared bytes are the assembled ones, and compares all 256 bits of the destination's YMM register
(a VEX form must zero bits 255:128, a legacy one keep them), the other two registers' 256 bits and the six arithmetic
flags. x86isa refuses all nine mnemonics, so every row is pinned (`mk_aes_anchors.py`, into `Tests/AnchorsAes.lean`).
Controls: `--plant` (bit 64 of row 0's expectation), `--plant-op`, and `--plant-hi` (one VEX row's expectation with the
destination's upper half NOT zeroed).

| file | role |
|---|---|
| `aes_ops.S` | one function per AES-NI / CLMUL / VEX form and imm8 (register conventions in its header) |
| `mk_aes_rows.py` | the rows, the textbook AES-128 and CLMUL and the KATs; `--plant` / `--plant-op` / `--plant-hi`; `--summary`, `--reach`, `--refuse-wrong`, `--selftest` |
| `aes_probe.c` | runs each row and compares all 256 bits of YMM1-3 and RFLAGS |
| `mk_aes_anchors.py` | the rows as Lean pins, with `--check` / `--selftest` |

**The VEX.128/VEX.256 twin path (D345, V7)** is an eighth program, sharing nothing with the other seven:
`vexsil_ops.S` (76 functions: one per form, length and imm8 — VSHUFPS imm, VPSRAD and VPSRAW with an xmm count and with
an imm8, VADDPS, VSUBPS, VMULPS, VPUNPCKLWD, VPUNPCKHWD, VPUNPCKLBW, VPACKUSWB at `%ymm2,%ymm1,%ymm3` and VPMOVMSKB at
`%ymm1,%eax`, each at VEX.128 and VEX.256: 26 encodings), `mk_vexsil_rows.py` (503 rows, derived from the SDM's rules and
written down in its docstring with the four places the SDM was read by its pseudo-code; every row is computed TWICE, by a
rule over 128-bit integers with floating point by exact rationals and by a textbook reading the flat pseudo-code over
bytes with floating point by integer significands and explicit round/sticky bits, and `build` REFUSES any row where they
differ; `--selftest` also holds both FP references to the host's IEEE binary32 at round-to-nearest; `--refuse-wrong`
shows `build` refusing D345's four wrong rules, each on a named row: the count taken per lane, the high lane's FP flags
dropped, VPMOVMSKB's lanes swapped, VSHUFPS's imm8 applied across lanes), and `vexsil_probe.c`, which reads CPUID.01H:ECX
(AVX, OSXSAVE), XCR0 and CPUID.(7,0):EBX (AVX2) and refuses without them with exit 3, refuses unless the declared bytes
are the assembled ones, and compares all 256 bits of YMM3 (a VEX.128 form must zero bits 255:128; a VEX.256 form writes
them with the high lane's result), all 64 bits of RAX (VPMOVMSKB's destination, upper bits zero), all 32 bits of MXCSR
(the six sticky flags OR'ed over every lane for the three FP forms, with RC rotated through all four modes; unchanged
otherwise), YMM1 and YMM2 whole and the six arithmetic flags. Every YMM3 upper half is seeded random and non-zero, and so
are the sources' at VEX.128. x86isa refuses all 26 encodings (D345 P1). Controls: `--plant` (bit 128 of one VEX.256 row's
expectation, `vshufps256_1b_p0`), `--plant-op`, and `--plant-hi` (one VEX.128 row, `vpackuswb128_edge0`, expecting the
destination's upper half kept); `--reach` counts the rows each wrong rule, and D345's two red-backwards mutants, disagree on.

| file | role |
|---|---|
| `vexsil_ops.S` | one function per VEX twin, length and imm8 (register conventions in its header) |
| `mk_vexsil_rows.py` | the rows, the rule and the textbook; `--plant` / `--plant-op` / `--plant-hi`; `--summary`, `--reach`, `--refuse-wrong`, `--selftest` |
| `vexsil_probe.c` | runs each row and compares all 256 bits of YMM1-3, RAX, MXCSR and RFLAGS |

**The second VEX-twin path (D348, V8b)** is a ninth program, sharing nothing with the other eight: `vexsilb_ops.S` (8
functions: VPMADDWD, VPMULHRSW, VPMADDUBSW and VPACKSSDW at `%ymm2,%ymm1,%ymm3`, each at VEX.128 and VEX.256),
`mk_vexsilb_rows.py` (66 rows, derived from the SDM's rules and written down in its docstring with the three places the
SDM was read by its pseudo-code; every row is computed TWICE, by a per-lane rule over 128-bit integers and by a textbook
reading the flat pseudo-code over bytes, and `build` REFUSES any row where they differ; `--refuse-wrong` shows `build`
refusing D348's four wrong rules, each on a named row: VPMADDUBSW's signedness swapped, VPACKSSDW packed across lanes,
VPMULHRSW without its rounding increment, VPMADDWD saturating where it wraps), and `vexsilb_probe.c` (V7's probe,
restated), which compares all 256 bits of YMM3, YMM1 and YMM2 whole, RAX and MXCSR (both unchanged: the four forms are
integer) and the six arithmetic flags. x86isa refuses all 8 encodings (D348 P1). Controls: `--plant` (bit 128 of
`vpackssdw256_lane`'s expectation), `--plant-op`, and `--plant-hi` (`vpmaddwd128_edge0`, expecting the destination's upper
half kept); `--reach` counts the rows each wrong rule and D348's two red-backwards mutants disagree on, and `--selftest`
asserts each mutant reds exactly the rows it reaches.

| file | role |
|---|---|
| `vexsilb_ops.S` | one function per VEX twin and length (register conventions in its header) |
| `mk_vexsilb_rows.py` | the rows, the rule and the textbook; `--plant` / `--plant-op` / `--plant-hi`; `--summary`, `--reach`, `--refuse-wrong`, `--selftest` |
| `vexsilb_probe.c` | runs each row and compares all 256 bits of YMM1-3, RAX, MXCSR and RFLAGS |

**The VEX memory-operand path (D350, V8c)** is a tenth program, sharing nothing with the other nine, and the first VEX path
with a MEMORY operand: `vexsilc_ops.S` (12 functions: VPBROADCASTD from `%xmm2` and from `(%rbx)`, and VPMADDWD, VPMULHRSW,
VPMADDUBSW and VPACKSSDW at `(%rbx),%ymm1,%ymm3`, each at VEX.128 and VEX.256), `mk_vexsilc_rows.py` (168 rows) and
`vexsilc_probe.c`. Each row carries a 64-byte buffer and an offset; PRE pushes RBX (callee-saved), points it at
`&mem[off]` and POST pops it. **Every memory case runs twice, with the same operand, at offset 0 and at an ODD offset**
(unaligned for every operand size), so VEX's no-fault-on-misalignment rule is read on silicon, not assumed. The twins'
per-lane function and its independent textbook are D348's, imported from `mk_vexsilb_rows.py`; the memory operand is
extracted twice here (one big integer sliced, a byte list sliced), and `build` refuses any row where they differ.
`--refuse-wrong` refuses D350's four wrong rules on named rows: VPBROADCASTD taking dword 1, a VEX.256 memory twin's high
lane read from bytes 15:0, the memory operand taken as SRC1 (VPMADDUBSW's signedness), and an m32 broadcast read as 64
bits. The probe compares YMM1-3, RAX, MXCSR, RFLAGS and **all 64 bytes of the buffer**. x86isa refuses all 12 encodings
(D350 P1). Controls: `--plant` (`vpmaddwd256_m_lane_u`, an UNALIGNED VEX.256 memory row), `--plant-op`, `--plant-hi`
(`vpbroadcastd128_m_k1_a`). ⚠️ **Limit: the buffer comparison has no planted control.** A planted write would need a
second instruction, so "memory is never written" is compared on every row but has not been shown able to fail.

| file | role |
|---|---|
| `vexsilc_ops.S` | one function per form and length; RBX = `&mem[off]` (register conventions in its header) |
| `mk_vexsilc_rows.py` | the rows; the memory operand extracted two ways; `--plant` / `--plant-op` / `--plant-hi`; `--summary`, `--reach`, `--refuse-wrong`, `--selftest` |
| `vexsilc_probe.c` | runs each row and compares YMM1-3, RAX, MXCSR, RFLAGS and the 64-byte buffer |

**The VEX move path, with FAULT ROWS (D354, V9b)** is an eleventh program, sharing nothing with the others:
`vexsild_ops.S` (24 functions: VMOVDQA VMOVDQU VMOVAPS VMOVUPS VMOVAPD VMOVUPD, each at VEX.128 and VEX.256, a load
`(%rbx) -> %ymm3` and a store `%ymm2 -> (%rbx)`), `mk_vexsild_rows.py` (126 rows, 30 of them FAULT rows) and
`vexsild_probe.c`. The buffer is 32-byte aligned, so a row's address alignment is its offset's. **A fault row is an
aligned kind off its width's alignment (16 bytes at VEX.128, 32 at VEX.256), and it must raise #GP:** the probe installs
a SIGSEGV/SIGBUS handler that `siglongjmp`s back to the caller, records the signal, restores MXCSR (POST never ran), and
requires the buffer unchanged. Offset 16 is placed on purpose: it must RUN at VEX.128 and FAULT at VEX.256 for the aligned
kinds, and RUN at both for the unaligned ones. A store row carries its expected 64-byte buffer. `--refuse-wrong` refuses
D354's four wrong rules on named rows (a VEX.128 load keeping YMM3's upper half, a VEX.256 load's high lane from bytes
15:0, the VEX.256 alignment taken as 16, a VEX.256 store writing 16 bytes). Controls, each reding exactly its row:
`--plant` (a value bit), `--plant-op` (a declared byte; the run refuses, exit 2), `--plant-nf` (an unaligned kind
expected to fault), `--plant-a0` (an aligned kind at offset 0 expected to fault) and `--plant-f` (a fault row expected to
run). ⚠️ **x86isa executes every fault row's encoding (D354 P1) and so does Rosetta 2** (measured on yukon 2026-10-23: 96 of
96 value rows agree and all 30 fault rows RUN), so neither can stand in for a processor here.

| file | role |
|---|---|
| `vexsild_ops.S` | one function per move, length and direction; RBX = `&mem[off]` (register conventions in its header) |
| `mk_vexsild_rows.py` | the rows, the rule and the textbook (alignment from two expressions); five plants; `--summary`, `--reach`, `--refuse-wrong`, `--selftest` |
| `vexsild_probe.c` | runs each row under a signal catch and compares YMM1-3, RAX, MXCSR, RFLAGS, the 64-byte buffer, and fault vs run |

**The VEX memory forms of the silicon rows (D361, V10)** are a twelfth program on V8c's memory path, restated:
`vexsile_ops.S` (22 functions: VPSHUFB and VPALIGNR imm8 ∈ {0, 5, 16, 20, 33} at `(%rbx),%xmm1,%xmm3`; VADDPS VSUBPS
VMULPS VPSRAD VPUNPCKLWD VPUNPCKHWD VPUNPCKLBW VPACKUSWB at VEX.128 and VEX.256), `mk_vexsile_rows.py` (356 rows) and
`vexsile_probe.c` (V8c's probe with its header and rows changed). The register rules and their textbooks are D345's
(`mk_vexsil_rows.py`) and D342's (`mk_aes_rows.py`, PSHUFB/PALIGNR, given a byte-list textbook here); the memory operand
is extracted twice, and every memory case runs at offset 0 and at an odd offset. **VPSRAD's memory operand is its COUNT,
16 bytes at both lengths** (the VEX.256 form's count operand is `xmm3/m128`). D345's FP and VPSRAD cases are THINNED
for the memory twin: one rounding mode per FP case group, every flag row, and VPSRAD's edge counts. `--refuse-wrong`
refuses D361's five wrong rules on named rows. x86isa refuses all 16 encodings measured (D361 P1). Controls: `--plant`
(`vmulps256_m_hionly_IE_a`), `--plant-op`, `--plant-hi` (`vpshufb128_m_ident_a`). ⚠️ The buffer comparison has no planted
control, as V8c's.

| file | role |
|---|---|
| `vexsile_ops.S` | one function per form, length and imm8; RBX = `&mem[off]` |
| `mk_vexsile_rows.py` | the rows; the memory operand extracted two ways; `--plant` / `--plant-op` / `--plant-hi`; `--summary`, `--reach`, `--refuse-wrong`, `--selftest` |
| `vexsile_probe.c` | runs each row and compares YMM1-3, RAX, MXCSR, RFLAGS and the 64-byte buffer |

**VEX `vmovd`/`vmovq` between an XMM register and a GPR or memory (D371)** are a thirteenth program on V10's path:
`vexsilf_ops.S` (8 functions: r → xmm, xmm → r, m → xmm, xmm → m, at 32 and 64 bits, all VEX.128),
`mk_vexsilf_rows.py` (72 rows) and `vexsilf_probe.c`. Every value is derived twice (an integer rule, a byte-list
textbook); YMM3's upper half is seeded nonzero so the VEX zeroing is read; every memory case runs at offset 0 and at an
odd offset. **The probe compares the buffer with an EXPECTED buffer**, because the two store forms write it, and
`--plant-mem` flips a bit just past one store's bytes: the buffer comparison's own control, which V8c's and V10's lack.
`--refuse-wrong` refuses D371's four wrong rules on named rows. x86isa refuses all 8 encodings (D371 P1). Controls:
`--plant` (`vmovd_ld_ones_a`), `--plant-op`, `--plant-hi` (`vmovq_gx_ones_r`), `--plant-mem` (`vmovd_st_ones_u`).

| file | role |
|---|---|
| `vexsilf_ops.S` | one function per form and width; RBX = `&mem[off]` |
| `mk_vexsilf_rows.py` | the rows, both references; four plants; `--summary`, `--reach`, `--refuse-wrong`, `--selftest` |
| `vexsilf_probe.c` | runs each row and compares YMM1-3, RAX, MXCSR, RFLAGS and the buffer against the expected buffer |

Locally, on an x86-64 machine:

```
(cd hwprobe && python3 mk_rows.py > rows.h && cc -O1 -o probe probe.c sse_ops.S && ./probe)
(cd hwprobe && python3 mk_int_rows.py > int_rows.h && cc -O1 -o int_probe int_probe.c int_ops.S && ./int_probe)
(cd hwprobe && python3 mk_bitstr_rows.py > bitstr_rows.h && cc -O1 -o bitstr_probe bitstr_probe.c bitstr_ops.S && ./bitstr_probe)
(cd hwprobe && python3 mk_shuf_rows.py > shuf_rows.h && cc -O1 -o shuf_probe shuf_probe.c shuf_ops.S && ./shuf_probe)
(cd hwprobe && python3 mk_simda_rows.py > simda_rows.h && cc -O1 -o simda_probe simda_probe.c simda_ops.S && ./simda_probe)
(cd hwprobe && python3 mk_sha_rows.py > sha_rows.h && cc -O1 -o sha_probe sha_probe.c sha_ops.S && ./sha_probe)
(cd hwprobe && python3 mk_aes_rows.py > aes_rows.h && cc -O1 -o aes_probe aes_probe.c aes_ops.S && ./aes_probe)
(cd hwprobe && python3 mk_vexsil_rows.py > vexsil_rows.h && cc -O1 -o vexsil_probe vexsil_probe.c vexsil_ops.S && ./vexsil_probe)
(cd hwprobe && python3 mk_vexsilb_rows.py > vexsilb_rows.h && cc -O1 -o vexsilb_probe vexsilb_probe.c vexsilb_ops.S && ./vexsilb_probe)
(cd hwprobe && python3 mk_vexsilc_rows.py > vexsilc_rows.h && cc -O1 -o vexsilc_probe vexsilc_probe.c vexsilc_ops.S && ./vexsilc_probe)
(cd hwprobe && python3 mk_vexsild_rows.py > vexsild_rows.h && cc -O1 -o vexsild_probe vexsild_probe.c vexsild_ops.S && ./vexsild_probe)
```

⚠️ On an arm64 Mac, `clang -arch x86_64` runs the probe under Rosetta 2. That is an emulator, so its agreement is
corroboration and never the referee's verdict. Rosetta hides AVX and AVX2 from CPUID unless the environment carries
`ROSETTA_ADVERTISE_AVX=1`; without it `vexsil_probe` (and `aes_probe`) refuse with exit 3. Run the binary as
`/usr/bin/arch -x86_64 ./vexsil_probe` and check that `/usr/bin/arch -x86_64 /usr/bin/uname -m` prints `x86_64`.
