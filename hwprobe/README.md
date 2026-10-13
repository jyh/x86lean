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

Locally, on an x86-64 machine:

```
(cd hwprobe && python3 mk_rows.py > rows.h && cc -O1 -o probe probe.c sse_ops.S && ./probe)
(cd hwprobe && python3 mk_int_rows.py > int_rows.h && cc -O1 -o int_probe int_probe.c int_ops.S && ./int_probe)
(cd hwprobe && python3 mk_bitstr_rows.py > bitstr_rows.h && cc -O1 -o bitstr_probe bitstr_probe.c bitstr_ops.S && ./bitstr_probe)
(cd hwprobe && python3 mk_shuf_rows.py > shuf_rows.h && cc -O1 -o shuf_probe shuf_probe.c shuf_ops.S && ./shuf_probe)
```

⚠️ On an arm64 Mac, `clang -arch x86_64` runs the probe under Rosetta 2. That is an emulator, so its agreement is
corroboration and never the referee's verdict.
