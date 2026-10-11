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

| file | role |
|---|---|
| `int_ops.S` | one function per integer form under test (register conventions in its header) |
| `mk_int_rows.py` | the integer rows and their expectations; `--plant` / `--plant-op` build the controls |
| `int_probe.c` | runs each integer row and compares GPRs and RFLAGS |
| `mk_int_anchors.py` | the MULX rows as Lean pins, with `--check` / `--selftest` |

Locally, on an x86-64 machine:

```
(cd hwprobe && python3 mk_rows.py > rows.h && cc -O1 -o probe probe.c sse_ops.S && ./probe)
(cd hwprobe && python3 mk_int_rows.py > int_rows.h && cc -O1 -o int_probe int_probe.c int_ops.S && ./int_probe)
```

⚠️ On an arm64 Mac, `clang -arch x86_64` runs the probe under Rosetta 2. That is an emulator, so its agreement is
corroboration and never the referee's verdict.
