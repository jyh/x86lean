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

Locally, on an x86-64 machine:

```
cd hwprobe && python3 mk_rows.py > rows.h && cc -O1 -o probe probe.c sse_ops.S && ./probe
```

⚠️ On an arm64 Mac, `clang -arch x86_64` runs the probe under Rosetta 2. That is an emulator, so its agreement is
corroboration and never the referee's verdict.
