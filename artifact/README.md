# x86lean — artifact for the CAV 2027 tool paper

This artifact is the x86lean repository at the commit the paper is pinned to, packaged as a `linux/amd64` Docker
image. The image contains the Lean toolchain the repository names, and the reference model the differential
validation runs against, already built: ACL2 at commit `c8897a34`, with the `x86isa` books certified. Everything in it
comes from public sources. Nothing in it needs a credential.

## What it reproduces

| Paper claim | Command (inside the container) | Expected output |
|---|---|---|
| The whole Lean tree builds | `bash artifact/measure.sh` | `lake-build rc=0 … lean_errors=0`, "Build completed successfully (85 jobs)" |
| The axiom gate passes (the policy is in `TRUSTBASE.md`) | `bash scripts/axiom_gate.sh` | its CLEAN line, with the declaration count it read. ⚠️ Not yet run inside the image. |
| The differential validation (Sect. 4.1) | `bash artifact/measure-diff.sh` | the main-table line, below |
| Every published figure re-derives at its commit | `python3 scripts/check_claims.py` | `check_claims: CLEAN`. ⚠️ Not yet run inside the image. It needs the repository's full history, because it re-derives each figure at the commit it names, and the image currently gets a shallow checkout. |

The main-table line the differential step must print, which is the record the paper cites
(`docs/DIFFERENTIAL-P2-BATCH45.md`):

```
cases=109208 matched=85692 explained=34407 unexplained=0 oracle-divergence=835 oracle-leaks=0 missing=0
```

`measure-diff.sh` first runs the whole suite, which has 132,176 cases (the main table, its VEX twins, and the further
tables). It then splits out the main table, the population the paper counts, using the method the records state
(`artifact/main_table.py`). That split's compare exits 1 for one expected reason: the declared VEX.256 divergences fall
outside the main table, so they do not occur in it. The script prints them by name.

## Host requirements

- **Architecture:** an x86-64 host runs the image natively. On Apple silicon or another ARM host, Docker runs it under
  amd64 emulation, which is slower by a factor not yet measured.
- **Memory:** 8 GB is enough. The largest single process measured 2.75 GB.
- **Cores:** 2 or more. The times below were measured on 4 cores, with Lean limited to 2 threads.
- **Disk:** about 1.6 GB for the compressed image, and several times that once it is loaded.
- **Network:** none after the image is loaded.

## Per-step times

Measured on a hosted GitHub `ubuntu-latest` runner (4 cores, 16 GB) with `LEAN_NUM_THREADS=2`.

| Step | Time |
|---|---|
| `docker load` of the image | not yet measured |
| Cold Lean build (`artifact/measure.sh`) | 5–8 min (5:13, 5:42 and 7:48 over three runs) |
| The full differential with its main-table split (`artifact/measure-diff.sh`) | 15–19 min (900 and 1108 s; about 9 min of that is the kernel-cost readings at the end, which are not a verdict) |
| Building the image from source, if you choose to | 30–34 min, of which 27–31 is certifying x86isa (two runs) |

The whole reproduction takes well under the call's 8-hour bound, so no reduced subset is provided: the artifact runs
everything.

## What it does not reproduce, and why

- **The processor probe (Sect. 5.3).** `hwprobe/` runs rows derived from the manual on real AMD and Intel processors.
  That needs those processors, so a reviewer on another machine cannot rerun it. What the artifact does check: the probe
  rows are in the repository, and `decide` checks the model against the same rows
  inside the Lean build above, so that part runs on any host.
- **Timing figures.** Kernel-cost readings depend on the machine. The ones the paper quotes name the machine they were
  taken on.

## Running it

```
docker load < x86lean-artifact.tar.gz
docker run --rm x86lean-artifact bash artifact/measure.sh
docker run --rm x86lean-artifact bash artifact/measure-diff.sh
```
