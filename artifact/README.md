# x86lean — artifact for the CAV 2027 tool paper

This artifact is the x86lean repository at the commit the paper is pinned to, packaged as a `linux/amd64` Docker
image. The image contains the Lean toolchain the repository names, and the reference model the differential
validation runs against, already built: ACL2 at commit `c8897a34`, with the `x86isa` books certified. Everything in it
comes from public sources. Nothing in it needs a credential.

## What it reproduces

| Paper claim | Command (inside the container) | Expected output |
|---|---|---|
| The whole Lean tree builds | `bash artifact/measure.sh` | `lake-build rc=0 … lean_errors=0`, "Build completed successfully (85 jobs)" |
| The axiom gate passes (the policy is in `TRUSTBASE.md`) | `bash scripts/axiom_gate.sh` | its CLEAN line, with the declaration count it read (6,212 at the pin; 32 s on a built tree; in a fresh container it builds first, 176 s in the clean-machine read) |
| The differential validation (Sect. 4.1) | `bash artifact/measure-diff.sh` | the main-table line, below |
| Every published figure re-derives at its commit | `python3 scripts/check_claims.py` | `check_claims: CLEAN` (3 s). It needs the repository's full history, because it re-derives each figure at the commit it names; the image carries it. |

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

- **Architecture:** an x86-64 host runs the image natively. On Apple silicon or another ARM host, Docker runs it under amd64 emulation. Under QEMU on a 4-core arm64 machine the cold
  Lean build took 1 h 21 min and 1 h 26 min in two runs, more than ten times the native time. The differential under emulation has not been measured,
  and Docker Desktop's Rosetta path on Apple silicon has not been measured either.
- **Memory:** 8 GB is enough. The largest single process measured 2.75 GB.
- **Cores:** 2 or more. The times below were measured on 4 cores, with Lean limited to 2 threads.
- **Disk:** about 1.6 GB for the compressed image, and several times that once it is loaded.
- **Network:** none after the image is loaded.

## Per-step times

Measured on a hosted GitHub `ubuntu-latest` runner (4 cores, 16 GB) with `LEAN_NUM_THREADS=2`.

| Step | Time |
|---|---|
| `docker load` of the image (1.59 GB compressed) | 29–41 s |
| Cold Lean build (`artifact/measure.sh`) | about 5–8 min on the native runs measured (5:01 to 8:00, the slowest in the clean-machine read, run 44017099389); 1 h 21 min and 1 h 26 min under QEMU on arm64 |
| The full differential with its main-table split (`artifact/measure-diff.sh`) | 15–27 min (the script's own total read 900, 1042, 1050, 1108 and 1572 s over five runs). Most of the spread is in two stages: the Lean build it starts with (307 s and 477 s in the last two runs) and the kernel-cost readings at the end (510 s and 750 s), which are not a verdict. A step still printing `MEASURE diff-stage` lines has not hung. |
| Building the image from source, if you choose to | 27–34 min, of which 25–31 is certifying x86isa (three runs; the deposited image took 27.2 min, 24.6 of it certifying) |

The whole reproduction takes well under the call's 8-hour bound, so no reduced subset is provided: the artifact runs
everything.

## What it does not reproduce, and why

- **The processor probe (Sect. 5.3).** `hwprobe/` runs rows derived from the manual on real AMD and Intel processors.
  That needs those processors, so a reviewer on another machine cannot rerun it. What the artifact does check: the probe
  rows are in the repository, and `decide` checks the model against the same rows
  inside the Lean build above, so that part runs on any host.
- **Timing figures.** Kernel-cost readings depend on the machine. The ones the paper quotes name the machine they were
  taken on.

## Getting the image

The image is one file, `x86lean-artifact.tar.gz` (1,586,592,248 bytes), with this SHA-256:

```
623837b23c3d452bb8ca598cfa4ac87317ae171a00e2e97cf81874d9a70d4a08
```

- **Archive (permanent):** the artifact's Zenodo record, which the paper's Data Availability section cites. The DOI is
  assigned when the record is deposited, and this line will then give it.
- **Provenance:** the file was built by `.github/workflows/artifact-image.yml`, run 44050927744, at commit `8ae2028` (the merge that put `artifact/` on `master`).
  That run keeps the same file as its artifact `x86lean-artifact` until 2026-11-24 09:53 UTC, and downloading it needs a GitHub login. GitHub serves it as a zip around the tarball: unzip it, then check the tarball's SHA-256.

Check the file before loading it: `sha256sum x86lean-artifact.tar.gz` must print the line above.

## Running it

```
docker load < x86lean-artifact.tar.gz
docker run --rm x86lean-artifact bash artifact/measure.sh
docker run --rm x86lean-artifact bash artifact/measure-diff.sh
```
