# The declared divergences, read off libLISA's processor-synthesized semantics — 2026-09-12

**Why this record exists (D221, `docs/TACAS-G1-POSITIONING.md` §1d).** Every entry in `Main.lean
knownDivergences` says the reference model (ACL2 x86isa) is wrong, and names K's rule file and the SDM as
the independent authorities that agree with x86lean. libLISA reports that K is itself wrong on 18–28
instruction variants per machine (D220), and neither authority is a processor. libLISA's semantics were
synthesized by executing instructions on five CPUs, so they are the one public source here whose origin is
hardware. This record reads the ten rules off them.
⚠️ Deliberately NOT named `DIFFERENTIAL-*.md` or `REFERENCE-PIN-RUN-*.md`: nothing here ran the differential
or the reference model, and those filename patterns are what the record-revision and batch-count gates read.

## What a libLISA dataflow says
Each output of an encoding carries the list of `inputs` that bit flips on the processor showed it to depend
on, and a synthesized computation over those inputs. **A byte absent from every output's inputs is a byte
the processor was observed not to read** (on the states libLISA sampled). That is the same one-bit probe that
isolated D108 against x86isa, taken on silicon.

## ⛔ The encodings x86lean tests are NOT in libLISA's population — the verdict is about a proxy
```
  CPU                        encodings   first byte 66 · F2 · F3   66 directly before 0F   controls: C4 · C5 · 0F
  amd-3900x                    118,025         0 ·  0 ·  0                   0              52,275 · 25,767 · 9,843
  amd-7700x                    118,019         0 ·  0 ·  0                   0              52,210 · 25,773 · 9,865
  i9-13900-e                   118,135         0 ·  0 ·  0                   0              52,515 · 25,773 · 9,861
  i9-13900-p                   117,605         0 ·  0 ·  0                   0              52,504 · 25,783 · 9,864
  intel-xeon-silver-4110       117,229         0 ·  0 ·  0                   0              52,168 · 25,801 · 9,750
```
(`liblisa-semantics-tool get <cpu>.json bitpatterns`, counted with `grep -c` on the leading byte; the encoding
count is the tool's own `Loaded N encodings`.) libLISA says so itself, §5.2.2 of its paper (liblisa.nl
rendering, read 2026-09-12): *"744 variants are out of enumeration scope for libLISA … Most variants in this
category are non-VEX versions of SSE/AVX instructions, which re-use the data size override prefix 66."*
⇒ `660ff1c1` (`psllw %xmm1,%xmm0`) and `660f6ec1` (`movd %ecx,%xmm0`) have no libLISA semantics on any machine.
What libLISA has is the **VEX.128 form of the same instruction** — `vpsllw %xmm1,%xmm0,%xmm0` = `c5f9f1c1` —
for which the SDM states the same count rule and the same low-half result. **A PASS below is a processor
reading of the RULE on that form. It is not a reading of the legacy encoding, and the VEX form differs from
it above bit 127** (VEX.128 zeroes the YMM upper half; the legacy form leaves it), which this check does not
look at.

## ⭐ And the scope discharges the owed K-verdict question without the container
The owed item (G1 §1d): are any of the K rules our divergences cite among the 18–28 variants libLISA
judged K incorrect on? **They cannot be.** All ten cited K files are the legacy forms
(`vendor/k-x86-64/semantics/registerInstructions/psllw_xmm_xmm.k` … `movq_xmm_r64.k`; K keeps the VEX forms in
separate files, e.g. `vpsllw_xmm_xmm_xmm.k`, `vmovd_xmm_r32.k`). A "Dasgupta et al. incorrect" verdict needs a
libLISA semantics to compare the K variant against, and no 66-prefixed encoding has one on any of the five
machines; libLISA files those variants as out of scope. ⇒ **Not a clearance of K. A statement that libLISA's
K comparison never reached these rules.** The Zenodo container (1.89 GB) would add only verdicts on the VEX
siblings, which nothing in the paper cites; its download was stopped and the partial file deleted.

## The check, verbatim
`python3 scripts/liblisa_hardware_check.py vendor/liblisa/*.check.jsonl` — exit 0, all five machines, unedited.
```
== amd-3900x.check.jsonl
  PASS ctl_imul               0fafc3      8 write targets
  PASS ctl_vpxor              c5f9efc1    xmm1 bytes 8..15 read: [8, 9, 10, 11, 12, 13, 14, 15]
  PASS ctl_legacy66_pxor      660fefc1    absent from the population
  PASS movd_to_x (vmovd)      c5f96ec1    xmm0[4..15]: 0 inputs, constant zero=True; rcx bytes into xmm0[0..3]: [0, 1, 2, 3]
  PASS movq_to_x (vmovq)      c4e1f96ec1  xmm0[8..15]: 0 inputs, constant zero=True; rcx bytes into xmm0[0..7]: [0, 1, 2, 3, 4, 5, 6, 7]
  PASS pslld_x (vpslld)       c5f9f2c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psllq_x (vpsllq)       c5f9f3c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psllw_x (vpsllw)       c5f9f1c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psrad_x (vpsrad)       c5f9e2c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psraw_x (vpsraw)       c5f9e1c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psrld_x (vpsrld)       c5f9d2c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psrlq_x (vpsrlq)       c5f9d3c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psrlw_x (vpsrlw)       c5f9d1c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  plants: 5 of 5 caught
== amd-7700x.check.jsonl
  PASS ctl_imul               0fafc3      8 write targets
  PASS ctl_vpxor              c5f9efc1    xmm1 bytes 8..15 read: [8, 9, 10, 11, 12, 13, 14, 15]
  PASS ctl_legacy66_pxor      660fefc1    absent from the population
  PASS movd_to_x (vmovd)      c5f96ec1    xmm0[4..15]: 0 inputs, constant zero=True; rcx bytes into xmm0[0..3]: [0, 1, 2, 3]
  PASS movq_to_x (vmovq)      c4e1f96ec1  xmm0[8..15]: 0 inputs, constant zero=True; rcx bytes into xmm0[0..7]: [0, 1, 2, 3, 4, 5, 6, 7]
  PASS pslld_x (vpslld)       c5f9f2c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psllq_x (vpsllq)       c5f9f3c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psllw_x (vpsllw)       c5f9f1c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psrad_x (vpsrad)       c5f9e2c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psraw_x (vpsraw)       c5f9e1c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psrld_x (vpsrld)       c5f9d2c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psrlq_x (vpsrlq)       c5f9d3c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psrlw_x (vpsrlw)       c5f9d1c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  plants: 5 of 5 caught
== i9-13900-e.check.jsonl
  PASS ctl_imul               0fafc3      12 write targets
  PASS ctl_vpxor              c5f9efc1    xmm1 bytes 8..15 read: [8, 9, 10, 11, 12, 13, 14, 15]
  PASS ctl_legacy66_pxor      660fefc1    absent from the population
  PASS movd_to_x (vmovd)      c5f96ec1    xmm0[4..15]: 0 inputs, constant zero=True; rcx bytes into xmm0[0..3]: [0, 1, 2, 3]
  PASS movq_to_x (vmovq)      c4e1f96ec1  xmm0[8..15]: 0 inputs, constant zero=True; rcx bytes into xmm0[0..7]: [0, 1, 2, 3, 4, 5, 6, 7]
  PASS pslld_x (vpslld)       c5f9f2c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psllq_x (vpsllq)       c5f9f3c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psllw_x (vpsllw)       c5f9f1c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psrad_x (vpsrad)       c5f9e2c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psraw_x (vpsraw)       c5f9e1c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psrld_x (vpsrld)       c5f9d2c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psrlq_x (vpsrlq)       c5f9d3c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psrlw_x (vpsrlw)       c5f9d1c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  plants: 5 of 5 caught
== i9-13900-p.check.jsonl
  PASS ctl_imul               0fafc3      12 write targets
  PASS ctl_vpxor              c5f9efc1    xmm1 bytes 8..15 read: [8, 9, 10, 11, 12, 13, 14, 15]
  PASS ctl_legacy66_pxor      660fefc1    absent from the population
  PASS movd_to_x (vmovd)      c5f96ec1    xmm0[4..15]: 0 inputs, constant zero=True; rcx bytes into xmm0[0..3]: [0, 1, 2, 3]
  PASS movq_to_x (vmovq)      c4e1f96ec1  xmm0[8..15]: 0 inputs, constant zero=True; rcx bytes into xmm0[0..7]: [0, 1, 2, 3, 4, 5, 6, 7]
  PASS pslld_x (vpslld)       c5f9f2c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psllq_x (vpsllq)       c5f9f3c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psllw_x (vpsllw)       c5f9f1c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psrad_x (vpsrad)       c5f9e2c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psraw_x (vpsraw)       c5f9e1c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psrld_x (vpsrld)       c5f9d2c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psrlq_x (vpsrlq)       c5f9d3c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psrlw_x (vpsrlw)       c5f9d1c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  plants: 5 of 5 caught
== intel-xeon-silver-4110.check.jsonl
  PASS ctl_imul               0fafc3      12 write targets
  PASS ctl_vpxor              c5f9efc1    xmm1 bytes 8..15 read: [8, 9, 10, 11, 12, 13, 14, 15]
  PASS ctl_legacy66_pxor      660fefc1    absent from the population
  PASS movd_to_x (vmovd)      c5f96ec1    xmm0[4..15]: 0 inputs, constant zero=True; rcx bytes into xmm0[0..3]: [0, 1, 2, 3]
  PASS movq_to_x (vmovq)      c4e1f96ec1  xmm0[8..15]: 0 inputs, constant zero=True; rcx bytes into xmm0[0..7]: [0, 1, 2, 3, 4, 5, 6, 7]
  PASS pslld_x (vpslld)       c5f9f2c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psllq_x (vpsllq)       c5f9f3c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psllw_x (vpsllw)       c5f9f1c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psrad_x (vpsrad)       c5f9e2c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psraw_x (vpsraw)       c5f9e1c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psrld_x (vpsrld)       c5f9d2c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psrlq_x (vpsrlq)       c5f9d3c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  PASS psrlw_x (vpsrlw)       c5f9d1c1    count-source xmm1 bytes read [0, 1, 2, 3, 4, 5, 6, 7]
  plants: 5 of 5 caught
```
The five blocks differ only in the imul control's write-target count (8 on the two AMD machines, 12 on the three
Intel ones); every other line is identical.
```
  rules decided      10 of 10 knownDivergences entries (8 D108 count width, 2 D93 clear-not-merge)
  machines           5 of 5 in libLISA's published semantics
  rule verdicts      50 PASS · 0 FAIL   (count: grep -cE 'PASS (mov[dq]_to|ps[a-z]+)_x ' on the block above)
  shift verdicts     40 PASS · 0 FAIL   (count: grep -cE 'PASS ps[a-z]+_x \(vp' on the block above)
```

## What each verdict tests, and what makes it specific
- **D108 (8 shifts).** The union of `xmm1` bytes over every `xmm0` output's inputs must be exactly bytes 0..7:
  the count is `SRC[63:0]`, and bytes 8..15 — the upper quadword whose single flipped bit changed x86isa's
  answer — are not read. x86isa's register path reads them; its memory path does not (D108 §3).
- **D93 (movd, movq).** `xmm0` above the moved width must be written from **no** input, and the constant
  written must be **zero**: CLEAR, not MERGE. The low bytes must read `rcx` at the moved width.
- **Controls.** `imul` (the example liblisa.nl links) must resolve, so an all-null run is refused as a broken
  instrument. The first query run had no such control: its positive control was the legacy-66 `pxor`, and it
  went null WITH the ten subjects (14 of 14 null) — which is what said the question was wrong, not the rules.
  `vpxor` must read `xmm1` bytes 8..15, so an upper-half read IS visible when it exists. The legacy-66 `pxor` must be absent, so the census above is re-checked per machine.
- **Plants (per machine, each must turn a PASS into a FAIL):** add `xmm1[8..15]` to a shift's inputs · add an
  input to `vmovd`'s upper bytes · strip `vpxor`'s upper-half inputs · a null record for a shift · a non-zero
  constant in `vmovq`'s byte 9. ⚠️ The last plant first went **uncaught**: it replaced the first
  `#x0000…` in the whole record, which is RIP's increment constant, not an `xmm0` byte. It is now planted in
  the byte's own computation.
- **Refusals (driven):** a `knownDivergences` entry added with no proxy → rc 2 · an entry renamed → rc 2 · a
  result file shorter than the query list → rc 2 · the unplanted control → rc 0.

## The ceiling, declared before the numbers (and what arrived)
Predicted: agreement with the SDM/K rule on all ten. Declared residue: some shifts might have failed synthesis
(libLISA reports 3–7 "libLISA incorrect" variants per machine against K, and 623–694 synthesis failures), and a
null is UNMEASURED, never agreement. **What arrived was not in the prediction:** the encodings asked about are
absent altogether, and the verdicts are on a proxy form. No shift failed synthesis on any machine.
⚠️ **A null from this tool is two states.** `server` prints `null` both when no encoding matches and when one
matches with an output whose synthesis failed (`liblisa-semantics-tool-0.3.0/src/server.rs`, the
`computation.is_none()` branch). The census above separates them for the legacy forms: no encoding exists.

## Recipe
```
  data     OSF project 2hfq9 (view-only link from github.com/liblisa/liblisa, cli/liblisa-semantics-tool/README.md):
           semantics.7z  67,338,371 B  sha256 da83bdac3f3ba4cb9e86335896d24f7fefa27b6b0f5cb7b1d14545e079753ff9
           five JSON files, 1.67 GB each, dated 2023-12-14 in the archive. OSF lists NO licence for the data
           (node_license null); libLISA's code is AGPLv3. Nothing from either is copied into this repository.
  tool     cargo +nightly install --root vendor/liblisa/tool liblisa-semantics-tool   (0.3.0; rustc 1.96.0-nightly)
           on this Mac it needed: Z3_SYS_Z3_HEADER=<homebrew>/include/z3.h, BINDGEN_EXTRA_CLANG_ARGS=-I<homebrew>/include,
           LIBRARY_PATH=<homebrew>/lib (z3 4.16.0), and an `llvm-ar` on PATH that execs Xcode's `ar` (xed-sys's build
           asks for llvm-ar by name; a symlink to /usr/bin/ar fails because that shim dispatches on argv[0])
  query    python3 scripts/liblisa_hardware_check.py --queries > q.txt
           liblisa-semantics-tool server --cache <cpu>.cache <cpu>.json < q.txt > <cpu>.check.jsonl
           (the first run per machine builds a ~590 MB cache in ~43 s; the tool then panics on the empty line at EOF
           with exit 101 AFTER answering — the check's line-count refusal is the gate, not that exit code)
  check    python3 scripts/liblisa_hardware_check.py vendor/liblisa/*.check.jsonl
```
