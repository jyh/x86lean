# O95 — the x86lean lowering spike over appendix A.4 (paris)

PRIVATE, LOCAL-ONLY. No remote. The router exhibit is unpublished O94 content: nothing here enters public x86lean
until O94 is published. x86lean is used as a library, pinned to a PUBLIC master sha.

Object: vir `cd64c9fd` (frozen); inputs and predictions: vir `8a73bc8c` (I1–I6, P1–P5). Read only `object/`,
`errata/`, `inputs/`, `predictions/` of vir. Never `vir/lean/`, never mojave's tree (the fence).

## Shape 1 (priced @[bus]): per-program translation validation against `X86.runP`

Two programs and two results.

1. **A.4 AS WRITTEN**, with E1's repaired form (vir's errata row: `LEA ACL_BITMAP(%rip),%r9` + `BT %r8,0(%r9,%rcx,8)`)
   and I6's exit convention. **P5's reading is a WITNESS per defect**, each a `decide`d (or `#eval`-pinned) run:
   - E2: `len = 2^63` (rsi's sign bit set). `CMP $24,%rsi; JLT` takes drop_truncated, while F's guard `len ≥ 24` passes.
   - E3: tokens = 0 reaches drop_rate_limited, but `SUB $1, BUCKET_ARR(%rdx,%rcx,4)` has already written −1 into the
     cell, while I6 requires memory unchanged on every drop exit.
   P5 is FALSIFIED if a refinement proof goes through with E2 or E3 as written. A witness is a positive reading;
   a failed proof alone is not.
2. **A.4 REPAIRED**: `JB` for E2, and for E3 the bucket tested before it is written (`CMPL $0, BUCKET_ARR(…)`;
   `JLE drop_rate_limited`; then `SUBL $1, …`), plus `SUB $24,%rsi` for I6 (E5's repaired form, per vir). The theorem:
   under I6's preconditions (topic < 64; buffer · ACL table · bucket array · code pairwise disjoint), `runP` reaches
   exactly one of the four exits, and the exit and final state are F's (I4) under I6's convention.

## The AST mapping (x86lean `X86/Syntax.lean`, checked at master `4a0d64a`)

| A.4 line | x86lean `Op` |
|---|---|
| `CMP $24,%rsi` | `.bin .cmp .q (.reg .rsi) (.imm 24)` |
| `JLT …` / repaired `JB …` | `.jcc .l d` / `.jcc .b d` |
| `MOV 0(%rdi), λ%eax` | `.mov .l (.reg .rax) (.mem {base := some .rdi})` (a 32-bit write zero-extends) |
| `CMP $0x4D534731,%eax` | `.bin .cmp .l (.reg .rax) (.imm 0x4D534731)` |
| `JNE …` | `.jcc .ne d` |
| `MOV 4(%rdi),λ%ecx` · `MOV 8(%rdi),λ%r8d` | `.mov .l …` with `disp := 4` / `8` |
| `LEA ACL_BITMAP(%rip),λ%r9` (E1 repair) | `.lea .q .r9 {ripRel := true, disp := ACL}` |
| `BT %r8,0(%r9,%rcx,8)` (E1 repair) | `.bit .bt .q (.mem {base := some .r9, index := some .rcx, scale := .s8}) (.reg .r8)` (D331's bit-string form) |
| `JNC …` | `.jcc .ae d` |
| `SUB $1,BUCKET_ARR(%rdx,%rcx,4)` | `.bin .sub .l (.mem {base := some .rdx, index := some .rcx, scale := .s4, disp := BUCKET}) (.imm 1)` |
| `LEA 24(%rdi),λ%rax` | `.lea .q .rax {base := some .rdi, disp := 24}` |
| exits | a branch to a label OUTSIDE the program: `runP` stops there, and the exit is `rip = label` at the stop |

⚠️ **A MODEL QUESTION THIS RAISES, CHECKED BEFORE ANY PROOF:** `Ea` carries `ripRel` AND `index`, so the AST can SPELL
E1's unencodable `ACL_BITMAP(%rip,%rcx,8)`. Does `Ea.addr` honour an index when `ripRel` is set, and does the decoder
ever produce that shape? If the semantics accepts it silently, x86lean has its own copy of E1, a spellable form no
encoding produces (the `vloadq` reason). Measure it, and file it in x86lean (public, no router content) if so.

## Steps, each a commit here

1. Lakefile: `require x86lean from git "<public url>" @ "<sha>"`, built through `saltbuild` (never bare lake).
2. `Router/AsWritten.lean`: the 14+1 instructions as a `Program` at fixed addresses, the exit labels, and the two
   witnesses (E2, E3) by `decide`.
3. `Router/Repaired.lean`: the repaired program and its refinement theorem, using `X86/Logic.lean`'s `Spec` kit
   (`seq`, `cc_direction_pinned`, `AgreeOutside` for the one write).
4. Silicon (optional, Shape 1 (d)): assemble the repaired routine and run it at the boundaries on the hwprobe pattern.
   That would be a PRIVATE run, so it is not hwprobe.yml, which lives in public x86lean. Price it separately.
