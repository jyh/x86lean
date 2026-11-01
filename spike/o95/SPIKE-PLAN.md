# O95 — the x86lean lowering spike over appendix A.4 (paris)

⚖️ PUBLISHED 2026-11-01 (council ask 2, his words "I'd like to publish today to establish precedent"), as `spike/o95/` on a branch of public x86lean. The paragraph below is as written while the spike was private.

PRIVATE, LOCAL-ONLY (until 2026-11-01). No remote. The router exhibit is unpublished O94 content: nothing here enters public x86lean
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

## The E1 model question, ANSWERED 2026-11-01 00:2x (read at x86lean `4a0d64a`, `X86/Semantics.lean:52`)
`Ea.offset` is `if ea.ripRel then nextRip + ea.disp else base + index·scale + disp`. **A `ripRel` Ea silently DROPS
`base` and `index`**, so the AST spells E1's unencodable form and the model computes RIP+disp from it, never refusing.
The decoder cannot produce that shape from bytes. A hand-written `Program` can, and this spike is one. Filed in x86lean
as its own item (STATUS-paris row 45): a well-formedness rule, `ripRel → base = none ∧ index = none`, enforced where it
binds (a refusal in `step`, or a decidable predicate the program theorems carry), red-first. The spike states the
as-written program with E1's REPAIRED form, so it does not depend on the fix.

## Step 2 READING (2026-11-01 00:4x; x86lean pinned at public `b1848ac`, built through saltbuild, EXIT=0)
- `ok_control` (16 steps, OK path): stops at emit_slice 0x103b with rax = b0+24, rsi = len−24, and the cell 5 → 4.
  It is PROVED FIRST, so the witnesses are not artifacts of a misplaced program.
- `e2_witness`: len = 2^63 stops at drop_truncated 0x1038, and 2^63 ≥ 24 unsigned (F's guard passes).
- `e3_witness`: tokens = 0 stops at drop_rate_limited 0x103a with the cell 0 → 0xFFFFFFFF.
- Axioms: all three `[propext, Quot.sound]`, from the same audit log as its EXIT=0.
- RED BACKWARDS: the two REFINEMENT statements (`e3_refines`: the cell unchanged on the drop exit; `e2_refines`:
  drop_truncated not taken) were driven as mutants in an audit file. `decide` PROVED EACH FALSE (EXIT=1, 2 errors).
⇒ **P5 HELD, positively:** A.4 as written is not a refinement on E2 or E3, and each failure has a concrete,
kernel-checked counterexample. The theorems took 347 ms, so the fast build was checked by the mutants, not trusted.
NEXT: step 3, `Router/Repaired.lean` (JB; the bucket tested before it is written) and the ∀-state refinement.

## Step 3's specification: vir's `F_exit` (offered 2026-11-01 00:44, @[bus]; read at vir HEAD, `lean/VIR/Exit.lean`)
vir proved F's meaning as an exit relation (`F_exit`, and `U_exit` for the unfused SPEC composition, so a refinement
against it is a refinement against the specs). Its imports are `VIR.Deep` and `VIR.Core`, with no mathlib. The toolchain
is the same v4.32.0-rc1. **Import it as a lake path dependency on vir's tree, PINNED to a vir sha**; do not copy it, or a
copy drifts from the object's meaning.
- Mapping (vir's): TRUNCATED ↔ drop_truncated · UNAUTH_OR_RATE ↔ drop_unauthorized OR drop_rate_limited (I6 splits F's
  one code) · OK ↔ emit_slice with rax = b0+24, rsi = len−24, the bucket cell decremented.
- **OWED BY THE SPIKE, the bridge:** vir's `Val` is abstract (wire bytes via `ByteArray.get!`, tokens as `Int`,
  principal and topic as `UInt32`). Step 3 states an abstraction relation from x86lean's `Cpu` (rdi/rsi/rdx, the
  buffer's bytes, the ACL bytes, the bucket dword as a SIGNED 32-bit count) to `F`'s inputs, and proves the repaired
  program's exit and final state satisfy `F_exit` under it.
- The fence: vir rules this file is the OBJECT's meaning, not the Lean arm's method, so reading it compares nothing.
  The spike still reads nothing else under `vir/lean/`.

## Step 3 READING (2026-11-01 ~07:0x PST; x86lean public `b1848ac`, vir `ba6f3fc` pinned; saltbuild EXIT=0)
**`Router.Refines.repaired_refines` IS PROVED, for every start state, on [propext, Classical.choice, Quot.sound]**
(`audit/axioms-step3.log`: the `sorryAx` control fires in the same log; 0 `sorry`, 0 tagged errors in the build).
It states: under the abstraction (`BufRel` buffer bytes · `AclRel` bit t%8 of the byte at ACL+8p+t/8 · `StRel` σ p = x86lean's
`Value.sval .d` of the dword at rdx+4p+0x3000 · len = rsi UNSIGNED) and I6's precondition as used (topic < 64; the buffer disjoint
from the bucket array), there is an n at which `runP repaired n s` has STOPPED and `Exit` holds of vir's
`den acl (F (.slice buf off len) (.state σ))`: TRUNCATED → 0x1040, memory unchanged · UNAUTH_OR_RATE → 0x1041 or 0x1042, memory
unchanged · OK → 0x1043, rax = rdi+24, rdx kept, len−24 = rsi, the payload slice's bytes at rax, the decremented state at the
cells, and memory = exactly one dword written. `F_exit` is IMPORTED (lake git dependency pinned to vir's sha), not copied.
- Layer 1 (`Router.Paths`): 16 per-address step lemmas + the stop; five exit paths (3 · 6 · 11 · 13 · 17 steps) ∀ states.
- Layer 2 (`Router.Refines`): the dword bridge (vir `rd` = x86lean `readSize .d`, by a 64-case bit lemma), the magic/ACL/sign
  bridges, read-back, the signed decrement without wrap, and the disjointness of distinct senders' cells.
- RED BACKWARDS: E2 restored (`jb` → `jl`, its concrete control removed so the ∀ proof is reached) ⇒ `Router.Paths` fails at
  `path_truncated` and `prefix_magic`, exactly the two places the length guard is read. The E3 order was NOT driven as a mutant
  here (step 2's witness already refutes it); declared.
- FINDINGS: (1) I6's "code disjoint" is VACUOUS in x86lean (a Program is not in memory) and is not assumed. (2) the ACL table
  needs no disjointness (read before the one write). (3) x86lean's pack lacked reg,imm and mem,imm cmp/sub and bit-string bt;
  they are proved here (spike-private), a candidate for the public pack (no router content in them).
