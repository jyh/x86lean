# P2 BATCH 7 — `movd`/`movq` across the register files, and a defect in the oracle

**Forms.** Rank 4 (`movq`, 3.05%) and rank 8 (`movd`, 2.05%) of the measured demand list — the
highest-demand forms this model did not have, and the first here whose two operands live in
**different register files**. Three vectors shipped; **two were written, run, and removed**, and that
removal is the batch.

```
cases=71208  matched=51322  explained=28774  unexplained=0  oracle-leaks=0  missing=0
828 vectors · 86 pre-states · P1 roster unchanged at 500/525
```

## 1. The first run went RED, and the model was right

```
159 unexplained `spec` disagreements, in exactly two vectors:
  movd_to_x   81 of 86        movq_to_x   78 of 86

movd_to_x/18  lean=…000000aaaaaaaa  oracle=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
movd_to_x/14  lean=…00000000000000  oracle=00000001000000000000000100000000
```

The oracle preserved the destination's upper bits and wrote only the low 32 or 64. **ACL2 x86isa
merges where the specification says clear** — and that is precisely the wrong model this batch had
*already planted as an arm*, which fired in 151 cases against the Lean side.

## 2. ⭐ K settled it

`vendor/k-x86-64`, public and already relied on for both rosters:

```
movd r32 -> xmm :  concatenateMInt( mi(96, 0), extractMInt(R1, 32, 64) )
movq r64 -> xmm :  concatenateMInt( mi(64, 0), getParentValue(R1) )
movq xmm -> xmm :  concatenateMInt( mi(64, 0), extractMInt(R1, 192, 256) )
```

Zero bits, then the datum. SDM Vol. 2B: `DEST[127:32] ← 0`.

⇒ 🔑 **THE THIRD SOURCE IS WHAT TURNS A DISAGREEMENT INTO A FINDING.** With two models a red run says
only *"one of you is wrong"*, and the tempting reading — the oracle carries 500 roster rows of
credibility — is the wrong one here.

⚠️ **The defect is directional**, which sharpens it: x86isa gets `movq %xmm1,%xmm0` right and both
out-of-XMM directions right. Failing exactly two of five is the signature of a specific defect, not
of vagueness — so the other three stay and remain differentially validated.

## 3. What it costs

The two into-XMM vectors are removed; the semantics stay, carried by
`vmovg_to_xmm_zeroes_upper`. **The arm that guarded them is removed with them** — with no vector it
could never fire again, and an arm no vector can distinguish is a false entry in the gate's inventory
(D91), not a weak test.

⚠️ This repository now has **two** rules its oracle cannot check — the `movdqa` alignment fault (D91,
oracle *incomplete*) and this one (oracle *wrong*). Both proved; neither differentially validated.
**Removing a vector stops the test permanently and silently**: if x86isa is fixed tomorrow, nothing
notices.

⭐ Both point at the same next mechanism: a **declared known-divergence channel**, carrying its
third-source citation and gated in *both* directions so it fires when the divergence disappears. Not
done here — it changes `classify`, and that deserves its own red-first batch.

## 4. What survives

| arm | caught in |
|---|---|
| `movq xmm,xmm` copies all 128 bits instead of zeroing the upper quadword | 76 (`xmm0`) |
| `movd` out of XMM does not zero-extend its 32-bit GPR write | 35 (`rcx`) |

⭐ Out of XMM needed **no code**: `Cpu.setReg` already zero-extends at `.d`, and that the rule applies
unchanged across a register-file boundary is why there is nothing to read here.

⚠️ Neither fires in all 82 of its cases, and that is **correct**: the adversarial list contains zeros,
and where the bits a wrong model fails to clear were already zero the models genuinely agree. A count
equal to the case count would have been the suspicious reading. See D93.
