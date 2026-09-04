# P2 BATCH 3 — `movabs`, a batch that changes no semantics, and the harness defect its ten bytes exposed

**Forms.** P2 addition 3, the last of the Captain's three. Three vectors, one planted arm, **not one
line of `X86/Semantics.lean` changed**, and **no new roster row**: K files `mov r,imm` as one row
with six variants and `mov_ri` already claims it. What moves is what the model can execute —
**3,791 occurrences, 0.41% of the uncovered gap.**

```
cases=69144  matched=49258  explained=28774  unexplained=0  oracle-leaks=0  missing=0
  spec: 0   refusal: 0   harness: 0   undefined-region: 28774
804 vectors · 86 pre-states · 84 mnemonics · roster unchanged at 500/525
```

⭐ **And the two discriminating values are confirmed from the oracle's own output**, not inferred
from a green:

```
movabs_q           rax=1122334455667788     the full 64 bits, untruncated
movabs_lo32_ones   rax=00000000ffffffff     NOT sign-extended to all-ones
movabs_hi32_ones   rbx=ffffffff00000000     NOT zeroed by a 32-bit path
```

x86isa writes exactly the immediate. Either wrong decoder would show in one of the last two.

## 1. ⛔ What a green run here does NOT contain

`Operand.imm` has carried a full `BitVec 64` since P0, and the decoder is trusted to have performed
any extension (`TRUSTBASE.md`). So `movabsq $imm64, %r64` and `movq $imm32, %r64` reach `step` as
the **same shape with different values**, and no semantics distinguishes them. This is P1 batch
20's finding again — a shape the model could always express and had never been asked — and the
same discipline applies: the batch has to say what its green is not evidence for.

**It is not evidence about immediate extension**, because there is no extension in this model to be
wrong about.

## 2. What it IS evidence for, in order of what could go wrong

| | |
|---|---|
| **the length path** | ten bytes, the longest encoding in the table; `Instr.len` is a datum the model cannot check about itself, and a wrong one is a wrong RIP on every case |
| **the decode-trust boundary** | two values no 32-bit immediate can sign-extend to, so the one plausible wrong decoder is caught |
| **the demand** | 3,791 occurrences, measured, not argued |

The two discriminating values are the whole test: `0x00000000ffffffff` is what a 32-bit `-1`
sign-extends **from**, and `0xffffffff00000000` has zero low bits. A decoder that re-derived the
value through the `imm32` path writes all-ones for the first and zero for the second.

**The arm, and its arithmetic is the receipt:**

```
movabs re-derives its immediate through the imm32 path
  caught — 164 disagreement(s) in `rax`, total unexplained 246
  164 = 2 vectors x 82 states (movabs_q, movabs_lo32_ones -> rax)
   82 = 1 vector  x 82 states (movabs_hi32_ones          -> rbx)
  246 = all three, and NOTHING else
```

⭐ **The 164/246 split is what says the claim below is true rather than hoped
for.** Every other `mov …, imm` vector in the table carries `0x5a`, `0x1234` or
`0x12345678` — all positive and below 2³¹ — so truncate-and-sign-extend is
identity on them, and the totals show exactly three vectors moving.

⚠️ **The arm is keyed on the VALUE, not on `i.len`.** Truncate-and-sign-extend is IDENTITY on every
immediate that fits in a signed 32 bits — every other `mov r,imm` vector in the table — so the arm
fires on exactly the three whose values cannot be reached by extending anything. Keying on the
length would have planted a defect in the decoder's output rather than in a model of it.

## 3. ⛔⛔ And the length path is where the finding was (D83)

`check_encodings.py` parsed objdump's byte column as `(?:[0-9a-f]{2} )+` — each byte followed by a
**space**. objdump pads that column, so for every instruction this repository had ever carried the
final byte was followed by padding. **Ten bytes fills the column exactly**, and the final byte
abuts the **tab** before the mnemonic:

```
  0: 48 b8 88 77 66 55 44 33 22 11	movabsq $0x1122334455667788, %rax
                              ^^ read as 9 bytes, not 10
```

The gate fired — `model says len=10, assembler says 9` — **because the model was right**.

⇒ 🔑 **A HARNESS THAT TRUNCATES ITS OWN READING CANNOT SEE A MODEL THAT TRUNCATES THE SAME WAY.**
Had the model claimed 9, the two would have agreed and the gate would have been green about a wrong
length. Latent since P0; only the first form wide enough to fill the column could expose it.

⚠️ **The class, not just the instance:** a parser that has only ever seen padded input has not been
tested on unpadded input, and column-filling is a property of the WIDEST datum. The widest datum is
where a column parser gets its first real test.
