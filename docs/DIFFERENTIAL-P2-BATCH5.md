# P2 BATCH 5 — the first vector SEMANTICS: sixteen forms that make the channel non-vacuous

**Forms.** `movdqa` / `movdqu` register-to-register, and the eleven packed integer operations
`paddb/w/d/q`, `psubb/w/d/q`, `pxor`, `pand`, `por`. Sixteen vectors, 13 new mnemonics, **no memory
forms**.

```
cases=70520  matched=50634  explained=28774  unexplained=0  oracle-leaks=0  missing=0
820 vectors · 86 pre-states · P1 roster unchanged at 500/525 (SIMD is excluded from it by derivation)
```

⚠️ **The arithmetic is the first check, not the verdict.** 16 new vectors × 86 pre-states = 1,376
new cases; `matched` rose by exactly 1,376 and `explained` did not move at all. That is the right
shape — a packed integer operation has no undefined bits, so nothing new can land in the
undefined-region class — but it is also what a run would look like if the new fields were not being
compared, which is why the batch is sealed on its ARMS and not on this table.

## 1. What this batch makes true that was not

Batch 4 built the sixteen-register channel and proved, narrowly and honestly, that it **transports**
a value. It could not prove anything **flowed** through it, because no instruction in the roster
could write a vector register — so by D27 the comparator was watching sixteen constants and
reporting agreement about them.

These are the first instructions in this model that write XMM.

## 2. ⛔ The finding: an arm that did not fire

`wrongVmovFixedRegisters` — every `movdqa`/`movdqu` moves xmm1 into xmm0 whatever it encodes — was
**NOT CAUGHT** against the first fourteen vectors:

```
⛔ movdqa/movdqu ignore their register fields: comparator reported ZERO unexplained
   disagreements against a KNOWN-WRONG model. The comparator does not work.
```

Both `vmov` vectors moved xmm1 into xmm0, so a model that ignored the register fields entirely was
**bit-identical** to this one on every vector in the table. `Op.vmov`'s operand decoding was tested
by nothing, and `unexplained=0` said nothing about it.

⚠️ **The arm's own comment claimed it was covered**, by `paddd_x2x3` — a `.vbin`, which cannot
exercise `vmov`'s operands at all. A pairing asserted in prose, and false.

⇒ 🔑 **ASK WHAT A PREDICTED GREEN DOES NOT CONTAIN** (P1 batch 20's rule, in the vector wave).
`movdqa_x4x5` and `movdqu_x4x5` exist because the arm failed; the pairing is proven **by that
failure** — the arm did not fire before they existed and fires in 164 cases after.

⚠️ Then it was caught **in the wrong field** — 328 disagreements, none in the declared `xmm2`,
because the new vectors write `xmm4`. The arm demands the disagreement in the field the bug is in,
and that precision turned a green into a correction.

## 3. ⚠️ The arm that could have passed silently

A wrong **lane width** is invisible unless a lane actually carries across its boundary. If every xmm
lane in the pre-state pattern were small, `paddd` and `paddq` would agree everywhere and the run
would report agreement about a rule it never tested.

| arm | caught in |
|---|---|
| a packed add/subtract uses 64-bit lanes whatever the mnemonic says | **355** cases (`xmm0`) |
| `psub` computes SRC − DEST | **328** cases (`xmm0`) |
| `movdqa`/`movdqu` ignore their register fields | **164** cases (`xmm4`) |
| a packed operation writes ZF | **696** cases (`zf`) |

So batch 4's deliberately non-zero, non-constant pre-state pattern **does** exercise the lane
boundary. The adds and the bitwise trio are commutative and cannot see the operand order, which is
why that is a separate arm.

## 4. What is NOT claimed

No memory form. They need a 128-bit memory path — `readMem`/`writeMem` are defined at `Size`, which
stops at 64 — **and** they are where `movdqa` and `movdqu` stop being the same instruction, since an
unaligned `movdqa` is #GP. That is a semantic question of its own and it gets its own batch.

The P1 roster's 500/525 does not move: it excludes an `xmm` operand **by derivation**, so these
mnemonics claim no row in it and are counted against the P2 roster. See D90.
