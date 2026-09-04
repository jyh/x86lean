# P2 BATCH 6 — the vector MEMORY forms, and the rule the oracle cannot check

**Forms.** `movdqa`/`movdqu` load and store at a memory operand, plus one **unaligned** `movdqu`
load. Five vectors, no new mnemonics — and the point at which `movdqa` and `movdqu` stop being the
same instruction.

```
cases=70950  matched=51064  explained=28774  unexplained=0  oracle-leaks=0  missing=0
825 vectors · 86 pre-states · P1 roster unchanged at 500/525
```

5 new vectors × 86 pre-states = 430 new cases; `matched` rose by exactly 430 and `explained` did not
move.

## 1. ⛔ The measurement that shaped the batch

An unaligned `movdqa` is **#GP(0)** in hardware (SDM Vol. 2B). Before writing a vector for it, the
oracle was asked — by execution:

```
movdqa (%rbx),%xmm0   @0x2000 aligned        -> executed
movdqa 8(%rbx),%xmm0  @0x2008 UNALIGNED      -> executed      ⛔
movdqu 8(%rbx),%xmm0  @0x2008 unaligned      -> executed
movdqa %xmm0,8(%rbx)  @0x2008 UNALIGNED      -> executed      ⛔
movl %ecx,(%rbx)      (control)              -> executed
```

**ACL2 x86isa does not implement the alignment check.**

⇒ 🔑 **THE ORACLE IS EVIDENCE, NOT THE SPECIFICATION.** Batch 18 found the SDM *wrong* twice and
followed x86isa and K against it. Here the arrow reverses: the oracle is **incomplete**. Following it
would make this model compute a result where silicon faults — the direction TRUSTBASE exists to
prevent.

So the model faults (`byDesign`, the class that means *"this model says: it faults"*), **and no
unaligned `movdqa` vector is shipped** — one would be a one-sided refusal in all 86 pre-states, which
`classify` correctly counts UNEXPLAINED, turning a right model into a red run.

## 2. What carries the rule instead

| theorem | claim |
|---|---|
| `vload_unaligned_faults` | an unaligned `movdqa` load stops the model |
| `vstore_unaligned_faults` | so does the store |
| `vload_unaligned_movdqu_runs` | `movdqu` at the **same** address does **not** — so `aligned` is what discriminates, not the address |

⚠️ **This is the weakest claim in the repository and is labelled as such.** It has no second source:
the SDM, and a proof that the model implements what was read there. It is a named item for the
hardware co-simulation lane, where real silicon **is** the oracle for it — a better argument for that
lane than the BMI group it was commissioned on, which the census prices at a rounding error.

## 3. The arms — and the one deliberately absent

| arm | caught in |
|---|---|
| a vector load reads only eight bytes | 224 (`xmm0`) |
| a vector store writes only eight bytes | 164 (`mem@0x1fe0`) |
| `movdqu` applies `movdqa`'s alignment check | 82 (`refused`) — every case it sees |

⚠️ The third is what `movdqu_load_unal` exists for: it is the table's only vector at an address that
is not 16-byte aligned, so without it that wrong model is indistinguishable from the right one.

⛔ **`movdqa` ignores its alignment requirement is NOT an arm**, because no vector that can exist
would catch it. ⇒ **An arm no vector can distinguish is not a weak test; it is a false entry in the
gate's own inventory** — D90's lesson, in the case where the repair is impossible and the honest move
is omission plus a stated reason.

⚠️ *(The selftest drives `preStates … 4` — 82 states — where the differential drives `… 8` — 86. The
82 above is every case the arm sees, not a shortfall.)*

## 4. Design

**`vload`/`vstore` rather than one constructor over an operand pair**: an operand type admitting
`xmm` and `mem` on both sides can represent `movdqa (%rax),(%rbx)`, which no encoding produces. Two
constructors make the illegal state **unrepresentable** rather than checked — strictly better than
the shape `Op.mov` is stuck with (`wellFormed2`).

**`readMem128` composes two 64-bit reads** rather than opening a second byte recursion beside the one
500 roster rows of evidence have settled.

⚠️ The stores exposed that `claimsMemDestLoose` is **vocabulary-bound** — its literal is `m,r`, so it
is blind to a vector store's `m,x`. Recorded in `memDestSweep`, not repaired: that function exists
only to be compared against. See D91.
