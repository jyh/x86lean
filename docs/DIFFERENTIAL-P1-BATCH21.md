# P1 BATCH 21 — the last claimable row, a branch reached by one accident, and 42% of a module's kernel time

**Forms.** `cmpxchg8b m64` — one roster row, one constructor, one vector, taking the model to
**498 of the 525 rows** and **AVAILABLE WORK to ZERO**. Plus four purpose-built pre-states, five
selftest arms, and two repairs that touch no form at all.

```
cases=66736  matched=46979  explained=28559  unexplained=0  oracle-leaks=0  missing=0
  spec: 0   refusal: 0   harness: 0   undefined-region: 28559
776 vectors · 86 pre-states · 84 mnemonics
```

## 1. The oracle was measured before the constructor existed

`cmpxchg8b (%rbx)` (`0f c7 0b`, clang) over the 82 inherited pre-states, with
`cmpxchg %ecx,(%rbx)` as a control in the same run:

| | executes | equal branch (ZF=1) | flags that EVER move |
|---|---|---|---|
| `cmpxchg8b (%rbx)` | 82/82 | **1** | `zf` |
| `cmpxchg %ecx,(%rbx)` *(control)* | 82/82 | 22 | `cf pf af zf sf of` |

⭐ **The flag rule is the OPPOSITE of the form beside it in the same family.** `cmpxchg`'s flags
are the whole comparison; `cmpxchg8b` moves ZF alone. That is where a reader assumes rather than
checks, so it was executed. The control is what makes the reading mean something — a form that
moved no flag would look the same as a harness that had stopped watching flags.

## 2. ⛔ The equal branch was reached by ONE accidental state

`mkPre` puts `~a` in RDX and `c` in the eight bytes at RBX, so `EDX:EAX` is `(~a)[31:0]:a[31:0]`
and the comparison succeeds only where `c = a` **and** `a`'s high half is the complement of its
low half — `a = 0x00000000ffffffff`, one entry of `adversarial`, and there for another reason
entirely.

⇒ **A BRANCH REACHED BY ONE ACCIDENTAL STATE IS A BRANCH NOBODY IS MAINTAINING.** Reordering
`adversarial` would take the equal branch out of the run and leave every gate green. This is
`carryBoundary`'s finding (batch 2) arriving in control flow instead of arithmetic.
`cmpxchg8bStates` makes it deliberate: 3 of 86 cases now, two of them on purpose.

**The arms, all caught:** always-stores 79 · never-stores **3** · EAX-only comparison 22 in `zf`
· merge-instead-of-zero-extend 71 in `rdx` (D53's defect in this instruction's shape) · stored
halves swapped 3.

## 3. ⭐ A gate refused the first pre-state design, and named a cheaper one

The states were first built by writing the wanted value into the memory operand.
`memory_operand_mirrors_rcx` refused them: batch 3 made `[0x2000] = RCX` an invariant of every
pre-state, and it is the only reason a memory operand sweeps rather than being a constant
wearing its shape (D14). Setting **EDX:EAX** instead reaches the same four comparisons and
weakens nothing — no exemption, no widened window, no gate to re-probe.
⇒ 🔑 **A GATE THAT REFUSES A NEW PRE-STATE IS USUALLY NAMING A CHEAPER WAY TO BUILD IT.**

## 4. ⛔⛔ And the comment justifying two of the four states was FALSE

Two of the states differ from the accumulator pair in ONE half, for the defect of comparing one
half. The comment shipped with them said *"no inherited pre-state is such a state."* Counted:
**21 of the 82 inherited states already agree in the low half and differ in the high half, and
11 do the reverse** — because `mkPre`'s diagonal has `RCX = RAX`, so the low halves match there
by construction. Both half-width arms are caught with or without them.
⇒ 🔑 **A STATE ADDED FOR A DEFECT IS NOT EVIDENCE THAT THE DEFECT NEEDED IT.** The plausible
sentence about a new pre-state is the one claiming necessity, and it costs one count to check.
They are kept for `carryBoundary`'s reason — they are the only DELIBERATE ones — and the comment
says that now.

⛔ **Named gap:** EBX is 0x2000 in every pre-state this harness has, so the low half of the value
stored on the equal branch is a CONSTANT. Swapped halves and any other register are still caught
(ECX sweeps); a model storing the literal 0x2000 there by another route is not. Making EBX sweep
means moving RBX, which moves every memory vector's address at once.

## 5. The unavailable list stopped being DECLARED (D65)

D61 measured `movnti` UNAVAILABLE at batch 20 and wrote it into `docs/DECISIONS.md` and
`docs/COVERAGE.md` **and into neither gate**, so `--remaining` went on printing it under
AVAILABLE WORK for a whole batch while two documents said the list had been corrected.
⇒ 🔑 **A CITATION IS AN UNGATED CLAIM.**

`scripts/oracle_availability.py` now measures it by executing one form per mnemonic over the real
pre-states, with two positive controls, checked in **both** directions and driven red-first —
**~6 seconds**, because a discipline expensive to exercise gets exercised less.

```
oracle availability over 86 real pre-states (12 forms, ACL2 x86isa):
  10 forms refuse 86/86 (the nine BMI mnemonics + movnti)
  CONTROL:mov          movl %ecx,(%rbx)    executes 86/86
  CONTROL:cmpxchg8b    cmpxchg8b (%rbx)    executes 86/86
```

**The residue, partitioned and checked:**

    27 = 2 no encoding (DERIVED) + 19 oracle-unavailable (MEASURED) + 6 declined (D23, D25)
       + 0 AVAILABLE WORK

⚠️ The batch-20 handover gave this as `27 = 2 + 19 + 6 + 1`, which sums to 28, describes a state
where `movnti` had already been declared, and disagrees with its own row count. Three of its four
terms were wrong, all in the direction that leaves work looking available.

## 6. `Tests.Coverage`: 37 900 → 22 400 ms (D63)

D62 named `vectorMnemonics`'s quadratic `eraseDups` as the honest next fix. Priced first, with a
control at the same shape: the dedup costs **935 ms** against **69 ms** for the same 775
projections without it — real, and worth 2.8 s of a 37 900 ms module (**7%**).

Measured instead: the three mem-dest sweeps cost **25 570 ms apart and 11 200 ms in one
declaration**. ⇒ 🔑 **THE KERNEL'S REDUCTION CACHE SPANS A DECLARATION AND NOT TWO.** Each group's
claims are now checked in ONE `decide` and the six original theorems are DERIVED from it, their
statements byte-for-byte unchanged — a merged statement weaker than any of them could not close
the derivations. `scripts/sharing_redprobe.sh` plants a defect in each of the six conjuncts alone
and requires the kernel to prove that conjunct `false`, with an unplanted positive control in the
same run: **7 arms, 28 s, in CI**.
