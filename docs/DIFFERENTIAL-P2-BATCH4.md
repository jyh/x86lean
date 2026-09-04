# P2 BATCH 4 — the VECTOR HARNESS, red-first: sixteen registers before one line of vector semantics

**Forms.** None. **No instruction was added and no semantics changed.** What was added is the
thing the oracle-availability run measured as P2's real first cost: a vector register file that
the differential harness can SEE.

```
cases=69144  matched=49258  explained=28774  unexplained=0  oracle-leaks=0  missing=0
804 vectors · 86 pre-states · roster unchanged at 500/525
the record grew by 16 fields — xmm0 … xmm15, 32 hex digits each
```

## 1. ⛔ Why a harness batch, and why before any vector form

`x86l-post` reported 16 GPRs, RIP, the flags and two memory windows. The oracle **executes** the
vector forms — measured in the oracle-availability run, not assumed. So a vector form run on both
sides would have been compared on **none of its results**, and an unobserved region does not
report "unknown": **it reports AGREEMENT.**

⇒ 🔑 **"THE ORACLE EXECUTES IT" IS NOT "THE HARNESS CAN SEE THE ANSWER."** The first vector
batch's `unexplained=0` would have been a statement about the harness, not about the model.

## 2. ⚠️ What this batch claims, stated narrowly

No instruction in this roster writes XMM, so the registers are **constants**, and D27 is explicit:
a comparator that watches a constant reports agreement it did not test. The claim is exactly:

> the channel exists, both models report it, they agree on it, and a planted difference in it is
> **CAUGHT**.

Only the last clause has teeth. `wrongXmmClobbered` zeroes `xmm3` on every step and is caught in
**64 746** cases — which is what says the sixteen fields are genuinely read, rendered, transported
to the oracle, rendered again on the far side, and diffed.

## 3. ⭐ And the oracle's own values confirm the transport, end to end

At case 70 the swept values are `a = 0x5555…55`, `c = 0x0f0f…0f`, and x86isa reports:

```
xmm0  = 5555555555555555 0f0f0f0f0f0f0f0f     (a+0)  : (c XOR 0)
xmm1  = 5555555555555556 1e1e1e1e1e1e1e1e     (a+1)  : (c XOR 0x1111…)
xmm15 = 5555555555555564 f0f0f0f0f0f0f0f0     (a+15) : (c XOR 0xf·0x1111…)
```

Lean → the case record → `wx128` into x86isa's pre-state → `rx128` out of it → the POST line →
the comparator. Byte for byte, on both sides.

## 4. Three design decisions, with their reasons

| decision | why |
|---|---|
| ONE `Cpu` field, sixteen registers nested in `Xmms` | D71 measured that two flat fields blew three inherited proofs, because a whole-record `rfl` costs O(fields). Sixteen would have cost eight times that. |
| the frame lemmas written the DAY the field was added | D71's bill was for `undefVal` shipping without the lemmas its sibling had. Every state-mutating helper in `X86/State.lean` got its `xmm` lemma immediately. |
| the pre-state pattern is NOT zero | All-zero on both sides is the unobserved-region trap in its purest form: a model reporting the wrong register, a constant, or nothing at all agrees in every case. Each register gets `(a+i) : (c XOR i·0x1111…)` — no two equal, none constant across cases. |

## 5. ⭐ Two gates, because the format is a duplicate across a language boundary

`Cpu.renderXmms` and `x86l-xmms` produce the same sixteen fields and cannot read each other's
source — the same duplicate the watch windows are, failing the same way: any drift makes every
record differ and costs a four-minute ACL2 run to discover.

`scripts/check_xmm_format.py` asks it in 20 ms and drives **seven** arms: each side's renderer
mutated separately, the WIDTH (a 16-digit reading would render half of every register and compare
it happily against a full one), the COUNT, and — the quietest failure of all — **each side's
call site**, because a renderer that is defined and not called leaves sixteen registers out of the
record while both files still parse and still describe the same format.

## 6. And the leak check widened on the same day

The two opposite oracle runs must now agree on every XMM register, with **no declaration channel**.
Nothing draws an oracle bit into a vector register yet, so the honest rule while that is true is
the absolute one. The day a form legitimately leaves one undefined, this and `undefinableFields`
are the two places that grow — batch 14 wrote that lesson about `bsf`/`bsr`, and it is cheaper to
widen the check now than to discover the gap from a leak that classified itself as explained.
