# P2 BATCH 17 — `PREFETCHh`, the form that changes nothing

> ⚠️ **TWO COUNTERS.** Seventeenth differential record; the seat's **batch 22** in
> `docs/DECISIONS.md`.

**Form.** `prefetchnta` and `prefetcht0` at a memory operand — `0f 18 /0` and
`/1`. Two roster rows, 4 vectors, one constructor, **no new state**, and `step`
advances RIP and does nothing else. **466 instructions** (nta 315, t0 151).

⭐ Found by the batch-21 census, which measured the unprobed remainder rather than
declaring it empty. Nobody knew this was buildable.

## 1. ⚠️ WHAT THESE VECTORS PROVE IS NARROW, AND SAYING SO IS THE BATCH

The form changes no architectural state, so the differential can witness only
that **both models leave every watched register, flag and memory window alone and
advance RIP by the right length**. That is exactly the claim `prefetch` makes, and
it is worth having — a model that read the memory, faulted on it, or mis-computed
the instruction length breaks it. But it is **not** evidence about the locality
hint, and the record says so rather than letting a green run imply it.

⇒ 🔑 [[feedback-unobserved-regions-report-agreement]] is the hazard this batch
lives closest to: a form that writes nothing is one whose vectors agree with
almost any wrong model. The two arms below are what stop the agreement from being
vacuous.

## 2. ⛔ NO ARM FOR THE HINT FIELD, AND THAT IS A DECISION

The obvious wrong model — *"prefetch ignores its locality hint"* — is
**architecturally invisible**, so no vector that can exist would distinguish it.
An arm no vector can distinguish is a **FALSE ENTRY in the gate's own inventory**,
not a weak test — D91's rule, which this repository has already paid for once.

The four spellings are held apart by `scripts/check_encodings.py`, which assembles
each vector's `asm` and compares bytes: **the instrument that can actually see a
`/reg` field.** The right response to an undistinguishable claim is to move it to a
gate that can see it, not to plant an arm that never fires.

Two arms remain, and both are real misreadings of the SDM's word *hint*:

```
prefetch faults on its operand          caught — 336 in `refused`
prefetch loads its operand into rax     caught — 292 in `rax`
```

## 3. ⛔⛔ TWO ROWS, NOT FOUR — AND THE KERNEL-COST GATE IS WHAT NAMED THE CHEAPER BUILD

The first cut modelled all four hints. The gate refused: four roster rows put
`Tests.Coverage`'s residue **700 ms over its ceiling**, because several `decide`
theorems are quadratic in the row count. `prefetcht1` and `prefetcht2` have
**zero measured demand** — they are absent from the census entirely — so modelling
them was completionism, not demand, which is the instinct this roster declines
elsewhere (`pshufw`).

⇒ 🔑 **THE REFUSAL NAMED A CHEAPER BUILD AND THE CHEAPER BUILD WAS THE MORE HONEST
ONE.** It weakens nothing: the two modelled rows are the two anyone executes.
Shortening the four `note` strings — prose the kernel walks character by character
— was the other half, and it moved `X86.Syntax` 204 → 200.

## 4. RECEIPTS

```
cases=83952 matched=63420 explained=29435 unexplained=0 oracle-divergence=171 oracle-leaks=0 missing=0
954 vectors · 88 pre-states · 83952 cases · 0 unexplained · 0 oracle leaks
```
171 oracle-divergences, unchanged; this batch adds none.

### ⭐⭐ The kernel-cost gate, and D111's method run for the first time

The gate could not return a verdict: four attempts, one-minute loads 3.60, 5.85,
6.20 and 6.38 against a calibrated band of 0.0–4.1, on a machine `ps` shows is
loaded by WebKit, a vendor updater and another seat's bus scanner — not by this
work. So **D111's prescribed repair was applied as a MEASUREMENT**: the parent tree
and this one, profiled back to back in one session.

```
                          parent 873a4d9      this batch      delta
X86.Syntax                     206.0 ⛔           205.0        ~0
Tests.Coverage (residue)      12540  ⛔          12900        +360
```

⛔ **THE PARENT IS ALREADY OVER BOTH CEILINGS**, with none of this batch in it. And
across four runs of substantially identical code `X86.Syntax` read **204, 205, 206
and 244** — a 20% spread that dwarfs any delta this batch could introduce.

⇒ 🔑 **A CEILING WHOSE MARGIN IS UNDER THE MACHINE'S OWN SPREAD REPORTS THE
MACHINE, NOT THE CODE** — and the delta method is the only reading here that means
anything. No ceiling was raised: deriving a gate's new allowance from the thing it
measures is the move that has no second source. The authoritative reading is CI's,
on a Linux runner, and this tree has not been pushed.

The remaining local gates are in the commit message.
