# HARDWARE CO-SIMULATION — the design, and what it is actually worth

*Plan v1 §4.4, commissioned at the 09/03 council (desk ES → the co-sim design on KENAI).
Written at the P1 seal; nothing here has been run yet, and every number in it is either
measured elsewhere in this repository or labelled as an estimate.*

## 1. ⛔ THE COMMISSIONING PREMISE, CHECKED — AND THE PRIZE IS NOT WHERE IT WAS PUT

The order names co-simulation as *"also an oracle for the BMI group's defined behaviour"* — the
19 roster rows ACL2 x86isa refuses. That is true, and the demand-side census (D66) prices it:

| corpus | BMI/BMI2-family instructions | of which the model already has |
|---|---|---|
| cc1 | 364 of 5,380,005 (0.0068%) | all 364 (`tzcnt`) |
| coreutils | 12 of 873,099 (0.0014%) | all 12 (`tzcnt`, `popcnt`) |
| glibc | 733 of 604,226 (0.1213%) | 633 (`tzcnt`, `lzcnt`, `sarx`/`shlx`/`shrx`, `movbe`) |
| vmlinux | 569 of 6,671,979 (0.0085%) | all 569 |

⇒ **The nine mnemonics no oracle can execute for us — `andn`, `bextr`, `blsmsk`, `blsr`, `bzhi`,
`mulx`, `pdep`, `pext`, `rorx` — occur about 100 times in glibc and nowhere else in the corpus:
0.017% of one column and 0.000% of the other three.** Building a hardware harness *for them*
would be a large instrument bought for a rounding error.

⭐ **What co-simulation is actually worth is independence, and that is worth a great deal.**
Every disagreement this project has ever resolved was resolved by MODELS agreeing with each
other: D53 and D54 found the SDM's pseudo-code wrong about 64-bit mode twice, and what settled
both was ACL2 x86isa and K agreeing against the manual. That method has a floor it cannot get
under:

> ⇒ 🔑 **TWO MODELS THAT MISREAD THE SAME SENTENCE AGREE, AND NOTHING IN A DIFFERENTIAL RUN CAN
> TELL THAT FROM BOTH BEING RIGHT.** x86isa and this model are both readings of the same manual by
> people with the same incentives. Silicon is not a reading.

That is the case for co-simulation, it is not the case the order made, and it is stronger.

## 2. WHAT IT CANNOT WITNESS, SAID FIRST

⛔ **One processor cannot witness an UNDEFINED bit.** Where the SDM declines to define a result,
a chip still produces one — and recording it as "the answer" would convert a refusal into a
claim, which is the exact defect `X86.Oracle` exists to prevent (D6). A single machine tells you
what *that* machine did, not what the architecture guarantees.
⇒ **To learn anything about an undefined bit, run on two DIFFERENT microarchitectures and require
them to DISAGREE.** Agreement between two chips on an undefined bit is not evidence that it is
defined; disagreement is evidence that it is not. This is plan v1 §4.5's nonvacuity rule, and
hardware is the place it finally has teeth. KENAI alone is a *defined-behaviour* oracle only.

⛔ **And it cannot witness what it cannot observe.** The harness reads the two watched windows and
the architectural registers. Anything else — cache state, an access outside the windows — is
invisible, and an unobserved region reports agreement.

## 3. THE HARNESS

The Lean side already emits, per case, exactly what a hardware run needs: instruction bytes,
16 GPRs, RFLAGS, and a memory image. `x86lean-diff emit-acl2` writes it as Lisp; a third emitter
writes the same records as a flat binary the runner reads.

```
parent (runner)                          child (the victim)
  fork + PTRACE_TRACEME                    raise(SIGSTOP)
  ── per case ─────────────────────────
  poke instruction bytes at RIP
  PTRACE_SETREGS   (16 GPRs, RIP, RFLAGS)
  poke the two watched windows
  PTRACE_SINGLESTEP  ──────────────────▶   executes exactly one instruction
  waitpid → status
  PTRACE_GETREGS + peek the windows
  emit one POST record, same format as the Lean and ACL2 sides
```

**Faults map to refusals.** `step` refuses by halting; the child faults by signalling. `SIGFPE` is
`#DE` (division by zero, quotient overflow), `SIGILL` is `ud2` and an invalid encoding, `SIGSEGV`
is a non-canonical address or an unmapped access. The runner records `refused=1` with the signal,
and `x86lean-diff compare` already classifies a refusal mismatch — no new comparator.

⚠️ **`PTRACE_SINGLESTEP` sets `TF`, and `TF` is architecturally visible — but not to anything
this model has, and the difference is worth stating rather than guessing at.** Checked against
the roster rather than assumed: `pushfq`, `popfq`, `lahf` and `sahf` are **not in it**, so no
modelled form copies RFLAGS wholesale. The ten forms that read a flag (`adc`, `sbb`, `rcl`,
`rcr`, `setcc`, `cmovcc`, `jcc`, `loope`, `loopne`, `cmc`) read CF/ZF/SF/OF/PF individually, and
the comparator compares those six plus DF — never TF.
⇒ So the instrument's own bit is invisible to the comparison **today**, and the requirement is a
standing one rather than an urgent one: the runner masks `TF` (bit 8) out of the RFLAGS it writes
and the RFLAGS it reads, and records that it did. ⛔ **The day `pushfq` joins the roster — it is
476 instructions in the kernel census, so it is a plausible P2 row — this stops being a
formality**, and a harness that had been silently correct for the wrong reason would start
disagreeing on every case of that form.

## 4. ⛔ THE ADDRESS PROBLEM, WHICH IS THE REAL ENGINEERING RISK

This harness's watched windows are at **0x1fe0** and **0x7fe0**, and `mkPre` fixes `RBX = 0x2000`,
`RSP = 0x8000` in all 86 pre-states. Linux refuses to map below `vm.mmap_min_addr`, **default
65536 (0x10000)** — so the pre-states cannot be reproduced on a stock kernel by an unprivileged
process. Two routes, and they are not equally safe:

- **(a) `sysctl -w vm.mmap_min_addr=0`** on KENAI, then `mmap(MAP_FIXED)` the two windows.
  Reproduces the emitted cases BYTE FOR BYTE, which is the whole point: the hardware run and the
  ACL2 run then answer the *same* question and their records are directly comparable.
  Needs root on that machine, and is a local, reversible setting.
- **(b) relocate the windows by a constant offset in the hardware runner only.**
  ⛔ **This is the dangerous one and it is recorded as such.** It introduces a translation layer
  between the case and the execution, and a translation layer is a place where a disagreement can
  be absorbed rather than reported — the addresses in the record would no longer be the addresses
  the model computed, so any address-dependent defect (a RIP-relative operand, a `lea`, a stack
  address written to memory) could be masked by the very arithmetic meant to compensate for it.
  If (b) is ever taken, the offset must appear in the record and the comparator must refuse a run
  whose offset it was not told about.

**Recommendation: (a).** It is one reversible sysctl on a machine we control, against a
translation layer that could hide the class of bug the harness exists to find.

## 5. WHAT TO CO-SIMULATE FIRST, RANKED BY THE CENSUS

Not the roster's order, and not BMI. D66 ranks the model's own covered forms by how often real
binaries execute them, and that is the order in which a wrong answer costs most:

1. `mov`, `jcc`, `call`, `cmp`, `lea`, `add`, `test`, `push`/`pop` — between them the large
   majority of every user-space column. These are the forms with the most differential evidence
   already, which is precisely why an error in them would be a *shared* error.
2. The forms where the SDM was already found wrong — `cmpxchg` at `.d`, `shld`/`shrd` at count 0
   (D53, D54). Two models and a manual disagree there and the manual lost; silicon is the witness
   that closes it.
3. The undefined-bit forms — `bsf`/`bsr` at a zero source, `shld`/`shrd` above the width, the
   multiply/divide flags — **on two machines**, per §2.
4. The nine BMI mnemonics, last, at 0.017% of one column.

## 6. COST, AS AN ESTIMATE AND LABELLED AS ONE

The runner is a few hundred lines of C and one new emitter mode. The 66,736 cases are one
`PTRACE_SINGLESTEP` each plus two window copies; a single-step round trip is order 10 µs, so the
whole suite is **seconds of machine time**, against four minutes for the ACL2 run. ⚠️ That figure
is arithmetic, not a measurement, and the first real run should replace it.

The cost is not the runtime. It is that the harness is a new instrument, and a new instrument
gets the same treatment every gate in this repository gets: **a deliberately wrong model driven
through it, red first**, before a single agreement is believed.
