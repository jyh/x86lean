# HARDWARE CO-SIMULATION — the design, and what it is actually worth

*Plan v1 §4.4, commissioned at the 09/03 council (desk ES → the co-sim design on KENAI).
Written at the P1 seal; nothing here has been run yet, and every number in it is either
measured elsewhere in this repository or labelled as an estimate.*

## 0. ⛔⛔ AMENDMENT 2026-09-06 — THIS DOCUMENT NAMED A MACHINE AND ASSUMED A DIFFERENT MACHINE'S KERNEL

**Everything below §1 was written on 2026-09-03 and is kept byte-for-byte except for the two
pointers marked `[see §0]`. Read this section first; two of its findings change what §3 and §4
mean.**

**① The harness in §3 and the address analysis in §4 are LINUX.** `PTRACE_TRACEME`,
`PTRACE_SETREGS`, `PTRACE_SINGLESTEP`, `vm.mmap_min_addr`, `mmap(MAP_FIXED)`, `SIGFPE`/`SIGILL`/
`SIGSEGV`. **This document names KENAI five times and never once names kenai's operating system.**

**Kenai is Windows 11 on an AMD Ryzen 7 8700F, and WSL is not installed on it.** Measured by
flask on 2026-08-28 (`fleet/FOR-JAS-wsl-is-absent-on-kenai-2026-08-28.md`):

```
Get-WindowsOptionalFeature Microsoft-Windows-Subsystem-Linux  -> State: Disabled
Get-WindowsOptionalFeature VirtualMachinePlatform             -> State: Disabled
wsl.exe --list --quiet                                        -> exit 1, "not installed"
```

⇒ **As committed, this design could not run on the machine it is a design for.** The reason is
not carelessness: it was written to plan v1 §4.4, whose premise is *"GitHub-hosted x86-64
runners"* — a Linux premise. The 09/03 council substituted a **machine**; the document kept the
**mechanism**.
⇒ 🔑 **A SUBSTITUTED SUBJECT INHERITS THE OLD SUBJECT'S ASSUMPTIONS IN SILENCE.** Nothing in the
edit was wrong at the point of edit; the assumption was never at the point of edit.

**② Desk row ES item (3)'s own words are "WSL or native", and that fork is not in this
document.** What *is* in it is a fork **inside** the WSL arm — §4's `sysctl` (a) versus a
relocation offset (b) — argued with a stated danger and a recommendation.
⇒ 🔑 **A WELL-ARGUED SUB-FORK IS THE BEST CAMOUFLAGE A SKIPPED FORK CAN HAVE.** A reader checking
*"did paris post a fork with a recommendation?"* gets **yes** at every level except the one that
decides whether any of it runs. The real fork is now §7.

**③ ⛔ AND §3'S INVENTORY OF THE RECORD WENT STALE SEVEN HOURS AFTER IT WAS WRITTEN.** §3 says the
Lean side emits *"instruction bytes, 16 GPRs, RFLAGS, and a memory image"*. That was true at
`902aff4` (09/03 13:31). At `c693ab7` (09/03 **21:04**, P2 batch 4) the record grew a **sixteen-
register 128-bit XMM file**, emitted as `:xmms` in every pre- and post-record — and it has stayed
in this document's blind spot for three days and thirty batches.
⇒ **The harness must transfer 16×`BitVec 128` in both directions.** It is one more state class,
it is cheap on both arms (§7.1), and the only thing that went wrong is that **nothing gates a
prose inventory against the emitter it describes.** This repository's own recurring shape.
⚠️ The model has **XMM only** — no YMM, no ZMM, no MXCSR in `Cpu`. That is load-bearing for §7.1
and it is why neither arm needs an extended-state API.


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

## 3. THE HARNESS  `[see §0 — this is a LINUX harness, and its record inventory is one register file short]`

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

## 4. ⛔ THE ADDRESS PROBLEM, WHICH IS THE REAL ENGINEERING RISK  `[see §7.2 — Windows has the same floor and no sysctl, and there is a route (c)]`

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

---

# 7. ⭐ THE FORK ROW ES ITEM (3) ACTUALLY ASKED FOR — WSL2 vs WINDOWS-NATIVE

*Written 2026-09-06. Every platform claim below is labelled **[measured]**, **[repo]**, or
**[unverified]**. Nothing in this section has been run on kenai; §7.8 is the list of what must be
measured there before any of it is trusted, and it is deliberately the last word rather than a
footnote.*

## 7.0 ⛔⛔ THE PREMISE GATE, WHICH COMES BEFORE THE FORK AND MAY CLOSE IT

**§1 argues that co-simulation is worth building because *"silicon is not a reading"*. That
argument assumes the silicon is running inside its own specification. Kenai's is not, on the
last evidence the fleet has.** **[measured, 2026-07-27, `fleet/KENAI-hardware-fault-2026-07-27.md`]**

```
Microsoft-Windows-WHEA-Logger Id 18  ×3 in one day, all at IDLE
  "A fatal hardware error has occurred. Reported by component: Processor Core
   Error Source: Machine Check Exception"
Memory SPD/JEDEC default   4800 MT/s
Memory actually running at 6000 MT/s     <- vendor-shipped EXPO profile, +25%
```

The fleet record carries **no resolution**. Three points make this a gate rather than a caveat:

- **The failure is silent.** *"The first two crashes self-healed and left no visible trace; only
  the third was noticed... Assume this has been happening since the machine arrived."* A machine
  that can lose a whole boot without leaving a trace can certainly return one wrong bit without
  leaving one.
- **It fails at idle, not under load.** So "it has been fine while flask worked on it" is not
  evidence. Idle instability points at voltage/memory margin, and a differential harness runs
  short bursts between long idles — the exact duty cycle that produced the three crashes.
- ⛔ **And the differential would ABSORB it.** A rare, unreproducible miscomputation arrives at
  `x86lean-diff compare` as one case where hardware disagrees with two models. The harness's job
  is to *file that with a class*. **A defective oracle does not look like a defective oracle; it
  looks like a model bug with a class.** That is worse than having no hardware oracle at all,
  because it consumes the one thing the hardware was bought for: credibility against the models.

⇒ **GATE: before either arm is built, ask kenai for (i) `Get-WinEvent -LogName System | where Id
-eq 18` since 2026-07-27 and (ii) its current memory MT/s.** Two commands, no build, flask's pane.
If EXPO is still enabled or any Id-18 has landed since, **the correct answer to row ES item (3)
is "not on this machine yet"** — and that is a finding about the hardware, not a failure of the
design.
📌 **If the box is clean, this section still stands as a standing requirement**: the runner
records the WHEA Id-18 count before and after every suite and refuses a run that straddles one.
An oracle must say what it saw.

## 7.1 WHAT BOTH ARMS MUST DO — the same list, so the fork turns on nothing else

Per case: set 16 GPRs · RIP · RFLAGS · **16×128-bit XMM** · two memory windows (0x1fe0+64 bytes,
0x7fe0+48) · FS base and GS base **[repo]**; execute **exactly one** instruction; read all of it
back; classify a fault as a refusal.

| | **Arm A — WSL2** | **Arm B — Windows native** |
|---|---|---|
| single-step | `PTRACE_SINGLESTEP` | `EFlags \|= TF (0x100)` + `ContinueDebugEvent`, catch `EXCEPTION_SINGLE_STEP` |
| GPRs/RIP/RFLAGS | `PTRACE_GETREGS`/`SETREGS` | `GetThreadContext`/`SetThreadContext`, `CONTEXT_FULL` |
| **16×XMM128** | `PTRACE_GETFPREGS` → `xmm_space[64]` | `CONTEXT.FltSave.XmmRegisters[16]` — **in the base CONTEXT** |
| memory | `process_vm_readv` / `PTRACE_PEEKDATA` | `ReadProcessMemory` / `WriteProcessMemory` |
| faults | `SIGFPE` / `SIGILL` / `SIGSEGV` | `EXCEPTION_INT_DIVIDE_BY_ZERO` / `_ILLEGAL_INSTRUCTION` / `_ACCESS_VIOLATION` |
| FS/GS base | in `user_regs_struct`, set by `PTRACE_SETREGS` | ⛔ **not in `CONTEXT` at all** — see §7.5 |

⭐ **The model has no YMM, no ZMM and no MXCSR (§0③), so NEITHER arm needs an extended-state
API** — no `PTRACE_GETREGSET`/`NT_X86_XSTATE`, no `InitializeContext`/`LocateXStateFeature`.
That is the single biggest simplification available to this design and it is a fact about the
**model**, not about either platform. **[repo]**
⚠️ It expires the day the roster grows a YMM form. Both arms then pay, and the native arm pays
more (the `CONTEXT_XSTATE` path is materially fiddlier than `NT_X86_XSTATE`). **Write it down
now**, because the shape of this whole document is a premise that outlived its edit.

## 7.2 ⛔⛔ THE ADDRESS FLOOR — AND THE ASYMMETRY RUNS THE OPPOSITE WAY TO INTUITION

§4 calls `vm.mmap_min_addr` *"the real engineering risk"*. It is — **and it is not a Linux
peculiarity that Windows escapes. Windows has the same floor and no sysctl.**

| | floor on the lowest mappable user address | can it be lowered? |
|---|---|---|
| Linux / WSL2 | `vm.mmap_min_addr`, default **0x10000** | ✅ **yes** — `sysctl -w vm.mmap_min_addr=0`, root, reversible |
| Windows x64 | `GetSystemInfo().lpMinimumApplicationAddress` = **0x10000** **[unverified on kenai]** | ⛔ **no user-mode route known to me** |

The pre-states need **0x1fe0** and **0x7fe0**. Both are below 0x10000. **[repo]**

⇒ **On Arm A, §4's route (a) — byte-for-byte reproduction, "the whole point" — is available.**
⇒ **On Arm B it is NOT, and Arm B is forced onto route (b), the route §4 records as DANGEROUS.**

⭐ **And a route §4 never considered, which dominates both: (c) MOVE THE MODEL'S WINDOWS ABOVE
0x10000.** Then route (a) is available on *both* arms, with no sysctl, no privilege and no
translation layer, and the fork stops being load-bearing at all.

⛔ **(c) IS NOT A `sed`, AND I CHECKED THAT AGAINST THE OBJECT RATHER THAN ASSUMING IT — WHICH
CORRECTED ME IN BOTH DIRECTIONS.**

**Cheaper than I first wrote:** the two windows are **already structured data, already declared on
both sides of the oracle boundary, and already gated across the language boundary** —
`Tests/Vectors.lean:3295` `windows = [{base := 0x1fe0, len := 64}, {base := 0x7fe0, len := 48}]`
and `scripts/x86isa_driver.lisp:150` `*x86l-windows* = ((#x1fe0 . 64) (#x7fe0 . 48))`, held
together by `scripts/check_windows.py`, which exists precisely because *"a duplicate born in
agreement diverges on the next ordinary append"*. **[repo]** So the windows themselves relocate by
editing two literals and re-running one 20 ms gate.
⇒ ⭐ **AND THAT GATE IS A REQUIREMENT ON BOTH ARMS, NOT ONLY ON (c): a C runner is a THIRD
declaration of the same windows, in a third language, and it must join `check_windows.py` on the
day it is written — not after the first drift.** Two copies were already judged worth a gate; a
third copy that the gate cannot see is strictly worse than the state that gate was built for.

**Dearer than the windows suggest:** what does *not* relocate cheaply is everything keyed to them
— `mkPre`'s six fixed registers (`rbx 0x2000`, `rsp 0x8000`, `rsi 0x1fe8`, `rdi 0x2010`,
`fsBase 0x1fd8`, `gsBase 0x1fe8`), `baseMem`'s four write bases, and roughly two hundred literal
sites across `Tests/Vectors.lean`, `Tests/Coverage.lean`, `Tests/Anchors.lean`, `Main.lean`,
`X86/Semantics.lean` and three scripts. **[repo]**
⛔ **And a blind rename would be worse than laborious, it would be silent:** **`0x8000` is BOTH
the stack pointer AND the 16-bit sign boundary in the `adversarial` sweep**
(`Tests/Vectors.lean:3258`: `0x7FFF, 0x8000, 0xFFFF`) — 32 bare occurrences, of which only some
are addresses. **[repo]** A `sed` would rewrite the adversarial corpus: a change to what is
*tested*, wearing the costume of a change to where it *runs*, in a repository whose every gate
reads that corpus.
⇒ **(c)'s first step is therefore to NAME the register anchors as `windows` is already named**,
with a gate that no address literal survives outside those definitions — and only then is the
relocation one edit. The precedent, the pattern and the cross-language gate all already exist.

📌 **If (b) is ever taken anyway, it can be made honest rather than merely careful.** §4 requires
the offset in the record and a comparator that refuses an unannounced one; that is necessary and
not sufficient. **Sufficient is a differential-of-differentials: run the whole suite at TWO
offsets and require the hardware deltas to match the MODEL's deltas between the same two
offsets.** Address-independent forms must agree; `lea`, `push` of a stack address and any
RIP-relative form must differ **exactly as the model says they differ**. That converts §4's
"a translation layer is where a disagreement gets absorbed" from a warning into an arm — and it
is the same shape as the wrong-model arms this repository already runs.

## 7.3 WHAT ARM A COSTS, AND THE PART THAT IS NOT TOOLING

| | |
|---|---|
| install | enable `Microsoft-Windows-Subsystem-Linux` + `VirtualMachinePlatform`, **reboot** **[measured]** |
| whose hand | ⛔ **the Captain's** — flask cannot enable an optional feature and reboot on its own word |
| is it still silicon? | ✅ yes — WSL2 is a real Linux kernel in a Hyper-V VM on AMD-V; user-level instructions execute on the physical core **[unverified: whether the hypervisor masks any CPUID feature the roster depends on]** |
| ⛔ **must be WSL2, never WSL1** | WSL1 is a syscall-translation layer, not a kernel; its `ptrace` is incomplete. A design that says only "WSL" has not said this. |
| route (a) | ✅ available — `sysctl` inside the VM, which **does not touch the Windows host's posture at all**. This is strictly better than §4's implied "sysctl KENAI". |

⛔ **And the cost that is not tooling, in flask's own words** (`FOR-JAS-wsl-is-absent-on-kenai`):
*"Installing WSL would put a POSIX multiplexer on the one box whose job is to have none... The
seat exists to catch what only the Windows-native lane can catch — and it has earned that keep
this week: the `cp1252` class, the `python3` stub, `core.filemode=false`, Smart App Control, the
truecolor `38;2` defect. Several of those are invisible from a POSIX shell."*

⇒ Installing WSL removes no capability; it removes the **forcing function**. That is a soft cost,
it is real, **and it is not mine to spend** — it belongs to flask and to the Captain. I name it
here so the fork is priced honestly rather than resolved by whoever finds the arm cheaper.

## 7.4 WHAT ARM B COSTS

| | |
|---|---|
| install | **nothing** — the Win32 debugging API ships with the OS **[unverified on kenai]** |
| whose hand | nobody's |
| code | more than Arm A: `DEBUG_ONLY_THIS_PROCESS`, a `WaitForDebugEvent` loop, per-thread `CONTEXT`. Call it 1.5–2× the ptrace runner. **[estimate]** |
| XMM | **free** — `CONTEXT.FltSave.XmmRegisters` is in the base CONTEXT (§7.1) |
| ⛔ addresses | **route (a) unavailable** (§7.2). Needs (c), or (b) with the §7.2 control. |
| ⛔ FS/GS base | see §7.5 |
| ⚠️ Smart App Control | is at **ENFORCE** on kenai and has already blocked a freshly built binary on this box, *irreversibly without a Windows reset* **[measured, flask, 08/27]**. A newly compiled runner is exactly the shape it blocks, and **the symptom is the app starting and dying, which reads as an application bug.** Read `Microsoft-Windows-CodeIntegrity/Operational` 3077/3033/3118 before believing any failure. This is a real, already-paid-for hazard on Arm B and it has no counterpart on Arm A. |

## 7.5 THE SEGMENT COST, MEASURED RATHER THAN FEARED

The roster carries FS/GS overrides. On Linux `fs_base`/`gs_base` are fields of
`user_regs_struct` and one `PTRACE_SETREGS` sets them. **Windows x64's `CONTEXT` has `SegFs` and
`SegGs` as 16-bit selectors and NO base fields, and there is no documented user-mode API to set a
thread's FS or GS base.** **[unverified — the single most important thing in §7.8]**

**So price it before treating it as a kill:** **8 of 1012 vectors** carry a segment override —
**7 FS, 1 GS**. **[repo: `grep -c 'seg := some' Tests/Vectors.lean`]** That is **0.79%**.

Two routes on Arm B, and they differ for FS and GS:
- **`WRFSBASE` / `WRGSBASE` executed by the child itself**, single-stepped as a setup instruction.
  Requires CR4.FSGSBASE, which Windows 10 1809+ enables on supporting hardware; Zen 4 supports it.
  **[unverified: `IsProcessorFeaturePresent(PF_RDWRFSGSBASE_AVAILABLE)` on kenai]**
- ⛔ **but not symmetrically: on Windows x64 GS is the TEB.** Clobbering the GS base leaves the
  child unable to dispatch its own exceptions through `KiUserExceptionDispatcher`, so a fault in a
  GS case would likely crash rather than report. FS is unused by Windows in user mode and is the
  safe one. ⇒ **7 recoverable, 1 not**, on this reading.

⛔ **Whatever the answer, the runner must REFUSE those vectors, never skip them.** This
repository's own law — an unobserved region does not report `unknown`, it positively reports
agreement — is exactly what a quietly-skipped segment vector would trigger, and 8 of 1012 is
small enough that nobody would notice the denominator move.

## 7.6 THE FORK, IN ONE TABLE

| | **A — WSL2** | **B — Windows native** |
|---|---|---|
| Captain's hand + reboot | ⛔ **yes** | ✅ no |
| cost to flask's seat's purpose | ⛔ **the forcing function** | ✅ none |
| route (a) without repo change | ✅ **yes** | ⛔ no |
| runner size | ✅ smaller; §3 already written for it | ~1.5–2× |
| XMM (16×128) | ✅ `GETFPREGS` | ✅ base `CONTEXT` |
| FS/GS base | ✅ `SETREGS` | ⛔ 7 of 8 via `WRFSBASE`; 1 doubtful |
| Smart App Control | ✅ n/a | ⚠️ **ENFORCE, has already blocked a fresh build here** |
| needs (c) to be clean | no | **yes** |
| **premise gate §7.0** | ⛔ **identical on both** | ⛔ **identical on both** |

## 7.7 ⭐ RECOMMENDATION

**It is not "pick an arm", and I want the reason on the record: the arm is decided by two facts
nobody has measured, both of which cost one command each. Choosing now would be choosing on my
reading of two APIs instead of on kenai's answer.** So:

1. ⛔ **Run the §7.0 premise gate first.** Two commands in flask's pane, no build. **If EXPO is
   still on or any WHEA Id 18 has landed since 07/27, the answer to item (3) is "not on this
   machine", and neither arm gets built.** It is the cheapest question here and the only one that
   can make the rest moot.
2. ⭐ **Then pay route (c)'s first step regardless of the arm — name `mkPre`'s register anchors
   the way `windows` is already named, and gate the literals.** It is worth doing on its own merits, it is the enabling step for Arm B, it makes
   Arm A's `sysctl` unnecessary rather than merely available, and **it is the only item here that
   cannot be wasted by whichever way the fork falls.** Do it in this repo, where the work is,
   before asking anyone for a machine.
3. **Then Arm B (native), unless §7.8's two measurements come back badly** — because it needs no
   hand, no reboot, and does not spend the one thing flask argued for; and because after (2) its
   only remaining disadvantages are runner size and Smart App Control, both of which are work
   rather than permission.
4. **Arm A is the fallback and a good one.** Take it if (c) prices above about a day, if
   `PF_RDWRFSGSBASE_AVAILABLE` is false on kenai, or if the Captain would rather spend a reboot
   than a refactor. **The two are not exclusive**: (c) makes Arm A strictly better too, and a
   suite that runs on both machines-in-one-box is the beginning of §2's two-microarchitecture
   requirement rather than a duplicate.

⛔ **I do not recommend route (b) alone, on either arm**, and §4's reasoning for that is
unchanged and correct. If (b) is taken, it must carry §7.2's differential-of-differentials.

## 7.8 ⛔ WHAT I HAVE NOT MEASURED, NAMED SO THE RECOMMENDATION CAN BE ATTACKED

Nothing in §7 has been run. These are the claims that would move the fork if they came back
differently, in the order they would move it:

1. **`IsProcessorFeaturePresent(PF_RDWRFSGSBASE_AVAILABLE)` on kenai**, and whether a
   `SetThreadContext`-driven TF single-step reports `EXCEPTION_SINGLE_STEP` reliably for the
   forms in the roster. *If FSGSBASE is false, Arm B loses 8 vectors instead of 1 and Arm A wins.*
2. **`GetSystemInfo().lpMinimumApplicationAddress` on kenai** — predicted 0x10000. *If it were
   lower, Arm B gets route (a) for free and §7.2's asymmetry vanishes.*
3. **The WHEA Id-18 count since 07/27 and the current memory MT/s** (§7.0). *Gates everything.*
4. **Whether Hyper-V masks any CPUID feature the roster depends on** inside WSL2. *Would cost
   Arm A its "it is still silicon" claim in part.*
5. **The runner's cost on each arm.** §6's *"a few hundred lines of C"* is arithmetic, not a
   measurement, and my 1.5–2× for Arm B is an estimate with no basis but the API surface.

📌 And the standing one from §2, which no arm on kenai can satisfy: **the fleet has exactly ONE
x86-64 machine.** §4.5's nonvacuity rule wants two *different* microarchitectures to disagree
about an undefined bit; kenai alone is a defined-behaviour oracle only, and §5's item 3 is not
reachable from this fork at any price. It should stop being listed as a deliverable of it.
⭐ One nuance worth having, since kenai is **AMD** and every oracle here is a reading of an
**Intel** manual: AMD and Intel genuinely differ on some Intel-UNDEFINED results (`bsf`/`bsr` at
a zero source is the standard example — AMD documents the destination as preserved). So kenai is
a **more** interesting single witness than an Intel box would be — and correspondingly more
dangerous, because an AMD-specific behaviour recorded as *"the answer"* is precisely the refusal-
into-claim conversion §2 forbids. Whichever arm is built, **the oracle-assigned bits must stay
oracle-assigned**; hardware may only ever *refute* a claim of definedness, never establish one.
