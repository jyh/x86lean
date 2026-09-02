/-
# AxiomGate — the CI axiom ALLOWLIST

Plan v1 §3.6 and TRUSTBASE.md: every declaration outside the `X86Native` tier
and the test tree may depend on EXACTLY these three axioms and no others —

    propext · Classical.choice · Quot.sound

⛔ WHY AN ALLOWLIST AND NOT A DENYLIST, which is the whole reason this program
exists.  The obvious gate is "reject anything that depends on
`Lean.ofReduceBool`".  It does not work: since Lean 4.29 a `native_decide` call
adds a FRESH, PER-COMPUTATION axiom whose NAME is derived from the computation,
so a denylist keyed on `Lean.ofReduceBool` sees nothing and passes.  An
allowlist cannot miss a name it has never heard of.  The red-first drive
(`scripts/axiom_gate_selftest.sh`) proves this on a real `native_decide`
declaration in `X86Native` rather than on a fixture.

USAGE
    x86lean-axioms <Module> [<Module> …]
Scans every constant DECLARED IN those modules (transitively imported modules
are loaded but not scanned) and reports any that depends on an axiom outside the
allowlist.  Exit 0 = clean, 1 = a violation, 2 = a usage or load error.

    x86lean-axioms --expect-violation <Module> [<Module> …]
Inverts the verdict: exit 0 only if a violation IS found.  This is what makes
the gate's own selftest a real test — a gate that has never been seen to FAIL is
not known to be a gate.
-/
import Lean
import X86

open Lean

namespace AxiomGate

/-- The allowlist.  Changing this list is a change to TRUSTBASE.md and must be
argued there, not here. -/
def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Collect the axioms of every constant declared in `scan`, and return the
offenders as (constant, disallowed axioms). -/
def offenders (env : Environment) (scan : List Name) : CoreM (Array (Name × Array Name)) := do
  let modNames := env.header.moduleNames
  let mut out : Array (Name × Array Name) := #[]
  for (n, _) in env.constants.toList do
    -- only constants DECLARED in a scanned module
    let some idx := env.getModuleIdxFor? n | continue
    let some m := modNames[idx.toNat]? | continue
    unless scan.contains m do continue
    let ax ← collectAxioms n
    let bad := ax.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      out := out.push (n, bad)
  return out

end AxiomGate

def main (args : List String) : IO UInt32 := do
  let expectViolation := args.contains "--expect-violation"
  let mods := (args.filter (fun a => !a.startsWith "--")).map String.toName
  if mods.isEmpty then
    IO.eprintln "usage: x86lean-axioms [--expect-violation] <Module> [<Module> …]"
    return 2
  initSearchPath (← findSysroot)
  let env ← importModules (mods.map (fun m => { module := m })).toArray {}
  let ctx : Core.Context := { fileName := "<axiom-gate>", fileMap := default }
  let st : Core.State := { env }
  let (bad, _) ← (AxiomGate.offenders env mods).toIO ctx st
  let scanned := mods.map toString
  if bad.isEmpty then
    IO.println s!"axiom-gate: CLEAN — every declaration in {scanned} depends only on \
{AxiomGate.allowed.map toString}"
    if expectViolation then
      IO.eprintln "axiom-gate: ⛔ SELFTEST FAILED — a violation was EXPECTED and none was found. \
The gate cannot be trusted to fail, so it cannot be trusted to pass."
      return 1
    return 0
  else
    IO.println s!"axiom-gate: {bad.size} declaration(s) outside the allowlist:"
    for (n, ax) in bad do
      IO.println s!"  {n}  ⟵  {ax.toList.map toString}"
    if expectViolation then
      IO.println "axiom-gate: SELFTEST PASSED — the gate fires on a real violation."
      return 0
    return 1
