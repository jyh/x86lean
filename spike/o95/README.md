# spike/o95 — the O95 router spike

A machine-code router (`Router/Repaired.lean`, the program as x86lean `Instr`s) proved to refine the VIR
specification's exit relation `F_exit` for ALL states (`Router.Refines.repaired_refines`), and two calls composed
(`Router.MultiCall.two_calls`, with `two_calls_witness` discharging every premise on one concrete layout). It is a
separate Lake package that uses x86lean as a library and VIR as the specification:

- x86lean, pinned to public master `b1848ac` (`lakefile.toml`)
- VIR, pinned to `ba6f3fc` at https://github.com/jyh/vir (`subDir = "lean"`)

Build: `lake build` in this directory. Axioms: `lake env lean audit/Axioms.lean`. The receipt of record is
`audit/axioms-public-2026-11-01.log`: the build exits 0, every theorem depends only on `propext`, `Classical.choice`
and `Quot.sound`, and the file's own `control_sorry` prints `sorryAx`, so the scan can see a sorry.

`SPIKE-PLAN.md` is the plan as it was written while the spike was private (until 2026-11-01). Its history is kept
under this path as it was made; see the merge commit that brought it here.
