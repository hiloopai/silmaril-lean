module

public import Silmaril.Wasm.SpecTec.Sim.IntNumeric.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Ops
public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Main
public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.BackwardParam
public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Findings

/-!
# SpecTec ↔ Core 3.0, integer numerics: what is proved

* `applies_binop_int`, `applies_unop_int`, `applies_testop_int`, `applies_relop_int`: in
  `simEnv B` with `IntB B`, the script's dispatchers `$binop_`, `$unop_`, `$testop_`, `$relop_` at
  `I32`/`I64` denote `IntegerN.ibinop_` (empty list exactly on a trap), `iunop_`, `itestop_`,
  `irelop_` (which `Numerics.ibinop_agree` & co. equate with Core's operators). The dispatch is the
  script's own; `B` supplies only the `hint(builtin)` primitives and `$truncz`, plus `$irem_`'s
  signed non-zero case, whose only clause the evaluator cannot run.
-/
