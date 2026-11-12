module

public import Silmaril.Wasm.SpecTec.Sim.IntNumeric.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Provenance

/-!
# Integer numerics: what the fixed script defines

Lookups of the definitions and rules the integer simulation uses, in `simEnv B`, each checked
against the generated script by the kernel (`rfl`). The dispatchers `$unop_`, `$binop_`,
`$testop_`, `$relop_` are read straight off the generated definitions (`Original.d503`–`d506`),
not retyped. The rule transcriptions of `Equiv.ExecNumeric` and `Equiv.Execution` transfer by
`hasRuleAt_simEnv`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.IntNumeric

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d132 Original.d143 Original.d503 Original.d504
  Original.d505 Original.d506)

/-- The `(params, type, clauses)` a `DecD` contributes to the environment. -/
def defOf : Def → Option DefDef
  | .decD _ ps t cs => some (ps, t, cs)
  | _ => none

variable (B : Builtins)

set_option maxRecDepth 100000 in
/-- The numerics group of `Equiv/Numerics.lean` (`$iadd_`, `$ieq_`, `$idiv_`, …) is in the fixed
script as it is in the pinned one. -/
theorem numEnv_baseEnv : Equiv.NumEnv baseEnv :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Installing primitives does not change a lookup. -/
theorem numEnv_withBuiltins {env : Env} (h : Equiv.NumEnv env) (B : Builtins) :
    Equiv.NumEnv (env.withBuiltins B) := by
  cases h
  constructor <;> rwa [Env.findDef?_withBuiltins]

/-- …and in every `simEnv B`. -/
theorem numEnv_simEnv : Equiv.NumEnv (simEnv B) := numEnv_withBuiltins numEnv_baseEnv B

set_option maxRecDepth 100000 in
theorem findDef_size : (simEnv B).findDef? "size" = defOf Original.d132 := rfl

set_option maxRecDepth 100000 in
theorem findDef_sizenn : (simEnv B).findDef? "sizenn" = defOf Original.d143 := rfl

set_option maxRecDepth 100000 in
theorem findDef_unop : (simEnv B).findDef? "unop_" = defOf Original.d503 := rfl

set_option maxRecDepth 100000 in
theorem findDef_binop : (simEnv B).findDef? "binop_" = defOf Original.d504 := rfl

set_option maxRecDepth 100000 in
theorem findDef_testop : (simEnv B).findDef? "testop_" = defOf Original.d505 := rfl

set_option maxRecDepth 100000 in
theorem findDef_relop : (simEnv B).findDef? "relop_" = defOf Original.d506 := rfl

/-- A `hint(builtin)` declaration: in the script, with no clause. -/
def NoClauses (env : Env) (x : IL.Id) : Prop := ∃ ps t, env.findDef? x = some (ps, t, [])

/-! The ten integer primitives and `$truncz` have no clause in the fixed script. -/

set_option maxRecDepth 100000 in
theorem noClauses_iclz : NoClauses (simEnv B) "iclz_" := ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem noClauses_ictz : NoClauses (simEnv B) "ictz_" := ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem noClauses_ipopcnt : NoClauses (simEnv B) "ipopcnt_" := ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem noClauses_iand : NoClauses (simEnv B) "iand_" := ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem noClauses_ior : NoClauses (simEnv B) "ior_" := ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem noClauses_ixor : NoClauses (simEnv B) "ixor_" := ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem noClauses_ishl : NoClauses (simEnv B) "ishl_" := ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem noClauses_ishr : NoClauses (simEnv B) "ishr_" := ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem noClauses_irotl : NoClauses (simEnv B) "irotl_" := ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem noClauses_irotr : NoClauses (simEnv B) "irotr_" := ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem noClauses_truncz : NoClauses (simEnv B) "truncz" := ⟨_, _, rfl⟩

/-- The eight numeric rules of `Step_pure` (46–53), in `simEnv B`. -/
theorem hasNumericRules_simEnv : Equiv.ExecNumeric.HasNumericRules (simEnv B) := by
  have h := Equiv.ExecNumeric.hasNumericRules_wasm30
  cases h
  constructor <;> (apply hasRuleAt_simEnv; assumption)

/-- The 23 non-numeric `Step_pure` rules of `Equiv.Execution` (0–30), in `simEnv B`. -/
theorem hasPureRules_simEnv : Equiv.Execution.HasStepRules (simEnv B) := by
  have h := Equiv.Execution.hasStepRules_wasm30
  cases h
  constructor <;> (apply hasRuleAt_simEnv; assumption)

end Silmaril.Wasm.SpecTec.Sim.IntNumeric
