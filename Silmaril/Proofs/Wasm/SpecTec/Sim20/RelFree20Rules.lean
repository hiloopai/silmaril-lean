module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.RelFree20Check

/-!
# Kernel checks: `Step_pure` and `Step_read` are unchanged by the erratum and relation-free

`pureRules20_spec`, `readRules20_spec`: each relation is the same in `simEnv20 B` and
`simEnv20S B`, and its rules refer to no relation and not to `$instantiate`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.RelFree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.StepFix

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `Step_pure` is the same relation in both environments, and its 56 rules are relation-free
(kernel); two of them (`ref.is_null-false`, `vtestop-false`) have an `otherwise` premise. -/
theorem pureRules20_spec (B : Builtins) : ∃ t rules,
    (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B).findRel? "Step_pure" = some ([], "%~>%", t, rules) ∧
    (simEnv20S B).findRel? "Step_pure" = some ([], "%~>%", t, rules) ∧
    rules.all (fun r => (Silmaril.Wasm.SpecTec.Sim.Round7.Script.evRule r).all (rfEvB bad20)) = true :=
  ⟨_, _, rfl, rfl, by decide +kernel⟩

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `Step_read` is the same relation in both environments, and its 47 rules are relation-free
(kernel); fifteen of them have an `otherwise` premise. -/
theorem readRules20_spec (B : Builtins) : ∃ t rules,
    (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B).findRel? "Step_read" = some ([], "%~>%", t, rules) ∧
    (simEnv20S B).findRel? "Step_read" = some ([], "%~>%", t, rules) ∧
    rules.all (fun r => (Silmaril.Wasm.SpecTec.Sim.Round7.Script.evRule r).all (rfEvB bad20)) = true :=
  ⟨_, _, rfl, rfl, by decide +kernel⟩

end Silmaril.Wasm.SpecTec.Sim20.RelFree
