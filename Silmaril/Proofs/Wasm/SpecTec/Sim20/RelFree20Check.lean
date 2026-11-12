module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.RelFreeEq
public import Silmaril.Wasm.SpecTec.Sim20.StepFix.Defs

/-!
# Kernel checks: the 2.0 script is relation-free away from `$instantiate`, and `Step`'s rules

* `defsOkB_fixed20`, `typsOkB_fixed20`: every definition other than `$instantiate`, and every
  type, of the fixed wasm-2.0 script is relation-free (`bad20 = ["instantiate"]`);
* `stepRules20_spec`: `Step` has the same type in `simEnv20 B` and `simEnv20S B`, its corrected
  rules are the five structural rules followed by the original rules 4–21, and those 18 rules pass
  `ruleOkB bad20`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.RelFree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.StepFix

/-- The definitions that may refer to relations in the wasm-2.0 script. -/
def bad20 : List String := ["instantiate"]

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- **Every definition of the fixed wasm-2.0 script other than `$instantiate` is relation-free**
(kernel). -/
theorem defsOkB_fixed20 : defsOkB bad20 (defsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed) = true := by
  decide +kernel

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- **Every type of the fixed wasm-2.0 script is relation-free** (kernel). -/
theorem typsOkB_fixed20 : typsOkB bad20 (typsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed) = true := by
  decide +kernel

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `Step` in both environments (kernel). -/
theorem stepRules20_spec (B : Builtins) : ∃ t rules,
    (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B).findRel? "Step" = some ([], "%~>%", t, rules) ∧
    (simEnv20S B).findRel? "Step" =
      some ([], "%~>%", t, [pureFix, readFix, ctxtInstrsFix, ctxtLabelFix, ctxtFrameFix] ++ rules.drop 4) ∧
    (rules.drop 4).all (ruleOkB bad20) = true :=
  ⟨_, _, rfl, rfl, by decide +kernel⟩

end Silmaril.Wasm.SpecTec.Sim20.RelFree
