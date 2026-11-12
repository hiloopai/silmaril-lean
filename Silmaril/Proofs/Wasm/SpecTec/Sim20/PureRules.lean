module

public import Silmaril.Wasm.SpecTec.Sim20.Pure.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Reading.Script

/-!
# The wasm-2.0 `Step_pure` rules in `simEnv20 B`, and the two readings

`hasRuleAt_*`: rule `k` of `Step_pure` in `simEnv20 B` is the verbatim rule of `Sim20.Pure.Defs`
(kernel `rfl`). `closedB_pure20`: `Step_pure` is closed in the wasm-2.0 script (no conclusion has
an empty-domain option iteration and no premise consults a relation), so under it the backend
reading `FiresB`/`SPureB` and the declarative reading `Fires`/`SPure` agree
(`firesB_pure20_iff`, `sPureB20_iff`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Pure

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading

variable (B : Builtins)

set_option maxRecDepth 100000


/-- `Step_pure/unreachable` is rule 0. -/
theorem hasRuleAt_unreachable : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 0 unreachableRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/nop` is rule 1. -/
theorem hasRuleAt_nop : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 1 nopRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/drop` is rule 2. -/
theorem hasRuleAt_drop : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 2 dropRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/select-true` is rule 3. -/
theorem hasRuleAt_selectTrue : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 3 selectTrueRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/select-false` is rule 4. -/
theorem hasRuleAt_selectFalse : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 4 selectFalseRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/if-true` is rule 5. -/
theorem hasRuleAt_ifTrue : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 5 ifTrueRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/if-false` is rule 6. -/
theorem hasRuleAt_ifFalse : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 6 ifFalseRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/label-vals` is rule 7. -/
theorem hasRuleAt_labelVals : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 7 labelValsRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/br-zero` is rule 8. -/
theorem hasRuleAt_brZero : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 8 brZeroRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/br-succ` is rule 9. -/
theorem hasRuleAt_brSucc : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 9 brSuccRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/br_if-true` is rule 10. -/
theorem hasRuleAt_brIfTrue : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 10 brIfTrueRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/br_if-false` is rule 11. -/
theorem hasRuleAt_brIfFalse : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 11 brIfFalseRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/br_table-lt` is rule 12. -/
theorem hasRuleAt_brTableLt : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 12 brTableLtRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/br_table-ge` is rule 13. -/
theorem hasRuleAt_brTableGe : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 13 brTableGeRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/frame-vals` is rule 14. -/
theorem hasRuleAt_frameVals : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 14 frameValsRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/return-frame` is rule 15. -/
theorem hasRuleAt_returnFrame : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 15 returnFrameRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/return-label` is rule 16. -/
theorem hasRuleAt_returnLabel : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 16 returnLabelRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/trap-vals` is rule 17. -/
theorem hasRuleAt_trapVals : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 17 trapValsRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/trap-label` is rule 18. -/
theorem hasRuleAt_trapLabel : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 18 trapLabelRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/trap-frame` is rule 19. -/
theorem hasRuleAt_trapFrame : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 19 trapFrameRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/unop-val` is rule 20. -/
theorem hasRuleAt_unopVal : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 20 unopValRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/unop-trap` is rule 21. -/
theorem hasRuleAt_unopTrap : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 21 unopTrapRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/binop-val` is rule 22. -/
theorem hasRuleAt_binopVal : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 22 binopValRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/binop-trap` is rule 23. -/
theorem hasRuleAt_binopTrap : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 23 binopTrapRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/testop` is rule 24. -/
theorem hasRuleAt_testop : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 24 testopRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/relop` is rule 25. -/
theorem hasRuleAt_relop : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 25 relopRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/cvtop-val` is rule 26. -/
theorem hasRuleAt_cvtopVal : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 26 cvtopValRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `Step_pure/cvtop-trap` is rule 27. -/
theorem hasRuleAt_cvtopTrap : HasRuleAt (simEnv20 B) "Step_pure" "%~>%" 27 cvtopTrapRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- `Step_pure` is closed in the wasm-2.0 script. -/
theorem closedB_pure20 :
    closedB (envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed) ["Step_pure"] = true := by
  rfl

/-- `Step_pure` is closed in `simEnv20 B`. -/
theorem closed_pure20 : Closed (simEnv20 B) (· ∈ ["Step_pure"]) :=
  closed_congr (fun _ => rfl) (closed_of_closedB closedB_pure20)

/-- On `Step_pure`, a rule fires under the backend reading exactly when it fires declaratively. -/
theorem firesB_pure20_iff {i : Nat} {v : Value} :
    FiresB (simEnv20 B) "Step_pure" i v ↔ Fires (simEnv20 B) "Step_pure" i v :=
  firesB_iff_of_closed (closed_pure20 B) (by simp)

/-- On `Step_pure`, the backend reading is the declarative reading. -/
theorem sPureB20_iff {is js : List Value} :
    SPureB (simEnv20 B) is js ↔ SPure (simEnv20 B) is js :=
  dderivesB_otherwise_iff_of_closed (closed_pure20 B) (by simp)

end Silmaril.Wasm.SpecTec.Sim20.Pure
