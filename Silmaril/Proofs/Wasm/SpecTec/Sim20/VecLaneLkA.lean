module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecLanePack

/-!
# Lookups in `simEnv20V` for `vextract_lane-pack` (kernel `rfl`)

Rule 47 of `Step_pure`, the clauses of `$psize`, and the clause-free declaration of `$extend__`, as
`simEnv20V B` finds them.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecLane

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)

set_option maxRecDepth 100000 in
theorem hasRuleAt_vextractLanePack20V (B : Builtins) :
    Equiv.Validation.HasRuleAt (simEnv20V B) "Step_pure" "%~>%" 47 vextractLanePackRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem findDef_psize20V (B : Builtins) : ∃ ps t, (simEnv20V B).findDef? "psize" = some (ps, t,
    [.defD [] [.expA (.caseE "I8" (.tupE []))] (.numE (.natN 8)) [],
     .defD [] [.expA (.caseE "I16" (.tupE []))] (.numE (.natN 16)) []]) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findDef_extend20V (B : Builtins) : ∃ ps t, (simEnv20V B).findDef? "extend__" = some (ps, t, []) :=
  ⟨_, _, rfl⟩

end Silmaril.Wasm.SpecTec.Sim20.VecLane
