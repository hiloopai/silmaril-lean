module

public import Silmaril.Wasm.SpecTec.Sim.Defs
public import Silmaril.Wasm.SpecTec.Scripts.Original.Thms
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecStepRules

/-!
# Provenance: the fixed script has the pinned script's relations

`Scripts.Wasm30.fixed` changes no relation, so every `HasRuleAt` fact proved against
`envOfScript Specs.wasm30` (the 218 rule transcriptions of `Equiv.Exec*`) holds of `baseEnv` and of
every `simEnv B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)

set_option maxRecDepth 100000 in
/-- The errata of `fixed` touch no relation: the two scripts bind the same relations. -/
theorem relsOfDefs_fixed :
    relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed =
      relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.original := by
  rfl

/-- `baseEnv` looks every relation up as the pinned script does. -/
theorem baseEnv_findRel (x : IL.Id) :
    baseEnv.findRel? x = (envOfScript Specs.wasm30).findRel? x := by
  simp only [baseEnv, Env.findRel?, rels_envOfScript, relsOfDefs_fixed,
    Silmaril.Wasm.SpecTec.Scripts.wasm30_original_eq]

/-- So does `simEnv B`, whatever the primitives. -/
theorem simEnv_findRel (B : Builtins) (x : IL.Id) :
    (simEnv B).findRel? x = (envOfScript Specs.wasm30).findRel? x := by
  rw [simEnv, Env.findRel?_withBuiltins, baseEnv_findRel]

/-- A rule fact transfers along an equality of lookups. -/
theorem hasRuleAt_of_findRel {env env' : Env} {x : IL.Id} {op : MixopS} {k : Nat} {r : Rule}
    (h : env'.findRel? x = env.findRel? x) (hr : HasRuleAt env x op k r) :
    HasRuleAt env' x op k r := by
  obtain ⟨ps, t, rules, hrel, hps, hk⟩ := hr
  exact ⟨ps, t, rules, h.trans hrel, hps, hk⟩

/-- Every rule fact about the pinned script holds of `simEnv B`. -/
theorem hasRuleAt_simEnv (B : Builtins) {x : IL.Id} {op : MixopS} {k : Nat} {r : Rule}
    (hr : HasRuleAt (envOfScript Specs.wasm30) x op k r) : HasRuleAt (simEnv B) x op k r :=
  hasRuleAt_of_findRel (simEnv_findRel B x) hr

/-- The 36 rules of `Step` (`Equiv.ExecStepRules`), in `simEnv B`. -/
theorem hasStepRules_simEnv (B : Builtins) : Equiv.ExecStepRules.HasStepRules (simEnv B) := by
  have h := Equiv.ExecStepRules.hasStepRules_wasm30
  cases h
  constructor <;> (apply hasRuleAt_simEnv; assumption)

end Silmaril.Wasm.SpecTec.Sim
