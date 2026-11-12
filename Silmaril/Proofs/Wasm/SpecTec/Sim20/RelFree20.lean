module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.RelFree20Check
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.RelFree20Rules

/-!
# The 2.0 script is relation-free away from `$instantiate`; the corrected script differs only in
# its relations

* `defsOkB_fixed20`, `typsOkB_fixed20` (kernel): in the fixed wasm-2.0 script, every definition
  other than `$instantiate` and every type is relation-free (`bad20 = ["instantiate"]`), so
  `defsGood_simEnv20`, `typsGood_simEnv20` hold at every builtins;
* `simEnv20S_eq`: `simEnv20S B` is `simEnv20 B` with another relation table. `stepErratum20`
  replaces one relation, so the type, definition and grammar tables are unchanged
  (`typsOfDefs_replace`, `defsOfDefs_replace`, `gramsOfDefs_replace`, structural);
* `stepRules20_spec` (kernel): `Step` has the same type in both environments, its corrected rules
  are the five structural rules followed by the original rules 4–21, and those 18 rules pass
  `ruleOkB bad20` (no relation reference, no `$instantiate`, no `otherwise`);
* `spure20S_iff`, `sread20S_iff`: `Step_pure` and `Step_read` derive alike in both environments
  (`pureRules20_spec`, `readRules20_spec`, kernel: the relations are unchanged and their rules are
  relation-free; `otherwise` premises are carried by `RelFree.otherwiseAt_withRels_iff`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.RelFree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.StepFix

/-! ## The tables of `simEnv20 B` -/

theorem mem_of_find?' {α : Type} {m : Map α} {x : IL.Id} {v : α} (h : m.find? x = some v) :
    (x, v) ∈ m :=
  Silmaril.Wasm.SpecTec.Sim.Round7.Script.mem_of_find? h

/-- **The definitions of `simEnv20 B` other than `$instantiate` are relation-free.** -/
theorem defsGood_simEnv20 (B : Builtins) :
    DefsGood bad20 (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) := by
  intro x d hx hd
  have hm : (x, d) ∈ defsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed := by
    have h' : (defsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed).find? x = some d := by
      simpa [Silmaril.Wasm.SpecTec.Sim20.simEnv20, Silmaril.Wasm.SpecTec.Sim20.baseEnv20,
        Env.withBuiltins, Env.findDef?] using hd
    exact mem_of_find?' h'
  have h := List.all_eq_true.1 defsOkB_fixed20 _ hm
  simp only [GoodName] at hx
  simp only [hx, Bool.false_or] at h
  intro c hc
  exact goodEvs_of_all (List.all_eq_true.1 h c hc)

/-- **The types of `simEnv20 B` are relation-free.** -/
theorem typsGood_simEnv20 (B : Builtins) : TypsGood bad20 (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) := by
  intro x td hd
  have hm : (x, td) ∈ typsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed := by
    have h' : (typsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed).find? x = some td := by
      simpa [Silmaril.Wasm.SpecTec.Sim20.simEnv20, Silmaril.Wasm.SpecTec.Sim20.baseEnv20,
        Env.withBuiltins, Env.findTyp?] using hd
    exact mem_of_find?' h'
  intro i hi
  exact goodEvs_of_all (List.all_eq_true.1 (List.all_eq_true.1 typsOkB_fixed20 _ hm) i hi)

/-! ## Replacing a relation leaves the other tables alone -/

mutual
theorem typsOfDef_replace (x ps op t rules) : ∀ d : Def,
    typsOfDef (replaceDef (.relD x ps op t rules) d) = typsOfDef d
  | .recD ds => by simp only [replaceDef, typsOfDef]; exact typsOfDefs_replace x ps op t rules ds
  | .typD _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .decD _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .gramD _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .relD _ _ _ _ _ => by simp only [replaceDef]; split <;> rfl
theorem typsOfDefs_replace (x ps op t rules) : ∀ ds : List Def,
    typsOfDefs (replaceDefs (.relD x ps op t rules) ds) = typsOfDefs ds
  | [] => rfl
  | d :: ds => by
    simp only [replaceDefs, typsOfDefs]
    rw [typsOfDef_replace x ps op t rules d, typsOfDefs_replace x ps op t rules ds]
end

mutual
theorem defsOfDef_replace (x ps op t rules) : ∀ d : Def,
    defsOfDef (replaceDef (.relD x ps op t rules) d) = defsOfDef d
  | .recD ds => by simp only [replaceDef, defsOfDef]; exact defsOfDefs_replace x ps op t rules ds
  | .typD _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .decD _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .gramD _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .relD _ _ _ _ _ => by simp only [replaceDef]; split <;> rfl
theorem defsOfDefs_replace (x ps op t rules) : ∀ ds : List Def,
    defsOfDefs (replaceDefs (.relD x ps op t rules) ds) = defsOfDefs ds
  | [] => rfl
  | d :: ds => by
    simp only [replaceDefs, defsOfDefs]
    rw [defsOfDef_replace x ps op t rules d, defsOfDefs_replace x ps op t rules ds]
end

mutual
theorem gramsOfDef_replace (x ps op t rules) : ∀ d : Def,
    gramsOfDef (replaceDef (.relD x ps op t rules) d) = gramsOfDef d
  | .recD ds => by simp only [replaceDef, gramsOfDef]; exact gramsOfDefs_replace x ps op t rules ds
  | .typD _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .decD _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .gramD _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .relD _ _ _ _ _ => by simp only [replaceDef]; split <;> rfl
theorem gramsOfDefs_replace (x ps op t rules) : ∀ ds : List Def,
    gramsOfDefs (replaceDefs (.relD x ps op t rules) ds) = gramsOfDefs ds
  | [] => rfl
  | d :: ds => by
    simp only [replaceDefs, gramsOfDefs]
    rw [gramsOfDef_replace x ps op t rules d, gramsOfDefs_replace x ps op t rules ds]
end

/-- The corrected `Step` is a relation declaration. -/
theorem stepFix20_relD : ∃ x ps op t rules, stepFix20 = .relD x ps op t rules := by
  unfold stepFix20 stepRel20
  exact ⟨_, _, _, _, _, rfl⟩

/-- **`simEnv20S B` is `simEnv20 B` with another relation table.** -/
theorem simEnv20S_eq (B : Builtins) :
    simEnv20S B = withRels (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) (simEnv20S B).rels := by
  obtain ⟨x, ps, op, t, rules, h⟩ := stepFix20_relD
  have ht := typsOfDefs_replace x ps op t rules Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed
  have hd := defsOfDefs_replace x ps op t rules Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed
  have hg := gramsOfDefs_replace x ps op t rules Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed
  rw [← h] at ht hd hg
  simp only [simEnv20S, Silmaril.Wasm.SpecTec.Sim20.simEnv20, Silmaril.Wasm.SpecTec.Sim20.baseEnv20,
    fixedS20, Env.withBuiltins, envOfScript, envOfDefs_eq, ht, hd, hg]

/-! ## `Step_pure` and `Step_read` agree -/

/-- A relation that `simEnv20 B` and `simEnv20S B` give the same relation-free rules fires alike
in both. -/
theorem fires20S_iff_of_spec {B : Builtins} {x : IL.Id} {t : Typ} {rules : List Rule}
    (h₁ : (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B).findRel? x = some ([], "%~>%", t, rules))
    (h₂ : (simEnv20S B).findRel? x = some ([], "%~>%", t, rules))
    (hok : rules.all (fun r => (Silmaril.Wasm.SpecTec.Sim.Round7.Script.evRule r).all (rfEvB bad20)) =
      true) (i : Nat) (v : Value) :
    Sim.Fires (simEnv20S B) x i v ↔ Sim.Fires (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) x i v := by
  have hx : (withRels (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) (simEnv20S B).rels).findRel? x =
      (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B).findRel? x := by
    have h₂' := h₂
    rw [simEnv20S_eq B] at h₂'
    exact h₂'.trans h₁.symm
  have hrules : ∀ ps op t' rules', (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B).findRel? x =
      some (ps, op, t', rules') → ∀ r ∈ rules',
        (Silmaril.Wasm.SpecTec.Sim.Round7.Script.evRule r).all (rfEvB bad20) = true := by
    intro ps op t' rules' h r hr
    rw [h₁] at h
    obtain rfl : rules = rules' := by simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.2.2
    exact List.all_eq_true.1 hok r hr
  rw [simEnv20S_eq B]
  exact fires_withRels_iff (defsGood_simEnv20 B) (typsGood_simEnv20 B) hx hrules i v

/-- **`Step_pure` fires alike in `simEnv20 B` and `simEnv20S B`.** -/
theorem spure20S_iff (B : Builtins) (is js : List Value) :
    Sim.SPure (simEnv20S B) is js ↔ Sim.SPure (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) is js := by
  obtain ⟨t, rules, h₁, h₂, hok⟩ := pureRules20_spec B
  rw [Sim.SPure, Sim.SPure, Sim.dderives_iff_fires h₁, Sim.dderives_iff_fires h₂]
  exact exists_congr fun i => fires20S_iff_of_spec h₁ h₂ hok i _

/-- **`Step_read` fires alike in `simEnv20 B` and `simEnv20S B`.** -/
theorem sread20S_iff (B : Builtins) (c : Value) (js : List Value) :
    Sim.SRead (simEnv20S B) c js ↔ Sim.SRead (Silmaril.Wasm.SpecTec.Sim20.simEnv20 B) c js := by
  obtain ⟨t, rules, h₁, h₂, hok⟩ := readRules20_spec B
  rw [Sim.SRead, Sim.SRead, Sim.dderives_iff_fires h₁, Sim.dderives_iff_fires h₂]
  exact exists_congr fun i => fires20S_iff_of_spec h₁ h₂ hok i _

end Silmaril.Wasm.SpecTec.Sim20.RelFree
