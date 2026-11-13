module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecAgreeEnvX
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecAgreeLk
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecAgreeCheck

/-!
# `simEnv20X` against `simEnv20V`: the family repair

`simEnv20V B` is `simEnv20X B` with the declarations of `vunop_`, `vbinop_` and `vrelop_` replaced
by their corrections (`fixedV20` is `fixedX20` with three more replacements, by `rfl`).

* `findTyp?_simEnv20V`: off the families, `simEnv20V B` finds what `simEnv20X B` finds; at a
  family, the corrected declaration.
* `envSameV`: the evaluator cannot tell `simEnv20X B` and `simEnv20V B` apart.
* **`famRelV`**: the pair is a `VecAgree.FamRel` at `C = 16`: off the families the tables agree,
  at each family the corrected instance list skips the float instances at a non-float shape and
  accepts the float operators at a float shape (`Raw/…/VecAgree/Fam`), and every declaration of
  `simEnv20X B` mentions the families only as payloads (`tableOkB_fixedX20`), with the one
  quantifier type `exp` typed alike (`qEq_exp`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (mem_of_find?)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (GoodT goodT_of_all)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V fixedV20 vunopFix20 vbinopFix20 vrelopFix20)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (repl typsOfDefs_replaceTyp defsOfDefs_replaceTyp
  relsOfDefs_replaceTyp gramsOfDefs_replaceTyp find?_map_repl EnvSame)

theorem fixedV20_eq : fixedV20 = replaceDefs (.typD "vrelop_" (typDecl vrelopFix20).1
    (typDecl vrelopFix20).2) (replaceDefs (.typD "vbinop_" (typDecl vbinopFix20).1
    (typDecl vbinopFix20).2) (replaceDefs (.typD "vunop_" (typDecl vunopFix20).1
    (typDecl vunopFix20).2) fixedX20)) := rfl

theorem simEnv20V_tables (B : Builtins) :
    (simEnv20V B).typs = (((simEnv20X B).typs.map (repl "vunop_" (typDecl vunopFix20))).map
        (repl "vbinop_" (typDecl vbinopFix20))).map (repl "vrelop_" (typDecl vrelopFix20)) ∧
      (simEnv20V B).defs = (simEnv20X B).defs ∧ (simEnv20V B).rels = (simEnv20X B).rels ∧
      (simEnv20V B).grams = (simEnv20X B).grams ∧ (simEnv20V B).builtins = B ∧
      (simEnv20X B).builtins = B := by
  simp only [simEnv20V, simEnv20X, Env.withBuiltins, envOfScript, envOfDefs_eq]
  rw [fixedV20_eq]
  refine ⟨?_, ?_, ?_, ?_, trivial, trivial⟩
  · rw [typsOfDefs_replaceTyp _ _ _ (by decide), typsOfDefs_replaceTyp _ _ _ (by decide),
      typsOfDefs_replaceTyp _ _ _ (by decide)]
    simp [Env.empty, Map.empty]
  · rw [defsOfDefs_replaceTyp, defsOfDefs_replaceTyp, defsOfDefs_replaceTyp]
  · rw [relsOfDefs_replaceTyp, relsOfDefs_replaceTyp, relsOfDefs_replaceTyp]
  · rw [gramsOfDefs_replaceTyp, gramsOfDefs_replaceTyp, gramsOfDefs_replaceTyp]

/-- **What `simEnv20V B` finds.** -/
theorem findTyp?_simEnv20V (B : Builtins) (y : IL.Id) :
    (simEnv20V B).findTyp? y =
      if y = "vrelop_" then ((simEnv20X B).findTyp? y).map fun _ => typDecl vrelopFix20
      else if y = "vbinop_" then ((simEnv20X B).findTyp? y).map fun _ => typDecl vbinopFix20
      else if y = "vunop_" then ((simEnv20X B).findTyp? y).map fun _ => typDecl vunopFix20
      else (simEnv20X B).findTyp? y := by
  simp only [Env.findTyp?]
  rw [(simEnv20V_tables B).1, find?_map_repl, find?_map_repl, find?_map_repl]
  by_cases h₁ : y = "vrelop_"
  · subst h₁; simp
  · by_cases h₂ : y = "vbinop_"
    · subst h₂; simp
    · by_cases h₃ : y = "vunop_"
      · subst h₃; simp
      · simp [h₁, h₂, h₃]

theorem findTyp_off_simEnv20V (B : Builtins) {y : IL.Id} (hy : fams.contains y = false) :
    (simEnv20V B).findTyp? y = (simEnv20X B).findTyp? y := by
  have h₁ : y ≠ "vrelop_" := by rintro rfl; simp [fams] at hy
  have h₂ : y ≠ "vbinop_" := by rintro rfl; simp [fams] at hy
  have h₃ : y ≠ "vunop_" := by rintro rfl; simp [fams] at hy
  rw [findTyp?_simEnv20V]
  simp [h₁, h₂, h₃]

theorem findTyp_fam_simEnv20V (B : Builtins) :
    (simEnv20V B).findTyp? "vunop_" = some (typDecl vunopFix20) ∧
      (simEnv20V B).findTyp? "vbinop_" = some (typDecl vbinopFix20) ∧
      (simEnv20V B).findTyp? "vrelop_" = some (typDecl vrelopFix20) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [findTyp?_simEnv20V] <;>
    simp [findTyp_vunopX, findTyp_vbinopX, findTyp_vrelopX]

/-! ## The evaluator cannot tell them apart -/

theorem memTyp_simEnv20V (B : Builtins) (x : IL.Id) :
    (simEnv20V B).memTyp x = (simEnv20X B).memTyp x := by
  simp only [Env.memTyp, Map.mem]
  have h := findTyp?_simEnv20V B x
  simp only [Env.findTyp?] at h
  rw [h]
  split
  · cases Map.find? (simEnv20X B).typs x <;> rfl
  · split
    · cases Map.find? (simEnv20X B).typs x <;> rfl
    · split
      · cases Map.find? (simEnv20X B).typs x <;> rfl
      · rfl

theorem subCaseOk_off {B : Builtins} {x : IL.Id} (hx : fams.contains x = false) (ρ : VarEnv)
    (v : Value) : subCaseOk (simEnv20V B) ρ (.varT x []) v = subCaseOk (simEnv20X B) ρ (.varT x []) v := by
  cases v with
  | case op w => simp only [subCaseOk, findTyp_off_simEnv20V B hx]
  | _ => simp only [subCaseOk]

theorem subCaseOk_fam {B : Builtins} {d d' : Def} {f : String} (hf : FamForm d d' f)
    (hX : (simEnv20X B).findTyp? f = some (typDecl d))
    (hV : (simEnv20V B).findTyp? f = some (typDecl d')) (ρ : VarEnv) (v : Value) :
    subCaseOk (simEnv20V B) ρ (.varT f []) v = subCaseOk (simEnv20X B) ρ (.varT f []) v := by
  obtain ⟨ps, ji, bs, pats, h₁, h₂⟩ := hf
  cases v with
  | case op w =>
    simp only [subCaseOk]
    rw [hX, hV, h₁, h₂]
    split <;> try rfl
    split <;> split <;> simp_all
  | _ => simp only [subCaseOk]

theorem subCaseOk_simEnv20V (B : Builtins) :
    subCaseOk (simEnv20V B) = subCaseOk (simEnv20X B) := by
  funext ρ t v
  obtain ⟨hV₁, hV₂, hV₃⟩ := findTyp_fam_simEnv20V B
  cases t with
  | varT x args =>
    cases args with
    | nil =>
      by_cases hx : fams.contains x = false
      · exact subCaseOk_off hx ρ v
      · simp only [fams, List.contains_cons, List.contains_nil, Bool.or_false, Bool.not_eq_false,
          Bool.or_eq_true, beq_iff_eq] at hx
        rcases hx with rfl | rfl | rfl
        · exact subCaseOk_fam famForm_vunop findTyp_vunopX hV₁ ρ v
        · exact subCaseOk_fam famForm_vbinop findTyp_vbinopX hV₂ ρ v
        · exact subCaseOk_fam famForm_vrelop findTyp_vrelopX hV₃ ρ v
    | cons _ _ => simp only [subCaseOk]
  | _ => simp only [subCaseOk]

/-- **The evaluator cannot tell `simEnv20X B` and `simEnv20V B` apart.** -/
theorem envSameV (B : Builtins) : EnvSame (simEnv20X B) (simEnv20V B) := by
  obtain ⟨-, hd, hr, hg, hb, hb'⟩ := simEnv20V_tables B
  refine ⟨fun x => ?_, fun x => ?_, hb.trans hb'.symm, ?_, ?_, ?_⟩
  · simp only [Env.findDef?, hd]
  · simp only [Env.findRel?, hr]
  · funext ρ pat t
    simp only [matchTypV, memTyp_simEnv20V]
  · funext ρ pat g
    have hm : ∀ x, (simEnv20V B).memGram x = (simEnv20X B).memGram x := by
      intro x; simp only [Env.memGram, hg]
    simp only [matchSymV, hm]
  · funext ρ e v
    simp only [argSubOk, subCaseOk_simEnv20V]

end Silmaril.Wasm.SpecTec.Sim20.VecAgree
