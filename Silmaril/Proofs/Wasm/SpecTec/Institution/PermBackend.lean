module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.PermInst

/-!
# Renaming identifiers: the backend conclusion reading is equivariant

`Round6.Reading.conclAlts` reads a conclusion with an empty-domain option iteration as each of its
`optAlts`. Renaming identifiers commutes with both `hasOptNil` and `optAlts`, so the backend
reading is equivariant (`backend_equivariant`) and `instP` exists at it (`instPBackend`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Perm

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading

variable (f : IL.Id → IL.Id)

mutual

theorem hasOptNil_rn : ∀ e : Exp, hasOptNil (rnExp f e) = hasOptNil e
  | .varE _ | .boolE _ | .numE _ | .textE _ => rfl
  | .unE _ _ e | .projE e _ | .caseE _ e | .uncaseE e _ | .theE e | .dotE e _ | .liftE e
  | .lenE e | .cvtE e _ _ => by simp only [rnExp, hasOptNil, hasOptNil_rn e]
  | .subE e _ _ => by simp only [rnExp, hasOptNil, hasOptNil_rn e]
  | .binE _ _ e₁ e₂ | .cmpE _ _ e₁ e₂ | .compE e₁ e₂ | .memE e₁ e₂ | .catE e₁ e₂
  | .idxE e₁ e₂ => by simp only [rnExp, hasOptNil, hasOptNil_rn e₁, hasOptNil_rn e₂]
  | .updE e₁ _ e₂ | .extE e₁ _ e₂ => by
    simp only [rnExp, hasOptNil, hasOptNil_rn e₁, hasOptNil_rn e₂]
  | .sliceE e₁ e₂ e₃ => by
    simp only [rnExp, hasOptNil, hasOptNil_rn e₁, hasOptNil_rn e₂, hasOptNil_rn e₃]
  | .tupE es | .listE es => by simp only [rnExp, hasOptNil, hasOptNilL_rn es]
  | .optE eo => by simp only [rnExp, hasOptNil, hasOptNilO_rn eo]
  | .strE fs => by simp only [rnExp, hasOptNil, hasOptNilF_rn fs]
  | .callE _ args => by simp only [rnExp, hasOptNil, hasOptNilA_rn args]
  | .iterE e ⟨it, ds⟩ => by
    rcases it with _ | _ | _ | ⟨_, _⟩ <;> rcases ds with _ | ⟨_, _⟩ <;>
      simp only [rnExp, rnIterExp, rnIter, rnDoms, hasOptNil, hasOptNil_rn e]

theorem hasOptNilL_rn : ∀ es : List Exp, hasOptNilL (rnExps f es) = hasOptNilL es
  | [] => rfl
  | e :: es => by simp only [rnExps, hasOptNilL, hasOptNil_rn e, hasOptNilL_rn es]

theorem hasOptNilO_rn : ∀ eo : Option Exp, hasOptNilO (rnExpOpt f eo) = hasOptNilO eo
  | none => rfl
  | some e => by simp only [rnExpOpt, hasOptNilO, hasOptNil_rn e]

theorem hasOptNilF_rn : ∀ fs : List ExpField, hasOptNilF (rnExpFields f fs) = hasOptNilF fs
  | [] => rfl
  | .mk _ e :: fs => by
    simp only [rnExpFields, rnExpField, hasOptNilF, hasOptNil_rn e, hasOptNilF_rn fs]

theorem hasOptNilA_rn : ∀ l : List Arg, hasOptNilA (rnArgs f l) = hasOptNilA l
  | [] => rfl
  | .expA e :: l => by simp only [rnArgs, rnArg, hasOptNilA, hasOptNil_rn e, hasOptNilA_rn l]
  | .typA _ :: l | .defA _ :: l | .gramA _ :: l => by
    simp only [rnArgs, rnArg, hasOptNilA, hasOptNilA_rn l]

end

section OptAlts

set_option linter.unusedSimpArgs false

mutual

theorem optAlts_rn : ∀ e : Exp, optAlts (rnExp f e) = (optAlts e).map (rnExp f)
  | .varE _ | .boolE _ | .numE _ | .textE _ => rfl
  | .unE _ _ e | .projE e _ | .caseE _ e | .uncaseE e _ | .theE e | .dotE e _ | .liftE e
  | .lenE e | .cvtE e _ _ | .subE e _ _ => by
    simp only [rnExp, optAlts, optAlts_rn e, List.map_map, Function.comp_def]
  | .binE _ _ e₁ e₂ | .cmpE _ _ e₁ e₂ | .compE e₁ e₂ | .memE e₁ e₂ | .catE e₁ e₂
  | .idxE e₁ e₂ | .updE e₁ _ e₂ | .extE e₁ _ e₂ => by
    simp only [rnExp, optAlts, optAlts_rn e₁, optAlts_rn e₂, prod2, List.flatMap_map,
      List.map_flatMap, List.map_map, Function.comp_def]
  | .sliceE e₁ e₂ e₃ => by
    simp only [rnExp, optAlts, optAlts_rn e₁, optAlts_rn e₂, optAlts_rn e₃, prod2,
      List.flatMap_map, List.map_flatMap, List.flatMap_assoc, List.map_map, Function.comp_def]
  | .tupE es | .listE es => by
    simp only [rnExp, optAlts, optAltsL_rn es, List.map_map, Function.comp_def]
  | .optE eo => by simp only [rnExp, optAlts, optAltsO_rn eo, List.map_map, Function.comp_def]
  | .strE fs => by simp only [rnExp, optAlts, optAltsF_rn fs, List.map_map, Function.comp_def]
  | .callE _ args => by
    simp only [rnExp, optAlts, optAltsA_rn args, List.map_map, Function.comp_def]
  | .iterE e ⟨it, ds⟩ => by
    rcases it with _ | _ | _ | ⟨_, _⟩ <;> rcases ds with _ | ⟨_, _⟩ <;>
      simp only [rnExp, rnIterExp, rnIter, rnDoms, rnExpOpt, optAlts, optAlts_rn e, List.map_map,
        List.map_cons, Function.comp_def]

theorem optAltsL_rn : ∀ es : List Exp, optAltsL (rnExps f es) = (optAltsL es).map (rnExps f)
  | [] => rfl
  | e :: es => by
    simp only [rnExps, optAltsL, optAlts_rn e, optAltsL_rn es, prod2, List.flatMap_map,
      List.map_flatMap, List.map_map, Function.comp_def]

theorem optAltsO_rn : ∀ eo : Option Exp, optAltsO (rnExpOpt f eo) = (optAltsO eo).map (rnExpOpt f)
  | none => rfl
  | some e => by
    simp only [rnExpOpt, optAltsO, optAlts_rn e, List.map_map, Function.comp_def]

theorem optAltsF_rn :
    ∀ fs : List ExpField, optAltsF (rnExpFields f fs) = (optAltsF fs).map (rnExpFields f)
  | [] => rfl
  | .mk _ e :: fs => by
    simp only [rnExpFields, rnExpField, optAltsF, optAlts_rn e, optAltsF_rn fs, prod2,
      List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]

theorem optAltsA_rn : ∀ l : List Arg, optAltsA (rnArgs f l) = (optAltsA l).map (rnArgs f)
  | [] => rfl
  | .expA e :: l => by
    simp only [rnArgs, rnArg, optAltsA, optAlts_rn e, optAltsA_rn l, prod2, List.flatMap_map,
      List.map_flatMap, List.map_map, Function.comp_def]
  | .typA _ :: l | .defA _ :: l | .gramA _ :: l => by
    simp only [rnArgs, rnArg, optAltsA, optAltsA_rn l, List.map_map, Function.comp_def]

end

end OptAlts

theorem conclAlts_rn (e : Exp) : conclAlts (rnExp f e) = (conclAlts e).map (rnExp f) := by
  simp only [conclAlts, hasOptNil_rn, optAlts_rn, List.map_cons]
  split <;> rfl

/-- **The backend reading is equivariant.** -/
theorem backend_equivariant : Equivariant backend := by
  intro g e e' he
  show rnExp g e' ∈ conclAlts (rnExp g e)
  rw [conclAlts_rn]
  exact List.mem_map_of_mem he

/-- The institution with renamings of identifiers at the backend reading. -/
def instPBackend : Silmaril.Logic.Institution.Inst.{0, 0, 0, 0, 0} := instP backend_equivariant

end Silmaril.Wasm.SpecTec.Institution.Perm
