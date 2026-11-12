module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.PrimsCall

/-!
# Round 7, the export swap: `$blocktype_`'s primitive does not see erasure (unrefined)

`$blocktype_` was left out of the checked part because its primitive reads `MODULE.TYPES` out of
the state it is given, and a state holds module records with `EXPORTS` fields, so the primitive is
not strict. It still commutes with erasure: `moduleTypesV?` reads the frame's `MODULE.TYPES`, which
erasure maps pointwise (`moduleTypesV?_eraseV`), and the type decoder `tyInv` and the index decoder
are strict, so they do not see it (`erase_inv_of_strict`). So `Prims.call` at `"blocktype_"`
commutes with erasure at every argument list (`call_blocktype_erase`), with export-free answers
(`btSpec_nx`).
-/

@[expose] public section

set_option linter.auxLemma false

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap

theorem erase_inv_of_strict {α : Type} {f : Value → Option α}
    (h : ∀ v a, f v = some a → nxB v = true) (v : Value) : f (eraseV v) = f v := by
  by_cases hv : nxB v = true
  · rw [eraseV_of_nxB v hv]
  · have h₁ : f v = none := by
      cases hf : f v with
      | none => rfl
      | some a => exact absurd (h v a hf) hv
    have h₂ : f (eraseV v) = none := by
      cases hf : f (eraseV v) with
      | none => rfl
      | some a => exact absurd ((nxB_eraseV v).symm.trans (h _ a hf)) hv
    rw [h₁, h₂]

theorem moduleTypesV?_eraseV (z : Value) :
    Prims.moduleTypesV? (eraseV z) = (Prims.moduleTypesV? z).map (List.map eraseV) := by
  rcases z with _ | _ | _ | _ | ⟨op, w⟩ | _ | _ | o
  all_goals try rfl
  · by_cases hop : op = "%;%"
    · subst hop
      rcases w with _ | _ | _ | vs | _ | _ | _ | o
      all_goals try rfl
      · rcases vs with _ | ⟨a, _ | ⟨F, _ | ⟨c, l⟩⟩⟩
        all_goals try rfl
        simp only [eraseV_case, eraseV_tuple', List.map_cons, List.map_nil, Prims.moduleTypesV?]
        rw [field?_eraseV (by decide)]
        cases F.field? "MODULE" with
        | none => rfl
        | some M =>
          simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
          rw [field?_eraseV (by decide)]
          cases M.field? "TYPES" with
          | none => rfl
          | some T => simp [asList?_eraseV]
      · cases o <;> rfl
    · simp [Prims.moduleTypesV?, hop]
  · cases o <;> rfl

theorem nxB_typeIdx (a : Silmaril.Wasm.TypeIdx) : nxB (Encode.toValue a) = true := by
  rfl


theorem ofValue_typeIdx_nx {v : Value} {a : Silmaril.Wasm.TypeIdx}
    (h : Encode.ofValue (α := Silmaril.Wasm.TypeIdx) v = some a) : nxB v = true := by
  rw [← Encode.toValue_ofValue v a h]
  exact nxB_typeIdx a

theorem tyInv_eraseV (k : Silmaril.Wasm.Validation.TKind) (v : Value) :
    Prims.tyInv k (eraseV v) = Prims.tyInv k v :=
  erase_inv_of_strict (fun _ _ h => tyInv_nx h) v

theorem mapM_tyInv_eraseV (k : Silmaril.Wasm.Validation.TKind) :
    ∀ l : List Value, (l.map eraseV).mapM (Prims.tyInv k) = l.mapM (Prims.tyInv k)
  | [] => rfl
  | v :: l => by simp only [List.map_cons, List.mapM_cons, tyInv_eraseV, mapM_tyInv_eraseV k l]

/-- **`$blocktype_`'s primitive does not see erasure**: it reads only `MODULE.TYPES` of the state
and the index, which erasure leaves alone. -/
theorem blocktypeCall_eraseV (z xv : Value) :
    Prims.blocktypeCall (eraseV z) (eraseV xv) = Prims.blocktypeCall z xv := by
  unfold Prims.blocktypeCall
  rw [moduleTypesV?_eraseV, erase_inv_of_strict (fun _ _ h => ofValue_typeIdx_nx h) xv]
  cases Prims.moduleTypesV? z with
  | none => rfl
  | some Ts =>
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
    rw [mapM_tyInv_eraseV]

theorem blocktypeCall_nx {z xv v : Value} (h : Prims.blocktypeCall z xv = some v) :
    nxB v = true := by
  unfold Prims.blocktypeCall at h
  xs_bind h
  obtain ⟨_, -, _, -, _, -, _, -, _, -, rfl⟩ := h
  simp [Exn.instrTypeV]


theorem floatCall_blocktype (P : Silmaril.Wasm.Numerics.Profile) (ws : List ArgV) :
    Floats.floatCall P "blocktype_" ws = none := by
  unfold Floats.floatCall
  simp [Floats.floatNames]

theorem intCall_blocktype (ws : List ArgV) : IntNumeric.intCall "blocktype_" ws = none := by
  unfold IntNumeric.intCall
  delta IntNumeric.intCall.match_3
  simp only [String.reduceEq, ↓reduceDIte]

theorem call_blocktype_erase {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) (ws : List ArgV) :
    Prims.call P hn host "blocktype_" (ws.map eraseA) = Prims.call P hn host "blocktype_" ws := by
  unfold Prims.call
  rw [floatCall_blocktype, floatCall_blocktype, intCall_blocktype, intCall_blocktype]
  delta Prims.call.match_1
  simp only [String.reduceEq, ↓reduceDIte]
  rcases ws with _ | ⟨a, l⟩
  · rfl
  cases a
  case val z =>
    rcases l with _ | ⟨b, l⟩
    · rfl
    cases b
    case val v =>
      cases v
      case case op w =>
        by_cases hop : op = "_IDX"
        · subst hop
          rcases l with _ | ⟨c, l⟩
          · exact blocktypeCall_eraseV z w
          · rfl
        · rcases l with _ | ⟨c, l⟩ <;>
          · refine (dite_eq_right hop).trans ?_
            symm
            exact dite_eq_right hop
      all_goals first | rfl | (rename_i o; cases o <;> rfl)
    all_goals rfl
  all_goals rfl


/-- `$blocktype_`'s primitive at its argument shape. -/
noncomputable def btSpec : List ArgV → Option Value
  | [.val z, .val (.case "_IDX" xv)] => Prims.blocktypeCall z xv
  | _ => none

theorem call_blocktype_eq {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) (ws : List ArgV) :
    Prims.call P hn host "blocktype_" ws = btSpec ws := by
  unfold Prims.call
  rw [floatCall_blocktype, intCall_blocktype]
  delta Prims.call.match_1
  simp only [String.reduceEq, ↓reduceDIte]
  unfold btSpec
  rcases ws with _ | ⟨a, l⟩
  · rfl
  cases a
  case val z =>
    rcases l with _ | ⟨b, l⟩
    · rfl
    cases b
    case val v =>
      cases v
      case case op w =>
        by_cases hop : op = "_IDX"
        · subst hop
          rcases l with _ | ⟨c, l⟩ <;> rfl
        · rcases l with _ | ⟨c, l⟩ <;>
          · refine (dite_eq_right hop).trans ?_
            split
            · simp_all
            · rfl
      all_goals rfl
    all_goals rfl
  all_goals rfl

theorem btSpec_nx {ws : List ArgV} {v : Value} (h : btSpec ws = some v) : nxB v = true := by
  unfold btSpec at h
  split at h
  · exact blocktypeCall_nx h
  · cases h

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
