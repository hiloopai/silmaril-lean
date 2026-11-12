module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Facts
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Types

/-!
# `Typed` holds for real configurations: values on an empty store

`typed_vals`: every configuration with the empty store, a frame with any locals and the empty
module instance, and code a sequence of value constants (integers, floats of every IEEE shape,
vectors, references) is `Typed` in every `simEnv B`. So `Typed` is not vacuous, and in
particular holds of float programs' values (round 1's gap 1). `typedV_instr_val`: a value is a
typed `instr`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Typing

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d265 Original.d269 Original.d271 Original.d571)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-- A case typed in `val` with the same case type in `instr` is typed in `instr`. -/
theorem typedV_instr_of_val {op : MixopS} {t : Typ} {w : Value}
    (hv : IntNumeric.findCase (IntNumeric.instCases Original.d269 0) op = some (t, []))
    (hi : IntNumeric.findCase (IntNumeric.recCases Original.d271 0 0) op = some (t, []))
    (h : TypedV (simEnv B) (.varT "val" []) (.case op w)) :
    TypedV (simEnv B) (.varT "instr" []) (.case op w) :=
  typedV_closedCase (IntNumeric.findTyp_instr' B) hi (IntNumeric.hasTyp_of_hasTypCase
    (hasTypCase_of_closedVariant findTyp_val (h _ ⟨rfl, rfl, rfl⟩)) hv)

set_option maxRecDepth 100000 in
/-- **Every value is a typed `instr`.** -/
theorem typedV_instr_val (v : Val) : TypedV (simEnv B) (.varT "instr" []) (valV v) := by
  rcases v with n | b | r
  · exact typedV_instr_of_val rfl rfl (typedV_val (.num n))
  · exact typedV_instr_of_val rfl rfl (typedV_val (.vec b))
  · have h := typedV_val (B := B) (.ref r)
    cases r <;> exact typedV_instr_of_val rfl rfl h

/-- The record of empty lists over a struct type's fields. -/
def emptyFields : List TypField → List (AtomS × Value)
  | [] => []
  | .mk a _ _ _ :: fs => (a, .list []) :: emptyFields fs

/-- Every field is a premise-free list type. -/
def allListFields : List TypField → Bool
  | [] => true
  | .mk _ (.iterT _ .list) _ [] :: fs => allListFields fs
  | _ => false

/-- A record of empty lists inhabits a struct type of list fields. -/
theorem hasTypFields_empty {σ : VarEnv} :
    ∀ fs : List TypField, allListFields fs = true →
      HasTypFields (simEnv B) σ fs (emptyFields fs)
  | [], _ => hasTypFields_nil_iff.2 rfl
  | .mk a (.iterT t .list) qs [] :: fs, h =>
      hasTypFields_cons_iff.2 ⟨_, _, rfl, hasTyp_iterT_list_iff.2 ⟨[], rfl,
        hasTypList_iff.2 (by simp)⟩, premsOk_nil, hasTypFields_empty fs h⟩

/-- The fields of a struct type definition. -/
def structFields : Def → List TypField
  | .typD _ _ [.instD _ _ (.structT fs)] => fs
  | _ => []

set_option maxRecDepth 100000 in
theorem findTyp_store : (simEnv B).findTyp? "store" =
    some ([], [.instD [] [] (.structT (structFields Original.d571))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_moduleinst : (simEnv B).findTyp? "moduleinst" =
    some ([], [.instD [] [] (.structT (structFields Original.d265))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_frame : (simEnv B).findTyp? "frame" = some ([], [.instD [] [] (.structT
    [.mk "LOCALS" (.iterT (.iterT (.varT "val" []) .opt) .list) [] [],
     .mk "MODULE" (.varT "moduleinst" []) [] []])]) := rfl

set_option maxRecDepth 100000 in
/-- The empty store is a typed `store`. -/
theorem typedV_store_empty {H : Type} (hn : H → String) :
    TypedV (simEnv B) storeT (storeV hn {}) := fun ρ hρ =>
  hasTyp_varT_struct (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) findTyp_store
    Equiv.evalArgs_nil matchArgs_nil (hasTypFields_empty _ rfl)

set_option maxRecDepth 100000 in
/-- The empty module instance is a typed `moduleinst`. -/
theorem typedV_moduleinst_empty :
    TypedV (simEnv B) (.varT "moduleinst" []) (Silmaril.SpecTec.Equiv.RuntimeBridge.moduleInstToValue CT {}) := fun ρ hρ =>
  hasTyp_varT_struct (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) findTyp_moduleinst
    Equiv.evalArgs_nil matchArgs_nil (hasTypFields_empty _ rfl)

/-- A list of optional values is a `(val?)*`. -/
theorem hasTyp_locals (ls : List (Option Val)) :
    HasTyp (simEnv B) VarEnv.empty (.iterT (.iterT (.varT "val" []) .opt) .list)
      (.list (ls.map fun o => .opt (o.map valV))) :=
  hasTyp_iterT_list_iff.2 ⟨_, rfl, hasTypList_iff.2 fun u hu => by
    obtain ⟨o, -, rfl⟩ := List.mem_map.1 hu
    cases o with
    | none => exact hasTyp_iterT_opt_iff.2 (.inl rfl)
    | some v => exact hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl, typedV_val v _ ⟨rfl, rfl, rfl⟩⟩)⟩

/-- A frame with any locals over the empty module instance is a typed `frame`. -/
theorem typedV_frame_empty (ls : List (Option Val)) :
    TypedV (simEnv B) frameT (frameV ⟨ls, {}⟩) := fun ρ hρ =>
  hasTyp_varT_struct (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) findTyp_frame
    Equiv.evalArgs_nil matchArgs_nil
    (hasTypFields_cons_iff.2 ⟨_, _, rfl, hasTyp_locals ls, premsOk_nil,
      hasTypFields_cons_iff.2 ⟨_, _, rfl, typedV_moduleinst_empty _ ⟨rfl, rfl, rfl⟩, premsOk_nil,
        hasTypFields_nil_iff.2 rfl⟩⟩)

/-- **`Typed` holds for real configurations**: the empty store, a frame with any locals over
the empty module instance, and any sequence of value constants (floats of every shape included). -/
theorem typed_vals {H : Type} (hn : H → String) (ls : List (Option Val)) (vs : List Val) :
    Typed (simEnv B) hn (⟨{}, ⟨ls, {}⟩, vals vs⟩ : Config H) := by
  have T := typingFacts_simEnv B hn
  refine (T.config _).2 ⟨(T.state _ _).2 ⟨typedV_store_empty hn, typedV_frame_empty ls⟩, ?_⟩
  show TypedV (simEnv B) instrsT (.list (adminsToV (vals vs)))
  rw [adminsToV_vals]
  exact typedV_list_iff.2 fun u hu => by
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hu
    exact typedV_instr_val v

end Silmaril.Wasm.SpecTec.Sim.Typing
