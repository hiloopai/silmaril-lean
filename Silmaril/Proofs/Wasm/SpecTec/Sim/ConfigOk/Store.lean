module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.ConfigOk.Bounds

/-!
# Inversions of a typed store, and the bundle fields they discharge

A typed `store` (`TypedV storeT (storeV hn s)`) has typed instances, field by field
(`hasTypFields_of_closedStruct` on the ten-field record, then the list of each field). This
discharges, for every `B`:

* `Residue.funcinst` (`funcinst_of_store`), `Residue.result` (`typedV_result`, unconditionally);
* `BwdOpen.exnFields` (`exnFields_simEnv`, unconditionally: every `Val` is a typed `val`);
* `Memory.InstTyping` (`instTyping_simEnv`), and the inversions `tableType`/`memType` of
  `Memory.MemTyping`;
* `Aggregates.AggTypes.arrayOfStore`, `structOfStore`, `mut_`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.ConfigOk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core (Store Frame FuncInst ExnInst TableInst MemInst ArrayInst
  StructInst Result)
open Silmaril.SpecTec.Equiv.RuntimeBridge (tableInstToValue memInstToValue)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {H : Type} {B : Builtins}

/-- Binding a term variable keeps a scope term-only. -/
theorem valsOnly_bindVal {ρ : VarEnv} (hρ : ValsOnly ρ) (x : IL.Id) (v : Value) :
    ValsOnly (ρ.bindVal x v) := hρ

/-- An element of a typed closed list is typed. -/
theorem typedV_of_mem_list {x : IL.Id} {l : List Value} {u : Value}
    (hl : HasTyp (simEnv B) VarEnv.empty (.iterT (.varT x []) .list) (.list l)) (hu : u ∈ l) :
    TypedV (simEnv B) (.varT x []) u := by
  obtain ⟨l', he, hl'⟩ := hasTyp_iterT_list_iff.1 hl
  cases he
  exact Typing.typedV_of_hasTyp valsOnly_empty (hasTypList_iff.1 hl' u hu)

/-- **The ten fields of a typed store**, as typed lists. -/
theorem store_fields {hn : H → String} {s : Store H}
    (h : TypedV (simEnv B) storeT (storeV hn s)) :
    HasTyp (simEnv B) VarEnv.empty (.iterT (.varT "meminst" []) .list)
        (.list (s.mems.map memInstToValue)) ∧
      HasTyp (simEnv B) VarEnv.empty (.iterT (.varT "tableinst" []) .list)
        (.list (s.tables.map (tableInstToValue CT))) ∧
      HasTyp (simEnv B) VarEnv.empty (.iterT (.varT "funcinst" []) .list)
        (.list (s.funcs.map (funcInstV hn))) ∧
      HasTyp (simEnv B) VarEnv.empty (.iterT (.varT "structinst" []) .list)
        (.list (s.structs.map structInstV)) ∧
      HasTyp (simEnv B) VarEnv.empty (.iterT (.varT "arrayinst" []) .list)
        (.list (s.arrays.map arrayInstV)) := by
  have hF := hasTypFields_of_closedStruct valsOnly_empty findTyp_store' (h _ valsOnly_empty)
  simp only [List.forall₂_cons, fieldTyp] at hF
  exact ⟨hF.2.2.1, hF.2.2.2.1, hF.2.2.2.2.1, hF.2.2.2.2.2.2.2.1, hF.2.2.2.2.2.2.2.2.1⟩

/-- **`Residue.funcinst`**: a function instance of a typed store is a typed `funcinst`. -/
theorem funcinst_of_store (hn : H → String) (s : Store H) (a : Nat) (fi : FuncInst H)
    (h : TypedV (simEnv B) storeT (storeV hn s)) (hfi : s.funcs[a]? = some fi) :
    TypedV (simEnv B) funcinstT (funcInstV hn fi) :=
  typedV_of_mem_list (store_fields h).2.2.1 (List.mem_map_of_mem (List.mem_of_getElem? hfi))

/-- **`AggTypes.arrayOfStore`**. -/
theorem arrayOfStore_simEnv (hn : H → String) (s : Store H) (ai : ArrayInst)
    (h : TypedV (simEnv B) storeT (storeV hn s)) (hai : ai ∈ s.arrays) :
    TypedV (simEnv B) Aggregates.arrayinstT (arrayInstV ai) :=
  typedV_of_mem_list (store_fields h).2.2.2.2 (List.mem_map_of_mem hai)

/-- **`AggTypes.structOfStore`**. -/
theorem structOfStore_simEnv (hn : H → String) (s : Store H) (si : StructInst)
    (h : TypedV (simEnv B) storeT (storeV hn s)) (hsi : si ∈ s.structs) :
    TypedV (simEnv B) Aggregates.structinstT (structInstV si) :=
  typedV_of_mem_list (store_fields h).2.2.2.1 (List.mem_map_of_mem hsi)

/-- The store of a typed state is typed. -/
theorem store_of_state {hn : H → String} {s : Store H} {f : Frame}
    (h : TypedV (simEnv B) stateT (stateV hn s f)) : TypedV (simEnv B) storeT (storeV hn s) :=
  ((Typing.typingFacts_simEnv B hn).state s f).1 h |>.1

/-- **`Memory.InstTyping`** holds in every `simEnv B`. -/
theorem instTyping_simEnv (B : Builtins) : Memory.InstTyping (simEnv B) where
  tableinst _ _ _ _ hti h := typedV_of_mem_list (store_fields (store_of_state h)).2.1
    (List.mem_map_of_mem hti)
  meminst _ _ _ _ hmi h := typedV_of_mem_list (store_fields (store_of_state h)).1
    (List.mem_map_of_mem hmi)

/-- **`BwdOpen.exnFields`**, unconditionally. -/
theorem exnFields_simEnv (B : Builtins) (hn : H → String) :
    ∀ (s : Store H) (f : Frame), TypedV (simEnv B) stateT (stateV hn s f) →
      ∀ (a : Nat) (e : ExnInst), s.exns[a]? = some e →
        TypedV (simEnv B) valsT (.list (e.fields.map valV)) :=
  fun _ _ _ _ e _ => typedV_list_iff.2 fun u hu => by
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hu
    exact Typing.typedV_val v

/-! ## `result` -/

set_option maxRecDepth 100000 in
theorem findTyp_result : (simEnv B).findTyp? "result" = some ([], [.instD [] [] (.variantT
    [.mk "_VALS" (.iterT (.varT "val" []) .list) [] [],
     .mk "(REF.EXN_ADDR%)THROW_REF" (.varT "exnaddr" []) [] [],
     .mk "TRAP" (.tupT []) [] []])]) := rfl

/-- **`Residue.result`**, unconditionally: every encoded result is a typed `result`. -/
theorem typedV_result (r : Result) : TypedV (simEnv B) resultT (resultV r) := by
  cases r with
  | values vs =>
    exact Typing.typedV_closedCase findTyp_result rfl
      ((typedV_list_iff.2 fun u hu => by
        obtain ⟨v, -, rfl⟩ := List.mem_map.1 hu
        exact Typing.typedV_val v) _ valsOnly_empty)
  | throw a =>
    exact Typing.typedV_closedCase findTyp_result rfl
      (Typing.typedV_alias Typing.findTyp_exnaddr (Typing.typedV_natAlias Typing.findTyp_addr a) _
        valsOnly_empty)
  | trap => exact Typing.typedV_closedCase findTyp_result rfl hasTyp_tupT_nil

/-! ## `AggTypes.mut_` -/

set_option maxRecDepth 100000 in
theorem findTyp_mut :
    (simEnv B).findTyp? "mut" =
      some ([], [.instD [] [] (.variantT [.mk "MUT" (.tupT []) [] []])]) :=
  rfl

/-- **`AggTypes.mut_`**: both mutabilities are a `mut?`. -/
theorem typedV_mut (m : Mutability) :
    TypedV (simEnv B) Aggregates.mutOptT (Equiv.Validation.mutV m) := by
  cases m
  · exact fun _ _ => hasTyp_iterT_opt_iff.2 (.inl rfl)
  · exact fun ρ hρ => hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl,
      Typing.typedV_closedCase findTyp_mut rfl hasTyp_tupT_nil ρ hρ⟩)

end Silmaril.Wasm.SpecTec.Sim.ConfigOk
