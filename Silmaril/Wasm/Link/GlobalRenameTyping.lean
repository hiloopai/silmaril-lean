module

public import Silmaril.Wasm.Link.GlobalPermutation
public import Silmaril.Wasm.Execution.Core.Typing.Config
public import Silmaril.Wasm.Execution.Core.Instantiation

/-! # Typing under global-address renaming

A bijection changes the global addresses in every stored module view while
preserving global values, runtime references and closed types. Module contexts
stay exactly the same. Store validity, including GC acyclicity, and invocation
validity therefore survive the renaming.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.GlobalRenameTyping

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open GlobalPermutation

variable {H : Type}

private theorem map_left {α β γ : Type} {R : α → β → Prop} {S : γ → β → Prop}
    {xs : List α} {ys : List β} (f : α → γ) (related : List.Forall₂ R xs ys)
    (lift : ∀ a b, R a b → S (f a) b) : List.Forall₂ S (xs.map f) ys := by
  induction related with
  | nil => exact .nil
  | cons pair _ ih => exact .cons (lift _ _ pair) ih

theorem external_ok {p : Nat ≃ Nat} {source target : Store H}
    (stores : Renamed p source target) {address : ExternAddr} {type : CExternType}
    (valid : ExternAddrOk source address type) : ExternAddrOk target (external p address) type := by
  induction valid with
  | tag lookup => exact .tag (stores.tags ▸ lookup)
  | @global address gi lookup => exact .global ((stores.globals address).trans lookup)
  | mem lookup => exact .mem (stores.mems ▸ lookup)
  | table lookup => exact .table (stores.tables ▸ lookup)
  | @func address fi lookup => exact .func (fi := function p fi) (stores.function_lookup lookup)
  | sub _ typed subtype ih => exact .sub ih typed subtype

theorem elem_ok {p : Nat ≃ Nat} {source target : Store H}
    (stores : Renamed p source target) {ei : ElemInst} (valid : ElemInstOk source ei) :
    ElemInstOk target ei := by
  obtain ⟨closed, refs⟩ := valid
  exact ⟨closed, fun r member => stores.refOk (refs r member)⟩

theorem export_ok {p : Nat ≃ Nat} {source target : Store H}
    (stores : Renamed p source target) {xi : ExportInst} (valid : ExportInstOk source xi) :
    ExportInstOk target {xi with addr := external p xi.addr} := by
  obtain ⟨type, typed⟩ := valid
  exact ⟨type, external_ok stores typed⟩

private theorem external_addresses (p : Nat ≃ Nat) (mi : ModuleInst) :
    (moduleView p mi).tags.map ExternAddr.tag ++
      (moduleView p mi).globals.map ExternAddr.global ++
      (moduleView p mi).mems.map ExternAddr.mem ++
      (moduleView p mi).tables.map ExternAddr.table ++
      (moduleView p mi).funcs.map ExternAddr.func =
    (mi.tags.map ExternAddr.tag ++ mi.globals.map ExternAddr.global ++
      mi.mems.map ExternAddr.mem ++ mi.tables.map ExternAddr.table ++
      mi.funcs.map ExternAddr.func).map (external p) := by
  simp only [moduleView, List.map_append, List.map_map, _root_.Function.comp_def, external]

/-- Renaming runtime addresses preserves the module's exact validation context,
including export validity and distinct export names. -/
theorem module_ok {p : Nat ≃ Nat} {source target : Store H}
    (stores : Renamed p source target) {mi : ModuleInst} {C : Context}
    (valid : ModuleInstOk source mi C) : ModuleInstOk target (moduleView p mi) C := by
  cases valid with
  | @mk tags globals mems tables funcs elems k types tagsOk globalsOk funcsOk memsOk tablesOk
      datasOk elemsOk exportsOk disjoint exportAddresses bound =>
    refine ModuleInstOk.mk types ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ bound
    · exact tagsOk.imp fun _ _ typed => external_ok stores typed
    · exact map_left p globalsOk fun _ _ typed => external_ok stores typed
    · exact funcsOk.imp fun _ _ typed => external_ok stores typed
    · exact memsOk.imp fun _ _ typed => external_ok stores typed
    · exact tablesOk.imp fun _ _ typed => external_ok stores typed
    · intro address member
      obtain ⟨di, lookup⟩ := datasOk address member
      exact ⟨di, stores.datas ▸ lookup⟩
    · exact elemsOk.imp fun address type valid => by
        obtain ⟨ei, lookup, typed, equal⟩ := valid
        exact ⟨ei, stores.elems ▸ lookup, elem_ok stores typed, equal⟩
    · intro xi member
      obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp member
      rw [← equal]
      exact export_ok stores (exportsOk original originalMember)
    · simpa only [moduleView, List.map_map, _root_.Function.comp_def] using disjoint
    · intro xi member
      obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp member
      rw [← equal, external_addresses]
      exact List.mem_map_of_mem (f := external p) (exportAddresses original originalMember)

theorem function_ok {p : Nat ≃ Nat} {source target : Store H}
    (stores : Renamed p source target) {fi : FuncInst H} (valid : FuncInstOk source fi) :
    FuncInstOk target (function p fi) := by
  cases valid with
  | wasm closed moduleTyped codeTyped functionTyped subtype =>
    refine .wasm closed ?_ codeTyped functionTyped subtype
    simpa only [function, codeTyped] using (module_ok stores moduleTyped)
  | host closed expanded codeTyped => exact .host closed expanded codeTyped

/-- Immutable reachability sees the unchanged GC objects and exception fields.
The global-address permutation cannot create a GC cycle. -/
theorem reachable {p : Nat ≃ Nat} {source target : Store H}
    (stores : Renamed p source target) {left right : FieldVal}
    (reach : ImmutReachable source left right) : ImmutReachable target left right := by
  induction reach with
  | trans _ _ left right => exact .trans left right
  | refStruct lookup expanded field value =>
    exact .refStruct (stores.structs ▸ lookup) expanded field value
  | refArray lookup expanded value => exact .refArray (stores.arrays ▸ lookup) expanded value
  | refExn lookup value => exact .refExn (stores.exns ▸ lookup) value
  | refExtern r => exact .refExtern r

theorem global_member {p : Nat ≃ Nat} {source target : Store H}
    (stores : Renamed p source target) {gi : GlobalInst} (member : gi ∈ target.globals) :
    gi ∈ source.globals := by
  obtain ⟨address, lookup⟩ := List.mem_iff_getElem?.mp member
  apply List.mem_of_getElem? (i := p.symm address)
  have related := stores.globals (p.symm address)
  simp only [Equiv.apply_symm_apply] at related
  exact related.symm.trans lookup

/-- Store typing survives an arbitrary bijective global renaming. Runtime values
and closed types are unchanged; stored wasm views are renamed consistently. -/
theorem store_ok {p : Nat ≃ Nat} {source target : Store H}
    (stores : Renamed p source target) (valid : StoreOk source) : StoreOk target := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ti member
    exact valid.tags ti (stores.tags ▸ member)
  · intro gi member
    obtain ⟨closed, value⟩ := valid.globals gi (global_member stores member)
    exact ⟨closed, (stores.valOk_iff _ _).mp value⟩
  · intro mi member
    exact valid.mems mi (stores.mems ▸ member)
  · intro ti member
    obtain ⟨closed, length, refs⟩ := valid.tables ti (stores.tables ▸ member)
    exact ⟨closed, length, fun r member => stores.refOk (refs r member)⟩
  · intro fi member
    rw [stores.functions] at member
    obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp member
    rw [← equal]
    exact function_ok stores (valid.funcs original originalMember)
  · intro ei member
    exact elem_ok stores (valid.elems ei (stores.elems ▸ member))
  · intro si member
    obtain ⟨fields, expanded, values⟩ := valid.structs si (stores.structs ▸ member)
    exact ⟨fields, expanded, values.imp fun _ _ typed => (stores.fieldValOk_iff _ _).mp typed⟩
  · intro ai member
    obtain ⟨field, expanded, values⟩ := valid.arrays ai (stores.arrays ▸ member)
    exact ⟨field, expanded, fun value member => (stores.fieldValOk_iff _ _).mp (values value member)⟩
  · intro ei member
    obtain ⟨ti, types, lookup, expanded, fields⟩ := valid.exns ei (stores.exns ▸ member)
    exact ⟨ti, types, stores.tags ▸ lookup, expanded,
      fields.imp fun _ _ typed => (stores.valOk_iff _ _).mp typed⟩
  · intro address bound reach
    exact valid.acyclicStructs address (stores.structs ▸ bound) (reachable stores.symm reach)
  · intro address bound reach
    exact valid.acyclicArrays address (stores.arrays ▸ bound) (reachable stores.symm reach)
  · intro address bound reach
    exact valid.acyclicExns address (stores.exns ▸ bound) (reachable stores.symm reach)
  · intro si member
    exact valid.structsClosed si (stores.structs ▸ member)
  · intro ai member
    exact valid.arraysClosed ai (stores.arrays ▸ member)

/-- The same address and arguments remain a valid invocation after renaming. -/
theorem invoke_ok {p : Nat ≃ Nat} {source target : Store H}
    (stores : Renamed p source target) {address : Nat} {args : List Val}
    (valid : InvokeOk source address args) : InvokeOk target address args := by
  obtain ⟨fi, params, results, lookup, signature, values⟩ := valid
  exact ⟨function p fi, params, results, stores.function_lookup lookup, signature,
    values.imp fun _ _ typed => (stores.valOk_iff _ _).mp typed⟩

end Silmaril.Wasm.Link.GC.GlobalRenameTyping
