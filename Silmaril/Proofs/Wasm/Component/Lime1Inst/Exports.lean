module

public import Silmaril.Wasm.Component.Lime1Bridge.Thms
public import Silmaril.Wasm.Instantiation.Thms

/-!
# Exports by name and exports by position

The engine instance of `Param.instOf` looks its exports up **by name** (`Param.exportAddrs`),
while a Core 3.0 `ScalarInstance` lists its function exports **in export order**
(`Game.exportFuncAddrs`). For a module instance with distinct export names, looking up the names
of its function exports, in order, gives its function addresses in order:

* `lookup_funcNames`: `(funcNames E).mapM (lookup · >>= asFunc?) = some (funcAddrs E)`, for
  export instances `E` with distinct names;
* `exportFuncAddrs_of_exports`: the Core module instance whose exports are the images of `E`
  has `exportFuncAddrs = (funcAddrs E).map (·.value)`;
* `allocExports_funcNames`: the export instances allocated by Lime1's `allocate?` keep the names
  and kinds of the module's exports, so their function names are `funcExportNames` of the Core
  image.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1Inst

open Silmaril.Wasm.Execution.Runtime (ExportInst ExternVal FuncAddr ModuleInst)

/-- The names of the function exports, in order. -/
def funcNames (E : List ExportInst) : List String :=
  E.filterMap fun e => match e.value with
    | .func _ => some e.name
    | _ => none

/-- The function addresses of the function exports, in order. -/
def funcAddrs (E : List ExportInst) : List FuncAddr :=
  E.filterMap fun e => match e.value with
    | .func a => some a
    | _ => none

/-- The function address of an external value. -/
def funcOf? : ExternVal → Option FuncAddr
  | .func a => some a
  | _ => none

theorem mapM_congr_mem {α β : Type _} {f g : α → Option β} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x = g x) → xs.mapM f = xs.mapM g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons, h x (by simp),
      mapM_congr_mem (xs := xs) (fun y hy => h y (by simp [hy]))]

theorem funcNames_sub {E : List ExportInst} {n : String} (h : n ∈ funcNames E) :
    n ∈ E.map (·.name) := by
  simp only [funcNames, List.mem_filterMap, List.mem_map] at h ⊢
  obtain ⟨e, he, hn⟩ := h
  refine ⟨e, he, ?_⟩
  split at hn <;> simp_all

/-- **Looking up the function export names, in order, gives the function addresses in
order**, when export names are distinct. -/
theorem lookup_funcNames :
    ∀ {E : List ExportInst}, (E.map (·.name)).Nodup →
      (funcNames E).mapM (fun n => ((E.map fun e => (e.name, e.value)).lookup n).bind funcOf?) =
        some (funcAddrs E)
  | [], _ => rfl
  | e :: E, hnd => by
    have hnd' : (E.map (·.name)).Nodup := (List.nodup_cons.mp hnd).2
    have hne : ∀ n ∈ funcNames E, n ≠ e.name := fun n hn heq =>
      (List.nodup_cons.mp hnd).1 (by simpa only [← heq] using funcNames_sub hn)
    have hrest : (funcNames E).mapM
        (fun n => (((e :: E).map fun e => (e.name, e.value)).lookup n).bind funcOf?) =
        some (funcAddrs E) := by
      rw [← lookup_funcNames hnd']
      refine mapM_congr_mem fun n hn => ?_
      have hb : (n == e.name) = false := by simpa using hne n hn
      simp only [List.map_cons, List.lookup_cons, hb]
    rcases e with ⟨nm, v⟩
    cases v <;> simp only [funcNames, funcAddrs, List.filterMap_cons] at hrest ⊢
    case func a =>
      rw [List.mapM_cons, hrest]
      simp [funcOf?]
    all_goals exact hrest

/-- The Core image of export instances lists their function addresses in order. -/
theorem exportFuncAddrs_of_exports {mC : Silmaril.Wasm.Execution.Core.ModuleInst}
    {E : List ExportInst} (h : mC.exports = E.map fun e => ⟨e.name, e.value.toCore⟩) :
    Silmaril.Wasm.Game.exportFuncAddrs mC = (funcAddrs E).map (·.value) := by
  rw [Silmaril.Wasm.Game.exportFuncAddrs, h, funcAddrs, List.filterMap_map, List.map_filterMap]
  refine List.filterMap_congr fun e _ => ?_
  rcases e with ⟨nm, v⟩
  cases v <;> rfl

/-- One allocated export instance keeps the name and the kind of its export. -/
theorem allocExport_shape {base : ModuleInst} {e : Silmaril.Wasm.V1.Export} {x : ExportInst}
    (h : (Silmaril.Wasm.Lime1.Execution.exportValue? base e.index).bind
      (fun v => some (⟨e.name, v⟩ : ExportInst)) = some x) :
    x.name = e.name ∧ (match x.value with | .func _ => some x.name | _ => none) =
      (match e.toCore.index with | .func _ => some e.name | _ => none) := by
  rcases e with ⟨nm, idx⟩
  cases idx <;>
    simp only [Silmaril.Wasm.Lime1.Execution.exportValue?, Option.bind_eq_some_iff,
      Option.map_eq_some_iff, Option.some.injEq] at h <;>
    obtain ⟨_, ⟨_, -, rfl⟩, rfl⟩ := h <;> exact ⟨rfl, rfl⟩

/-- **The export instances allocated by Lime1 keep the names and kinds of the exports.** -/
theorem allocExports_funcNames {base : ModuleInst} :
    ∀ {es : List Silmaril.Wasm.V1.Export} {xs : List ExportInst},
      List.Forall₂ (fun e x => (Silmaril.Wasm.Lime1.Execution.exportValue? base e.index).bind
        (fun v => some (⟨e.name, v⟩ : ExportInst)) = some x) es xs →
      xs.map (·.name) = es.map (·.name) ∧
        funcNames xs = Silmaril.Wasm.Component.Reference.funcExportNames
          { exports := es.map Silmaril.Wasm.V1.Export.toCore }
  | [], [], .nil => ⟨rfl, rfl⟩
  | e :: es, x :: xs, .cons h hs => by
    have ⟨h1, h2⟩ := allocExport_shape h
    have ⟨ih1, ih2⟩ := allocExports_funcNames hs
    refine ⟨by simp only [List.map_cons, h1, ih1], ?_⟩
    simp only [funcNames, Silmaril.Wasm.Component.Reference.funcExportNames, List.map_cons,
      List.filterMap_cons] at ih2 ⊢
    rw [h2, ih2]
    rcases e with ⟨nm, idx⟩
    cases idx <;> rfl

end Silmaril.Proofs.Wasm.Component.Lime1Inst
