module

public import Silmaril.Proofs.Wasm.Component.Lime1Inst.Residue

/-!
# Lime1 allocation succeeds on valid import-free modules

Lime1's `allocate?` can fail only by evaluating a global initializer, by an export index or a
function type index out of range. On a valid module without imports whose initializers evaluate,
neither of the last two happens (`allocate?_some`): the index spaces of the module instance are
at least as long as those of the validation context (`ctx_funcs_le` and its siblings).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1Eng

open Silmaril.Wasm Silmaril.Wasm.Lime1 Silmaril.Wasm.Lime1.Validation
open Silmaril.Wasm.Execution.Runtime (Value ModuleInst)

/-- `mapM` succeeds when every element maps to some value. -/
theorem mapM_some {α β : Type _} {f : α → Option β} :
    ∀ {xs : List α}, (∀ x ∈ xs, ∃ y, f x = some y) → ∃ ys, xs.mapM f = some ys
  | [], _ => ⟨[], rfl⟩
  | x :: xs, h => by
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := mapM_some (xs := xs) (fun z hz => h z (by simp [hz]))
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

theorem getElem?_addresses {k : Silmaril.Wasm.Execution.Runtime.AddrKind} {start n i : Nat}
    (hi : i < n) :
    (Silmaril.Wasm.V1.Execution.addresses k start n)[i]? = some ⟨start + i⟩ := by
  simp [Silmaril.Wasm.V1.Execution.addresses, List.getElem?_range hi]

theorem lt_of_getElem? {α : Type _} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    i < l.length := (List.getElem?_eq_some_iff.mp h).1

/-- The function index space of the context of an import-free module. -/
theorem ctx_funcs_le {l : Lime1.Module} (hlimp : l.imports = []) :
    (moduleContext l).funcs.length ≤ l.funcs.length := by
  simp only [moduleContext, hlimp, List.filterMap_nil, List.nil_append]
  exact List.length_filterMap_le _ _

theorem ctx_tables {l : Lime1.Module} (hlimp : l.imports = []) :
    (moduleContext l).tables = l.tables := by
  simp [moduleContext, hlimp]

theorem ctx_memories {l : Lime1.Module} (hlimp : l.imports = []) :
    (moduleContext l).memories = l.memories := by
  simp [moduleContext, hlimp]

theorem ctx_globals {l : Lime1.Module} (hlimp : l.imports = []) :
    (moduleContext l).globals = l.globals.map Lime1.Global.type := by
  simp [moduleContext, importedGlobals, hlimp]

/-- The module instance that `allocate? {} l []` builds before recording exports. -/
def baseL (l : Lime1.Module) : ModuleInst where
  types := l.types
  funcs := [] ++ Silmaril.Wasm.V1.Execution.addresses .func 0 l.funcs.length
  tables := [] ++ Silmaril.Wasm.V1.Execution.addresses .table 0 l.tables.length
  memories := [] ++ Silmaril.Wasm.V1.Execution.addresses .memory 0 l.memories.length
  globals := [] ++ Silmaril.Wasm.V1.Execution.addresses .global 0 l.globals.length

theorem lt_of_map_some {α β : Type _} {f : α → β} {l : List α} {i : Nat} {b : β}
    (h : (l[i]?).map f = some b) : i < l.length := by
  obtain ⟨a, ha, -⟩ := Option.map_eq_some_iff.mp h
  exact lt_of_getElem? ha

/-- Every valid export of an import-free module has a value in the base instance. -/
theorem exportValue_some {l : Lime1.Module} (hlimp : l.imports = []) {e : V1.Export}
    (he : ExportValid (moduleContext l) e) :
    ∃ v, Silmaril.Wasm.Lime1.Execution.exportValue? (baseL l) e.index = some v := by
  obtain ⟨et, het⟩ : ∃ et, exportType? (moduleContext l) e.index = some et := he
  rcases e with ⟨nm, idx⟩
  cases idx with
  | func i =>
    have hi : i.toNat < l.funcs.length := (lt_of_map_some het).trans_le (ctx_funcs_le hlimp)
    exact ⟨.func ⟨i.toNat⟩, by simp [Silmaril.Wasm.Lime1.Execution.exportValue?, baseL,
      getElem?_addresses hi]⟩
  | table i =>
    have hi : i.toNat < l.tables.length := ctx_tables hlimp ▸ lt_of_map_some het
    exact ⟨.table ⟨i.toNat⟩, by simp [Silmaril.Wasm.Lime1.Execution.exportValue?, baseL,
      getElem?_addresses hi]⟩
  | memory i =>
    have hi : i.toNat < l.memories.length := ctx_memories hlimp ▸ lt_of_map_some het
    exact ⟨.memory ⟨i.toNat⟩, by simp [Silmaril.Wasm.Lime1.Execution.exportValue?, baseL,
      getElem?_addresses hi]⟩
  | global i =>
    have hi : i.toNat < l.globals.length := by
      simpa only [ctx_globals hlimp, List.length_map] using lt_of_map_some het
    exact ⟨.global ⟨i.toNat⟩, by simp [Silmaril.Wasm.Lime1.Execution.exportValue?, baseL,
      getElem?_addresses hi]⟩

/-- Lime1 allocation from its parts (no failure once the initializers, the exports and the
function types resolve). -/
theorem allocate?_ne_none {H : Type} {l : Lime1.Module} {vals : List Value}
    (hvals : l.globals.mapM (fun g => Silmaril.Wasm.Lime1.Execution.constExpr?
      ({} : Silmaril.Wasm.Lime1.Execution.Store H) {} g.init) = some vals)
    {exports : List Silmaril.Wasm.Execution.Runtime.ExportInst}
    (hex : l.exports.mapM (fun e => (Silmaril.Wasm.Lime1.Execution.exportValue? (baseL l)
      e.index).bind fun v => some (⟨e.name, v⟩ : Silmaril.Wasm.Execution.Runtime.ExportInst)) =
      some exports)
    {funcs : List (Silmaril.Wasm.Execution.Runtime.FuncInst Lime1.Func H)}
    (hfn : l.funcs.mapM (fun (f : Lime1.Func) => (l.types[f.type.toNat]?).bind fun ft =>
      some (Silmaril.Wasm.Execution.Runtime.FuncInst.wasm (Host := H) ft
        { baseL l with exports := exports } f)) = some funcs) :
    Silmaril.Wasm.Lime1.Execution.allocate? ({} : Silmaril.Wasm.Lime1.Execution.Store H) l [] ≠
      none := by
  intro hnone
  simp only [Silmaril.Wasm.Lime1.Execution.allocate?, Option.bind_eq_bind] at hnone
  erw [hvals] at hnone
  simp only [Option.bind_some] at hnone
  erw [hex] at hnone
  simp only [Option.bind_some] at hnone
  erw [hfn] at hnone
  simp at hnone

/-- **Lime1 allocation of a valid import-free module whose initializers evaluate succeeds.** -/
theorem allocate?_some {H : Type} {l : Lime1.Module} (hv : ModuleValid l)
    (hlimp : l.imports = []) {vals : List Value}
    (hvals : l.globals.mapM (fun g => Silmaril.Wasm.Lime1.Execution.constExpr?
      ({} : Silmaril.Wasm.Lime1.Execution.Store H) {} g.init) = some vals) :
    ∃ r, Silmaril.Wasm.Lime1.Execution.allocate? ({} : Silmaril.Wasm.Lime1.Execution.Store H) l []
      = some r := by
  have hexp : ∀ e ∈ l.exports, ∃ x, (Silmaril.Wasm.Lime1.Execution.exportValue? (baseL l)
      e.index).bind (fun v => some (⟨e.name, v⟩ : Silmaril.Wasm.Execution.Runtime.ExportInst)) =
      some x := fun e he => by
    obtain ⟨v, hv'⟩ := exportValue_some hlimp (hv.exports e he)
    exact ⟨_, by rw [hv']; rfl⟩
  obtain ⟨exports, hex⟩ := mapM_some hexp
  have hfun : ∀ f ∈ l.funcs, ∃ x, (l.types[f.type.toNat]?).bind (fun ft =>
      some (Silmaril.Wasm.Execution.Runtime.FuncInst.wasm (Host := H) ft
        { baseL l with exports := exports } f)) = some x := fun f hf => by
    obtain ⟨ft, hft⟩ := hv.function_type_exists hf
    exact ⟨_, by rw [hft]; rfl⟩
  obtain ⟨funcs, hfn⟩ := mapM_some hfun
  exact Option.ne_none_iff_exists'.mp (allocate?_ne_none hvals hex hfn)

end Silmaril.Proofs.Wasm.Component.Lime1Eng
