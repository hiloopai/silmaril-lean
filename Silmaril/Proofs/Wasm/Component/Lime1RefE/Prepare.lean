module

public import Silmaril.Proofs.Wasm.Component.Lime1RefE.Relabel

/-!
# Relabelling commutes with Lime1 preparation

`Lime1.Execution.prepare?` (allocation and segment initialisation) reads a store only through
the length of its function list, its tables, memories and globals, and adds `.wasm` functions
only. So it commutes with relabelling the host codes (`prepare_relabel`), and so does the
engine's `lime1.prepare?` (`lime1_prepare_relabel`). It also adds no host function
(`prepare_noHost`, `lime1_prepare_noHost`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1RefE

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Lime1.Execution
open Silmaril.Wasm.Component.Engine.Lime1 (lime1)

variable {H H' : Type} (g : H → H')

theorem mapM_wasm (types : List V1.FuncType) (module : ModuleInst) :
    ∀ L : List Lime1.Func,
    (L.mapM fun (f : Lime1.Func) => types[f.type.toNat]?.bind fun ft =>
        some (FuncInst.wasm ft module f : FuncInst Lime1.Func H')) =
      (L.mapM fun (f : Lime1.Func) => types[f.type.toNat]?.bind fun ft =>
        some (FuncInst.wasm ft module f : FuncInst Lime1.Func H)).map
        (List.map (FuncInst.relabel g))
  | [] => rfl
  | f :: L => by
    simp only [List.mapM_cons, mapM_wasm types module L]
    cases types[f.type.toNat]? <;> cases (L.mapM fun (f : Lime1.Func) =>
        types[f.type.toNat]?.bind fun ft =>
        some (FuncInst.wasm ft module f : FuncInst Lime1.Func H)) <;> rfl

theorem relabel_tables (s : Lime1.Execution.Store H) : (Store.relabel g s).tables = s.tables := rfl
theorem relabel_memories (s : Lime1.Execution.Store H) : (Store.relabel g s).memories = s.memories := rfl
theorem relabel_globals (s : Lime1.Execution.Store H) : (Store.relabel g s).globals = s.globals := rfl
theorem relabel_funcs (s : Lime1.Execution.Store H) : (Store.relabel g s).funcs = s.funcs.map (FuncInst.relabel g) := rfl
theorem constExpr_relabel (s : Lime1.Execution.Store H) (mi : ModuleInst) (es) :
  constExpr? (Store.relabel g s) mi es = constExpr? s mi es := rfl

theorem allocate_relabel (s : Lime1.Execution.Store H) (m : Lime1.Module) (imps : List ExternVal) :
    allocate? (Store.relabel g s) m imps =
      (allocate? s m imps).map fun p => (Store.relabel g p.1, p.2) := by
  unfold allocate?
  have hl : (Store.relabel g s).funcs.length = s.funcs.length := List.length_map _
  simp only [hl, constExpr_relabel, relabel_tables, relabel_memories, relabel_globals, Option.bind_eq_bind, Option.pure_def, Option.map_bind, Function.comp_def]
  simp only [mapM_wasm g, Option.bind_map, Function.comp_def, Option.map_some, Store.relabel, List.map_append]

theorem resolveElem_relabel (s : Lime1.Execution.Store H) (mi : ModuleInst) :
  resolveElem? (Store.relabel g s) mi = resolveElem? s mi := rfl
theorem resolveData_relabel (s : Lime1.Execution.Store H) (mi : ModuleInst) :
  resolveData? (Store.relabel g s) mi = resolveData? s mi := rfl
theorem foldl_applyElem_relabel : ∀ (ws : List ElemWrite) (s : Lime1.Execution.Store H),
    ws.foldl applyElem (Store.relabel g s) = Store.relabel g (ws.foldl applyElem s)
  | [], _ => rfl
  | w :: ws, s => foldl_applyElem_relabel ws (applyElem s w)
theorem foldl_applyData_relabel : ∀ (ws : List DataWrite) (s : Lime1.Execution.Store H),
    ws.foldl applyData (Store.relabel g s) = Store.relabel g (ws.foldl applyData s)
  | [], _ => rfl
  | w :: ws, s => foldl_applyData_relabel ws (applyData s w)

def Prepared.relabel (p : Prepared H) : Prepared H' := ⟨Store.relabel g p.store, p.module, p.start⟩

theorem prepare_relabel (s : Lime1.Execution.Store H) (m : Lime1.Module) (imps : List ExternVal) :
    prepare? (Store.relabel g s) m imps = (prepare? s m imps).map (Prepared.relabel g) := by
  unfold prepare?
  simp only [Option.bind_eq_bind, allocate_relabel g, Option.bind_map, Function.comp_def]
  cases allocate? s m imps with
  | none => rfl
  | some p =>
    simp only [Option.bind_some, resolveElem_relabel, resolveData_relabel,
      foldl_applyElem_relabel, foldl_applyData_relabel, Option.map_bind, Function.comp_def]
    cases m.start <;> simp [Option.map_bind, Prepared.relabel, Function.comp_def]

/-- **The engine's preparation commutes with relabelling.** -/
theorem lime1_prepare_relabel (s : Lime1.Execution.Store H) (m : Lime1.Module)
    (imps : List ExternVal) :
    lime1.prepare? (Store.relabel g s) m imps =
      (lime1.prepare? s m imps).map fun p => (Store.relabel g p.1, p.2.1, p.2.2) := by
  change (Lime1.Execution.prepare? _ m imps).map _ =
    ((Lime1.Execution.prepare? s m imps).map _).map _
  rw [prepare_relabel, Option.map_map, Option.map_map]
  rfl

/-! ## Prepared stores have no host function beyond the old ones -/

theorem mapM_wasm_noHost (types : List V1.FuncType) (module : ModuleInst) :
    ∀ (L : List Lime1.Func) (fs : List (FuncInst Lime1.Func H)),
    (L.mapM fun (f : Lime1.Func) => types[f.type.toNat]?.bind fun ft =>
        some (FuncInst.wasm ft module f : FuncInst Lime1.Func H)) = some fs →
      ∀ (i : Nat) (ft : V1.FuncType) (h : H), fs[i]? ≠ some (.host ft h)
  | [], fs, e, i, ft, h => by
    cases (Option.some.inj e).symm
    simp
  | f :: L, fs, e, i, ft, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at e
    obtain ⟨x, ⟨ft', -, hx⟩, xs, hxs, e⟩ := e
    cases hx
    cases e
    cases i with
    | zero => simp
    | succ i => exact mapM_wasm_noHost types module L xs hxs i ft h

theorem foldl_applyElem_funcs : ∀ (ws : List ElemWrite) (s : Lime1.Execution.Store H),
    (ws.foldl applyElem s).funcs = s.funcs
  | [], _ => rfl
  | w :: ws, s => foldl_applyElem_funcs ws (applyElem s w)

theorem foldl_applyData_funcs : ∀ (ws : List DataWrite) (s : Lime1.Execution.Store H),
    (ws.foldl applyData s).funcs = s.funcs
  | [], _ => rfl
  | w :: ws, s => foldl_applyData_funcs ws (applyData s w)

theorem prepare_noHost {s : Lime1.Execution.Store H} (hs : NoHost s) {m : Lime1.Module}
    {imps : List ExternVal} {p : Prepared H} (h : prepare? s m imps = some p) : NoHost p.store := by
  unfold prepare? allocate? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨a, ⟨gs, -, es, -, fs, hfs, ha⟩, elems, -, data, -, h⟩ := h
  have hp : p.store.funcs = s.funcs ++ fs := by
    have e : p.store = data.foldl applyData (elems.foldl applyElem a.1) := by
      split at h
      · cases h; rfl
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨_, -, h⟩ := h
        cases h; rfl
    rw [e, foldl_applyData_funcs, foldl_applyElem_funcs, ← Option.some.inj ha]
  intro i ft hh e
  rw [hp] at e
  rcases Nat.lt_or_ge i s.funcs.length with hi | hi
  · rw [List.getElem?_append_left hi] at e
    exact hs i ft hh e
  · rw [List.getElem?_append_right hi] at e
    exact mapM_wasm_noHost _ _ _ fs hfs _ ft hh e

theorem noHost_empty : NoHost ({} : Lime1.Execution.Store H) := fun i ft h e => by
  simp at e

/-- **The engine's preparation adds no host function.** -/
theorem lime1_prepare_noHost {s : Lime1.Execution.Store H} (hs : NoHost s) {m : Lime1.Module}
    {imps : List ExternVal} {st : Lime1.Execution.Store H} {mi : ModuleInst}
    {o : Option FuncAddr} (h : lime1.prepare? s m imps = some (st, mi, o)) : NoHost st := by
  change (Lime1.Execution.prepare? s m imps).map _ = _ at h
  obtain ⟨p, hp, e⟩ := Option.map_eq_some_iff.1 h
  cases e
  exact prepare_noHost hs hp

end Silmaril.Proofs.Wasm.Component.Lime1RefE
