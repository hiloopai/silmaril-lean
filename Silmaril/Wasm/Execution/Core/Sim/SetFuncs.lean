module

public import Silmaril.Wasm.Execution.Core.Step
public import Silmaril.Wasm.Execution.Core.Sim.Store

@[expose] public section

/-! # Replacing the function instances of a store

`Store.setFuncs s g` replaces the function instances of `s` by `g`. The reduction
families other than calls never inspect function instances except through their
types (`RefOk/func`), so each family step is matched on `s.setFuncs g` whenever
`g` has the same function types as `s` (`ParametricStep` … `AggregateStep` are
either store-free or proved here in bulk). A store related by `StoreRel F` to `s`
is `s.setFuncs t.funcs` (`StoreRel.eq_setFuncs`), which reduces store transport
(`Step.transport_storeRel`, `Sim/Context.lean`) to these lemmas.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation

variable {H : Type}

/-- Replace the function instances of a store. -/
def Store.setFuncs (s : Store H) (g : List (FuncInst H)) : Store H := { s with funcs := g }

namespace Store

variable (s : Store H) (g : List (FuncInst H))

@[simp] theorem setFuncs_funcs : (s.setFuncs g).funcs = g := rfl

theorem setGlobal_setFuncs (a : Nat) (v : Val) :
    (s.setGlobal a v).setFuncs g = (s.setFuncs g).setGlobal a v := rfl
theorem setTable_setFuncs (a : Nat) (ti : TableInst) :
    (s.setTable a ti).setFuncs g = (s.setFuncs g).setTable a ti := rfl
theorem setMem_setFuncs (a : Nat) (mi : MemInst) :
    (s.setMem a mi).setFuncs g = (s.setFuncs g).setMem a mi := rfl
theorem setElem_setFuncs (a : Nat) (refs : List Ref) :
    (s.setElem a refs).setFuncs g = (s.setFuncs g).setElem a refs := rfl
theorem setData_setFuncs (a : Nat) (bytes : ByteArray) :
    (s.setData a bytes).setFuncs g = (s.setFuncs g).setData a bytes := rfl
theorem setStructField_setFuncs (a i : Nat) (fv : FieldVal) :
    (s.setStructField a i fv).setFuncs g = (s.setFuncs g).setStructField a i fv := rfl
theorem setArrayField_setFuncs (a i : Nat) (fv : FieldVal) :
    (s.setArrayField a i fv).setFuncs g = (s.setFuncs g).setArrayField a i fv := rfl
theorem addStruct_setFuncs (si : StructInst) :
    (s.addStruct si).setFuncs g = (s.setFuncs g).addStruct si := rfl
theorem addArray_setFuncs (ai : ArrayInst) :
    (s.addArray ai).setFuncs g = (s.setFuncs g).addArray ai := rfl
theorem addExn_setFuncs (e : ExnInst) :
    (s.addExn e).setFuncs g = (s.setFuncs g).addExn e := rfl

end Store

/-- A function list with the same types as `s.funcs` has a same-typed instance
wherever `s.funcs` has one. -/
theorem exists_funcs_of_types {s : Store H} {g : List (FuncInst H)}
    (hg : g.map FuncInst.type = s.funcs.map FuncInst.type) {a : Nat} {fi : FuncInst H}
    (hf : s.funcs[a]? = some fi) : ∃ fi', g[a]? = some fi' ∧ fi'.type = fi.type := by
  have h1 := congrArg (fun l : List DefType => l[a]?) hg
  simp only [List.getElem?_map, hf] at h1
  cases hga : g[a]? with
  | none => simp [hga] at h1
  | some fi' =>
    simp [hga] at h1
    exact ⟨fi', rfl, h1⟩

/-- `RefOk` reads function instances only through their types. -/
theorem RefOk.setFuncs {s : Store H} {g : List (FuncInst H)}
    (hg : g.map FuncInst.type = s.funcs.map FuncInst.type) {r : Ref} {t : CRefType}
    (h : RefOk s r t) : RefOk (s.setFuncs g) r t := by
  induction h with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct h => exact .struct h
  | array h => exact .array h
  | @func a fi h =>
    obtain ⟨fi', hga, hty⟩ := exists_funcs_of_types hg h
    rw [← hty]
    exact .func hga
  | exn h => exact .exn h
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih hn
  | sub _ hok hs ih => exact .sub ih hok hs

theorem RefOk.setFuncs_iff {s : Store H} {g : List (FuncInst H)}
    (hg : g.map FuncInst.type = s.funcs.map FuncInst.type) {r : Ref} {t : CRefType} :
    RefOk (s.setFuncs g) r t ↔ RefOk s r t :=
  ⟨fun h => RefOk.setFuncs (s := s.setFuncs g) (g := s.funcs) hg.symm h, RefOk.setFuncs hg⟩

theorem CatchMatches.setFuncs_iff {s : Store H} {g : List (FuncInst H)} {f : Frame} {a : Nat}
    {c : Catch} : CatchMatches (s.setFuncs g) f a c ↔ CatchMatches s f a c := by
  cases c <;> exact Iff.rfl

/-! ## Family steps on `s.setFuncs g` -/

section Families

open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {c c' : Config H}

theorem VariableStep.setFuncs (h : VariableStep c c') (g : List (FuncInst H)) :
    VariableStep (H := H) ⟨c.store.setFuncs g, c.frame, c.code⟩
      ⟨c'.store.setFuncs g, c'.frame, c'.code⟩ := by
  cases h <;> (try simp only [Store.setGlobal_setFuncs]) <;> constructor! <;> assumption

theorem VariableStep.funcs_eq (h : VariableStep c c') : c'.store.funcs = c.store.funcs := by
  cases h <;> rfl

theorem TableStep.setFuncs (h : TableStep P c c') (g : List (FuncInst H)) :
    TableStep P (H := H) ⟨c.store.setFuncs g, c.frame, c.code⟩
      ⟨c'.store.setFuncs g, c'.frame, c'.code⟩ := by
  cases h <;> (try simp only [Store.setTable_setFuncs, Store.setElem_setFuncs]) <;>
    constructor! <;> assumption

theorem TableStep.funcs_eq (h : TableStep P c c') : c'.store.funcs = c.store.funcs := by
  cases h <;> rfl

theorem MemoryStep.setFuncs (h : MemoryStep P c c') (g : List (FuncInst H)) :
    MemoryStep P (H := H) ⟨c.store.setFuncs g, c.frame, c.code⟩
      ⟨c'.store.setFuncs g, c'.frame, c'.code⟩ := by
  cases h <;> (try simp only [Store.setMem_setFuncs, Store.setData_setFuncs]) <;>
    constructor! <;> assumption

theorem MemoryStep.funcs_eq (h : MemoryStep P c c') : c'.store.funcs = c.store.funcs := by
  cases h <;> rfl

theorem RefStep.setFuncs (h : RefStep c c') {g : List (FuncInst H)}
    (hg : g.map FuncInst.type = c.store.funcs.map FuncInst.type) :
    RefStep (H := H) ⟨c.store.setFuncs g, c.frame, c.code⟩
      ⟨c'.store.setFuncs g, c'.frame, c'.code⟩ := by
  cases h <;> (try dsimp only at hg ⊢) <;> constructor! <;>
    first
      | assumption
      | exact (RefOk.setFuncs_iff hg).2 ‹_›
      | exact fun h' => ‹¬ RefOk _ _ _› ((RefOk.setFuncs_iff hg).1 h')

theorem RefStep.funcs_eq (h : RefStep c c') : c'.store.funcs = c.store.funcs := by
  cases h <;> rfl

theorem AggregateStep.setFuncs (h : AggregateStep c c') (g : List (FuncInst H)) :
    AggregateStep (H := H) ⟨c.store.setFuncs g, c.frame, c.code⟩
      ⟨c'.store.setFuncs g, c'.frame, c'.code⟩ := by
  cases h <;>
    (try simp only [Store.setStructField_setFuncs, Store.setArrayField_setFuncs,
      Store.addStruct_setFuncs, Store.addArray_setFuncs]) <;>
    first
      | (constructor! <;> assumption)
      | (apply AggregateStep.arrayCopyOob₂ <;> assumption)
      | (apply AggregateStep.arrayInitElemOob₂ <;> assumption)
      | (apply AggregateStep.arrayInitDataOob₂ <;> assumption)

theorem AggregateStep.funcs_eq (h : AggregateStep c c') : c'.store.funcs = c.store.funcs := by
  cases h <;> rfl

end Families

namespace Sim

/-- A store related to `s` is `s` with the related function instances. -/
theorem StoreRel.eq_setFuncs {F : FuncInst H → FuncInst H → Prop} {s t : Store H}
    (h : StoreRel F s t) : t = s.setFuncs t.funcs := by
  have ho := h.other
  cases s; cases t
  simp_all [Store.setFuncs]

/-- A store with the functions of `s` is related to itself with the functions of
`t`, when `s` and `t` are related. -/
theorem StoreRel.setFuncs_of {F : FuncInst H → FuncInst H → Prop} {s t s' : Store H}
    (h : StoreRel F s t) (hs : s'.funcs = s.funcs) : StoreRel F s' (s'.setFuncs t.funcs) :=
  ⟨by rw [hs]; exact h.types, rfl, by rw [hs]; exact h.funcs⟩

end Sim

end Silmaril.Wasm.Execution.Core
