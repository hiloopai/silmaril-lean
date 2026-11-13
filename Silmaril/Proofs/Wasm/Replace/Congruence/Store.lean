module

public import Silmaril.Wasm.Replace.Congruence.Defs

/-!
# `Store.replaceFunc` commutes with the store writes and keeps arities

The rules of Wasm 1.0 reduction that write the store write a global (`setGlobal`) or a memory
(`setMemory`); `Store.replaceFunc` writes the function table only, so the two commute. Under
`SameFuncType`, every address holds an instance of the same type before and after the
replacement, so `Saturated` (an arity condition) transports both ways.

Ported from an earlier development `Silmaril/Wasm/Equiv/Congruence.lean`. -/

@[expose] public section

namespace Silmaril.Wasm.Replace

open Silmaril.Wasm.V1.Execution
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

variable {H : Type}

/-- Replacement and a global write commute: they touch different fields. -/
theorem replaceFunc_setGlobal (s : Store H) (a b : FuncAddr) (α : GlobalAddr)
    (g : GlobalInst) :
    (setGlobal s α g).replaceFunc a b = setGlobal (s.replaceFunc a b) α g := by
  cases h : s.funcs[b.value]? <;> simp [Store.replaceFunc, setGlobal, h]

/-- Replacement and a memory write commute: they touch different fields. -/
theorem replaceFunc_setMemory (s : Store H) (a b : FuncAddr) (α : MemAddr) (m : MemInst) :
    (setMemory s α m).replaceFunc a b = setMemory (s.replaceFunc a b) α m := by
  cases h : s.funcs[b.value]? <;> simp [Store.replaceFunc, setMemory, h]

/-- The replacement moves no memory, so the frame's memory is the same. -/
@[simp] theorem frameMemory_replaceFunc (s : Store H) (a b : FuncAddr) (f : Frame) :
    frameMemory (s.replaceFunc a b) f = frameMemory s f := by
  simp [frameMemory]

/-- The replacement moves no table, so the frame's table is the same. -/
@[simp] theorem frameTable_replaceFunc (s : Store H) (a b : FuncAddr) (f : Frame) :
    frameTable (s.replaceFunc a b) f = frameTable s f := by
  simp [frameTable]

/-- Under the type side condition, an instance after the replacement is matched by one of the
same type before it. -/
theorem exists_funcInst_of_replaceFunc {s : Store H} {a b : FuncAddr}
    (h : SameFuncType s a b) {i : Nat} {fn : FuncInst Silmaril.Wasm.V1.Func H}
    (hfn : (s.replaceFunc a b).funcs[i]? = some fn) :
    ∃ fn', s.funcs[i]? = some fn' ∧ fn'.type = fn.type := by
  have ht : (s.funcs[i]?.map FuncInst.type) = some fn.type := by
    rw [← funcType_replaceFunc h i, hfn]; rfl
  exact Option.map_eq_some_iff.mp ht

/-- Under the type side condition, an instance before the replacement is matched by one of the
same type after it. -/
theorem exists_funcInst_replaceFunc {s : Store H} {a b : FuncAddr}
    (h : SameFuncType s a b) {i : Nat} {fn : FuncInst Silmaril.Wasm.V1.Func H}
    (hfn : s.funcs[i]? = some fn) :
    ∃ fn', (s.replaceFunc a b).funcs[i]? = some fn' ∧ fn'.type = fn.type := by
  have ht : ((s.replaceFunc a b).funcs[i]?.map FuncInst.type) = some fn.type := by
    rw [funcType_replaceFunc h i, hfn]; rfl
  exact Option.map_eq_some_iff.mp ht

/-- `Saturated` mentions only the arity, which the replacement keeps. -/
theorem saturated_replaceFunc {s : Store H} {a b : FuncAddr} (h : SameFuncType s a b)
    {c : FuncAddr} {args : List Runtime.Value} (hs : Saturated s c args) :
    Saturated (s.replaceFunc a b) c args := by
  obtain ⟨fi, hfi, hlen⟩ := hs
  obtain ⟨fi', hfi', hty⟩ := exists_funcInst_replaceFunc h hfi
  exact ⟨fi', hfi', by rw [hlen, hty]⟩

/-- `Saturated` transports back across the replacement. -/
theorem saturated_of_replaceFunc {s : Store H} {a b : FuncAddr} (h : SameFuncType s a b)
    {c : FuncAddr} {args : List Runtime.Value} (hs : Saturated (s.replaceFunc a b) c args) :
    Saturated s c args := by
  obtain ⟨fi, hfi, hlen⟩ := hs
  obtain ⟨fi', hfi', hty⟩ := exists_funcInst_of_replaceFunc h hfi
  exact ⟨fi', hfi', by rw [hlen, hty]⟩

/-- Function addresses are determined by their index. -/
theorem funcAddr_eq_of_value {α β : FuncAddr} (h : α.value = β.value) : α = β := by
  cases α; cases β; simp_all

/-- Away from `a`, the replacement keeps the instance at `α`. -/
theorem getElem?_replaceFunc_of_ne' {s : Store H} {a b α : FuncAddr} (hα : α ≠ a) :
    (s.replaceFunc a b).funcs[α.value]? = s.funcs[α.value]? :=
  Store.getElem?_replaceFunc_of_ne fun hc => hα (funcAddr_eq_of_value hc)

end Silmaril.Wasm.Replace
