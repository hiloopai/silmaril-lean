module

public import Silmaril.Wasm.Binaryen.Toolkit.CtorEvalRun

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit.CtorEval

open Execution.Core Execution.Core.Sim Numerics Validation
open Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec
open GrowWrapper (Forced)
open GrowOOM (forced_trans forced_label forced_frame)

variable {H : Type} {P : Profile}

theorem expand_dt (t : IntType) (get : Bool) :
    (dt t get).expand? = some (.func .nil
      (if get then .cons (.num (.int t)) .nil else .nil)) := by
  cases t <;> cases get <;> rfl

theorem ctor_lookup (s : Store H) (t : IntType) (scratch current value : BitVec t.width) :
    (store s t scratch current value).funcs[s.funcs.length]? =
      some ⟨dt t false, moduleInst s t, .wasm (ctor t value)⟩ := by simp [store]

theorem getter_lookup (s : Store H) (t : IntType) (scratch current value : BitVec t.width) :
    (store s t scratch current value).funcs[s.funcs.length + 1]? =
      some ⟨dt t true, moduleInst s t, .wasm getter⟩ := by simp [store]

theorem global_lookup (s : Store H) (t : IntType) (scratch current value : BitVec t.width) :
    (store s t scratch current value).global? {module := moduleInst s t} ⟨0⟩ =
      some (s.globals.length + 1, ⟨⟨.var, .num (.int t)⟩, .num ⟨.int t, current⟩⟩) := by
  simp [store, moduleInst, Store.global?, Idx.toNat]

theorem set_global (s : Store H) (t : IntType) (scratch current value : BitVec t.width) :
    (store s t scratch current value).setGlobal (s.globals.length + 1) (.num ⟨.int t, value⟩) =
      store s t scratch value value := by
  have modification (xs : List GlobalInst) (g₁ g₂ : GlobalInst) (fn : GlobalInst → GlobalInst) :
      (xs ++ [g₁, g₂]).modify (xs.length + 1) fn = xs ++ [g₁, fn g₂] := by
    induction xs with
    | nil => rfl
    | cons x xs ih => exact congrArg (List.cons x) ih
  simp [store, Store.setGlobal, modification]

/-- Generic empty-result administrative completion. -/
theorem finish_empty_forced (s : Store H) (f fi : Frame) :
    Forced (P := P) ⟨s, f, [.frame 0 fi [.label 0 [] []]]⟩ ⟨s, f, []⟩ := by
  have label : Forced (P := P) ⟨s, fi, [.label 0 [] (vals [])]⟩ ⟨s, fi, vals []⟩ :=
    .step .labelVals (fun _ h => GrowWrapper.label_values_unique h) (.done _)
  apply forced_trans (d := ⟨s, f, [.frame 0 fi []]⟩)
  · simpa [vals] using forced_frame label 0 f
  · simpa [vals] using (Forced.step
      (Step.frameVals (P := P) (host := closedHost) (s := s) (f := f) (fi := fi) (vs := []) rfl)
      (fun _ h => GrowWrapper.frame_values_unique h) (.done _))

/-- The actual start function executes its assignment, retaining the temporary
slot explicitly rather than claiming equality to a different allocation. -/
theorem constructor_forced (s : Store H) (t : IntType) (i v : BitVec t.width) :
    Forced (P := P) (initial s t i v false)
      ⟨store s t i v v, {module := moduleInst s t}, []⟩ := by
  let f : Frame := {module := moduleInst s t}
  have hidx : f.module.funcs[(⟨0⟩ : FuncIdx).toNat]? = some s.funcs.length := by
    simp [f, moduleInst, Idx.toNat]
  refine .step (Step.call hidx (ctor_lookup s t i i v))
    (fun _ h => call_unique hidx (ctor_lookup s t i i v) h) ?_
  refine .step (d := ⟨store s t i i v, f,
      [.frame 0 f [.label 0 [] (expression (ctor t v).body)]]⟩)
    (by simpa [f, Frame.forCall, ctor, vals, Ty.length] using
      (Step.callRefFunc (P := P) (host := closedHost) (s := store s t i i v) (f := f)
        (c := .callRefType (dt t false)) (vs := []) trivial (ctor_lookup s t i i v)
        (Expand.iff.mpr (expand_dt t false)) rfl rfl))
    (fun c h => by
      have unique := callRef_noargs_unique (rs := .nil) (fn := ctor t v)
        (ctor_lookup s t i i v) (Expand.iff.mpr (expand_dt t false)) rfl h
      simpa [f, Frame.forCall, ctor, Ty.length] using unique) ?_
  have body : Forced (P := P) ⟨store s t i i v, f, expression (ctor t v).body⟩
      ⟨store s t i v v, f, []⟩ := by
    refine .step ?_ ?_ (.done _)
    · simpa [ctor, expression, f, set_global, Val.toAdmin] using
        (Step.variable (P := P) (host := closedHost)
          (VariableStep.globalSet (v := .num ⟨.int t, v⟩) (global_lookup s t i i v)))
    · intro c h
      have h' : Step P closedHost
          ⟨store s t i i v, {module := moduleInst s t},
            [(.num ⟨.int t, v⟩ : Val).toAdmin, .plain (.globalSet ⟨0⟩)]⟩ c := by
        simpa [ctor, expression, f, Val.toAdmin] using h
      have unique := globalSet_unique (global_lookup s t i i v) h'
      simpa [set_global, f] using unique
  apply forced_trans (d := ⟨store s t i v v, f, [.frame 0 f [.label 0 [] []]]⟩)
  · exact forced_frame (forced_label body 0 []) 0 f
  · exact finish_empty_forced _ _ _

/-- A getter call has exactly one finite execution, preserving the full store. -/
theorem getter_forced (s : Store H) (t : IntType) (scratch current value : BitVec t.width) :
    Forced (P := P) (invoke (store s t scratch current value) (s.funcs.length + 1) [])
      ⟨store s t scratch current value, {}, vals [.num ⟨.int t, current⟩]⟩ := by
  let f : Frame := {module := moduleInst s t}
  refine .step (d := ⟨store s t scratch current value, {},
      [.frame 1 f [.label 1 [] (expression getter.body)]]⟩)
    (by simpa [invoke, getter_lookup, f, Frame.forCall, getter, vals, Ty.length] using
      (Step.callRefFunc (P := P) (host := closedHost) (s := store s t scratch current value) (f := {})
        (c := .callRefType (dt t true)) (vs := []) trivial (getter_lookup s t scratch current value)
        (Expand.iff.mpr (expand_dt t true)) rfl rfl))
    (fun c h => by
      have unique := invoke_noargs_unique (rs := .cons (.num (.int t)) .nil) (fn := getter)
        (getter_lookup s t scratch current value) (Expand.iff.mpr (expand_dt t true)) rfl h
      simpa [f, Frame.forCall, getter, Ty.length] using unique) ?_
  have body : Forced (P := P) ⟨store s t scratch current value, f, expression getter.body⟩
      ⟨store s t scratch current value, f, vals [.num ⟨.int t, current⟩]⟩ :=
    .step (.variable (.globalGet (global_lookup s t scratch current value)))
      (fun _ h => globalGet_unique (global_lookup s t scratch current value) h) (.done _)
  exact forced_trans (forced_frame (forced_label body 1 []) 1 {})
    (GrowOOM.finish_values_forced _ _ _ _)

end Silmaril.Wasm.Binaryen.Toolkit.CtorEval
