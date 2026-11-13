module

public import Silmaril.Wasm.Execution.Runtime.Map

/-!
# Injective transport of runtime syntax and stores

silmaril-lean's `Silmaril.Wasm.Execution.Runtime.Map` transports runtime syntax, stores, host
outcomes and host relations along a map `f` of function code. When `f` is injective, so are the
transports:

* `funcInst_mapCode_injective`, `store_mapCode_injective`, `hostOutcome_mapCode_injective`;
* `adminInstr_map_injective`, `adminInstr_mapList_injective` (for a map of instructions);
* `hostSemantics_mapCode_iff`: the transported host relation has exactly the original outcomes
  on transported stores.

Ported from an earlier development `Silmaril/Wasm/Execution/Runtime/Map/Injective.lean`,
with the declarations renamed into `Silmaril.Wasm.RuntimeMap` and the case analyses rewritten to
state each injectivity fact instead of substituting through `cases`.
-/

@[expose] public section

namespace Silmaril.Wasm.RuntimeMap

open Silmaril.Wasm.Execution.Runtime

variable {A B H I J : Type*}

/-- Transporting a function instance along an injective code map is injective. -/
theorem funcInst_mapCode_injective {f : A → B} (hf : Function.Injective f) :
    Function.Injective (FuncInst.mapCode (H := H) f) := by
  intro x y h
  cases x <;> cases y <;>
    simp only [FuncInst.mapCode, FuncInst.wasm.injEq, FuncInst.host.injEq, reduceCtorEq] at h
  · obtain ⟨rfl, rfl, hc⟩ := h
    rw [hf hc]
  · obtain ⟨rfl, rfl⟩ := h
    rfl

/-- Transporting a store along an injective code map is injective. -/
theorem store_mapCode_injective {f : A → B} (hf : Function.Injective f) :
    Function.Injective (Store.mapCode (H := H) f) := by
  rintro ⟨xf, xt, xm, xg⟩ ⟨yf, yt, ym, yg⟩ h
  obtain ⟨hfuncs, rfl, rfl, rfl⟩ := Store.mk.inj h
  have hf' : xf = yf := List.map_injective_iff.mpr (funcInst_mapCode_injective hf) hfuncs
  rw [hf']

/-- Transporting a host outcome along an injective code map is injective. -/
theorem hostOutcome_mapCode_injective {f : A → B} (hf : Function.Injective f) :
    Function.Injective (HostOutcome.mapCode (H := H) f) := by
  intro x y h
  cases x <;> cases y <;>
    simp only [HostOutcome.mapCode, Silmaril.Wasm.Execution.Host.Outcome.returned.injEq,
      reduceCtorEq] at h
  · obtain ⟨hs, rfl⟩ := h
    rw [store_mapCode_injective hf hs]
  · rfl

/-- Along an injective code map, the transported host relation has exactly the original
outcomes on transported stores. -/
theorem hostSemantics_mapCode_iff {f : A → B} (hf : Function.Injective f)
    (host : HostSemantics A H) (h : H) (s : Store A H) (args : List Value)
    (out : HostOutcome A H) :
    host.mapCode f h (s.mapCode f) args (out.mapCode f) ↔ host h s args out := by
  constructor
  · rintro ⟨s', out', hs, hout, run⟩
    rw [store_mapCode_injective hf hs, hostOutcome_mapCode_injective hf hout]
    exact run
  · exact HostSemantics.compatible_mapCode f host h s args out

mutual
/-- Transporting an administrative instruction along an injective instruction map is
injective. -/
theorem adminInstr_map_injective {f : I → J} (hf : Function.Injective f)
    (x y : AdminInstr I) (h : AdminInstr.map f x = AdminInstr.map f y) : x = y := by
  cases x with
  | source i =>
    cases y with
    | source j => exact congrArg AdminInstr.source (hf (AdminInstr.source.inj h))
    | _ => cases h
  | invoke a =>
    cases y with
    | invoke b => exact congrArg AdminInstr.invoke (AdminInstr.invoke.inj h)
    | _ => cases h
  | label n cont body =>
    cases y with
    | label m cont' body' =>
      obtain ⟨hn, hc, hb⟩ : n = m ∧ cont.map f = cont'.map f ∧
          AdminInstr.mapList f body = AdminInstr.mapList f body' := AdminInstr.label.inj h
      rw [hn, List.map_injective_iff.mpr hf hc, adminInstr_mapList_injective hf body body' hb]
    | _ => cases h
  | frame n fr body =>
    cases y with
    | frame m fr' body' =>
      obtain ⟨hn, hfr, hb⟩ : n = m ∧ fr = fr' ∧
          AdminInstr.mapList f body = AdminInstr.mapList f body' := AdminInstr.frame.inj h
      rw [hn, hfr, adminInstr_mapList_injective hf body body' hb]
    | _ => cases h
  | trap => cases y <;> first | rfl | cases h
termination_by sizeOf x

/-- Transporting a list of administrative instructions along an injective instruction map is
injective. -/
theorem adminInstr_mapList_injective {f : I → J} (hf : Function.Injective f)
    (xs ys : List (AdminInstr I)) (h : AdminInstr.mapList f xs = AdminInstr.mapList f ys) :
    xs = ys := by
  cases xs with
  | nil => cases ys <;> first | rfl | cases h
  | cons x xs =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      obtain ⟨hx, hxs⟩ := List.cons.inj h
      rw [adminInstr_map_injective hf x y hx, adminInstr_mapList_injective hf xs ys hxs]
termination_by sizeOf xs
end

end Silmaril.Wasm.RuntimeMap
