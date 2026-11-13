module

public import Silmaril.Proofs.Wasm.Component.Lime1RT.Inst.Store
public import Silmaril.Wasm.Component.Reference.Defs

/-!
# The engine instance of a Lime1 module has a store of Lime1

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1RT.Inst

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Numerics (Profile)

/-- Host allocation keeps a store of `S`: host functions have no Wasm body. -/
theorem allocHosts_storeIn {S : FeatureSet} (P : Profile) :
    ∀ (s : Store Nat) (i : Nat) (imps : CoreIface), Rt.StoreIn S s →
      Rt.StoreIn S (allocHosts (core3P P) s i imps).1
  | s, _, [], hs => hs
  | s, i, (_, ft) :: is, hs => by
    show Rt.StoreIn S (allocHosts (core3P P)
      (SingleThreaded.allocHost s (v1Type ft) i).1 (i + 1) is).1
    refine allocHosts_storeIn P _ (i + 1) is (storeIn_append hs (new := [_]) rfl ?_)
    intro fi hfi fn hc
    rw [List.mem_singleton] at hfi
    subst hfi
    cases hc

/-- The empty store is of every feature set. -/
theorem storeIn_empty {S : FeatureSet} {P : Profile} : Rt.StoreIn S ((core3P P).empty Nat) :=
  fun _ _ _ ha => by simp [core3P, Silmaril.Wasm.Component.Engine.core3] at ha

/-- **The Core 3.0 engine instance of a module of `S` has a store of `S`.** -/
theorem instOf_storeIn {S : FeatureSet} (P : Profile) {m : Module} (hm : Module.InFeat S m)
    {imps exps : CoreIface} {I : EInstance (core3P P)}
    (h : instOf (core3P P) m imps exps = some I) : Rt.StoreIn S (H := Nat) I.store := by
  unfold instOf at h
  have hs₀ : Rt.StoreIn S (allocHosts (core3P P) ((core3P P).empty Nat) 0 imps).1 :=
    allocHosts_storeIn P _ 0 imps storeIn_empty
  revert h hs₀
  generalize allocHosts (core3P P) ((core3P P).empty Nat) 0 imps = p
  obtain ⟨s, as⟩ := p
  intro h hs₀
  simp only at h hs₀
  split at h
  · rename_i s' inst hp
    obtain ⟨addrs, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact prepareE?_storeIn hm hs₀ hp
  · cases h

end Silmaril.Proofs.Wasm.Component.Lime1RT.Inst
