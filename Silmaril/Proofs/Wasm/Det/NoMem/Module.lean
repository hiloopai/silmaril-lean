module

public import Silmaril.Wasm.Det.NoMem.Module.Defs
public import Silmaril.Proofs.Wasm.Det.NoMem.Main

/-!
# The memory-free, float-free subset: soundness of the module check

`seq_of_plainsB`: code passing `plainsB` is subset code; `detInst_of_moduleB`: a module passing
`moduleB` is a deterministic instance (instantiation phase and every later call), at every
profile. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.NoMem

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Det.NoMem Silmaril.Wasm.Det.Core
open Silmaril.Wasm.Numerics (Profile)

theorem seq_of_plainsB {q : Nat → Bool} {ind : Bool} {fs : List Nat} {p : Prop} :
    ∀ {l : List Admin}, plainsB q ind fs l = true → Seq q ind fs p l
  | [], _ => trivial
  | .plain i :: l, h => by
    simp only [plainsB, Bool.and_eq_true] at h
    exact ⟨fun hc => absurd hc isCRT_plain, Or.inl h.1, seq_of_plainsB h.2⟩
  | .ref _ :: _, h | .callRefType _ :: _, h | .returnCallRefType _ :: _, h
  | .label .. :: _, h | .handler .. :: _, h | .frame .. :: _, h | .trap :: _, h => by
    simp [plainsB] at h

/-- **A module passing `moduleB` is a deterministic instance**, at every profile. -/
theorem detInst_of_moduleB {P : Profile} {m : Module} {Entry : Nat → Prop}
    (h : moduleB m = true) : DetInst P (instC₀ m) Entry := by
  simp only [moduleB, Bool.and_eq_true] at h
  exact detInst_of_storeB h.1.2 (seq_of_plainsB h.2)

end Silmaril.Proofs.Wasm.Det.NoMem
