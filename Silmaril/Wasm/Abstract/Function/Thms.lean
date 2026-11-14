module

public import Silmaril.Wasm.Abstract.Function.Defs
public import Silmaril.Wasm.Abstract.Outcome.Thms
public import Silmaril.Games.Abstract.Function.Thms

/-!
# Core 3.0 functions as abstract functions: theorems

* `image_wasmFun`: forgetting the final store, the behaviours of `wasmFun P
  host a` at `s` and `vs` are exactly the existing `behaviours P host s a vs`.
  The square "code → abstract function → behaviours" commutes with the
  existing semantics.
* `obsEquiv_behaviour_iff`: two functions are equivalent under the
  store-forgetting observation iff they have the same behaviours at every
  store and argument.
* `obsEquiv_trapDiv_iff`: under the store-forgetting trap ≈ divergence
  observation, they are equivalent iff their behaviour sets are
  `Behaviours.Equiv TrapDiv` at every store and argument. This is the
  existing partial-correctness equivalence.

Both observations forget the final store, so by
`Silmaril.Games.Abstract.AFun.exists_forgetState_not_congr` they need not be
congruences for code that runs afterwards in the same store. The observation
that keeps the store (`obsCollapse`) is one (`seq_obsCollapse`).
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

theorem endOfResult_toBehaviour (r : Result) (s : Store H) :
    endToBehaviour (endOfResult r s) = r.toBehaviour := by
  cases r <;> rfl

/-- The abstract function agrees with the existing behaviours. -/
theorem image_wasmFun (P : Profile) (host : HostSemantics H) (a : Nat) (s : Store H)
    (vs : List Val) :
    (fun x => endToBehaviour x.2) '' wasmFun P host a s vs = behaviours P host s a vs := by
  ext b
  constructor
  · rintro ⟨x, ⟨c', r, hs, hc, rfl⟩ | ⟨rfl, hd⟩, rfl⟩
    · exact .inl ⟨c', r, hs, hc, endOfResult_toBehaviour r _⟩
    · exact .inr ⟨rfl, hd⟩
  · rintro (⟨c', r, hs, hc, rfl⟩ | ⟨rfl, hd⟩)
    · exact ⟨_, .inl ⟨c', r, hs, hc, rfl⟩, endOfResult_toBehaviour r _⟩
    · exact ⟨_, .inr ⟨rfl, hd⟩, rfl⟩

/-- Equivalence under the store-forgetting observation is equality of
behaviours. -/
theorem obsEquiv_behaviour_iff {P P' : Profile} {host host' : HostSemantics H} {a a' : Nat} :
    AFun.ObsEquiv (fun x => endToBehaviour x.2) (wasmFun P host a) (wasmFun P' host' a') ↔
      ∀ s vs, behaviours P host s a vs = behaviours P' host' s a' vs := by
  simp only [AFun.ObsEquiv, image_wasmFun]

/-- Equivalence under the store-forgetting trap ≈ divergence observation is the
existing `Behaviours.Equiv TrapDiv`. -/
theorem obsEquiv_trapDiv_iff {P P' : Profile} {host host' : HostSemantics H} {a a' : Nat} :
    AFun.ObsEquiv (fun x => (toTag (endToBehaviour x.2)).collapse) (wasmFun P host a)
        (wasmFun P' host' a') ↔
      ∀ s vs, Behaviours.Equiv Behaviour.TrapDiv (behaviours P host s a vs)
        (behaviours P' host' s a' vs) := by
  have e : ∀ (P : Profile) (host : HostSemantics H) a s vs,
      (fun x : CallBeh Sig.empty (Store H) (List Val ⊕ Nat) =>
        (toTag (endToBehaviour x.2)).collapse) '' wasmFun P host a s vs =
      (fun b => (toTag b).collapse) '' behaviours P host s a vs := by
    intro P host a s vs
    rw [← image_wasmFun, Set.image_image]
  simp only [AFun.ObsEquiv, e, ← coarseEquiv_iff, CoarseEquiv]

end Silmaril.Wasm.Abstract
