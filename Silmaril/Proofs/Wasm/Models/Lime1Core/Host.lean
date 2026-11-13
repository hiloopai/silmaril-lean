module

public import Silmaril.Wasm.Models.Lime1Core.Defs

/-!
# The induced Core host of a Lime1 host

* `erase_withFuncs`: the Core image of a returned Lime1 store, with the functions of the Core
  store the call started from, is again an image;
* `compat`: `HostCompatible src (liftHostC src)` (the copied simulation's notion) for a Lime1
  host that preserves the simulation's store invariant and keeps functions;
* `keeps`, `throwsIn`: the induced host keeps functions and never throws, so the image point
  lies in the domain of `core|S` as far as the host is concerned.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.Lime1Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Models Silmaril.Wasm.Models.Lime1Core
open Silmaril.Wasm.Models.V10 (LStore LHost HostKeepsL)
open Silmaril.Wasm.Models.V2Core (CStore CHost)
open Silmaril.Wasm.Lime1.Execution.ToCore (Store.erase)

variable {H : Type}

/-- Erasure commutes with replacing the functions. -/
theorem erase_with (X : CStore H) (fs : List (Silmaril.Wasm.Execution.Core.FuncInst H)) :
    Store.erase { X with funcs := fs } =
      { Store.erase X with funcs := fs.map fun fi => { fi with
          module := Silmaril.Wasm.Lime1.Execution.ToCore.ModuleInst.erase fi.module } } := rfl

/-- The Core image of the returned store with the old functions is an image. -/
theorem erase_withFuncs {s s' : LStore H} {S : CStore H} (hf : s'.funcs = s.funcs)
    (hE : Store.erase S = s.toCore) :
    Store.erase { s'.toCore with funcs := S.funcs } = s'.toCore := by
  have h₁ : (S.funcs.map fun fi => { fi with
      module := Silmaril.Wasm.Lime1.Execution.ToCore.ModuleInst.erase fi.module }) =
      s.funcs.map FuncInst.toCore := congrArg Silmaril.Wasm.Execution.Core.Store.funcs hE
  have h₂ := Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase_toCore s'
  rw [erase_with, h₁, ← hf, h₂]
  rfl

/-- The induced host matches every behaviour of the Lime1 host. -/
theorem lift_matches {src : LHost H} (hk : HostKeepsL src) {h : H} {s : LStore H}
    {vs : List Value} {out : HostOutcome Silmaril.Wasm.Lime1.Func H} {S : CStore H}
    (hsrc : src h s vs out) (hE : Store.erase S = s.toCore) :
    ∃ out', liftHostC src h S (vs.map Value.toCore) out' ∧
      Silmaril.Wasm.Lime1.Execution.HostOutcomeSim out out' := by
  cases out with
  | diverged => exact ⟨.diverged, ⟨s, vs, hE, rfl, Or.inl ⟨hsrc, rfl⟩⟩, trivial⟩
  | returned s' r =>
    have hf : s'.funcs = s.funcs := hk h s vs s' r hsrc
    have he := erase_withFuncs hf hE
    exact ⟨.returned { s'.toCore with funcs := S.funcs } r.toCore,
      ⟨s, vs, hE, rfl, Or.inr ⟨s', r, _, hsrc, rfl, he, rfl⟩⟩, he, rfl⟩

/-- **The induced Core host is compatible with the Lime1 host.** -/
theorem compat {src : LHost H} (hp : Silmaril.Wasm.Lime1.Execution.HostPreserves src)
    (hk : HostKeepsL src) : Silmaril.Wasm.Lime1.Execution.HostCompatible src (liftHostC src) :=
  ⟨hp, fun _ _ _ _ _ hsrc hE => lift_matches hk hsrc hE⟩

/-- The induced host keeps functions. -/
theorem keeps (src : LHost H) : Rt.HostKeeps (liftHostC src) := by
  rintro h S args S' r ⟨s, vs, -, -, ⟨-, hout⟩ | ⟨s', r', S'', -, hout, -, hfun⟩⟩
  · cases hout
  · cases hout
    exact hfun

/-- The induced host never throws. -/
theorem throwsIn (S : FeatureSet) (src : LHost H) : Rt.HostThrowsIn S (liftHostC src) := by
  rintro h X args X' a ⟨s, vs, -, -, ⟨-, hout⟩ | ⟨s', r', S'', -, hout, -, -⟩⟩
  · cases hout
  · cases r' <;> cases hout

end Silmaril.Proofs.Wasm.Models.Lime1Core
