module

public import Silmaril.Proofs.Wasm.Component.Core3G.Sim
public import Silmaril.Proofs.Wasm.Component.Param.Restrict
import all Silmaril.Wasm.Component.Semantics.Thms

/-!
# Restrictions of the Core 3.0 engine against `modSem P`

Proofs for `Silmaril.Wasm.Component.Core3G.Thms`. With the bridge `engineSem_eq_modSem`, the
restriction theorems of `Silmaril.Wasm.Component.Param` become statements about `modSem P`:

* `restrict_le_modSem`: the game semantics of a restriction `restrict (core3P P) r` of the Core
  3.0 engine refines `modSem P` on every module with the same instance on both sides;
* `restrict_eq_modSem`: it is `modSem P` when the instance respects the restriction
  (`Respects`: the runtime invariant is closed, holds at every invocation of an export and at
  every resumption, and its stores satisfy a store invariant holding at instantiation).
-/

public section

namespace Silmaril.Proofs.Wasm.Component.Core3G

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {r : Restriction (core3P P)} {m : NumModule} {I : ScalarInstance}

/-- The restricted engine semantics of a module whose engine instance is `I`. -/
theorem restrict_engineSem_of_sameInst
    (hS : instOf (core3P P) m.mod [] m.exports = some ⟨I.store, I.addrs⟩) :
    (engineSem (restrict (core3P P) r) NumModule NumModule.mod).sem m =
      engineStrategy (restrict (core3P P) r) (EInstance.res ⟨I.store, I.addrs⟩) [] m.exports := by
  have hS' : instOf (core3P P) (NumModule.mod m) (CoreModule.imports m) (CoreModule.exports m) =
      some ⟨I.store, I.addrs⟩ := hS
  have h2 : instOf (restrict (core3P P) r) (NumModule.mod m) (CoreModule.imports m)
      (CoreModule.exports m) = some (EInstance.res ⟨I.store, I.addrs⟩) :=
    (Silmaril.Proofs.Wasm.Component.Param.instOf_restrict (E := core3P P) (r := r) (NumModule.mod m)
      _ _).trans (by rw [hS']; rfl)
  unfold engineSem
  dsimp only
  rw [h2]
  rfl

/-- **A restriction of the Core 3.0 engine refines `modSem P`.** -/
theorem restrict_le_modSem (hI : m.IsInst I)
    (hS : instOf (core3P P) m.mod [] m.exports = some ⟨I.store, I.addrs⟩) :
    (engineSem (restrict (core3P P) r) NumModule NumModule.mod).sem m ≤ (modSem P).sem m := by
  have hle : (engineSem (restrict (core3P P) r) NumModule NumModule.mod).Le
      (engineSem (core3P P) NumModule NumModule.mod) :=
    Silmaril.Proofs.Wasm.Component.Param.engineSem_restrict_le (E := core3P P) NumModule
      NumModule.mod
  exact (hle m).trans (engineSem_eq_modSem P hI hS).le

/-- **A restriction respected by the instance has the semantics `modSem P`.** -/
theorem restrict_eq_modSem (hI : m.IsInst I)
    (hS : instOf (core3P P) m.mod [] m.exports = some ⟨I.store, I.addrs⟩)
    {Sto : (core3P P).Store Nat → Prop}
    (hR : Silmaril.Proofs.Wasm.Component.Param.Respects r ⟨I.store, I.addrs⟩ Sto) :
    (engineSem (restrict (core3P P) r) NumModule NumModule.mod).sem m = (modSem P).sem m := by
  rw [restrict_engineSem_of_sameInst hS,
    Silmaril.Proofs.Wasm.Component.Param.engineStrategy_restrict_eq hR]
  rw [← engineSem_of_sameInst hS]
  exact engineSem_eq_modSem P hI hS

end Silmaril.Proofs.Wasm.Component.Core3G
