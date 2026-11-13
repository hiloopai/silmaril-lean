module

public import Silmaril.Wasm.Models.V2CoreInstFn.Thms

/-!
# Instantiation into stores with host functions: definitions

's instantiation domain `V2CoreInstImp.domInstP P` reads the behaviours of a 2.0
instantiation at the closed host `closedV`, and every theorem putting points into it assumes a
host-free store (`V2Sound.HostFree`). A store with a host function is stuck under `closedV` as
soon as that function is called, so the closed-host reading does not fit such stores.

* `domInstHost P p`: the same domain condition with the behaviours read at the point's **own**
  host `p.2`.
* `hostFunc`, `hostFnStore`, `hostDivPt`: a store whose only function is a host function of type
  `[] → []`, with the host `divV` (every host call diverges).
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V2CoreInstHostFn

open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec
open Silmaril.Wasm.Models.V2CoreInstFn (nopType nopModInst)

/-- **The instantiation domain, behaviours read at the point's own host.** -/
def domInstHost (P : Silmaril.Wasm.Numerics.Profile) (p : Pt Nat) : Prop :=
  (v20instHT P).dom p ∧
    ∀ (m : Silmaril.Wasm.V2.Module) (cm : Silmaril.Wasm.Module)
      (xas : List Silmaril.Wasm.V2.Execution.ExternAddr),
      Silmaril.Wasm.V2.Validation.ModuleValid m → Silmaril.Wasm.V2.Module.toCore m = some cm →
      (∃ C, Silmaril.Wasm.Execution.Core.Instantiate P (ptCore p).2 (ptCore p).1 cm
        (xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) C) →
      ∃ c, Silmaril.Wasm.V2.Execution.Instantiate P p.2 p.1 m xas c ∧
        (Silmaril.Wasm.V2.Execution.behavioursOf P p.2 c).Nonempty

/-- A host function (host name `0`) of type `[] → []`. -/
def hostFunc : Silmaril.Wasm.V2.Execution.FuncInst Nat :=
  { type := nopType, module := nopModInst, code := .host 0 }

/-- The 2.0 store holding `hostFunc` and nothing else. -/
def hostFnStore : Silmaril.Wasm.V2.Execution.Store Nat := { funcs := [hostFunc] }

/-- `hostFnStore` with the host whose every call diverges. -/
def hostDivPt : Pt Nat := (hostFnStore, Silmaril.Proofs.Wasm.Models.V2Sound.divV)

end Silmaril.Wasm.Models.V2CoreInstHostFn
