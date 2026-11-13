module

public import Silmaril.Wasm.Models.V2CoreInstData.Thms

/-!
# The instantiation domain with imports, at every profile: definitions

An earlier step restated the `eq` instantiation embedding at `Profile.deterministic g` on the domain
`V2CoreInstDet.domInstDet g`. Its points so far (`emptyPt`, `dataPt`) hold nothing a module can
import. The definitions below are what this topic needs to go further:

* `domInstP P`: `domInstDet` with the deterministic profile replaced by any profile `P`
  (`domInstDet g` is `domInstP (Profile.deterministic g)` by definition);
* `ImportsTransport p`: at the point `p`, Core's typing of the image addresses against the
  import types of a module's Core image gives 2.0's typing of the addresses against the 2.0
  import types. This is the step from Core's `Externaddr_ok` back to 2.0's;
* `NoFuncs s`: the 2.0 store has no function instance. Every address Core types in its image is
  a memory, a global or a table;
* `impStore`, `impPt`: the store with one empty memory of limits `[0 ..]`, one immutable `i32`
  global holding `0` and one empty `funcref` table of limits `[0 ..]`, with the closed host. A
  module can import all three.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V2CoreInstImp

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec

/-- **`domInstDet` at any profile**: `v20instHT P`'s domain, and every image call of a 2.0-valid
module that Core instantiates has a 2.0 instantiation run whose closed-host behaviours are not
empty. -/
def domInstP (P : Profile) (p : Pt Nat) : Prop :=
  (v20instHT P).dom p ∧
    ∀ (m : Silmaril.Wasm.V2.Module) (cm : Silmaril.Wasm.Module)
      (xas : List Silmaril.Wasm.V2.Execution.ExternAddr),
      Silmaril.Wasm.V2.Validation.ModuleValid m → Silmaril.Wasm.V2.Module.toCore m = some cm →
      (∃ C, Silmaril.Wasm.Execution.Core.Instantiate P (ptCore p).2 (ptCore p).1 cm
        (xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) C) →
      ∃ c, Silmaril.Wasm.V2.Execution.Instantiate P p.2 p.1 m xas c ∧
        (Silmaril.Wasm.V2.Execution.behavioursOf P closedV c).Nonempty

/-- **Core import typing transports back to 2.0 at `p`**: whenever a 2.0-valid module's Core
image is valid with import types `xtI` and Core types the image addresses at `xtI`, 2.0 types
the addresses at the module's 2.0 import types. -/
def ImportsTransport (p : Pt Nat) : Prop :=
  ∀ (m : Silmaril.Wasm.V2.Module) (cm : Silmaril.Wasm.Module)
    (xas : List Silmaril.Wasm.V2.Execution.ExternAddr)
    (ixt xt : List Silmaril.Wasm.V2.ExternType)
    (xtI xtE : List Silmaril.Wasm.Validation.CExternType),
    Silmaril.Wasm.V2.Validation.ModuleOk m ixt xt → Silmaril.Wasm.V2.Module.toCore m = some cm →
    Silmaril.Wasm.Validation.ModuleOk cm ⟨xtI, xtE⟩ →
    List.Forall₂ (Silmaril.Wasm.Execution.Core.ExternAddrOk (ptCore p).1)
      (xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) xtI →
    List.Forall₂ (Silmaril.Wasm.V2.Execution.ExternAddrOk p.1) xas ixt

/-- A 2.0 store with no function instance. -/
def NoFuncs {H : Type} (s : Silmaril.Wasm.V2.Execution.Store H) : Prop :=
  s.funcs = []

/-- The 2.0 store with one empty memory of limits `[0 ..]`, one immutable `i32` global holding
`0` and one empty `funcref` table of limits `[0 ..]`. -/
def impStore : Silmaril.Wasm.V2.Execution.Store Nat :=
  { mems := [{ type := ⟨⟨0, none⟩⟩, bytes := ByteArray.empty }],
    globals := [{ type := ⟨.const, .num (.int .i32)⟩, value := .num ⟨.int .i32, 0⟩ }],
    tables := [{ type := ⟨⟨0, none⟩, .funcref⟩, refs := [] }] }

/-- `impStore` with the closed host. -/
def impPt : Pt Nat := (impStore, closedV)

end Silmaril.Wasm.Models.V2CoreInstImp
