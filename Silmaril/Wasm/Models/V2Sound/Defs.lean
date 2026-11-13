module

public import Silmaril.Wasm.Models.V2Core.Defs
public import Silmaril.Wasm.Versions.Soundness.Thms

/-!
# Typed points of the own Wasm 2.0 model

The judgments of 2.0 type soundness, read on the points and calls of `v20own`
(`Silmaril/Wasm/Models/V2Core/Defs.lean`). The judgments themselves come from the copied
`Silmaril/Raw/Wasm/Versions/V2/Soundness/{Store,Defs,Config}.lean` (an earlier development,
source namespace `Silmaril.Wasm.V2.Execution`):

* `StoreOk s`: `Store_ok`, rebuilt from the W3C 2.0 appendix and Core 3.0's
  `7.1-soundness`, because SpecTec 2.0 has no soundness file;
* `HostOk host`: on a typed store and typed arguments a host function has an outcome, and each
  returned outcome is a typed result on a typed, extending store;
* `InvokeOk s a vs`: `$invoke`'s premises (`9-module:196-199`) with the argument types;
* `ConfigOk c ts`, `Extend s s'`: configuration typing and store extension.

Here:

* `Typed p`: the store of the point is typed and its host keeps `HostOk`;
* `CallTyped p c`: the call satisfies `InvokeOk` on the point's store;
* `v20typed P H`: `v20own P H` on typed points, observing only typed calls.

`Typed` is independent of `dom`: `dom` asks for the structural well-formedness `StoreWF` and a
Core image, which the simulation into Core 3.0 needs. `v20typed` asks for both.

New definitions; `Thms` states the theorems.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V2Sound

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **A typed 2.0 point**: `Store_ok` holds for the store and the host keeps `HostOk`. -/
def Typed (p : Pt H) : Prop :=
  Silmaril.Wasm.V2.Execution.StoreOk p.1 ∧ Silmaril.Wasm.V2.Execution.HostOk p.2

/-- **A typed call**: the premises of `$invoke`, with the argument types, on the point's
store. -/
def CallTyped (p : Pt H) (c : Call) : Prop :=
  Silmaril.Wasm.V2.Execution.InvokeOk p.1 c.1 c.2

/-- The observations of a typed call (none for an untyped one). -/
def obsTyped (P : Profile) (p : Pt H) (c : Call) : Set (Behaviour CVal) :=
  {b | CallTyped p c ∧ b ∈ obs P p c}

/-- **The typed own 2.0 model** at profile `P`: `v20own P H` on typed points of its domain,
observing typed calls. -/
def v20typed (P : Profile) (H : Type) : WasmModel :=
  { v20own P H with
    obs := obsTyped P
    dom := fun p => dom p ∧ Typed p }

end Silmaril.Wasm.Models.V2Sound
