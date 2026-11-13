module

public import Silmaril.Wasm.Models.Model.Thms
public import Silmaril.Wasm.Versions.Thms
public import Silmaril.Wasm.Behaviour.Semantics.V2

/-!
# The own Wasm 2.0 model `v20own` and its embedding data into `core|v20`

The **own 2.0 model** is silmaril-lean's rule-by-rule transcription of
`wasm-2.0/8-reduction.spectec`, `Silmaril.Wasm.V2.Execution.Step P`, observed through
`Silmaril.Wasm.V2.Execution.behaviours P`. The forward simulation into Core 3.0 is the copied
`Silmaril.Wasm.V2.Execution.Step.toCore` (`Silmaril/Raw/Wasm/Versions/V2/ToCore/Execution.lean`).

* `HostKeepsV`: a 2.0 host keeps the store's functions (the 2.0 analogue of
  `Rt.HostKeeps`);
* `closedV`: the closed 2.0 host, which has no outcome;
* `liftHost src`: the **Core host induced by a 2.0 host**. On a Core store whose erasure is the
  image of a 2.0 store, it does what `src` does, with translated arguments and results, and a
  returning call keeps the Core store's functions. It is defined, not assumed, so the point map
  of the embedding is a function of the 2.0 point alone;
* `Pt H`: a 2.0 point (a store and a host); `dom`: the 2.0 store is well formed
  (`StoreWF`) and has a Core image, and the host preserves well-formedness and keeps
  functions;
* `obs P`: the observations of a call `(a, vs)` are the 2.0 behaviours **read in Core values**
  (`Behaviour.mapSet Val.toCore`) when `a` is an allocated address. Core values are the common
  observation type because the translation forgets the reference type of a null (Core nulls are
  untyped), so it has no read-back; calls of unallocated addresses are not observed (`$invoke`
  requires the address to be allocated, `9-module:191`);
* `v20own P H`: the model. Its modules are the valid 2.0 modules that have a Core image
  (`Module.toCore` is undefined only for `CVTOP` immediates no binary module can express; see
  `Silmaril.Wasm.V2.ToCore.Instructions`);
* `ptCore`: the point map into `core|v20`.

New definitions; `Thms` states the embedding.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V2Core

open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)

/-- 2.0 stores. -/
abbrev VStore (H : Type) := Silmaril.Wasm.V2.Execution.Store H
/-- 2.0 host semantics. -/
abbrev VHost (H : Type) := Silmaril.Wasm.V2.Execution.HostSemantics H
/-- 2.0 values. -/
abbrev VVal := Silmaril.Wasm.V2.Execution.Val
/-- Core 3.0 values. -/
abbrev CVal := Silmaril.Wasm.Execution.Core.Val
/-- Core 3.0 stores. -/
abbrev CStore (H : Type) := Silmaril.Wasm.Execution.Core.Store H
/-- Core 3.0 host semantics. -/
abbrev CHost (H : Type) := Silmaril.Wasm.Execution.Core.HostSemantics H

/-- A 2.0 host keeps the store's functions. -/
def HostKeepsV {H : Type} (src : VHost H) : Prop :=
  ∀ h s vs s' r, src h s vs (.returned s' r) → s'.funcs = s.funcs

/-- **The Core host induced by a 2.0 host**: on a Core store `S` whose erasure is the image of
a 2.0 store `s`, a call with translated arguments diverges when `src` does, and returns the
translated result on a store `S'` with `S`'s functions whose erasure is the image of the
returned 2.0 store. -/
def liftHost {H : Type} (src : VHost H) : CHost H := fun h S args out =>
  ∃ (s : VStore H) (vs : List VVal),
    Silmaril.Wasm.V2.Execution.Store.toCore s =
        some (Silmaril.Wasm.V2.Execution.ToCore.Store.erase S) ∧
      args = vs.map Silmaril.Wasm.V2.Execution.Val.toCore ∧
      ((src h s vs .diverged ∧ out = .diverged) ∨
       ∃ s' r S', src h s vs (.returned s' r) ∧
         out = .returned S' (Silmaril.Wasm.V2.Execution.Result.toCore r) ∧
         Silmaril.Wasm.V2.Execution.Store.toCore s' =
           some (Silmaril.Wasm.V2.Execution.ToCore.Store.erase S') ∧
         S'.funcs = S.funcs)

/-- The closed 2.0 host: no host function returns or diverges. -/
def closedV {H : Type} : VHost H := fun _ _ _ _ => False

/-- 2.0 points: a store and a host. -/
abbrev Pt (H : Type) := VStore H × VHost H

/-- 2.0 calls: a function address and 2.0 arguments. -/
abbrev Call := Nat × List VVal

/-- The domain of the own 2.0 model. -/
def dom {H : Type} (p : Pt H) : Prop :=
  Silmaril.Wasm.V2.Execution.StoreWF p.1 ∧
    (Silmaril.Wasm.V2.Execution.Store.toCore p.1).isSome ∧
    Silmaril.Wasm.V2.Execution.HostPreserves p.2 ∧ HostKeepsV p.2

/-- The observations of a call: the 2.0 behaviours, in Core values, of an allocated address. -/
def obs (P : Profile) {H : Type} (p : Pt H) (c : Call) : Set (Behaviour CVal) :=
  {b | c.1 < p.1.funcs.length ∧
    b ∈ Behaviour.mapSet Silmaril.Wasm.V2.Execution.Val.toCore
      (Silmaril.Wasm.V2.Execution.behaviours P p.2 p.1 c.1 c.2)}

/-- **The own Wasm 2.0 model** at profile `P`. -/
def v20own (P : Profile) (H : Type) : WasmModel where
  feats := Silmaril.Wasm.Models.v20
  Module := Silmaril.Wasm.V2.Module
  Valid m := Silmaril.Wasm.V2.Validation.ModuleValid m ∧ (Silmaril.Wasm.V2.Module.toCore m).isSome
  Pt := Pt H
  Call := Call
  Obs := Behaviour CVal
  obs := obs P
  dom := dom

/-- The point map into `core|v20`: the Core image of the store and the induced host. -/
def ptCore {H : Type} (p : Pt H) : Silmaril.Wasm.Atlas.Core.Pt H :=
  ((Silmaril.Wasm.V2.Execution.Store.toCore p.1).getD {}, liftHost p.2)

/-- The call map: translate the arguments. -/
def callCore (c : Call) : Silmaril.Wasm.Atlas.Core.Call :=
  (c.1, c.2.map Silmaril.Wasm.V2.Execution.Val.toCore)

/-- The module map (`{}` off the domain of `Module.toCore`). -/
def modCore (m : Silmaril.Wasm.V2.Module) : Silmaril.Wasm.Module :=
  (Silmaril.Wasm.V2.Module.toCore m).getD {}

end Silmaril.Wasm.Models.V2Core
