module

public import Silmaril.Wasm.Models.Model.Thms
public import Silmaril.Wasm.Models.V10.Defs
public import Silmaril.Wasm.Versions.Thms

/-!
# The own Lime1 model `lime1own` and its embedding data into Core 3.0

The **own Lime1 model** is silmaril-lean's Lime1 execution
`Silmaril.Wasm.Lime1.Execution.Step` (its own syntax, validation and reduction rules), observed
through `behavioursL`. The forward simulation into Core 3.0 is the copied
`Silmaril.Wasm.Lime1.Execution.{Step,Steps,Diverges}.toCore` and `Sim.result`
(`Silmaril/Raw/Wasm/Versions/Lime1/ToCore/*`, an earlier development; provenance in

* `invokeL`, `behavioursOfL`, `behavioursL`: the entry configuration `$invoke` and the
  behaviours of Lime1, defined exactly as silmaril-lean defines them for 1.0
  (`Silmaril.Wasm.V1.Execution.behaviours`), since Lime1 has no behaviour adapter of its own;
* `liftHostC src`: the **Core host induced by a Lime1 host**: on a Core store whose erasure is the
  image of a Lime1 store, it does what `src` does, with translated arguments and results, and a
  returning call keeps the Core store's functions;
* `dom p`: the Lime1 store is well formed in the copied simulation's sense (`StoreWF`: allocated
  module functions, memories fitting 32-bit addresses), and the host preserves it and keeps
  functions;
* `obs p (a, vs)`: the Lime1 behaviours of an allocated address, read in Core values
  (`Value.toCore`);
* `lime1own H`: the model (`feats = lime1`). Its modules are the valid Lime1 modules
  (silmaril-lean's `Lime1.Validation.ModuleValid`);
* `ptCore`, `callCore`: the point and call maps into Core.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.Lime1Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Models.V10 (LStore LHost HostKeepsL)
open Silmaril.Wasm.Models.V2Core (CVal CStore CHost)

/-- The Lime1 entry configuration `$invoke(s, a, vs)` (the 1.0 one, at Lime1 code). -/
def invokeL {H : Type} (s : LStore H) (a : FuncAddr) (vs : List Value) :
    Silmaril.Wasm.Lime1.Execution.Config H :=
  ⟨s, ⟨[], {}⟩, Silmaril.Wasm.Lime1.Execution.values vs ++ [.invoke a]⟩

/-- The observable behaviours of running a Lime1 configuration. -/
def behavioursOfL {H : Type} (host : LHost H) (c : Silmaril.Wasm.Lime1.Execution.Config H) :
    Set (Behaviour Value) :=
  {b | ∃ (c' : Silmaril.Wasm.Lime1.Execution.Config H) (r : Result),
        Silmaril.Wasm.Lime1.Execution.Steps host c c' ∧
          c'.code = Silmaril.Wasm.Lime1.Execution.result r ∧ b = r.toBehaviour} ∪
  {b | b = .diverges ∧ Silmaril.Wasm.Lime1.Execution.Diverges host c}

/-- The observable behaviours of invoking a Lime1 function address. -/
def behavioursL {H : Type} (host : LHost H) (s : LStore H) (a : FuncAddr) (vs : List Value) :
    Set (Behaviour Value) :=
  behavioursOfL host (invokeL s a vs)

/-- **The Core host induced by a Lime1 host.** -/
def liftHostC {H : Type} (src : LHost H) : CHost H := fun h S args out =>
  ∃ (s : LStore H) (vs : List Value),
    Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase S = s.toCore ∧
      args = vs.map Value.toCore ∧
      ((src h s vs .diverged ∧ out = .diverged) ∨
       ∃ s' r S', src h s vs (.returned s' r) ∧ out = .returned S' r.toCore ∧
         Silmaril.Wasm.Lime1.Execution.ToCore.Store.erase S' = s'.toCore ∧ S'.funcs = S.funcs)

/-- Lime1 points: a store and a host. -/
abbrev Pt (H : Type) := LStore H × LHost H

/-- Lime1 calls. -/
abbrev Call := FuncAddr × List Value

/-- The domain of the own Lime1 model. -/
def dom {H : Type} (p : Pt H) : Prop :=
  Silmaril.Wasm.Lime1.Execution.StoreWF p.1 ∧
    Silmaril.Wasm.Lime1.Execution.HostPreserves p.2 ∧ HostKeepsL p.2

/-- The observations of a call: the Lime1 behaviours of an allocated address, in Core values. -/
def obs {H : Type} (p : Pt H) (c : Call) : Set (Behaviour CVal) :=
  {b | c.1.value < p.1.funcs.length ∧
    b ∈ Behaviour.mapSet Value.toCore (behavioursL p.2 p.1 c.1 c.2)}

/-- **The own Lime1 model.** -/
def lime1own (H : Type) : WasmModel where
  feats := Silmaril.Wasm.Models.lime1
  Module := Silmaril.Wasm.Lime1.Module
  Valid := Silmaril.Wasm.Lime1.Validation.ModuleValid
  Pt := Pt H
  Call := Call
  Obs := Behaviour CVal
  obs := obs
  dom := dom

/-- The point map into Core: the Core image of the store and the induced host. -/
def ptCore {H : Type} (p : Pt H) : Silmaril.Wasm.Atlas.Core.Pt H := (p.1.toCore, liftHostC p.2)

/-- The call map. -/
def callCore (c : Call) : Silmaril.Wasm.Atlas.Core.Call := (c.1.value, c.2.map Value.toCore)

end Silmaril.Wasm.Models.Lime1Core
