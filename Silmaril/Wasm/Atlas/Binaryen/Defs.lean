module

public import Silmaril.Wasm.Atlas.Defs
public import Silmaril.Wasm.Binaryen.PassAPI.Instances

/-!
# The session charts: Core modules and Binaryen IR

Module-level charts. Points are modules; a call is a valid store, an import list and a session
script (a list of export calls); its observations are the module's observation lists
(`Binaryen.moduleObs`: the instantiation outcome followed by the session's behaviours).

* `Binaryen.coreChart P host`: Core modules.
* `Binaryen.birChart P host`: Binaryen IR modules, observed through their lowering
  (`BModule.obs`). Domain: `BModule.Ok` (the pass invariant).

In `Thms`: `Binaryen.toCore` (lowering, equal on every sentence), `Binaryen.equiv_of_exportEquiv`
(`ExportEquiv Eq` is model equivalence) and `Binaryen.pass_equiv` (every pass of the
equivalence contract, e.g. every Silmaril pipeline stage `ExtraStage.equivP`, produces an
equivalent point).
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.Binaryen

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- Session calls: a store, an import list and a script. -/
abbrev SCall (H : Type) : Type := Store H × List ExternAddr × List Binaryen.Call

/-- The observations of a Core module at a valid store. -/
def coreObs (P : Profile) {H : Type} (host : HostSemantics H) (m : Module) (c : SCall H) :
    Set (List (Behaviour Val)) :=
  {bs | StoreOk c.1 ∧ bs ∈ moduleObs P host c.1 c.2.1 m c.2.2}

/-- **The Core session chart.** -/
def coreChart (P : Profile) {H : Type} (host : HostSemantics H) : Chart :=
  BChart Module (SCall H) (List (Behaviour Val)) (fun _ => True) (coreObs P host)

/-- **The Binaryen IR session chart**: observations of the lowering. -/
def birChart (P : Profile) {H : Type} (host : HostSemantics H) : Chart :=
  BChart BModule (SCall H) (List (Behaviour Val)) BModule.Ok
    (fun m => coreObs P host m.lower)

end Silmaril.Wasm.Atlas.Binaryen
