module

public import Silmaril.Wasm.Wasmi.Defs
public import Silmaril.Wasm.Execution.Core.Sim.Store

/-!
# The wasmi and loose charts

Placement of the nonconformant model of wasmi 2.0.0 and of the loose model in the atlas
(`docs/projects/spectec/README.md` §4.3). All charts have the points (a store and a host) and calls
(a function address and arguments) of the Core chart.

* `Dom`: the wasmi domain: the store's Wasm code is in wasmi 2.0.0's feature set
  (`Silmaril.Wasm.Wasmi.StoreSupported`), and the host is parametric in function code
  (silmaril-lean's `HostParametric`, as for every code-transformation result in silmaril-lean);
* `chart P H`: **the wasmi chart**, the Core observations of the translated store on `Dom`;
* `coreOn P H`: the Core chart restricted to `Dom`, the overlap with the wasmi chart;
* `coreNF P H`: the Core chart on the `NoFusedSelect` sub-domain (`Dom` and no pattern);
* `looseChart P H`: **the loose chart**, `Core + selectEither`, domain everything.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.Wasmi

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.Numerics (Profile)

/-- The wasmi domain: code in wasmi 2.0.0's feature set and a host parametric in function
code. -/
def Dom {H : Type} (x : Core.Pt H) : Prop := Silmaril.Wasm.Wasmi.StoreSupported x.1 ∧ HostParametric x.2

/-- The `NoFusedSelect` sub-domain: the wasmi domain without the reported pattern. -/
def DomNF {H : Type} (x : Core.Pt H) : Prop := Dom x ∧ Silmaril.Wasm.Wasmi.StorePatFree x.1

/-- **The wasmi chart** at profile `P`. -/
def chart (P : Profile) (H : Type) : Chart :=
  BChart (Core.Pt H) Core.Call (Behaviour Val) Dom (Silmaril.Wasm.Wasmi.obs P)

/-- The Core chart on the wasmi domain. -/
def coreOn (P : Profile) (H : Type) : Chart :=
  BChart (Core.Pt H) Core.Call (Behaviour Val) Dom (Core.obs P)

/-- The Core chart on the `NoFusedSelect` sub-domain. -/
def coreNF (P : Profile) (H : Type) : Chart :=
  BChart (Core.Pt H) Core.Call (Behaviour Val) DomNF (Core.obs P)

/-- **The loose chart** at profile `P`: Core 3.0 with `selectEither`. -/
def looseChart (P : Profile) (H : Type) : Chart :=
  Variant.chartR (H := H) (Silmaril.Wasm.Wasmi.Loose.Step P) (fun _ => True)

end Silmaril.Wasm.Atlas.Wasmi
