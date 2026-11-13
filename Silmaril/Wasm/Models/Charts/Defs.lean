module

public import Silmaril.Wasm.Models.Runtime.Defs
public import Silmaril.Wasm.Atlas.Core.Defs

/-!
# Restricted Core charts `core|S`

`coreR P H S` (written `core|S` in [wasm-models.md](../../../../docs/projects/spectec/README.md)) is the
Core chart `Silmaril.Wasm.Atlas.Core.chart P H` with a smaller domain: points whose store has
every function in `S` (`Rt.StoreIn S`) and whose host keeps the functions and throws only under
`exn` (`Rt.HostKeeps`, `Rt.HostThrowsIn S`). Observations are unchanged (`Core.obs P`), so the
embeddings `core|S → core|T` (`S ≤ T`) and `core|S → core` are equality transitions by
definition (`Thms`), and every run of an invoked function stays in `Rt.InFeat S`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Atlas
open Silmaril.Wasm.Numerics (Profile)

/-- The domain of `core|S`: the store's functions are in `S`, the host keeps them and throws
only under `exn`. -/
def coreDom (S : FeatureSet) {H : Type} (x : Core.Pt H) : Prop :=
  Rt.StoreIn S x.1 ∧ Rt.HostKeeps x.2 ∧ Rt.HostThrowsIn S x.2

/-- **The restricted Core chart `core|S`** at profile `P`. -/
def coreR (P : Profile) (H : Type) (S : FeatureSet) : Chart :=
  BChart (Core.Pt H) Core.Call (Behaviour Val) (coreDom S) (Core.obs P)

end Silmaril.Wasm.Models
