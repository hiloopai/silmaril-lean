module

public import Silmaril.Wasm.Atlas.SpecTecR7Runs.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.HostMods.Defs

/-!
# The SpecTec run charts at the round-7 reading, for a host that invents no module

`Atlas.SpecTecR7Runs` builds the round-7 run charts from `Round7.Runs.runsRE`, for an
export-parametric host (`HostExportParam`) and with `StripInj` at every reachable configuration.
Round 5's `Round7.HostMods.runsREM` needs only `HostModsSub`, and for such a host `StripInj` and
`NamesBnd` hold along every run from a source that has them (`Round7.HostMods.reachE_of_stripInj`).
`Atlas.SpecTecR7RunsM.Thms` restates the charts with `HostModsSub`. This header adds domains that
ask for `StripInj` and `NamesBnd` at the source only.

* `RunSrcE P host c`: `c` is valid, `StripInj c` and `NamesBnd c`, and every configuration Core
  reaches from `c` satisfies round 6's `Round6.MemSimd.BoundedSelE`.
* `RunSrcDetE P host c`: `RunSrcE`, and every reachable configuration has at most one Core
  successor.

For a host with `HostModsSub` these are inside `RunDomE` and `RunDomDetE`
(`Atlas.SpecTecR7RunsM.runDomE_of_src`).
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.SpecTecR7RunsM

open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec

variable {H : Type}

/-- **The source-only domain**: valid, `StripInj` and `NamesBnd` at the source, and round 6's
selection bounds at every reachable configuration. -/
def RunSrcE (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  (∃ ts : List CValType, ConfigOk c ts) ∧ Sim.Round7.StripInj c ∧ Sim.Round7.NamesBnd c ∧
    ∀ c', Steps P host c c' → Sim.Round6.MemSimd.BoundedSelE c'

/-- `RunSrcE`, and every reachable configuration has at most one Core successor. -/
def RunSrcDetE (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  RunSrcE P host c ∧ ∀ c', Steps P host c c' → SpecTecR6.StepDet P host c'

end Silmaril.Wasm.Atlas.SpecTecR7RunsM
