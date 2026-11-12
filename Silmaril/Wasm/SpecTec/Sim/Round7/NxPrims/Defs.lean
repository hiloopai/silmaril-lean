module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxSound.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round4Int.Defs

/-!
# Round 7, REH route 2: the primitives conform

`Task.flowSound` assumes `NxSound.BuiltinsVT`: the primitives answer conforming values on
conforming arguments. This header names the environment at round 4's concrete primitives:

* `envBI P hn host`: `utf8Env (Round4Int.BI P hn host)`, the round-7 environment at
  `Prims.builtins P hn host` (with `$utf8` answered by the UTF-8 encoding).

The results (`Round7/NxPrims/Thms.lean`): every primitive of `envBI` conforms. `$hostcall`
answers lists of `outcomeV` images; their stores conform at `store`, because every field
of `storeV`, of `funcInstV` and of `moduleInstToValue` is export-free except the module
records, whose fields are export-free. Every other primitive answers export-free values.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxPrims

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- **The round-7 environment at round 4's primitives.** -/
noncomputable abbrev envBI {H : Type} (P : Profile) (hn : H → String) (host : HostSemantics H) :
    Env :=
  utf8Env (Round4Int.BI P hn host)

end Silmaril.Wasm.SpecTec.Sim.Round7.NxPrims
