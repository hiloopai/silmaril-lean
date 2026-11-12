module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NullHost.Defs

/-!
# Round 7, memory SIMD: round 6's primitives do not depend on the host off `$hostcall`

`agreeOff_host`: `Prims.builtins P hn host` and `Prims.builtins P hn host'` agree at every name
other than `$hostcall` (`Prims.call` consults the host only in its `"hostcall"` arm), so off
`$vbytes_` and `$hostcall` (`HAgree.AgreeOff`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NullHost

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- `Prims.call` at a name other than `$hostcall` does not depend on the host. -/
theorem call_host (P : Profile) (hn : H → String) (host host' : HostSemantics H) {x : String}
    (hx : x ≠ "hostcall") (ws : List ArgV) :
    Prims.call P hn host x ws = Prims.call P hn host' x ws := by
  unfold Prims.call
  split
  · rfl
  split
  · rfl
  split
  · exact absurd rfl hx
  all_goals rfl

/-- **Round 6's primitives at two hosts agree off `$hostcall`.** -/
theorem agreeOff_host (P : Profile) (hn : H → String) (host host' : HostSemantics H) :
    HAgree.AgreeOff (Prims.builtins P hn host) (Prims.builtins P hn host') :=
  fun _ ws _ hx => call_host P hn host host' hx ws

end Silmaril.Wasm.SpecTec.Sim.Round7.NullHost
