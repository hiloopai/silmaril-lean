module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int2.Defs

/-!
# SpecTec ↔ Core 3.0, round 5, pass 3, track fwdref: definitions

Track fwdref proves `FwdRef.StoreInjT (simEnv B) hn` for every injective `hn`
(`Round5.FwdRef2.storeInjT_simEnv`), which gives `FwdRef.HostRespectsT` for every host. So the
pass-2 leaf `Open2.hostRespects` is discharged, and this header drops it:

* `Open3`: `Round5.Int2.Open2` without `hostRespects`. It gives `Open2`
  (`Round5.FwdRef2.open2_of_open3`), hence the restated target and its run corollaries.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4Int (BI)

variable {H : Type}

/-- **The leaves still open after round 5, pass 3, track fwdref**: `Round5.Int2.Open2` without
the discharged `hostRespects`. -/
structure Open3 (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- Typing of the SIMD instructions other than `v128.const`. -/
  simd : Pos.SimdTyping (BI P hn host)
  /-- SpecTec's `Ref_ok` is Core's `RefOk` on typed stores and bounded types. -/
  refOk : Fwd.RefOkB (simEnv (BI P hn host))
  /-- The non-bitwise SIMD operators, forward. -/
  vector : Int.VectorFwd hn P host
  /-- The lane-wise vector operators agree with Core. -/
  vecOps : Simd.VecAgreeOps (simEnv (BI P hn host)) P
  /-- `Step_pure` 64 (`vtestop`), backward. -/
  vtestop : Simd.PureOpenVtestop hn P host
  /-- The `Step_read` rules still open, backward, under `ReadValidS`. -/
  read : Round5.Read.ReadRest hn P host

end Silmaril.Wasm.SpecTec.Sim.Round5.FwdRef2
