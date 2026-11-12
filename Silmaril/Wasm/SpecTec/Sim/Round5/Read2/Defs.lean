module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int2.Defs

/-!
# SpecTec ↔ Core 3.0, round 5, pass 3, track read: definitions

Pass 2 left `Round5.Read.ReadRest` open: the backward `Step_read` rules 39, 41, 69, 71, 76, 79,
91, 92 and 102 under `Round5.Read.ReadValidS`, at the concrete builtins. This track discharges
all of them (`readDone2`), so `ReadRest` holds, and `Open3` is pass 2's `Round5.Int2.Open2`
without its `read` leaf. Everything is additive.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read2

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4Int (BI)

variable {H : Type}

/-- The `Step_read` rules this track dispatches, backward, for the concrete builtins:
`load-num-val` (39), `load-pack-val` (41), `struct.new_default` (69), `struct.get-struct` (71),
`array.new_data-num` (76), `array.get-array` (79), `array.copy-le` (91), `array.copy-gt` (92) and
`array.init_data-num` (102). -/
def readDone2 : List Nat := [39, 41, 69, 71, 76, 79, 91, 92, 102]

/-- **The leaves still open after round 5, pass 3, track read**: `Round5.Int2.Open2` without
its `read` leaf (`Round5.Read.ReadRest`, now proved: `Round5.Read2.readRest`). -/
structure Open3 (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- Typing of the SIMD instructions other than `v128.const`. -/
  simd : Pos.SimdTyping (BI P hn host)
  /-- SpecTec's `Ref_ok` is Core's `RefOk` on typed stores and bounded types. -/
  refOk : Fwd.RefOkB (simEnv (BI P hn host))
  /-- The host respects the encoding at calls on typed store images. -/
  hostRespects : FwdRef.HostRespectsT (simEnv (BI P hn host)) hn host
  /-- The non-bitwise SIMD operators, forward. -/
  vector : Int.VectorFwd hn P host
  /-- The lane-wise vector operators agree with Core. -/
  vecOps : Simd.VecAgreeOps (simEnv (BI P hn host)) P
  /-- `Step_pure` 64 (`vtestop`), backward. -/
  vtestop : Simd.PureOpenVtestop hn P host

end Silmaril.Wasm.SpecTec.Sim.Round5.Read2
