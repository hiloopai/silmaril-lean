module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int2.Defs

/-!
# SpecTec ↔ Core 3.0, round 5, pass-3 integration: definitions

Pass 3 discharged four of `Round5.Int2.Open2`'s seven leaves:

* `hostRespects`: `Round5.FwdRef2.hostRespectsT_all` (every host, injective `hn`);
* `read`: `Round5.Read2.readRest`;
* `vtestop`: `Round5.Simd.pureOpenVtestop`;
* `vector`: `Round5.SimdTy.vectorFwd_of_ops`, from the `vecOps` leaf.

`Open4` holds the three leaves left. Pass 3 also showed that two of them can never hold
(`Round5.Int3.not_open4`, `Round5.Int3.not_open4_spec`), so `wholeStepValidOk_of_open4`, like
its predecessors, is vacuous as stated. See `docs/projects/spectec/README.md`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Int3

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4Int (BI)

variable {H : Type}

/-- **The leaves still open after round 5, pass 3**, at one encoding, host and profile. -/
structure Open4 (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- Typing of the SIMD instructions other than `v128.const`. False for every
  builtins: `Round5.SimdTy.not_simdTyping`. -/
  simd : Pos.SimdTyping (BI P hn host)
  /-- SpecTec's `Ref_ok` is Core's `RefOk` on typed stores and bounded types.
  Argued false (nested `REC 1`), not refuted. -/
  refOk : Fwd.RefOkB (simEnv (BI P hn host))
  /-- The lane-wise vector operators agree with Core. False under the spec NaN
  profile, through its `convert` field: `Round5.Simd.not_vecAgreeOps_spec`. -/
  vecOps : Simd.VecAgreeOps (simEnv (BI P hn host)) P

end Silmaril.Wasm.SpecTec.Sim.Round5.Int3
