module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.FwdR
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int3.Thms

/-!
# Round 5: `Open5`, the restated `Open4`

`Open5` replaces `Int3.Open4.vecOps` by `Simd.VecAgreeLanes` and `Simd.VecConvertR`, both proved
at the concrete builtins, so `Open5` is exactly `simd ∧ refOk` (`open5_iff`). Its forward vector
steps hold up to Core's choice (`vectorFwdR_of_open5`). `simd` is false (track simdty's
`not_simdTyping`), so `Open5` is unsatisfiable as well (`not_open5`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Convert

open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core
open Round4Int (BI)

variable {H : Type} {P : Profile} {hn : H → String} {host : HostSemantics H}

/-- **`Open5` asks no more than `Int3.Open4`.** -/
theorem open5_of_open4 (O : Int3.Open4 hn P host) : Open5 hn P host :=
  ⟨O.simd, O.refOk, Simd.vecAgreeLanes_builtins, vecConvertR_builtins⟩

/-- **`Open5` is its two unproved leaves.** -/
theorem open5_iff : Open5 hn P host ↔
    Pos.SimdTyping (BI P hn host) ∧ Fwd.RefOkB (simEnv (BI P hn host)) :=
  ⟨fun O => ⟨O.simd, O.refOk⟩,
    fun ⟨hs, hr⟩ => ⟨hs, hr, Simd.vecAgreeLanes_builtins, vecConvertR_builtins⟩⟩

/-- **The forward vector steps, up to Core's choice, from `Open5`'s vector leaves.** -/
theorem vectorFwdR_of_open5 (O : Open5 hn P host) : VectorFwdR hn P host :=
  vectorFwdR_of O.vecLanes O.vecConvert

/-- **`Open5` is unsatisfiable**, through `simd`. -/
theorem not_open5 : ¬ Open5 hn P host := fun O => SimdTy.not_simdTyping _ O.simd

end Silmaril.Wasm.SpecTec.Sim.Round5.Convert
