module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Fwd.Exn

/-!
# Round 5: `Obl` from `TypesB`, the host conditions and `Rest`

Eleven of `Obl`'s seventeen fields (`block`, `loop`, `tryTable`, the three `call_ref` rules,
`return_call_ref`-frame-addr, `throw` and the three `throw_ref` handler rules) are proved from
`TypesB` and the bounds of `Round4.Bounded` (the host rules also from `HostFinite` and
`Prims.HostRespects`). `forward_valid_of` is the forward conjunct from `TypesB`, the host
conditions and the six remaining fields `Rest`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Fwd

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4 (Bounded)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **`Obl` from `TypesB`, a finite host respecting the encoding, and `Rest`.** -/
theorem obl_of (TB : TypesB (simEnv (BI P hn host))) (hf : HostFinite host)
    (hr : Prims.HostRespects hn host) (R : Rest (BI P hn host) hn P host) :
    Obl (BI P hn host) hn P host where
  vector := R.vector
  aggregate := R.aggregate
  refTest := R.refTest
  refCast := R.refCast
  brOnCast := R.brOnCast
  brOnCastFail := R.brOnCastFail
  block _ _ _ _ _ _ _ h₁ h₂ hb := fwd_block5 TB h₁ h₂ hb.frame
  loop _ _ _ _ _ _ _ h₁ h₂ hb := fwd_loop5 TB h₁ h₂ hb.frame
  tryTable _ _ _ _ _ _ _ _ h₁ h₂ hb := fwd_tryTable5 TB h₁ h₂ hb.frame
  callRefFunc _ _ _ _ _ _ _ _ _ hc hfa hex hlen hcode hb :=
    fwd_callRefFunc5 TB hc hfa hex hlen hcode (tyBnd_funcType hb.storeBnd hfa)
  callRefHost _ _ _ _ _ _ _ _ _ _ _ hc hfa hex hlen hcode hh hb :=
    fwd_callRefHost5 TB hf hr hc hfa hex hlen hcode hh (tyBnd_funcType hb.storeBnd hfa)
  callRefHostDiv _ _ _ _ _ _ _ _ _ hc hfa hex hlen hcode hh hb :=
    fwd_callRefHostDiv5 TB hf hr hc hfa hex hlen hcode hh (tyBnd_funcType hb.storeBnd hfa)
  returnCallRefFrameAddr _ _ _ _ _ _ _ _ _ _ _ _ hc hfn hex hlen hb :=
    fwdUp_returnCallRefFrameAddr5 TB hc hfn hex hlen (tyBnd_funcType hb.storeBnd hfn)
  throw _ _ _ _ _ _ _ htag hex hlen hb := fwd_throw5 TB htag hex hlen hb.storeBnd
  throwRefHandlerCatch _ _ _ _ _ _ _ _ he ht _ := fwd_throwRefHandlerCatch5 he ht
  throwRefHandlerCatchRef _ _ _ _ _ _ _ _ he ht _ := fwd_throwRefHandlerCatchRef5 he ht
  throwRefHandlerNext _ _ _ _ _ _ hnm _ := fwd_throwRefHandlerNext5 hnm

/-- **The forward conjunct on valid, bounded sources** (the `fwd` field of `Round4Int.Parts`),
from `TypesB`, a finite host respecting the encoding, and `Rest`. -/
theorem forward_valid_of (TB : TypesB (simEnv (BI P hn host))) (hf : HostFinite host)
    (hr : Prims.HostRespects hn host) (R : Rest (BI P hn host) hn P host) :
    R4Fwd.Forward (BI P hn host) hn P host Round4Int.Valid :=
  forward_valid5 (obl_of TB hf hr R)

end Silmaril.Wasm.SpecTec.Sim.Round5.Fwd
