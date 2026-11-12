module

public import Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.AgreeSub.Main

/-!
# SpecTec ↔ Core 3.0, round 6, track agreety-subintro: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub`; see `docs/projects/spectec/README.md`.

* `subIntro_BI`: **the field `subIntro` of `RefOkV.AgreeTy` holds in
  `simEnv (BI P hn host)`**, for every profile `P` (so in particular `Profile.spec nd r`),
  every `hn` and every `host`: Core's `Sub {}` between bounded, Core-valid reference types gives
  SpecTec's `Reftype_sub {}` under `DDerivesB`, under every reading of `otherwise`.
* `agreeTy_iff`: `AgreeTy env` is exactly its four fields (`OkIntro`, `SubIntro`, `OkElim`,
  `SubElim`); `agreeTy_of_rest`: in `simEnv (BI P hn host)`, `AgreeTy` follows from the three
  fields that remain open.

The proof builds canonical derivations from `Sem` normal form
(`RefOkV.semK_of_subS`): abstract middle types only (`Heaptype_sub/trans` through `EQ` or the
kind of a defined type), `none`-family steps, `struct`/`array`/`func` from `Expand`, and chains
of `Deftype_sub/super` for reachability along declared supertypes.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core (HostSemantics)
open Silmaril.Wasm.Numerics (Profile)
open Round4Int (BI)

variable {H : Type}

/-- **`AgreeTy.subIntro` holds** in `simEnv (BI P hn host)`, for every profile. -/
theorem subIntro_BI (P : Profile) (hn : H → String) (host : HostSemantics H) :
    SubIntro (simEnv (BI P hn host)) :=
  fun O p rt hbp hbr hp hr hs => subIntro O p rt hbp hbr hp hr hs

/-- `AgreeTy` is exactly its four fields. -/
theorem agreeTy_iff {env : Env} :
    RefOkV.AgreeTy env ↔ OkIntro env ∧ SubIntro env ∧ OkElim env ∧ SubElim env :=
  ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

/-- **`AgreeTy` in `simEnv (BI P hn host)` from its three open fields**: `subIntro` is
`subIntro_BI`. -/
theorem agreeTy_of_rest {P : Profile} {hn : H → String} {host : HostSemantics H}
    (hok : OkIntro (simEnv (BI P hn host))) (hokE : OkElim (simEnv (BI P hn host)))
    (hsubE : SubElim (simEnv (BI P hn host))) : RefOkV.AgreeTy (simEnv (BI P hn host)) :=
  agreeTy_iff.2 ⟨hok, subIntro_BI P hn host, hokE, hsubE⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub.subIntro_BI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.AgreeSub.subIntro_BI

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub.agreeTy_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.AgreeSub.agreeTy_of_rest

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub.dderivesB_of_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.AgreeSub.dderivesB_of_sem

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub.dderivesB_reach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.AgreeSub.dderivesB_reach

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub.dderivesB_expandB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.AgreeSub.dderivesB_expandB
