module

public import Silmaril.Wasm.SpecTec.Sim.Round8.NxElse.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.NxElse.Lhs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.NxElse.CheckNames

/-!
# Round 8, REH: SpecTec's `otherwise` goes to the erased side (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round8.NxElse`; see `docs/projects/spectec/README.md`. Definitions are in `Round8/NxElse/Defs.lean`; the proofs are unrefined, in
`Silmaril/Raw/…/Round8/NxElse/`, and the kernel checks in `Silmaril/Proofs/…/Round8/NxElse/`.

* **`derFwdS`**: in `utf8Env B`, with primitives that conform and commute with erasure on `gdE`,
  every `DDerivesB` derivation of a `grE` relation read with SpecTec's `otherwise` gives one of the
  erased value from the erased arguments, read with SpecTec's `otherwise`. This is
  `NxDer.derFwdN` with its hypothesis `hO` discharged.
* **`derFwdS_BI`**: the same at round 4's primitives, with no hypothesis.
* **`sPureB_fwd_BI`**: SpecTec's `Step_pure` goes to the erased side, at round 4's primitives.
* **`elseLhs_fixed`** (kernel): every `otherwise` rule of a `grE` relation has a left-hand side
  that reads only quantifiers of export-free type; **`elseRules_fixed`** (kernel): these rules are
  the seven `otherwise` rules of `Step_pure`.

`hO` is discharged without the backward direction. An `otherwise` premise is read only where its
rule fires, and there the left-hand side is export-free, so erasure leaves it unchanged; SpecTec's
`otherwise` reads the value only through its left-hand side.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.NxElse

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Round6.Reading (otherwiseB SPureB)

/-- **Derivations of checked relations go to the erased side under SpecTec's `otherwise`**, given
conforming primitives that commute with erasure on `gdE`. -/
theorem derFwdS {B : Builtins} (hB : NxSound.BuiltinsVT NxTyped.sigX NxTyped.tsigFixed (utf8Env B))
    (H : EraseAll.BIErase NxErase.QT EraseAll.gdE (utf8Env B)) :
    NxDer.DerFwdN (utf8Env B) (otherwiseB (utf8Env B)) (otherwiseB (utf8Env B)) :=
  fun hx hd => NxDer.derFwdN hB H (hO_else hB H) hx (dderivesB_fire hx hd)

/-- **`derFwdS` at round 4's primitives**, with no hypothesis. -/
theorem derFwdS_BI {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) :
    NxDer.DerFwdN (NxPrims.envBI P hn host) (otherwiseB (NxPrims.envBI P hn host))
      (otherwiseB (NxPrims.envBI P hn host)) :=
  derFwdS (NxPrims.builtinsVT_BI P hn host) (NxClause.biErase_QT_BI P hn host)

/-- **SpecTec's `Step_pure` goes to the erased side**, at round 4's primitives. -/
theorem sPureB_fwd_BI {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) {is js : List Value}
    (h : SPureB (NxPrims.envBI P hn host) is js) :
    SPureB (NxPrims.envBI P hn host) (is.map Swap.eraseV) (js.map Swap.eraseV) := by
  have hx : EraseAll.grE "Step_pure" = true := by decide
  have := derFwdS_BI P hn host hx h
  simpa [SPureB, Swap.eraseV, Swap.eraseVs_eq_map] using this

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round8.NxElse.derFwdS_BI' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms derFwdS_BI

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round8.NxElse.sPureB_fwd_BI' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sPureB_fwd_BI

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round8.NxElse.elseRules_fixed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms elseRules_fixed

end Silmaril.Wasm.SpecTec.Sim.Round8.NxElse
