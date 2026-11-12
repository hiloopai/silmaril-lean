module

public import Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.AgreeOk.Main

/-!
# SpecTec ↔ Core 3.0, round 6, track agreety-okintro: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk`; see `docs/projects/spectec/README.md`.

* `okIntro_BI`: **the field `okIntro` of `RefOkV.AgreeTy` holds in `simEnv (BI P hn host)`**,
  for every profile `P` (so in particular `Profile.spec nd r`), every `hn` and every `host`:
  SpecTec's `Reftype_ok {}` holds under `DDerivesB` at every bounded reference type valid in
  Core's `{}`, under every reading of `otherwise`.
* `tyOkB_empty` (Core only): a bounded type valid in Core's `{}` has a **canonical** derivation
  (`TyOkB`): SpecTec's validation rules on Core types (`Deftype_ok` appends the group to `RECS`,
  `rec-*` need parent-free members), where every `Heaptype_sub/trans` has a bounded middle type.
  Inside groups, Core's subtyping premises are rebuilt from Silmaril's `REC`-aware checker
  (`Sub.checkRWith_complete`, `subB_checkCompR`), whose middles are abstract heap types or
  declared supertypes of the group's members.
* `okD_of`, `subD_of` (`Trans.lean`): canonical derivations are read rule for rule by
  `DDerivesB` in `simEnv (BI P hn host)`, in the context whose `RECS` are the images of the
  canonical context's.
* `agreeTy_of_elim`: with `subIntro_BI`, `AgreeTy` in
  `simEnv (BI P hn host)` follows from its two elimination fields `okElim`, `subElim` (open here);
  `wholeStepValidR_backend_of_elim`: so does `Round6.Task.wholeStepValidR Int.backend`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk.okIntro_BI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.AgreeOk.okIntro_BI

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk.okIntro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.AgreeOk.okIntro

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk.tyOkB_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.AgreeOk.tyOkB_empty

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk.okD_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.AgreeOk.okD_of

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk.subD_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.AgreeOk.subD_of

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk.agreeTy_of_elim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.AgreeOk.agreeTy_of_elim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk.wholeStepValidR_backend_of_elim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.AgreeOk.wholeStepValidR_backend_of_elim
