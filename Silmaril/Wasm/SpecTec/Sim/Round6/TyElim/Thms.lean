module

public import Silmaril.Wasm.SpecTec.Sim.Round6.TyElim.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.TyElim.Assemble

/-!
# SpecTec ↔ Core 3.0, round 6, track agreety-elim: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round6.TyElim`; see `docs/projects/spectec/README.md`.

**Both elimination fields of `RefOkV.AgreeTy` are proved** on the concrete builtins
`Prims.builtins prof hn host` (every profile, encoding and host; `Round4Int.BI` is this `B`):

* `okElim_BI`: `Reftype_ok {}` at the image of a reference type makes its heap type coherent
  (`RefOkV.CohH`), by inverting `Reftype_ok`, `Heaptype_ok`, `Typeuse_ok`, `Deftype_ok`,
  `Rectype_ok2` and `Subtype_ok2` under `DDerivesB`, plus the head constructor of
  `Comptype_sub` (`coh_of_deftypeOk`);
* `subElim_BI`: `Reftype_sub {}` from the image of a reference type is `RefOkV.SubE` to the
  image of a reference type, by the recursor of `DDerivesB` over `Heaptype_sub` and
  `Deftype_sub` in `{}` (`subM_of_dderivesB`); the typed middle and right-hand types are images
  (`img_heap`, `img_def`), `typeidx-*` and `rec-*` never fire in `{}`, and `Deftype_sub/refl`
  never fires because `$clos_deftype` has no value.

So `AgreeTy` on the concrete builtins is its introduction half `AgreeTyIntro` (`okIntro`,
`subIntro`, verbatim; `agreeTy_of_intro`), and `Round6.Task.wholeStepValidR Int.backend`, its
multi-step corollary and `Target.OpenR` follow from `AgreeTyIntro` alone
(`wholeStepValidR_backend_of_intro`, `runsR_backend_of_intro`, `openR_backend_of_intro`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.TyElim.okElim_BI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.TyElim.okElim_BI

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.TyElim.img_heap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.TyElim.img_heap

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.TyElim.subElim_BI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.TyElim.subElim_BI

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.TyElim.agreeTy_of_intro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.TyElim.agreeTy_of_intro

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.TyElim.openR_backend_of_intro' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.TyElim.openR_backend_of_intro

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.TyElim.wholeStepValidR_backend_of_intro' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.TyElim.wholeStepValidR_backend_of_intro

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.TyElim.runsR_backend_of_intro' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.TyElim.runsR_backend_of_intro

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.TyElim.coh_of_deftypeOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.TyElim.coh_of_deftypeOk

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.TyElim.subM_of_dderivesB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.TyElim.subM_of_dderivesB
