module

public import Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.RefOkV.Assemble

/-!
# SpecTec ↔ Core 3.0, round 6, track refokbv-prove: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV`; see `docs/projects/spectec/README.md`.

`Round6.RefOkB.RefOkBV` splits into a Core half and an interpreter half. The **Core half is
proved**: SpecTec's `Ref_ok`, `Reftype_ok {}` and `Reftype_sub {}` transcribed rule for rule onto
Core types (`RefOkS`, `TyOkS`, `SubS`: append instead of replace for `C, RECS`, parent-free
`rec-*` rules) agree with Core's `RefOk` on Core-valid stores and Core-valid closed types:

* `refOkS_iff`: `RefOkS s r rt ↔ RefOk s r rt` when `StoreOk s` and `TyOk {} rt`;
* `tyOkS_empty`, `subS_empty`: Core's `TyOk {}`/`Sub {}` are SpecTec's (`recKind`: Core's
  `rec-*` rules with supertypes are admissible through `rec-sub` and `trans` over a valid
  group);
* `sub_of_subS_ref`: SpecTec's `Reftype_sub {}` between coherent types is Core's `Sub {}`, even
  through middle types that only SpecTec accepts (`coh_of_tyOkS`: SpecTec-valid defined types
  keep their kind along declared supertypes; `semK_of_subS`, `sub_of_sem`).

The **interpreter half `Agree`** (that `DDerivesB` reads `Ref_ok` as `RefOkS`) is reduced, for
every `B`, to **`AgreeTy`**, four statements about `Reftype_ok {}` and `Reftype_sub {}` alone (no
store), which is **open**:

* `agree_of_agreeTy : AgreeTy (simEnv B) → Agree (simEnv B)`: the nine rules of `Ref_ok`, both
  directions (`dderivesB_refOk_of_refOk`, `refM_of_dderivesB`);
* `refOkBV_of_agreeTy : AgreeTy (simEnv B) → RefOkB.RefOkBV (simEnv B)`;
* `refOkBV_of_agree : Agree env → RefOkB.RefOkBV env`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.refOkS_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.RefOkV.refOkS_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.refOkBV_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.RefOkV.refOkBV_of_agree

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.sub_of_subS_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.RefOkV.sub_of_subS_ref

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.subS_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.RefOkV.subS_empty

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.tyOkS_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.RefOkV.tyOkS_empty

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.coh_of_tyOkS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.RefOkV.coh_of_tyOkS

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.agree_of_agreeTy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.RefOkV.agree_of_agreeTy

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.refOkBV_of_agreeTy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.RefOkV.refOkBV_of_agreeTy

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.dderivesB_refOk_of_refOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.RefOkV.dderivesB_refOk_of_refOk

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.RefOkV.refM_of_dderivesB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.RefOkV.refM_of_dderivesB
