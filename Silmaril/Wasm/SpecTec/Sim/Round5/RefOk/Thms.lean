module

public import Silmaril.Wasm.SpecTec.Sim.Round5.RefOk.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.RefOk.Refute
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.RefOk.Open5

/-!
# SpecTec ↔ Core 3.0, round 5, track refok: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round5.RefOk`; see `docs/projects/spectec/README.md`.

* `not_reftypeOk`: `Reftype_ok` is never derivable in `simEnv B` (its conclusion's `NULL?` is an
  option iteration with an empty domain, which never evaluates). So `Ref_ok/sub` never fires,
  and `eq_bot_of_dderives_null`: SpecTec types `null` at `REF NULL BOT` only.
* `not_refOkB`, `not_refOkBV`: `Fwd.RefOkB` is false, and so is its restriction `RefOkBV` to
  Core-valid stores and Core-valid closed types. The counterexample is `null` at
  `REF NULL ANY` on the empty store (`not_refOkAt_nullAny`).
* `refOkAt_nested_null`, `not_tyOk_nested`: the nested `REC 1` type that pass 2 argued from is
  no counterexample; both sides reject `null` there.
* `open5_of_open4`, `wholeStepValidOk_of_open5`, `not_open5`: `Open5` is `Open4` without
  `refOk`, with the cast-rule obligations instead; it is unsatisfiable through `simd`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.RefOk.not_reftypeOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.RefOk.not_reftypeOk

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round5.RefOk.eq_bot_of_dderives_null' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Round5.RefOk.eq_bot_of_dderives_null

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.RefOk.not_refOkAt_nullAny' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.RefOk.not_refOkAt_nullAny

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.RefOk.not_refOkBV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.RefOk.not_refOkBV

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.RefOk.not_refOkB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.RefOk.not_refOkB

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.RefOk.refOkAt_nested_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.RefOk.refOkAt_nested_null

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.RefOk.not_tyOk_nested' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.RefOk.not_tyOk_nested

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.RefOk.open5_of_open4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.RefOk.open5_of_open4

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.RefOk.not_open5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.RefOk.not_open5

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.RefOk.partsOkS_of_open5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.RefOk.partsOkS_of_open5

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.RefOk.wholeStepValidOk_of_open5' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Round5.RefOk.wholeStepValidOk_of_open5
