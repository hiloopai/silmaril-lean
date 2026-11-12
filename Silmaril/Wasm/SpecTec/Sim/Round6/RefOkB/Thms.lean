module

public import Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.RefOkB.Restate

/-!
# SpecTec ↔ Core 3.0, round 6, track refokbb: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB`; see `docs/projects/spectec/README.md`.

* `not_refOkBB`: **`Round6.Reading.RefOkBB (simEnv B)` is false, for every `B`**, at the empty
  store and round 5's nested type `REF NULL D_out` (`not_refOkAtB_nested`, on every typed
  store).
* `dderivesB_reftypeOk_nested`: under `DDerivesB`, SpecTec accepts `REF NULL D_out` in `{}`
  (Core does not, `Round5.RefOk.not_tyOk_nested`), because `Deftype_ok` appends the group's
  subtypes to `C.RECS` where Core replaces them; `dderivesB_refOk_nested`: so SpecTec types
  `null` there, through `Ref_ok/sub`, on every typed store, under every reading of `otherwise`.
* Rule lemmas under `DDerivesB` (`Derive.lean`): `Heaptype_ok/typeuse`, `Typeuse_ok/rec`,
  `Typeuse_ok/deftype`, `Valtype_ok/ref`, `Storagetype_ok/val`, `Comptype_ok/struct` (one
  field), `Subtype_ok2` (no supertypes, both finalities), `Rectype_ok2/empty`,
  `Rectype_ok2/cons`, `Deftype_ok` (one-member groups); `dderivesB_refOk_null_of`: `Ref_ok` of
  `null` at `REF NULL ht` from `Reftype_ok {} (REF NULL ht)`.
* `refOkBV_of_refOkBB`, `refOkBV_nested_excluded`, `refOkAtB_nullAny`: the restatement
  `RefOkBV` (Core-valid stores and types; open) is weaker than `RefOkBB`, excludes the witness,
  and covers round 5's `REF NULL ANY`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB.not_refOkBB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.RefOkB.not_refOkBB

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB.not_refOkAtB_nested' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.RefOkB.not_refOkAtB_nested

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB.dderivesB_reftypeOk_nested' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.RefOkB.dderivesB_reftypeOk_nested

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB.dderivesB_refOk_nested' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.RefOkB.dderivesB_refOk_nested

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB.dderivesB_refOk_null_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.RefOkB.dderivesB_refOk_null_of

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB.dderivesB_deftypeOk1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.RefOkB.dderivesB_deftypeOk1

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB.dderivesB_subtypeOk2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.RefOkB.dderivesB_subtypeOk2

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB.refOkBV_of_refOkBB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.RefOkB.refOkBV_of_refOkBB

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB.refOkAtB_nullAny' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.RefOkB.refOkAtB_nullAny
