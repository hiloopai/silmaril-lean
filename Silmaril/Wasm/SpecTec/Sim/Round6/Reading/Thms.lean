module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Reading.Script
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Reading.Ref
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Reading.Lift
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Reading.CastsBwd

/-!
# SpecTec ↔ Core 3.0, round 6, track reading: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round6.Reading`; see `docs/projects/spectec/README.md`.

* `dderivesB_of_dderives`: the new reading `DDerivesB` extends `DDerives`.
* `dderivesB_iff_of_closed`, `otherwiseAtB_iff_of_closed`, `firesB_iff_of_closed`: on a set of
  relations closed under plainness (no empty-domain option in a conclusion, premises inside the
  set) the two readings agree, `otherwise` included.
* `firesB_iff_at`, `dderivesB_iff_at`: the same for one relation at one left-hand side, when
  every rule is plain or cannot fire there.
* `firesB_pure_iff`, `sPureB_iff`: every `Step_pure` rule transfers.
* `firesB_read_iff`, `sReadB_iff`: every `Step_read` rule transfers at a left-hand side whose
  code names none of the cast constructors.
* `firesB_step_iff`: every rule of `Step` except `read` and the four context rules transfers;
  `sstepB_read`, `sstepB_pure`, `sstepB_ctxtInstrs`, `sstepB_ctxtLabel`, `sstepB_ctxtHandler`,
  `sstepB_ctxtFrame` lift steps through those five.
* `dderivesB_reftypeOk`, `dderivesB_reftypeSub_null`, `dderivesB_fieldtypeOk`,
  `conclAlts_subtypeOk2`: the rules with an optional atom in their conclusion now fire (or, for
  `Subtype_ok2`, have both alternatives).
* `dderivesB_refOk_nullAny`: round 5's counterexample to `RefOkB` is none under `DDerivesB`.
* `castsFwdB_of`, `castsBwdB_of`: the cast rules (`Step_read` 2–5, 65–68), forward and backward,
  from `RefOkBB` (`Ref_ok` under `DDerivesB` is Core's `RefOk` on typed stores and bounded types;
  not proved).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.dderivesB_of_dderives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.dderivesB_of_dderives

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.dderivesB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.dderivesB_iff

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.dderivesB_iff_of_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.dderivesB_iff_of_closed

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.otherwiseAtB_iff_of_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.otherwiseAtB_iff_of_closed

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.firesB_iff_of_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.firesB_iff_of_closed

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.dderivesB_otherwise_iff_of_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.dderivesB_otherwise_iff_of_closed

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.otherwiseAtB_iff_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.otherwiseAtB_iff_at

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.firesB_iff_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.firesB_iff_at

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.dderivesB_iff_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.dderivesB_iff_at

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.closed_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.closed_pure

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.closed_expand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.closed_expand

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.firesB_pure_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.firesB_pure_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.sPureB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.sPureB_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.closedAt_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.closedAt_read

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.firesB_read_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.firesB_read_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.sReadB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.sReadB_iff

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.conclAlts_reftypeOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.conclAlts_reftypeOk

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.conclAlts_reftypeSubNull' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.conclAlts_reftypeSubNull

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.conclAlts_fieldtypeOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.conclAlts_fieldtypeOk

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.conclAlts_subtypeOk2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.conclAlts_subtypeOk2

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.dderivesB_reftypeOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.dderivesB_reftypeOk

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.dderivesB_reftypeSub_null' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.dderivesB_reftypeSub_null

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.dderivesB_fieldtypeOk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.dderivesB_fieldtypeOk

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.dderivesB_heaptypeOk_abs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.dderivesB_heaptypeOk_abs

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.dderivesB_heaptypeSub_bot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.dderivesB_heaptypeSub_bot

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.dderivesB_refOk_null' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.dderivesB_refOk_null

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.dderivesB_refOk_nullAny' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.dderivesB_refOk_nullAny

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.refOkAtB_nullAny_null' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.refOkAtB_nullAny_null

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.firesB_step_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.firesB_step_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.sstepB_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.sstepB_read

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.sstepB_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.sstepB_pure

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.sstepB_ctxtInstrs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.sstepB_ctxtInstrs

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.sstepB_ctxtLabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.sstepB_ctxtLabel

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.sstepB_ctxtHandler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.sstepB_ctxtHandler

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.sstepB_ctxtFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.sstepB_ctxtFrame

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.firesB_iff_of_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.firesB_iff_of_plain

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.otherwiseB_of_ruleAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.otherwiseB_of_ruleAt

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.castsFwdB_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.castsFwdB_of

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.read_doneKB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.read_doneKB

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round6.Reading.castsBwdB_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round6.Reading.castsBwdB_of
