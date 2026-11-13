module

public import Silmaril.Wasm.SpecTec.Institution.Cover.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Cover
public import Silmaril.Proofs.Wasm.SpecTec.Institution.CoverWitness

/-!
# Choice cover on round 6's domain: results

Namespace `Silmaril.Wasm.SpecTec.Institution.Cover`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.{Cover,CoverWitness}`; see `docs/projects/spectec/README.md`,
"choice".

* `forwardSel`, `fwd_exact`: on round 6's domain `Dom`, the forward half is **exact** at the
  concrete primitives `Round4Int.BI`: every Core successor is, up to `ConfigEq`, a step fact of
  `stepModel BI`. Round 6's "up to Core's choice" came only from `vcvtop`, whose
  non-`FloatMissel` (`extend`) operators are deterministic (`vecConvertRel_extend_fun`).
* `choiceCover`: the frozen `Nondet.Task.choiceCover` holds, with `B := BI` for every successor.
* `sat_iff_dom`, `toModelDom`: an `equal` transition from Core on all of `Dom` to
  `modelChart (stepModel BI)`, on every `CfgRel`-respecting sentence (no choice independence).
* `toUnion`: `Nondet.toUnion`, now unconditional.
* `nanCfg`, `dom_nanCfg`, `not_domDet_nanCfg`, `nonvacuous`: `f32.const nan; f64.promote_f32` is
  a point of `Dom \ DomDet` (host-free), with two distinct Core successors, both matched.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Cover.choiceCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Cover.choiceCover

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Cover.sat_iff_dom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Cover.sat_iff_dom

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Cover.toModelDom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Cover.toModelDom

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Cover.nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Cover.nonvacuous
