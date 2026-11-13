module

public import Silmaril.Wasm.SpecTec.Institution.Typing30.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Typing30

/-!
# Typing judgements of the wasm-3.0 script against Core 3.0 validation: results

Namespace `Silmaril.Wasm.SpecTec.Institution.Typing30`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.Typing30`; see `docs/projects/spectec/README.md`,
"fwdinst".

The model is `stepModel BI` (`Round4Int.BI`), as in `Cover.toModelDom`. The sentence map is
`TySen.toSen hn`, Core's reading is `TySen.Holds`, and the domain is `TySen.Dom`.

* `preserves`: on the domain, every judgement Core validates (`TyOk {}`, `Sub {}`, `RefOk`) is a
  fact of `stepModel BI`.
* `reflects`, `sat_iff`: for `Reftype_sub {}` and `Ref_ok` the satisfaction condition is an
  equivalence on the domain.
* `ok_coh`: a `Reftype_ok {}` fact gives coherence of the heap type only.
* `ok_not_reflects`, `refOk_nested`: `REF NULL D_out` is bounded, valid in `stepModel BI` and types
  `null` there, while Core rejects both, so `Reftype_ok` is not reflected, and `Ref_ok` is not
  reflected off the domain.
* `refOk_dom_of_config`: `refOk` judgements at the store of a valid `BoundedSel` configuration
  are in the domain at every bounded Core-valid type.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Typing30.sat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Typing30.sat_iff

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Typing30.preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Typing30.preserves

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Typing30.ok_not_reflects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Typing30.ok_not_reflects

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Typing30.refOk_nested' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Typing30.refOk_nested

/-- info: 'Silmaril.Wasm.SpecTec.Institution.Typing30.refOk_dom_of_config' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Typing30.refOk_dom_of_config
