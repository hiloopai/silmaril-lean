module

public import Silmaril.Wasm.SpecTec.Institution.Amalg.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.Amalg

/-!
# Whole SpecTec scripts with a shared evaluator: results

Proofs in `Silmaril.Proofs.Wasm.SpecTec.Institution.Amalg`; see `docs/projects/spectec/README.md`.

* `ainst alts`: the amalgamated institution of whole scripts (relations and grammars with one
  evaluator); `asatisfaction` is its satisfaction condition.
* `asatTh_wholeTheory_iff`: a model of the whole theory at `env` is a model of the relational
  theory and of the grammar theory `GrammarInst.scriptAxioms env`, both at `env`.
* `canonW_sat`, `canonW_least_rel`, `canonW_least_gram`: `DDerivesB env noElse` with the least
  model of `gramOf env` is the least model with evaluator `env`.
* `entailsAt_fact_iff`, `entailsAt_derives_iff`: relation facts and grammar derivations
  (`gramRelSup`) as consequences of one theory.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec

/-- info: 'Silmaril.Wasm.SpecTec.Institution.ainst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Institution.ainst

/-- info: 'Silmaril.Wasm.SpecTec.Institution.entailsAt_derives_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Institution.entailsAt_derives_iff

/-- info: 'Silmaril.Wasm.SpecTec.Institution.entailsAt_fact_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Institution.entailsAt_fact_iff
