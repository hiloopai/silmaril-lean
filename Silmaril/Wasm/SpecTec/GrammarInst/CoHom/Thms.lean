module

public import Silmaril.Wasm.SpecTec.GrammarInst.Defs
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.CoHom
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.CoHomWhole

/-!
# The full comorphism of grammar institutions: results

Proofs in `Silmaril.Proofs.Wasm.SpecTec.GrammarInst.CoHom`; see `docs/projects/spectec/README.md`
("Pass 3, grammar-comorph").

* `AttrHom.injective`: every attribute-algebra homomorphism is injective.
* `fullCoHom f : Inst.CoHom (inst A D) (instIn B f.toFun D)`: every sentence, productions
  included, translated by `mapSen f`; models by preimage. Satisfaction condition
  `holds_mapSen_iff` (on models supported on the image of `f`).
* `fullCoHom_modelExpansive`, `fullCoHom_entails_iff`, `fullCoHom_prodAxioms_iff`: borrowing.
* `fullCoHomSurj f hs : Inst.CoHom (inst A D) (inst B D)` for surjective `f`, and
  `surjective_of_prod_satisfaction`: surjectivity is necessary for the preimage translation to
  satisfy the condition in all of `inst B D`.
* `lebCoHom D = fullCoHom lebHom D`; `lebHom_not_surjective`.
* `wholeCoHom f D`: `fullCoHom` followed by `Institution.grammarInclusion`, into whole SpecTec
  specifications; `grammarInclusion_modelExpansive`, `wholeCoHom_entails_iff`; `lebWholeCoHom`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec

/-- info: 'Silmaril.Wasm.SpecTec.GrammarInst.fullCoHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms GrammarInst.fullCoHom

/-- info: 'Silmaril.Wasm.SpecTec.GrammarInst.fullCoHom_entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms GrammarInst.fullCoHom_entails_iff

/--
info: 'Silmaril.Wasm.SpecTec.GrammarInst.surjective_of_prod_satisfaction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms GrammarInst.surjective_of_prod_satisfaction

/-- info: 'Silmaril.Wasm.SpecTec.GrammarInst.lebCoHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms GrammarInst.lebCoHom

/-- info: 'Silmaril.Wasm.SpecTec.GrammarInst.wholeCoHom_entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms GrammarInst.wholeCoHom_entails_iff
