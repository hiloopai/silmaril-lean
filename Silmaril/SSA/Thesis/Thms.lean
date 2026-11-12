module

public import Silmaril.Raw.SSA.Thesis.LambdaIter.Models.Initial
public import Silmaril.Raw.SSA.Thesis.LambdaCase.Models.Initial

/-! # Initiality of the quotiented lambda-iter and lambda-case syntax (thesis copy)

Raw copy of the import closures of `Isotope.LambdaIter.Models.Initial` and
`Isotope.LambdaCase.Models.Initial` from the CC0 thesis formalization
`imbrem/thesis` at 69a8126f2d3eb6d32050e0bd9511251b33dbcea7, under the namespace
`Silmaril.Thesis` (source namespace `Isotope`); see `NOTICES/imbrem-thesis`.

What is proved, for a fixed signature `S : Sig.{u}`:

* lambda-iter (`Silmaril.Thesis.LambdaIter.Syn`): `Syn.toHom` (existence),
  `Syn.hom_eq_toHom` (uniqueness), `Syn.uniqueHom : Unique (Syn S ⟶ X)`,
  `Syn.isInitial : IsInitial (Syn S)` in `Alg.{u, u} S`, `Syn.hasInitial`;
  `Syn.eqv_of_denote_eq` (equational completeness with respect to algebras) and
  `Syn.denote_eq_iff_eqv` (soundness and completeness together).
* lambda-case (`Silmaril.Thesis.LambdaCase.Syn`): `Syn.toHom`, `Syn.hom_eq_toHom`,
  `Syn.uniqueHom`, `Syn.isInitial`; `Syn.equiv_of_denote_eq` and
  `Syn.denote_eq_iff_equiv`.

Honest boundary.  A "model" is an object of `Alg S`, the category of algebras
of the equational presentation; it is not a Freyd or Elgot category.  These
are initiality in the category of algebras and completeness with respect to
algebras only; they may not be read as statements about "all models" in the
informal sense, nor as Freyd, Elgot or monadic semantics.  Initiality into
strong Elgot Freyd models and the non-vacuity examples for lambda-iter are in
`Silmaril.SSA.Thesis.Categorical.Thms`; the source files `Models/Monadic` and
`Semantics/Kleisli` were not ported.  Universes: `Syn S : Alg.{u, u} S`.
-/
