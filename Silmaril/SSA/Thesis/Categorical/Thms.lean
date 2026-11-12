module

public import Silmaril.Raw.SSA.Thesis.LambdaIter.Models.Categorical.Initial
public import Silmaril.Raw.SSA.Thesis.LambdaIter.Models.Examples
public import Silmaril.Raw.SSA.Thesis.LambdaIter.Models.Categorical

/-!
# λiter: from strong Elgot Freyd categories to algebras, and initiality there (thesis port)

Re-exports a Raw port of imbrem/thesis @ `69a8126` (CC0-1.0; `NOTICES/imbrem-thesis`).

* `Silmaril.Thesis.LambdaIter.Alg.ofCategorical J M` — every strong Elgot Freyd category
  `J : V ⥤ C` (cartesian `V`, symmetric premonoidal `C`, distributive, with Elgot iteration),
  with a type model `M` and an instruction model, **satisfying the two coherence classes**
  `LocallyNameless.Categorical.TypingCoherent J M` and `LocallyNameless.Categorical.LawfulModel J M`,
  is an algebra of the equational presentation (`Alg S`).
* `Silmaril.Thesis.LambdaIter.Categorical.uniqueHomCategorical` — **initiality into Freyd models**:
  there is exactly one algebra morphism from the quotiented syntax `Syn S` into
  `Alg.ofCategorical J M`, and (`toHom_ofCategorical_mk`) it sends the class of a derivation to
  its categorical denotation.
* Non-vacuity of `Alg S` (`Models/Examples`): `Alg.const_not_terminal`, `Alg.constHom_ne_id`,
  `Alg.powReindex_ne_id`.

Boundary (as in the source): the two coherence classes are hypotheses; this port contains no
instance of them (the thesis instantiates them at the Kleisli category of a lawful Elgot monad in
`Semantics/Kleisli`, not ported here). λcase, λseq and λSSA have no categorical initiality here.
-/
