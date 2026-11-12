# imbrem/thesis

The Raw modules under `Silmaril/Raw/SSA/Thesis/` are ports of the Lean formalisation in
[imbrem/thesis](https://github.com/imbrem/thesis) by Jad Ghalayini, at commit
`69a8126f2d3eb6d32050e0bd9511251b33dbcea7`, subdirectory `formalization/thesis` (source
namespace `Isotope`, here `Silmaril.Thesis`). The thesis repository is dedicated to the public
domain under CC0 1.0 Universal, reproduced in `LICENSE` (SHA-256
`a2010f343487d3f7618affe54f789f5487602331c0a8d03f49e9a7c547cf0499`, the repository's `LICENSE`).

The port moved the modules to the toolchain of this repository: module paths and code
namespaces changed (`Isotope.` to `Silmaril.Thesis.`; docstrings keep the source names), the
module system was adopted, deprecated Mathlib names and imports were updated, two private
helpers used by public definitions became public as `Tm.upAux` and `Tm.upSubAux`, and proofs
were repaired where the newer Mathlib required it. Each file reproduces the source's
`autoImplicit` setting as a per-file option.

| Source file (`formalization/thesis/…`) | Module |
| --- | --- |
| `Isotope/Elgot/Basic.lean` | `Silmaril.Raw.SSA.Thesis.Elgot.Basic` |
| `Isotope/LambdaCase/Equiv.lean` | `Silmaril.Raw.SSA.Thesis.LambdaCase.Equiv` |
| `Isotope/LambdaCase/Metatheory.lean` | `Silmaril.Raw.SSA.Thesis.LambdaCase.Metatheory` |
| `Isotope/LambdaCase/Models/Alg.lean` | `Silmaril.Raw.SSA.Thesis.LambdaCase.Models.Alg` |
| `Isotope/LambdaCase/Models/Initial.lean` | `Silmaril.Raw.SSA.Thesis.LambdaCase.Models.Initial` |
| `Isotope/LambdaCase/Models/Limits.lean` | `Silmaril.Raw.SSA.Thesis.LambdaCase.Models.Limits` |
| `Isotope/LambdaCase/Models/Setoid.lean` | `Silmaril.Raw.SSA.Thesis.LambdaCase.Models.Setoid` |
| `Isotope/LambdaCase/Models/Syntax.lean` | `Silmaril.Raw.SSA.Thesis.LambdaCase.Models.Syntax` |
| `Isotope/LambdaCase/Syntax.lean` | `Silmaril.Raw.SSA.Thesis.LambdaCase.Syntax` |
| `Isotope/LambdaCase/Typing.lean` | `Silmaril.Raw.SSA.Thesis.LambdaCase.Typing` |
| `Isotope/LambdaCase/TypingSubst.lean` | `Silmaril.Raw.SSA.Thesis.LambdaCase.TypingSubst` |
| `Isotope/LambdaIter/Context.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Context` |
| `Isotope/LambdaIter/Context/Derivation.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Context.Derivation` |
| `Isotope/LambdaIter/Context/Shadowing.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Context.Shadowing` |
| `Isotope/LambdaIter/Equiv.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Equiv` |
| `Isotope/LambdaIter/LocallyNameless/Context.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.LocallyNameless.Context` |
| `Isotope/LambdaIter/LocallyNameless/Syntax.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.LocallyNameless.Syntax` |
| `Isotope/LambdaIter/Metatheory.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Metatheory` |
| `Isotope/LambdaIter/Metatheory/EquivSubst.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Metatheory.EquivSubst` |
| `Isotope/LambdaIter/Metatheory/Syntax.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Metatheory.Syntax` |
| `Isotope/LambdaIter/Models/Alg.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Models.Alg` |
| `Isotope/LambdaIter/Models/Categorical.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Models.Categorical` |
| `Isotope/LambdaIter/Models/Categorical/Alg.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Models.Categorical.Alg` |
| `Isotope/LambdaIter/Models/Categorical/Denotation.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Models.Categorical.Denotation` |
| `Isotope/LambdaIter/Models/Categorical/Initial.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Models.Categorical.Initial` |
| `Isotope/LambdaIter/Models/Examples.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Models.Examples` |
| `Isotope/LambdaIter/Models/Initial.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Models.Initial` |
| `Isotope/LambdaIter/Models/Limits.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Models.Limits` |
| `Isotope/LambdaIter/Models/Setoid.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Models.Setoid` |
| `Isotope/LambdaIter/Models/Syntax.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Models.Syntax` |
| `Isotope/LambdaIter/Named/Alpha.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Named.Alpha` |
| `Isotope/LambdaIter/Named/Defs.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Named.Defs` |
| `Isotope/LambdaIter/Named/Subst.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Named.Subst` |
| `Isotope/LambdaIter/Semantics/Categorical.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Semantics.Categorical` |
| `Isotope/LambdaIter/Semantics/Denotation.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Semantics.Denotation` |
| `Isotope/LambdaIter/Semantics/Soundness.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Semantics.Soundness` |
| `Isotope/LambdaIter/Signature.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Signature` |
| `Isotope/LambdaIter/Signature/Category.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Signature.Category` |
| `Isotope/LambdaIter/Subtyping.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Subtyping` |
| `Isotope/LambdaIter/Subtyping/LocallyNameless/Typing.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Subtyping.LocallyNameless.Typing` |
| `Isotope/LambdaIter/Subtyping/Semantics/Categorical.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Subtyping.Semantics.Categorical` |
| `Isotope/LambdaIter/Subtyping/Semantics/Denotation.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Subtyping.Semantics.Denotation` |
| `Isotope/LambdaIter/Subtyping/Semantics/Instruction.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Subtyping.Semantics.Instruction` |
| `Isotope/LambdaIter/Subtyping/Semantics/IterationDiagrams.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Subtyping.Semantics.IterationDiagrams` |
| `Isotope/LambdaIter/Subtyping/Semantics/Model.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Subtyping.Semantics.Model` |
| `Isotope/LambdaIter/Ty.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Ty` |
| `Isotope/LambdaIter/Typing.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Typing` |
| `Isotope/LambdaIter/Weakening.lean` | `Silmaril.Raw.SSA.Thesis.LambdaIter.Weakening` |
