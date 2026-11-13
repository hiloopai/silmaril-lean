module

public import Silmaril.Raw.SSA.Thesis.LambdaIter.Semantics.Kleisli.Model
public import Silmaril.SSA.Thesis.Categorical.Thms

/-!
# λiter: the Kleisli category of a lawful Elgot monad is a categorical model (thesis port)

Re-exports a Raw port of imbrem/thesis @ `69a8126` (CC0-1.0; `NOTICES/imbrem-thesis`),
`Isotope.LambdaIter.Semantics.Kleisli.Model` and its closure, adapted to this repository's toolchain.

Setting: an object-language type universe `τ` with type formers, subtyping and injective binary
formers, a set-valued type model (`Subtyping.Semantics.TypeModel.{u, v} τ`), instructions `Φ` with
effects `ε` (`⊥` = pure), and a monad `m : Type v → Type v` that is a lawful Elgot monad
(`Silmaril.Thesis.Elgot.LawfulElgotMonad m`) carrying a monadic instruction interpretation
(`Subtyping.Semantics.InstructionModel Φ τ ε m`).  The categorical model is the free Freyd
embedding `kleisliJ m : Type v ⥤ Kleisli (ofTypeMonad m)` with value category `Type v`, the type
model `Subtyping.Semantics.Categorical.ofTypeModel` and the instruction model
`Subtyping.Semantics.Categorical.ofInstructionModel`.

* `kleisli_typingCoherent` (`Semantics.instTypingCoherentKleisli`): the categorical denotation of
  an exact typing derivation in this model depends only on the term and its type.
* `kleisli_lawfulModel` (`Semantics.instLawfulModelKleisli`): the structural, sequencing,
  iteration and uniformity axioms of the λiter equational theory (`pureEff := ⊥`) hold in it.
* `uniqueHomKleisli` / `kleisli_initial`: instantiating
  `Silmaril.Thesis.LambdaIter.Categorical.uniqueHomCategorical` (from
  `Silmaril.SSA.Thesis.Categorical.Thms`), for every signature `S : Sig.{v}` (with `⊥ := S.pureEff`)
  there is exactly one morphism of λiter algebras from the quotiented syntax `Syn S` into the
  algebra `Alg.ofCategorical (kleisliJ m) ofTypeModel` of the Kleisli model; it sends the class
  of a derivation to its categorical denotation (`Categorical.toHom_ofCategorical_mk`).
* `uniqueHomKleisliPart` / `kleisli_initial_part`: the same at the concrete lawful Elgot monad
  `Part` (partial computations, `Silmaril.Raw.SSA.Thesis.Elgot.Basic`).

Hypotheses are exactly the instance arguments listed above; nothing is assumed beyond them.  The
model is the thesis' Kleisli model: the monadic instruction interpretation and the type model are
parameters, so these statements are about every such interpretation, not about one fixed
instruction set.
-/

@[expose] public section

namespace Silmaril.Thesis.LambdaIter.Semantics.KleisliModel

open _root_.CategoryTheory
open Silmaril.Thesis.LambdaIter.Subtyping.Semantics
open Silmaril.Thesis.LambdaIter.LocallyNameless
open Silmaril.Thesis.Elgot

universe u v w q r

section General

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ] [InjectiveFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
variable [InstructionModel Φ τ ε m]

/-- **Typing coherence of the Kleisli model.**  In the Kleisli category of a lawful Elgot monad,
the categorical denotation of an exact typing derivation depends only on the term and its type. -/
theorem kleisli_typingCoherent :
    @LocallyNameless.Categorical.TypingCoherent τ _ _ ν _ Φ _ (Type v)
      (Kleisli (ofTypeMonad m)) _ _ _ _ _ _ _ _ _ _ _ _
      (kleisliJ m) _ (Categorical.ofTypeModel (τ := τ))
      (Categorical.ofInstructionModel (ε := ε)) :=
  instTypingCoherentKleisli

/-- **The Kleisli model is lawful.**  The structural, sequencing and iteration axioms of λiter
(with `⊥` as the pure effect) and the uniformity rule hold in the Kleisli category of a lawful
Elgot monad. -/
theorem kleisli_lawfulModel :
    @LocallyNameless.Categorical.LawfulModel τ _ _ ν _ Φ _ ε _ (⊥ : ε)
      (Type v) (Kleisli (ofTypeMonad m)) _ _ _ _ _ _ _ _ _ _ _ _
      (kleisliJ m) _ (Categorical.ofTypeModel (τ := τ))
      (Categorical.ofInstructionModel (ε := ε)) :=
  instLawfulModelKleisli

end General

section Initiality

/-- The bottom effect of a signature is its distinguished pure effect. -/
@[reducible] def sigBot (S : Sig.{u}) : Bot S.Eff := ⟨S.pureEff⟩

attribute [local instance] sigBot

variable (S : Sig.{v}) [Subtyping S.Ty] [InjectiveFormers S.Ty] [TypeModel.{v, v} S.Ty]
variable (m : Type v → Type v) [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
variable [InstructionModel S.Instr S.Ty S.Eff m]

/-- **Initiality into the Kleisli model.**  For a signature `S` (pure effect `S.pureEff`) and a
lawful Elgot monad `m` with an interpretation of `S`'s instructions, there is exactly one
morphism of λiter algebras from the quotiented syntax `Syn S` into the algebra of the Kleisli
categorical model; this is `Categorical.uniqueHomCategorical` at `kleisliJ m`. -/
@[instance_reducible] noncomputable def uniqueHomKleisli :
    letI := Categorical.ofInstructionModel (τ := S.Ty) (Φ := S.Instr) (ε := S.Eff) (m := m)
    Unique (Syn.{v} S ⟶
      Alg.ofCategorical (kleisliJ m) (Categorical.ofTypeModel (τ := S.Ty))) :=
  letI := Categorical.ofInstructionModel (τ := S.Ty) (Φ := S.Instr) (ε := S.Eff) (m := m)
  LambdaIter.Categorical.uniqueHomCategorical (kleisliJ m)
    (Categorical.ofTypeModel (τ := S.Ty))

/-- Propositional form of `uniqueHomKleisli`: the morphism from the quotiented syntax into the
Kleisli model's algebra exists and is unique. -/
theorem kleisli_initial :
    letI := Categorical.ofInstructionModel (τ := S.Ty) (Φ := S.Instr) (ε := S.Eff) (m := m)
    Nonempty (Unique (Syn.{v} S ⟶
      Alg.ofCategorical (kleisliJ m) (Categorical.ofTypeModel (τ := S.Ty)))) :=
  ⟨uniqueHomKleisli S m⟩

/-- **Initiality at the partiality monad.**  `Part` is a lawful Elgot monad, so for every
signature with a partial-function interpretation of its instructions the quotiented syntax maps
uniquely into the Kleisli model of `Part`. -/
@[instance_reducible] noncomputable def uniqueHomKleisliPart [InstructionModel S.Instr S.Ty S.Eff Part.{v}] :
    letI := Categorical.ofInstructionModel (τ := S.Ty) (Φ := S.Instr) (ε := S.Eff) (m := Part.{v})
    Unique (Syn.{v} S ⟶
      Alg.ofCategorical (kleisliJ Part.{v}) (Categorical.ofTypeModel (τ := S.Ty))) :=
  uniqueHomKleisli S Part.{v}

/-- Propositional form of `uniqueHomKleisliPart`. -/
theorem kleisli_initial_part [InstructionModel S.Instr S.Ty S.Eff Part.{v}] :
    letI := Categorical.ofInstructionModel (τ := S.Ty) (Φ := S.Instr) (ε := S.Eff) (m := Part.{v})
    Nonempty (Unique (Syn.{v} S ⟶
      Alg.ofCategorical (kleisliJ Part.{v}) (Categorical.ofTypeModel (τ := S.Ty)))) :=
  ⟨uniqueHomKleisliPart S⟩

end Initiality

end Silmaril.Thesis.LambdaIter.Semantics.KleisliModel
