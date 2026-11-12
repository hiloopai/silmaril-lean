module

public import Silmaril.Proofs.SSA.Isotope.Bridge.Equiv
public import Silmaril.Raw.SSA.Isotope.Theory.Models.LetIter

/-!
# Bridge between legacy and thesis let-iter: the two completeness theorems (proofs)

Legacy completeness (`Silmaril.Isotope.LetIter.LocallyNameless.Models.interpret_eq_iff`,
the propositional-typing form of `semantic_iff`) quantifies over the legacy equational
models of a free context; thesis completeness (`Silmaril.Thesis.LambdaIter.Syn.denote_eq_iff_eqv`)
quantifies over `Alg S` for a signature `S`, in the empty free context. Composing both with
the equivalence bridge `equiv_iff` (in the empty context, `ν = Empty`) shows that the two
notions of semantic validity coincide on closed typable terms, and transfers each
completeness statement to the other calculus' equational theory.

This uses *both* completeness theorems. It does not translate models: no functor between
the legacy model category and `Alg S` is constructed, so neither completeness theorem is
derived from the other alone, and no equivalence of model categories is claimed.
Restated in `Silmaril.SSA.Isotope.Bridge.Thms`.
-/

@[expose] public section

universe u

namespace Silmaril.Proofs.SSA.Isotope.Bridge

open Silmaril.Isotope.Bridge

local notation "LTm" => Silmaril.Isotope.LetIter.LocallyNameless.Tm

variable {τ Φ ε : Type u}
variable [Silmaril.TypeFormers τ] [Silmaril.Thesis.LambdaIter.TypeFormers τ]
variable [Silmaril.HasTy Φ τ] [Silmaril.Thesis.LambdaIter.HasTy Φ τ]
variable [Silmaril.HasEff Φ ε] [Silmaril.Thesis.LambdaIter.HasEff Φ ε]

/-- **Semantic validity agrees.** For closed (empty free context) typable terms, equality of
interpretations in every legacy equational model is equivalent to equality of denotations
in every thesis algebra of `thesisSig τ Φ ε pe`. -/
theorem semantic_iff_semantic (hT : TypeCompat τ) (hI : InstrCompat Φ τ)
    (hE : EffCompat Φ ε) (pe : ε) {n : Nat} {β : Silmaril.Isotope.BoundCtx τ n}
    {a b : LTm Empty Φ n} {A : τ}
    (ha : Silmaril.Isotope.LetIter.LocallyNameless.HasType Φ
      (Silmaril.Isotope.Ctx.nil : Silmaril.Isotope.Ctx Empty τ) β a A)
    (hb : Silmaril.Isotope.LetIter.LocallyNameless.HasType Φ
      (Silmaril.Isotope.Ctx.nil : Silmaril.Isotope.Ctx Empty τ) β b A)
    (da : Silmaril.Thesis.LambdaIter.LocallyNameless.HasType (thesisSig τ Φ ε pe).Instr
      Silmaril.Thesis.LambdaIter.Ctx.nil (BoundCtx.toThesis β) (toThesis a) A)
    (db : Silmaril.Thesis.LambdaIter.LocallyNameless.HasType (thesisSig τ Φ ε pe).Instr
      Silmaril.Thesis.LambdaIter.Ctx.nil (BoundCtx.toThesis β) (toThesis b) A) :
    (∀ M : Silmaril.Isotope.LetIter.LocallyNameless.Models.EquationalModels (Φ := Φ) pe
        (Silmaril.Isotope.Ctx.nil : Silmaril.Isotope.Ctx Empty τ),
      Silmaril.Isotope.LetIter.LocallyNameless.Models.interpret M ha =
        Silmaril.Isotope.LetIter.LocallyNameless.Models.interpret M hb) ↔
      ∀ X : Silmaril.Thesis.LambdaIter.Alg.{u, u} (thesisSig τ Φ ε pe),
        X.denote da = X.denote db :=
  (Silmaril.Isotope.LetIter.LocallyNameless.Models.interpret_eq_iff ha hb).symm.trans
    ((equiv_iff hT hI hE pe).trans (Silmaril.Thesis.LambdaIter.Syn.denote_eq_iff_eqv da db).symm)

/-- Legacy semantic validity yields a thesis equation (legacy completeness, transported). -/
theorem eqv_of_legacy_semantic (hT : TypeCompat τ) (hI : InstrCompat Φ τ)
    (hE : EffCompat Φ ε) (pe : ε) {n : Nat} {β : Silmaril.Isotope.BoundCtx τ n}
    {a b : LTm Empty Φ n} {A : τ}
    (ha : Silmaril.Isotope.LetIter.LocallyNameless.HasType Φ
      (Silmaril.Isotope.Ctx.nil : Silmaril.Isotope.Ctx Empty τ) β a A)
    (hb : Silmaril.Isotope.LetIter.LocallyNameless.HasType Φ
      (Silmaril.Isotope.Ctx.nil : Silmaril.Isotope.Ctx Empty τ) β b A)
    (H : ∀ M : Silmaril.Isotope.LetIter.LocallyNameless.Models.EquationalModels (Φ := Φ) pe
        (Silmaril.Isotope.Ctx.nil : Silmaril.Isotope.Ctx Empty τ),
      Silmaril.Isotope.LetIter.LocallyNameless.Models.interpret M ha =
        Silmaril.Isotope.LetIter.LocallyNameless.Models.interpret M hb) :
    Silmaril.Thesis.LambdaIter.LocallyNameless.Eqv (Φ := (thesisSig τ Φ ε pe).Instr) pe
      Silmaril.Thesis.LambdaIter.Ctx.nil (BoundCtx.toThesis β) (toThesis a) (toThesis b) A :=
  (equiv_iff hT hI hE pe).1
    ((Silmaril.Isotope.LetIter.LocallyNameless.Models.interpret_eq_iff ha hb).2 H)

/-- Thesis semantic validity yields a legacy equation (thesis completeness, transported). -/
theorem equiv_of_thesis_semantic (hT : TypeCompat τ) (hI : InstrCompat Φ τ)
    (hE : EffCompat Φ ε) (pe : ε) {n : Nat} {β : Silmaril.Isotope.BoundCtx τ n}
    {a b : LTm Empty Φ n} {A : τ}
    (da : Silmaril.Thesis.LambdaIter.LocallyNameless.HasType (thesisSig τ Φ ε pe).Instr
      Silmaril.Thesis.LambdaIter.Ctx.nil (BoundCtx.toThesis β) (toThesis a) A)
    (db : Silmaril.Thesis.LambdaIter.LocallyNameless.HasType (thesisSig τ Φ ε pe).Instr
      Silmaril.Thesis.LambdaIter.Ctx.nil (BoundCtx.toThesis β) (toThesis b) A)
    (H : ∀ X : Silmaril.Thesis.LambdaIter.Alg.{u, u} (thesisSig τ Φ ε pe),
        X.denote da = X.denote db) :
    Silmaril.Isotope.LetIter.LocallyNameless.Equiv pe
      (Silmaril.Isotope.Ctx.nil : Silmaril.Isotope.Ctx Empty τ) β a b A :=
  (equiv_iff hT hI hE pe).2 (Silmaril.Thesis.LambdaIter.Syn.eqv_of_denote_eq da db H)

end Silmaril.Proofs.SSA.Isotope.Bridge
