module

public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.Equiv
public import Silmaril.SSA.Thesis.Thms

/-!
# Bridge between the legacy and thesis copies of let-iter (definitions)

Two Raw copies of the same locally nameless calculus λiter live in Silmaril:

* legacy: `Silmaril.Isotope.LetIter.LocallyNameless` (typing classes from
  `Silmaril.SSA.Isotope.Types.Defs`, contexts `Silmaril.Isotope.Ctx` / `Silmaril.Isotope.BoundCtx`);
* thesis: `Silmaril.Thesis.LambdaIter.LocallyNameless` (typing classes from
  `Silmaril.Thesis.LambdaIter.{Ty,Signature}`, contexts `Silmaril.Thesis.LambdaIter.Ctx` /
  `Silmaril.Thesis.LambdaIter.LocallyNameless.BoundCtx`).

This file defines the constructor-for-constructor translations of terms and contexts in
both directions, and the three compatibility hypotheses relating the two families of
type-former / instruction-typing / effect classes on the same carriers. Proofs are in
`Silmaril.Proofs.SSA.Isotope.Bridge.*`; statements are collected in
`Silmaril.SSA.Isotope.Bridge.Thms`.
-/

@[expose] public section

universe u v w r

namespace Silmaril.Isotope.Bridge

/-! ## Terms -/

/-- Legacy raw terms to thesis raw terms, constructor for constructor. -/
def toThesis {ν : Type w} {Φ : Type v} :
    {n : Nat} → Silmaril.Isotope.LetIter.LocallyNameless.Tm ν Φ n →
      Silmaril.Thesis.LambdaIter.LocallyNameless.Tm ν Φ n
  | _, .fv x => .fv x
  | _, .bv i => .bv i
  | _, .op f a => .op f (toThesis a)
  | _, .let₁ a b => .let₁ (toThesis a) (toThesis b)
  | _, .unit => .unit
  | _, .pair a b => .pair (toThesis a) (toThesis b)
  | _, .let₂ a b => .let₂ (toThesis a) (toThesis b)
  | _, .inl a => .inl (toThesis a)
  | _, .inr a => .inr (toThesis a)
  | _, .case e l r => .case (toThesis e) (toThesis l) (toThesis r)
  | _, .abort a => .abort (toThesis a)
  | _, .iter a b => .iter (toThesis a) (toThesis b)

/-- Thesis raw terms to legacy raw terms, constructor for constructor. -/
def ofThesis {ν : Type w} {Φ : Type v} :
    {n : Nat} → Silmaril.Thesis.LambdaIter.LocallyNameless.Tm ν Φ n →
      Silmaril.Isotope.LetIter.LocallyNameless.Tm ν Φ n
  | _, .fv x => .fv x
  | _, .bv i => .bv i
  | _, .op f a => .op f (ofThesis a)
  | _, .let₁ a b => .let₁ (ofThesis a) (ofThesis b)
  | _, .unit => .unit
  | _, .pair a b => .pair (ofThesis a) (ofThesis b)
  | _, .let₂ a b => .let₂ (ofThesis a) (ofThesis b)
  | _, .inl a => .inl (ofThesis a)
  | _, .inr a => .inr (ofThesis a)
  | _, .case e l r => .case (ofThesis e) (ofThesis l) (ofThesis r)
  | _, .abort a => .abort (ofThesis a)
  | _, .iter a b => .iter (ofThesis a) (ofThesis b)

/-! ## Contexts -/

namespace Ctx

/-- Legacy free contexts to thesis free contexts. -/
def toThesis {ν : Type w} {τ : Type u} :
    Silmaril.Isotope.Ctx ν τ → Silmaril.Thesis.LambdaIter.Ctx ν τ
  | .nil => .nil
  | .snoc Γ x A => .snoc (toThesis Γ) x A

/-- Thesis free contexts to legacy free contexts. -/
def ofThesis {ν : Type w} {τ : Type u} :
    Silmaril.Thesis.LambdaIter.Ctx ν τ → Silmaril.Isotope.Ctx ν τ
  | .nil => .nil
  | .snoc Γ x A => .snoc (ofThesis Γ) x A

end Ctx

namespace BoundCtx

/-- Legacy bound contexts to thesis bound contexts. -/
def toThesis {τ : Type u} :
    {n : Nat} → Silmaril.Isotope.BoundCtx τ n →
      Silmaril.Thesis.LambdaIter.LocallyNameless.BoundCtx τ n
  | _, .nil => .nil
  | _, .snoc β A => .snoc (toThesis β) A

/-- Thesis bound contexts to legacy bound contexts. -/
def ofThesis {τ : Type u} :
    {n : Nat} → Silmaril.Thesis.LambdaIter.LocallyNameless.BoundCtx τ n →
      Silmaril.Isotope.BoundCtx τ n
  | _, .nil => .nil
  | _, .snoc β A => .snoc (ofThesis β) A

end BoundCtx

/-! ## Compatibility of the two class families

Both developments state typing against their own copies of the type-former, instruction
typing and effect classes. On a common carrier we require exactly that the operations
agree; nothing else (no laws, no decidability) is assumed. -/

/-- The legacy type formers (`Silmaril.TypeFormers`) and the thesis type formers
(`Silmaril.Thesis.LambdaIter.TypeFormers`) on `τ` agree. -/
structure TypeCompat (τ : Type u) [Silmaril.TypeFormers τ]
    [Silmaril.Thesis.LambdaIter.TypeFormers τ] : Prop where
  product : ∀ A B : τ, Silmaril.product A B = Silmaril.Thesis.LambdaIter.tensor A B
  unit : (Silmaril.unit : τ) = Silmaril.Thesis.LambdaIter.unit
  coprod : ∀ A B : τ, Silmaril.coprod A B = Silmaril.Thesis.LambdaIter.coprod A B
  empty : (Silmaril.empty : τ) = Silmaril.Thesis.LambdaIter.empty

/-- The legacy and thesis instruction source/target assignments agree. -/
structure InstrCompat (Φ : Type v) (τ : Type u) [Silmaril.HasTy Φ τ]
    [Silmaril.Thesis.LambdaIter.HasTy Φ τ] : Prop where
  src : ∀ f : Φ, (Silmaril.instrSrc f : τ) = Silmaril.Thesis.LambdaIter.instrSrc f
  trg : ∀ f : Φ, (Silmaril.instrTrg f : τ) = Silmaril.Thesis.LambdaIter.instrTrg f

/-- The legacy and thesis instruction effect assignments agree. -/
structure EffCompat (Φ : Type v) (ε : Type r) [Silmaril.HasEff Φ ε]
    [Silmaril.Thesis.LambdaIter.HasEff Φ ε] : Prop where
  eff : ∀ f : Φ, (Silmaril.instrEff f : ε) = Silmaril.Thesis.LambdaIter.instrEff f

/-! ### Canonical thesis instances induced by legacy ones -/

/-- Thesis type formers read off legacy ones. -/
abbrev thesisTypeFormers (τ : Type u) [Silmaril.TypeFormers τ] :
    Silmaril.Thesis.LambdaIter.TypeFormers τ where
  tensor := Silmaril.product
  unit := Silmaril.unit
  coprod := Silmaril.coprod
  empty := Silmaril.empty

/-- Thesis instruction typing read off legacy instruction typing. -/
abbrev thesisHasTy (Φ : Type v) (τ : Type u) [Silmaril.HasTy Φ τ] :
    Silmaril.Thesis.LambdaIter.HasTy Φ τ where
  src := Silmaril.instrSrc
  trg := Silmaril.instrTrg

/-- Thesis effects read off legacy effects. -/
abbrev thesisHasEff (Φ : Type v) (ε : Type r) [Silmaril.HasEff Φ ε] :
    Silmaril.Thesis.LambdaIter.HasEff Φ ε where
  eff := Silmaril.instrEff

theorem TypeCompat.canonical (τ : Type u) [Silmaril.TypeFormers τ] :
    @TypeCompat τ _ (thesisTypeFormers τ) :=
  @TypeCompat.mk τ _ (thesisTypeFormers τ) (fun _ _ => rfl) rfl (fun _ _ => rfl) rfl

theorem InstrCompat.canonical (Φ : Type v) (τ : Type u) [Silmaril.HasTy Φ τ] :
    @InstrCompat Φ τ _ (thesisHasTy Φ τ) :=
  @InstrCompat.mk Φ τ _ (thesisHasTy Φ τ) (fun _ => rfl) (fun _ => rfl)

theorem EffCompat.canonical (Φ : Type v) (ε : Type r) [Silmaril.HasEff Φ ε] :
    @EffCompat Φ ε _ (thesisHasEff Φ ε) :=
  @EffCompat.mk Φ ε _ (thesisHasEff Φ ε) (fun _ => rfl)

/-! ## The thesis signature on common carriers -/

/-- The thesis signature (`Silmaril.Thesis.LambdaIter.Sig`) whose type universe, instructions
and effects are the given carriers with their thesis-class instances and the chosen pure
effect. This is how a legacy instance of λiter is read as a thesis signature. -/
abbrev thesisSig (τ Φ ε : Type u) [Silmaril.Thesis.LambdaIter.TypeFormers τ]
    [Silmaril.Thesis.LambdaIter.HasTy Φ τ] [Silmaril.Thesis.LambdaIter.HasEff Φ ε] (pe : ε) :
    Silmaril.Thesis.LambdaIter.Sig.{u} where
  Ty := τ
  formers := inferInstance
  Instr := Φ
  Eff := ε
  pureEff := pe
  hasTy := inferInstance
  hasEff := inferInstance

end Silmaril.Isotope.Bridge
