module

public import Silmaril.Raw.SSA.Isotope.LetCase.LocallyNameless.Typing

/-!
# Raw equations for LetCase

This presentation is generated within this fragment's own grammar. Its laws
follow the locally nameless lambda calculus presentation in imbrem/thesis
(commit 3691b30), with products and unit retained in let-seq. In particular,
pure-let beta is guarded by syntactic purity. No embedding in a larger
calculus is used to define the relation.

`RawEquiv` is deliberately the type-erased closure. Unlike `Equiv`, it permits
ill-typed intermediate terms: unrestricted unit eta and pure beta identify
all pure terms, and with coproducts this collapses all raw terms. Accordingly,
typed equations imply raw equations, but there is no reflection theorem.
For reasoning about the typed calculus use `Equiv`; arbitrary theories over
untyped syntax are supplied separately by the generic theory framework.
-/

@[expose] public section
set_option autoImplicit true

namespace Silmaril.Isotope.LetCase.LocallyNameless

variable {ν : Type u} {Φ : Type v} {ε : Type w} [HasEff Φ ε]

/-- Product, coproduct, unit, empty, and pure-let beta/eta laws. -/
inductive StructuralAxiom (pureEff : ε) :
    {n : Nat} → Tm ν Φ n → Tm ν Φ n → Prop where
  | letBeta (hp : Pure pureEff a) :
      StructuralAxiom pureEff (.let₁ a b)
        (Tm.instantiate b a)
  | letEta (a : Tm ν Φ n) : StructuralAxiom pureEff (.let₁ a (.bv 0)) a
  | unitEta (a : Tm ν Φ n) : StructuralAxiom pureEff (.let₁ a .unit) a
  | pairBeta (a b : Tm ν Φ n) (c : Tm ν Φ (n + 2)) :
      StructuralAxiom pureEff (.let₂ (.pair a b) c)
        (.let₁ a (.let₁ (Tm.lift b) c))
  | pairEta (a : Tm ν Φ n) :
      StructuralAxiom pureEff (.let₂ a (.pair (.bv 1) (.bv 0))) a
  | caseBetaL (e : Tm ν Φ n) (l r : Tm ν Φ (n + 1)) :
      StructuralAxiom pureEff (.case (.inl e) l r) (.let₁ e l)
  | caseBetaR (e : Tm ν Φ n) (l r : Tm ν Φ (n + 1)) :
      StructuralAxiom pureEff (.case (.inr e) l r) (.let₁ e r)
  | caseEta (e : Tm ν Φ n) :
      StructuralAxiom pureEff (.case e (.inl (.bv 0)) (.inr (.bv 0))) e
  | emptyInitial (a : Tm ν Φ n) (b c : Tm ν Φ (n + 1)) :
      StructuralAxiom pureEff (.let₁ (.abort a) b) (.let₁ (.abort a) c)

/-- Sequencing and commuting conversions. -/
inductive SequencingAxiom (pureEff : ε) :
    {n : Nat} → Tm ν Φ n → Tm ν Φ n → Prop where
  | bindOp (a : Tm ν Φ n) (c : Tm ν Φ (n + 1)) :
      SequencingAxiom pureEff (.let₁ (.op f a) c)
        (.let₁ a (.let₁ (.op f (.bv 0))
          (Tm.underBinder c)))
  | bindLet (a : Tm ν Φ n) (b c : Tm ν Φ (n + 1)) :
      SequencingAxiom pureEff (.let₁ (.let₁ a b) c)
        (.let₁ a (.let₁ b (Tm.underBinder c)))
  | bindLetPair (e : Tm ν Φ n) (c : Tm ν Φ (n + 2)) (d : Tm ν Φ (n + 1)) :
      SequencingAxiom pureEff (.let₁ (.let₂ e c) d)
        (.let₂ e (.let₁ c (Tm.underBinder
          (Tm.underBinder d))))
  | bindLetCase (e : Tm ν Φ n) (l r d : Tm ν Φ (n + 1)) :
      SequencingAxiom pureEff (.let₁ (.case e l r) d)
        (.case e
          (.let₁ l (Tm.underBinder d))
          (.let₁ r (Tm.underBinder d)))
  | bindPair (a : Tm ν Φ n) (c : Tm ν Φ (n + 2)) :
      SequencingAxiom pureEff (.let₂ a c)
        (.let₁ a (.let₂ (.bv 0)
          (Tm.underTwoBinders c)))
  | bindCase (e : Tm ν Φ n) (l r : Tm ν Φ (n + 1)) :
      SequencingAxiom pureEff (.case e l r)
        (.let₁ e (.case (.bv 0)
          (Tm.underBinder l)
          (Tm.underBinder r)))

/-- The structural and sequencing schemes of this fragment. -/
inductive CoreAxiom (pureEff : ε) :
    {n : Nat} → Tm ν Φ n → Tm ν Φ n → Prop where
  | structural : StructuralAxiom pureEff a b → CoreAxiom pureEff a b
  | sequencing : SequencingAxiom pureEff a b → CoreAxiom pureEff a b

/-- The least compatible equivalence relation containing the raw schemes. -/
inductive RawEquiv (pureEff : ε) : {n : Nat} → Tm ν Φ n → Tm ν Φ n → Prop where
  | refl (a : Tm ν Φ n) : RawEquiv pureEff a a
  | symm : RawEquiv pureEff a b → RawEquiv pureEff b a
  | trans : RawEquiv pureEff a b → RawEquiv pureEff b c → RawEquiv pureEff a c
  | ax : CoreAxiom pureEff a b → RawEquiv pureEff a b
  | op : RawEquiv pureEff a a' → RawEquiv pureEff (.op f a) (.op f a')
  | let₁ : RawEquiv pureEff a a' → RawEquiv pureEff b b' →
      RawEquiv pureEff (.let₁ a b) (.let₁ a' b')
  | pair : RawEquiv pureEff a a' → RawEquiv pureEff b b' →
      RawEquiv pureEff (.pair a b) (.pair a' b')
  | let₂ : RawEquiv pureEff a a' → RawEquiv pureEff b b' →
      RawEquiv pureEff (.let₂ a b) (.let₂ a' b')
  | inl : RawEquiv pureEff a a' → RawEquiv pureEff (.inl a) (.inl a')
  | inr : RawEquiv pureEff a a' → RawEquiv pureEff (.inr a) (.inr a')
  | case : RawEquiv pureEff e e' → RawEquiv pureEff l l' → RawEquiv pureEff r r' →
      RawEquiv pureEff (.case e l r) (.case e' l' r')
  | abort : RawEquiv pureEff a a' → RawEquiv pureEff (.abort a) (.abort a')

end Silmaril.Isotope.LetCase.LocallyNameless
