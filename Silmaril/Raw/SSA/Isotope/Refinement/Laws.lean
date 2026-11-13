module

public import Silmaril.Raw.SSA.Isotope.Refinement.Typing
public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.TheorySubstitution

/-!
# Primitive laws of the written quantitative refinement calculus

The binding and structural equations, directional reduction laws, and
conditional uniformity rule are separated from closure under derivation.
All three fragments share this presentation; sum and iteration rules require
the corresponding grammatical capability.

The paper's beta rule is read with the quantity bound on the context typing
the substituted expression, as required by its substitution judgment and
explanatory prose. Negative beta and uniformity use the dual mover relation.
In uniformity the body with state `S` returns `C + S`.
-/

@[expose] public section
set_option autoImplicit true

namespace Silmaril.Isotope.Refinement

universe u v w

open LetIter.LocallyNameless (Tm)

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]

/-- The equations displayed in the binding, reduction, and iteration figures.
Directional beta and elimination are deliberately not equations. -/
inductive EquationAxiom (F : Fragment) :
    {n : Nat} → QCtx τ n → Term Φ n → Term Φ n → τ → Prop where
  | letOp {Γ Γl Γr : QCtx τ n} {a : Term Φ n} {c : Term Φ (n + 1)}
      {f : Φ} {e : ε} {C : τ}
      (split : Γ.Split Γl Γr) (hf : instrEff f ≤ e)
      (ha : HasType F Γr e a (instrSrc f))
      (hc : HasType F (Γl.snoc (instrTrg f)) e c C) :
      EquationAxiom F Γ (.let₁ (.op f a) c)
        (.let₁ a (.let₁ (.op f (.bv 0)) c.underBinder)) C
  | letLet {Γ Γl Γm Γr Γc : QCtx τ n}
      {a : Term Φ n} {b c : Term Φ (n + 1)} {A B C : τ} {e : ε}
      (outer : Γ.Split Γc Γr) (inner : Γc.Split Γl Γm)
      (ha : HasType F Γr e a A) (hb : HasType F (Γm.snoc A) e b B)
      (hc : HasType F (Γl.snoc B) e c C) :
      EquationAxiom F Γ (.let₁ (.let₁ a b) c)
        (.let₁ a (.let₁ b c.underBinder)) C
  | letLetPair {Γ Γl Γm Γr Γc : QCtx τ n}
      {a : Term Φ n} {c : Term Φ (n + 2)} {d : Term Φ (n + 1)}
      {A B C D : τ} {e : ε}
      (outer : Γ.Split Γc Γr) (inner : Γc.Split Γl Γm)
      (ha : HasType F Γr e a (product A B))
      (hc : HasType F ((Γm.snoc A).snoc B) e c C)
      (hd : HasType F (Γl.snoc C) e d D) :
      EquationAxiom F Γ (.let₁ (.let₂ a c) d)
        (.let₂ a (.let₁ c d.underBinder.underBinder)) D
  | letCase {Γ Γl Γm Γr Γc : QCtx τ n}
      {a : Term Φ n} {l r d : Term Φ (n + 1)} {A B C D : τ} {e : ε}
      (fragment : F.HasCase) (outer : Γ.Split Γc Γr) (inner : Γc.Split Γl Γm)
      (ha : HasType F Γm e a (coprod A B))
      (hl : HasType F (Γl.snoc A) e l C) (hr : HasType F (Γl.snoc B) e r C)
      (hd : HasType F (Γr.snoc C) e d D) :
      EquationAxiom F Γ (.let₁ (.case a l r) d)
        (.case a (.let₁ l d.underBinder) (.let₁ r d.underBinder)) D
  | pairBind {Γ Γl Γr : QCtx τ n} {a : Term Φ n} {c : Term Φ (n + 2)}
      {A B C : τ} {e : ε} (split : Γ.Split Γl Γr)
      (ha : HasType F Γr e a (product A B))
      (hc : HasType F ((Γl.snoc A).snoc B) e c C) :
      EquationAxiom F Γ (.let₂ a c)
        (.let₁ a (.let₂ (.bv 0) c.underTwoBinders)) C
  | caseBind {Γ Γl Γr : QCtx τ n} {a : Term Φ n} {l r : Term Φ (n + 1)}
      {A B C : τ} {e : ε} (fragment : F.HasCase) (split : Γ.Split Γl Γr)
      (ha : HasType F Γr e a (coprod A B))
      (hl : HasType F (Γl.snoc A) e l C) (hr : HasType F (Γl.snoc B) e r C) :
      EquationAxiom F Γ (.case a l r)
        (.let₁ a (.case (.bv 0) l.underBinder r.underBinder)) C
  | iterBind {Γ Γl Γr : QCtx τ n} {a : Term Φ n} {b : Term Φ (n + 1)}
      {A B : τ} {e : ε} (fragment : F.HasIter) (split : Γ.Split Γl Γr)
      (unrestricted : Γl.linearity = ⊤) (iterable : EffectSystem.iterable e)
      (ha : HasType F Γr e a A) (hb : HasType F (Γl.snoc A) e b (coprod B A)) :
      EquationAxiom F Γ (.iter a b) (.let₁ a (.iter (.bv 0) b.underBinder)) B
  | term {Γ : QCtx τ n} {a : Term Φ n} {e : ε}
      (ha : HasType F Γ e a Silmaril.unit) :
      EquationAxiom F Γ (.let₁ a .unit) a Silmaril.unit
  | initial {Γ Γl Γr : QCtx τ n} {a : Term Φ n} {b c : Term Φ (n + 1)}
      {A B : τ} {e : ε} (fragment : F.HasCase) (split : Γ.Split Γl Γr)
      (ha : HasType F Γr e a Silmaril.empty)
      (hb : HasType F (Γl.snoc A) e b B) (hc : HasType F (Γl.snoc A) e c B) :
      EquationAxiom F Γ (.let₁ (.abort a) b) (.let₁ (.abort a) c) B
  | pairEta {Γ : QCtx τ n} {a : Term Φ n} {A B : τ} {e : ε}
      (ha : HasType F Γ e a (product A B)) :
      EquationAxiom F Γ (.let₂ a (.pair (.bv 1) (.bv 0))) a (product A B)
  | pairBeta {Γ Γl Γr Γa Γb : QCtx τ n}
      {a b : Term Φ n} {c : Term Φ (n + 2)} {A B C : τ} {e : ε}
      (outer : Γ.Split Γl Γr) (inner : Γl.Split Γa Γb)
      (ha : HasType F Γa e a A) (hb : HasType F Γb e b B)
      (hc : HasType F ((Γr.snoc A).snoc B) e c C) :
      EquationAxiom F Γ (.let₂ (.pair a b) c) (.let₁ a (.let₁ b.lift c)) C
  | caseBetaL {Γ Γl Γr : QCtx τ n} {a : Term Φ n} {l r : Term Φ (n + 1)}
      {A B C : τ} {e : ε} (fragment : F.HasCase) (split : Γ.Split Γl Γr)
      (ha : HasType F Γr e a A) (hl : HasType F (Γl.snoc A) e l C)
      (hr : HasType F (Γl.snoc B) e r C) :
      EquationAxiom F Γ (.case (.inl a) l r) (.let₁ a l) C
  | caseBetaR {Γ Γl Γr : QCtx τ n} {a : Term Φ n} {l r : Term Φ (n + 1)}
      {A B C : τ} {e : ε} (fragment : F.HasCase) (split : Γ.Split Γl Γr)
      (ha : HasType F Γr e a B) (hl : HasType F (Γl.snoc A) e l C)
      (hr : HasType F (Γl.snoc B) e r C) :
      EquationAxiom F Γ (.case (.inr a) l r) (.let₁ a r) C
  | caseEta {Γ : QCtx τ n} {a : Term Φ n} {A B : τ} {e : ε}
      (fragment : F.HasCase) (ha : HasType F Γ e a (coprod A B)) :
      EquationAxiom F Γ (.case a (.inl (.bv 0)) (.inr (.bv 0))) a (coprod A B)
  | fixpoint {Γ Γl Γr : QCtx τ n} {a : Term Φ n} {b : Term Φ (n + 1)}
      {A B : τ} {e : ε} (fragment : F.HasIter) (split : Γ.Split Γl Γr)
      (unrestricted : Γl.linearity = ⊤) (iterable : EffectSystem.iterable e)
      (ha : HasType F Γr e a A) (hb : HasType F (Γl.snoc A) e b (coprod B A)) :
      EquationAxiom F Γ (.iter a b)
        (.let₁ a (.case b (.bv 0) (.iter (.bv 0) b.underBinder.underBinder))) B
  | naturality {Γ Γl Γm Γr Γc : QCtx τ n}
      {a : Term Φ n} {b c : Term Φ (n + 1)} {A B C : τ} {e : ε}
      (fragment : F.HasIter) (outer : Γ.Split Γl Γc) (inner : Γc.Split Γm Γr)
      (unrestrictedLeft : Γl.linearity = ⊤) (unrestrictedMiddle : Γm.linearity = ⊤)
      (ha : HasType F Γr e a A) (hb : HasType F (Γm.snoc A) e b (coprod B A))
      (hc : HasType F (Γl.snoc B) e c C) :
      EquationAxiom F Γ (.let₁ (.iter a b) c)
        (.iter a (.case b (.inl c.underBinder) (.inr (.bv 0)))) C
  | codiagonal {Γ Γl Γr : QCtx τ n} {a : Term Φ n} {b : Term Φ (n + 1)}
      {A B : τ} {e : ε} (fragment : F.HasIter) (split : Γ.Split Γl Γr)
      (unrestricted : Γl.linearity = ⊤) (iterable : EffectSystem.iterable e)
      (ha : HasType F Γr e a A) (hb : HasType F (Γl.snoc A) e b (coprod (coprod B A) A)) :
      EquationAxiom F Γ (.iter a (.iter (.bv 0) b.underBinder))
        (.iter a (.case b (.bv 0) (.inr (.bv 0)))) B

/-- Directional reduction schemes, retaining polarity-sensitive effect guards. -/
inductive DirectionalAxiom (F : Fragment) (p : Polarity) :
    {n : Nat} → QCtx τ n → Term Φ n → Term Φ n → τ → Prop where
  | eliminate {Γ Γl : QCtx τ n} {a b : Term Φ n} {B : τ} {e η : ε}
      (split : Γ.Split Γl Γ) (ha : HasType F Γl e a Silmaril.unit)
      (delete : Usage.zero ≤ Usage.used (EffectSystem.quantity p e))
      (hb : HasType F Γ η b B) :
      DirectionalAxiom F p Γ (.let₁ a b.lift) (.let₁ .unit b.lift) B
  | beta {Γ Γl Γr : QCtx τ n} {a : Term Φ n} {b : Term Φ (n + 1)}
      {A B : τ} {q : Usage} {e η : ε}
      (split : Γ.Split Γl Γr) (ha : HasType F Γl e a A)
      (hb : HasType F (Γr.snoc A q) η b B)
      (hbDefault : HasType F (Γr.snoc A) η b B)
      (mover : EffectSystem.moves p e η)
      (usage : q ≤ Usage.used (Γl.linearity ⊓ EffectSystem.quantity p e)) :
      DirectionalAxiom F p Γ (.let₁ a b) (Tm.instantiate b a) B

/-- Full effectful directed uniformity, before supplying its recursive premise.
The premise context can differ from the conclusion context. -/
inductive UniformityRule (F : Fragment) (p : Polarity) :
    {n m : Nat} → QCtx τ n → Term Φ n → Term Φ n → τ →
      QCtx τ m → Term Φ m → Term Φ m → τ → Prop where
  | square {Γ Γl Γr Γc : QCtx τ n} {a : Term Φ n}
      {s b b' c : Term Φ (n + 1)} {A B C S : τ} {e η : ε}
      (fragment : F.HasIter) (outer : Γ.Split Γc Γr) (inner : Γc.Split Γl Γc)
      (unrestricted : Γl.linearity = ⊤) (iterable : EffectSystem.iterable e)
      (ha : HasType F Γr e a A) (hs : HasType F (Γc.snoc A) η s S)
      (hb : HasType F (Γl.snoc S) e b (coprod C S))
      (hb' : HasType F (Γl.snoc A) (⊤ : ε) b' (coprod B A))
      (hc : HasType F (Γc.snoc B) (⊤ : ε) c C)
      (mover : EffectSystem.moves p η e) :
      UniformityRule F p (Γc.snoc A)
        (.let₁ s b.underBinder)
        (.case b' (.inl c.underBinder) (.inr s.underBinder)) (coprod C S)
        Γ (.let₁ a (.iter s b.underBinder)) (.let₁ (.iter a b') c) C

end Silmaril.Isotope.Refinement
