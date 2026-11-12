module

public import Silmaril.Raw.SSA.Isotope.Refinement.Contexts
public import Silmaril.Raw.SSA.Isotope.Refinement.Effects
public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.Syntax
public import Silmaril.SSA.Isotope.Types.Thms

@[expose] public section

noncomputable section

/-! # Quantity- and effect-sensitive typing for the written calculus

This is Figure `expr-typing` of `complete-refinement-ssa.tex`.  The same native
inductive judgment covers the three grammatical fragments.  A fragment guard
prevents a derivation from using a sum or iteration constructor absent from
that calculus; no equations of the larger fragment are pulled back.

All variables use finite de Bruijn indices.  Thus `Γ : QCtx τ n` accounts for
all the paper's free variables and `Tm Empty Φ n` has no additional names.
-/

namespace Silmaril.Isotope.Refinement

universe u v w

inductive Fragment where
  | seq | case | iter
  deriving DecidableEq, Repr

namespace Fragment

def HasCase : Fragment → Prop
  | .seq => False
  | .case | .iter => True

def HasIter : Fragment → Prop
  | .seq | .case => False
  | .iter => True

/-- Grammatical inclusions between the three calculi. -/
def Includes (F G : Fragment) : Prop :=
  (F.HasCase → G.HasCase) ∧ (F.HasIter → G.HasIter)

theorem Includes.refl (F : Fragment) : Includes F F := ⟨id, id⟩

theorem Includes.trans {F G H : Fragment} (h : Includes F G) (k : Includes G H) :
    Includes F H := ⟨k.1 ∘ h.1, k.2 ∘ h.2⟩

theorem seq_case : Includes .seq .case := ⟨False.elim, False.elim⟩
theorem case_iter : Includes .case .iter := ⟨id, False.elim⟩

end Fragment

abbrev Term (Φ : Type v) (n : Nat) := LetIter.LocallyNameless.Tm Empty Φ n

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]

set_option autoImplicit true in
/-- The written syntax-directed typing rules.  Effects are upper bounds;
quantitative context splitting is part of each derivation. -/
inductive HasType (F : Fragment) :
    {n : Nat} → QCtx τ n → ε → Term Φ n → τ → Type (max u v w)
  | var {Γ : QCtx τ n} {e : ε} (i : Fin n) (h : Γ.VarAllowed i) :
      HasType F Γ e (.bv i) (Γ i).1
  | op {Γ : QCtx τ n} {e : ε} {f : Φ} {a : Term Φ n}
      (hf : instrEff f ≤ e) (ha : HasType F Γ e a (instrSrc f)) :
      HasType F Γ e (.op f a) (instrTrg f)
  | let₁ {Γ Γl Γr : QCtx τ n} {e : ε} {a : Term Φ n} {b : Term Φ (n + 1)} {A B : τ}
      (split : Γ.Split Γl Γr) (ha : HasType F Γr e a A)
      (hb : HasType F (Γl.snoc A) e b B) : HasType F Γ e (.let₁ a b) B
  | unit {Γ : QCtx τ n} {e : ε} (h : Γ.Discardable) :
      HasType F Γ e .unit Silmaril.unit
  | pair {Γ Γl Γr : QCtx τ n} {e : ε} {a b : Term Φ n} {A B : τ}
      (split : Γ.Split Γl Γr) (ha : HasType F Γl e a A) (hb : HasType F Γr e b B) :
      HasType F Γ e (.pair a b) (product A B)
  | let₂ {Γ Γl Γr : QCtx τ n} {e : ε} {a : Term Φ n} {b : Term Φ (n + 2)} {A B C : τ}
      (split : Γ.Split Γl Γr) (ha : HasType F Γr e a (product A B))
      (hb : HasType F ((Γl.snoc A).snoc B) e b C) : HasType F Γ e (.let₂ a b) C
  | inl {Γ : QCtx τ n} {e : ε} {a : Term Φ n} {A B : τ}
      (fragment : F.HasCase) (ha : HasType F Γ e a A) :
      HasType F Γ e (.inl a) (coprod A B)
  | inr {Γ : QCtx τ n} {e : ε} {a : Term Φ n} {A B : τ}
      (fragment : F.HasCase) (ha : HasType F Γ e a B) :
      HasType F Γ e (.inr a) (coprod A B)
  | case {Γ Γl Γr : QCtx τ n} {e : ε} {a : Term Φ n}
      {l r : Term Φ (n + 1)} {A B C : τ}
      (fragment : F.HasCase) (split : Γ.Split Γl Γr)
      (ha : HasType F Γr e a (coprod A B))
      (hl : HasType F (Γl.snoc A) e l C) (hr : HasType F (Γl.snoc B) e r C) :
      HasType F Γ e (.case a l r) C
  | abort {Γ : QCtx τ n} {e : ε} {a : Term Φ n} {A : τ}
      (fragment : F.HasCase) (ha : HasType F Γ e a Silmaril.empty) :
      HasType F Γ e (.abort a) A
  | iter {Γ Γl Γr : QCtx τ n} {e : ε} {a : Term Φ n} {b : Term Φ (n + 1)} {A B : τ}
      (fragment : F.HasIter) (split : Γ.Split Γl Γr)
      (unrestricted : Γl.linearity = ⊤) (iterable : EffectSystem.iterable e)
      (ha : HasType F Γr e a A) (hb : HasType F (Γl.snoc A) e b (coprod B A)) :
      HasType F Γ e (.iter a b) B

namespace HasType

variable {F G : Fragment} {n : Nat} {Γ : QCtx τ n} {e e' : ε} {t : Term Φ n} {A : τ}

/-- Enlarging an effect bound preserves typing and quantitative splits. -/
def effectMono (h : HasType F Γ e t A) (he : e ≤ e') : HasType F Γ e' t A := by
  induction h with
  | var i h => exact .var i h
  | op hf _ ih => exact .op (hf.trans he) (ih he)
  | let₁ s _ _ ih ik => exact .let₁ s (ih he) (ik he)
  | unit h => exact .unit h
  | pair s _ _ ih ik => exact .pair s (ih he) (ik he)
  | let₂ s _ _ ih ik => exact .let₂ s (ih he) (ik he)
  | inl f _ ih => exact .inl f (ih he)
  | inr f _ ih => exact .inr f (ih he)
  | case f s _ _ _ ih il ir => exact .case f s (ih he) (il he) (ir he)
  | abort f _ ih => exact .abort f (ih he)
  | iter f s u it _ _ ih ik =>
    exact .iter f s u (EffectSystem.iterable_mono he it) (ih he) (ik he)

/-- Every effect-specific derivation gives a top-effect derivation. -/
def top (h : HasType F Γ e t A) : HasType F Γ (⊤ : ε) t A := h.effectMono le_top

/-- Grammatical inclusion preserves the native quantitative derivation. -/
def embed (h : HasType F Γ e t A) (hFG : F.Includes G) : HasType G Γ e t A := by
  induction h with
  | var i h => exact .var i h
  | op hf _ ih => exact .op hf ih
  | let₁ s _ _ ih ik => exact .let₁ s ih ik
  | unit h => exact .unit h
  | pair s _ _ ih ik => exact .pair s ih ik
  | let₂ s _ _ ih ik => exact .let₂ s ih ik
  | inl f _ ih => exact .inl (hFG.1 f) ih
  | inr f _ ih => exact .inr (hFG.1 f) ih
  | case f s _ _ _ ih il ir => exact .case (hFG.1 f) s ih il ir
  | abort f _ ih => exact .abort (hFG.1 f) ih
  | iter f s u it _ _ ih ik => exact .iter (hFG.2 f) s u it ih ik

end HasType
end Silmaril.Isotope.Refinement
