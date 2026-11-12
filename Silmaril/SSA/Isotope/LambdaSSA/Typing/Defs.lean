module

public import Silmaril.Prelude.DeBruijnTyped
public import Silmaril.SSA.Isotope.Types.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Defs

/-!
# Lambda-SSA typing

Value and label contexts, typed renamings, and the typing judgements of
lambda-SSA terms, bodies, terminators, blocks and regions over an instruction
signature (`Silmaril.HasTy`). The structural laws (renaming, weakening,
substitution) are in `Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms`.
-/

@[expose] public section

/-!
# SSA value and label contexts
-/


universe u

namespace Silmaril.Isotope.SSA

variable {τ : Type u}

/-- Value contexts, with de Bruijn index zero at the list head. -/
abbrev VCtx (τ : Type u) := List τ

/-- Label contexts, with de Bruijn index zero at the list head. -/
abbrev LCtx (τ : Type u) := List τ

/-- Lookup evidence for a de Bruijn index; definitionally the shared `Silmaril.DeBruijn.At`. -/
abbrev At (Γ : List τ) (i : Nat) (A : τ) : Prop := Γ[i]? = some A

/-- SSA lookup evidence is exactly the shared `Silmaril.DeBruijn.At`. -/
theorem At.iff_deBruijnAt {Γ : List τ} {i : Nat} {A : τ} : At Γ i A ↔ Silmaril.DeBruijn.At Γ i A :=
  Iff.rfl

/-- A typed renaming from `Γ` into `Δ`; definitionally the shared `Silmaril.DeBruijn.TypedRen`
(see `Ren.iff_typedRen`). -/
def Ren (Γ Δ : List τ) (ρ : Nat → Nat) : Prop :=
  ∀ ⦃i A⦄, At Γ i A → At Δ (ρ i) A

namespace Ren

theorem id (Γ : List τ) : Ren Γ Γ id := Silmaril.DeBruijn.TypedRen.id Γ

theorem comp {Γ Δ Θ : List τ} {ρ σ : Nat → Nat} (hρ : Ren Γ Δ ρ) (hσ : Ren Δ Θ σ) :
    Ren Γ Θ (σ ∘ ρ) := Silmaril.DeBruijn.TypedRen.comp hρ hσ

theorem lift {Γ Δ : List τ} {ρ : Nat → Nat} (h : Ren Γ Δ ρ) (A : τ) :
    Ren (A :: Γ) (A :: Δ) (Silmaril.DeBruijn.lift ρ) := Silmaril.DeBruijn.TypedRen.lift h A

theorem wk (Γ : List τ) (A : τ) : Ren Γ (A :: Γ) Nat.succ := Silmaril.DeBruijn.TypedRen.wk Γ A

theorem append {Γ Δ : List τ} {ρ : Nat → Nat} (h : Ren Γ Δ ρ) (Ξ : List τ) :
    Ren (Ξ ++ Γ) (Ξ ++ Δ) (Silmaril.DeBruijn.liftN Ξ.length ρ) := Silmaril.DeBruijn.TypedRen.append h Ξ

/-- SSA renamings are exactly the shared typed de Bruijn renamings. -/
theorem iff_typedRen {Γ Δ : List τ} {ρ : Nat → Nat} : Ren Γ Δ ρ ↔ Silmaril.DeBruijn.TypedRen Γ Δ ρ :=
  Iff.rfl

end Ren

end Silmaril.Isotope.SSA

end

@[expose] public section

/-! # Value and label contexts for lambda-SSA -/


namespace Silmaril.Isotope.LambdaSSA

export SSA (VCtx LCtx At Ren)

namespace Ren
export SSA.Ren (id comp lift wk)
end Ren

end Silmaril.Isotope.LambdaSSA

end

@[expose] public section

/-!
# SSA typing
-/


universe u v

namespace Silmaril.Isotope.LambdaSSA

variable {Φ : Type u} {τ : Type v}

variable [Silmaril.TypeFormers τ] [Silmaril.HasTy Φ τ]

/-- Exact expression typing, independent of an effect or purity discipline.
The right case branch binds `B`. -/
inductive Tm.HasType : VCtx τ → Tm Φ → τ → Prop where
  | var {Γ : VCtx τ} {i : Nat} {A : τ} : At Γ i A → HasType Γ (.var i) A
  | op {Γ : VCtx τ} {a : Tm Φ} {f : Φ} :
      HasType Γ a (Silmaril.instrSrc f) → HasType Γ (.op f a) (Silmaril.instrTrg f)
  | let₁ {Γ : VCtx τ} {a b : Tm Φ} {A B : τ} :
      HasType Γ a A → HasType (A :: Γ) b B → HasType Γ (.let₁ a b) B
  | pair {Γ : VCtx τ} {a b : Tm Φ} {A B : τ} :
      HasType Γ a A → HasType Γ b B → HasType Γ (.pair a b) (Silmaril.product A B)
  | unit {Γ : VCtx τ} : HasType Γ .unit Silmaril.unit
  | let₂ {Γ : VCtx τ} {a b : Tm Φ} {A B C : τ} : HasType Γ a (Silmaril.product A B) →
      HasType (B :: A :: Γ) b C → HasType Γ (.let₂ a b) C
  | inl {Γ : VCtx τ} {a : Tm Φ} {A B : τ} :
      HasType Γ a A → HasType Γ (.inl a) (Silmaril.coprod A B)
  | inr {Γ : VCtx τ} {b : Tm Φ} {A B : τ} :
      HasType Γ b B → HasType Γ (.inr b) (Silmaril.coprod A B)
  | case {Γ : VCtx τ} {a l r : Tm Φ} {A B C : τ} : HasType Γ a (Silmaril.coprod A B) →
      HasType (A :: Γ) l C → HasType (B :: Γ) r C → HasType Γ (.case a l r) C
  | abort {Γ : VCtx τ} {a : Tm Φ} {A : τ} : HasType Γ a Silmaril.empty → HasType Γ (.abort a) A

/-- Typing for terminators: the branch argument matches the target label. -/
inductive Terminator.HasType : VCtx τ → Terminator Φ → LCtx τ → Prop where
  | br {Γ : VCtx τ} {L : LCtx τ} {ℓ : Nat} {a : Tm Φ} {A : τ} :
      At L ℓ A → Tm.HasType Γ a A → HasType Γ (.br ℓ a) L
  | case {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {l r : Terminator Φ} {A B : τ} :
      Tm.HasType Γ a (Silmaril.coprod A B) →
      HasType (A :: Γ) l L → HasType (B :: Γ) r L → HasType Γ (.case a l r) L

/-- Typing for straight-line block bodies, exposing their final value context. -/
inductive Body.HasType : VCtx τ → Body Φ → VCtx τ → Prop where
  | nil {Γ : VCtx τ} : HasType Γ .nil Γ
  | let₁ {Γ Δ : VCtx τ} {a : Tm Φ} {b : Body Φ} {A : τ} :
      Tm.HasType Γ a A → HasType (A :: Γ) b Δ → HasType Γ (.let₁ a b) Δ
  | let₂ {Γ Δ : VCtx τ} {a : Tm Φ} {b : Body Φ} {A B : τ} :
      Tm.HasType Γ a (Silmaril.product A B) →
      HasType (B :: A :: Γ) b Δ → HasType Γ (.let₂ a b) Δ

/-- A block types by threading the context produced by its body into its terminator. -/
def Block.HasType (Γ : VCtx τ) (b : Block Φ) (L : LCtx τ) : Prop :=
  ∃ Δ, Body.HasType Γ b.body Δ ∧ Terminator.HasType Δ b.terminator L

/-- Exact typing skeleton for regions. `cfg` binds all internal labels in the
entry and block bodies and one block parameter in each body. -/
inductive Region.HasType : VCtx τ → Region Φ → LCtx τ → Prop where
  | br {Γ : VCtx τ} {L : LCtx τ} {ℓ : Nat} {a : Tm Φ} {A : τ} :
      At L ℓ A → Tm.HasType Γ a A → HasType Γ (.br ℓ a) L
  | case {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {l r : Region Φ} {A B : τ} :
      Tm.HasType Γ a (Silmaril.coprod A B) →
      HasType (A :: Γ) l L → HasType (B :: Γ) r L → HasType Γ (.case a l r) L
  | let₁ {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {r : Region Φ} {A : τ} :
      Tm.HasType Γ a A → HasType (A :: Γ) r L → HasType Γ (.let₁ a r) L
  | let₂ {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {r : Region Φ} {A B : τ} :
      Tm.HasType Γ a (Silmaril.product A B) →
      HasType (B :: A :: Γ) r L → HasType Γ (.let₂ a r) L
  | cfg {Γ : VCtx τ} {L : LCtx τ} {entry : Region Φ} {n : Nat}
      {blocks : Fin n → Region Φ} (R : Fin n → τ) :
      HasType Γ entry (List.ofFn R ++ L) →
      (∀ i, HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) →
      HasType Γ (.cfg entry n blocks) L

end Silmaril.Isotope.LambdaSSA

end
