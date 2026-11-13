module

public import Silmaril.Raw.SSA.Isotope.Refinement.Typing
public import Silmaril.Raw.SSA.Isotope.Refinement.TypeQuantity

/-! # Type coherence boundaries for quantitative syntax

Sequential syntax has a unique result type once variable types are fixed.
Coproduct injections and empty elimination deliberately omit type annotations,
so the analogous statement for the larger fragments is false. This module
separates type reconstruction from the further semantic coherence question.
-/

@[expose] public section

namespace Silmaril.Isotope.Refinement
universe u v w

namespace QCtx
variable {τ : Type u} {n : Nat}
/-- Forget resource annotations, retaining each variable's value type. -/
def types (Γ : QCtx τ n) : Fin n → τ := fun i => (Γ i).1

@[simp] theorem types_snoc (Γ : QCtx τ n) (A : τ) (q : Usage) :
    types (Γ.snoc A q) = Fin.cases A (types Γ) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

variable [HasQuantity τ]
theorem Split.types_left {Γ Γl Γr : QCtx τ n} (s : Split Γ Γl Γr) : types Γl = types Γ :=
  funext (fun i => (s i).1)
theorem Split.types_right {Γ Γl Γr : QCtx τ n} (s : Split Γ Γl Γr) : types Γr = types Γ :=
  funext (fun i => (s i).2.1)
end QCtx

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)]

/-- Reconstruct the sequential result type. This is not a type checker: it
omits primitive-argument checks and all quantity/effect premises. -/
def inferSeq : {n : Nat} → (Fin n → Ty α) → Term Φ n → Option (Ty α)
  | _, Γ, .bv i => some (Γ i)
  | _, _, .fv x => nomatch x
  | _, _, .op f _ => some (instrTrg f)
  | _, Γ, .let₁ a b => (inferSeq Γ a).bind (fun A => inferSeq (Fin.cases A Γ) b)
  | _, _, .unit => some .unit
  | _, Γ, .pair a b => (inferSeq Γ a).bind (fun A => (inferSeq Γ b).map (Ty.product A))
  | _, Γ, .let₂ a b => (inferSeq Γ a).bind (fun
      | .product A B => inferSeq (Fin.cases B (Fin.cases A Γ)) b
      | _ => none)
  | _, _, .inl _ | _, _, .inr _ | _, _, .case _ _ _ | _, _, .abort _ | _, _, .iter _ _ => none

variable [HasQuantity α] {ε : Type w} [EffectSystem ε] [HasEff Φ ε]

namespace HasType
/-- The native sequential typing rules agree with quantity-free type reconstruction. -/
theorem inferSeq_eq {n : Nat} {Γ : QCtx (Ty α) n} {e : ε} {t : Term Φ n} {A : Ty α}
    (h : HasType .seq Γ e t A) : inferSeq Γ.types t = some A := by
  induction h with
  | var => rfl
  | op => rfl
  | let₁ s _ _ iha ihb =>
    simp only [inferSeq]
    rw [← s.types_right, iha]
    simpa only [Option.bind_some, QCtx.types_snoc, s.types_left, s.types_right, product_ty] using ihb
  | unit => rfl
  | pair s _ _ iha ihb =>
    simp only [inferSeq]
    rw [← s.types_left, iha]
    simpa only [Option.bind_some, s.types_left, s.types_right, ihb, Option.map_some, product_ty] using
      congrArg (Option.map (Ty.product _)) ihb
  | let₂ s _ _ iha ihb =>
    simp only [inferSeq]
    rw [← s.types_right, iha]
    simpa only [Option.bind_some, QCtx.types_snoc, s.types_left, s.types_right, product_ty] using ihb
  | inl h => exact False.elim h
  | inr h => exact False.elim h
  | case h => exact False.elim h
  | abort h => exact False.elim h
  | iter h => exact False.elim h

/-- Quantitative resource splitting does not make sequential result types ambiguous. -/
theorem seq_result_eq {n : Nat} {Γ Δ : QCtx (Ty α) n} {e e' : ε} {t : Term Φ n} {A B : Ty α}
    (h : HasType .seq Γ e t A) (k : HasType .seq Δ e' t B) (hΓ : Γ.types = Δ.types) : A = B := by
  have he := h.inferSeq_eq
  rw [hΓ, k.inferSeq_eq] at he
  exact (Option.some.inj he).symm

end HasType
end Silmaril.Isotope.Refinement
