module

public import Silmaril.Raw.SSA.Isotope.Refinement.Weakening
public import Silmaril.Raw.SSA.Isotope.Refinement.ContextSplitting

@[expose] public section

namespace Silmaril.Isotope.Refinement.QCtx

universe u
variable {τ : Type u} [HasQuantity τ]

omit [HasQuantity τ] in
theorem snoc_injective {n : Nat} {Γ Δ : QCtx τ n} {A B : τ} {q r : Usage}
    (h : Γ.snoc A q = Δ.snoc B r) : Γ = Δ ∧ A = B ∧ q = r := by
  have hh : (A, q) = (B, r) := congrFun h 0
  exact ⟨funext (fun i => congrFun h i.succ), (Prod.mk.inj hh).1, (Prod.mk.inj hh).2⟩

omit [HasQuantity τ] in
/-- Induct on a context in canonical empty/extension form, hiding the transport
needed by its finite-function representation. -/
@[elab_as_elim] theorem inductionOn {P : {n : Nat} → QCtx τ n → Prop}
    {n : Nat} (Γ : QCtx τ n) (nil : P QCtx.nil)
    (snoc : ∀ {n : Nat} (Δ : QCtx τ n) (A : τ) (q : Usage), P Δ → P (Δ.snoc A q)) : P Γ := by
  induction n with
  | zero =>
    have he : Γ = QCtx.nil := funext (fun i => Fin.elim0 i)
    simpa only [he] using nil
  | succ n ih =>
    simpa only [snoc_tail] using snoc (fun i => Γ i.succ) (Γ 0).1 (Γ 0).2 (ih _)

omit [HasQuantity τ] in
/-- Expose the tail and quantity of a context with a prescribed newest type. -/
theorem exists_snoc_of_type {n : Nat} (Γ : QCtx τ (n + 1)) (A : τ)
    (h : (Γ 0).1 = A) : ∃ (Δ : QCtx τ n) (q : Usage), Γ = Δ.snoc A q :=
  exists_snoc_type Γ A h

/-- The newest ordinary binder may be returned when every outer slot is discardable. -/
theorem varAllowed_snoc {n : Nat} {Γ : QCtx τ n} (hd : Γ.Discardable) (A : τ) :
    (Γ.snoc A).VarAllowed 0 := by
  constructor
  · change Usage.effective (.used .linear) (quantity A) ≤ Usage.effective (.used ⊤) (quantity A)
    rw [Usage.effective_linear, Usage.effective_used]
    change Quantity.linear ≤ ⊤ ⊓ quantity A
    exact bot_le
  · intro j hj
    cases j using Fin.cases with
    | zero => exact (hj rfl).elim
    | succ j => exact hd j

namespace Weakening

/-- Insert an unused ambient variable while preserving the top two binders. -/
theorem insertZeroUnderTwo {n : Nat} (Γ : QCtx τ n) (X A B : τ) :
    Weakening (((Γ.snoc X .zero).snoc A).snoc B) ((Γ.snoc A).snoc B)
      (Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ))) := by
  convert ((insertZero Γ X).up A).up B using 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact Fin.cases rfl (fun _ => rfl) j

/-- Invert weakening from a nonempty context without dependent elimination
through the function representation of contexts. -/
theorem cases_snoc {n k : Nat} {Γ : QCtx τ n} {A : τ} {q : Usage}
    {Θ : QCtx τ (k + 1)} {σ : Fin (k + 1) → Fin (n + 1)}
    (h : Weakening (Γ.snoc A q) Θ σ) :
    (∃ (Δ : QCtx τ k) (r : Usage) (ρ : Fin k → Fin n),
      Θ = Δ.snoc A r ∧ σ = Fin.cases 0 (fun i => (ρ i).succ) ∧
      Weakening Γ Δ ρ ∧ Usage.effective r (quantity A) ≤ Usage.effective q (quantity A)) ∨
    (∃ ρ : Fin (k + 1) → Fin n, σ = (fun i => (ρ i).succ) ∧
      Weakening Γ Θ ρ ∧ Usage.zero ≤ Usage.effective q (quantity A)) := by
  generalize he : Γ.snoc A q = Ξ at h
  cases h with
  | cons h hq =>
    obtain ⟨rfl, rfl, rfl⟩ := snoc_injective he
    exact .inl ⟨_, _, _, rfl, rfl, h, hq⟩
  | skip h hq =>
    obtain ⟨rfl, rfl, rfl⟩ := snoc_injective he
    exact .inr ⟨_, rfl, h, hq⟩

/-- Native ordered weakening composes, retaining the composite index embedding. -/
theorem comp {n m k : Nat} {Γ : QCtx τ n} {Δ : QCtx τ m} {Θ : QCtx τ k}
    {ρ : Fin m → Fin n} {σ : Fin k → Fin m}
    (h : Weakening Γ Δ ρ) (g : Weakening Δ Θ σ) : Weakening Γ Θ (ρ ∘ σ) := by
  induction h generalizing k with
  | nil =>
    cases g
    exact .nil
  | @cons n m Γ Δ ρ A q q' h hq ih =>
    generalize he : Δ.snoc A q' = Ξ at g
    cases g with
    | cons g hg =>
      obtain ⟨rfl, rfl, rfl⟩ := snoc_injective he
      convert Weakening.cons (ih g) (hg.trans hq) using 1
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    | skip g hg =>
      obtain ⟨rfl, rfl, rfl⟩ := snoc_injective he
      exact Weakening.skip (ih g) (hg.trans hq)
  | skip h hq ih => exact Weakening.skip (ih g) hq

end Weakening
end Silmaril.Isotope.Refinement.QCtx
