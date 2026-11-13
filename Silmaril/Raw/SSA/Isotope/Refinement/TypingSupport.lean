module

public import Silmaril.Raw.SSA.Isotope.Refinement.TypingCoherence
public import Silmaril.Raw.SSA.Isotope.Refinement.ContextComposition

@[expose] public section

namespace Silmaril.Isotope.Refinement
universe u v w

namespace Term
variable {Φ : Type v}
/-- Syntactic occurrence of an outer variable, respecting every binder. -/
def uses : {n : Nat} → Term Φ n → Fin n → Bool
  | _, .bv j, i => decide (i = j)
  | _, .fv x, _ => nomatch x
  | _, .op _ a, i => uses a i
  | _, .let₁ a b, i => uses a i || uses b i.succ
  | _, .unit, _ => false
  | _, .pair a b, i => uses a i || uses b i
  | _, .let₂ a b, i => uses a i || uses b i.succ.succ
  | _, .inl a, i | _, .inr a, i | _, .abort a, i => uses a i
  | _, .case a l r, i => uses a i || (uses l i.succ || uses r i.succ)
  | _, .iter a b, i => uses a i || uses b i.succ
end Term

namespace QCtx
variable {τ : Type u} [HasQuantity τ]

/-- Used variables cannot be zero; unused variables must be discardable. -/
def SlotAllows (A : τ) (q : Usage) (used : Bool) : Prop :=
  (used = true → q ≠ .zero) ∧ (used = false → Usage.zero ≤ Usage.effective q (quantity A))

namespace SlotAllows
variable {A : τ} {q : Usage} {b c : Bool}
theorem or (h : SlotAllows A q b) (k : SlotAllows A q c) : SlotAllows A q (b || c) := by
  constructor
  · intro hb
    rcases Bool.or_eq_true_iff.mp hb with hb | hc
    · exact h.1 hb
    · exact k.1 hc
  · intro hb
    exact h.2 (Bool.or_eq_false_iff.mp hb).1
end SlotAllows

theorem SlotSplit.allows {A : τ} {q ql qr : Usage} (s : SlotSplit A q ql qr)
    {b c : Bool} (h : SlotAllows A ql b) (k : SlotAllows A qr c) : SlotAllows A q (b || c) := by
  constructor
  · intro hb hq
    subst q
    have he : ql = .zero ∧ qr = .zero := by cases s <;> simp_all
    rcases Bool.or_eq_true_iff.mp hb with hb | hc
    · exact h.1 hb he.1
    · exact k.1 hc he.2
  · intro hb
    have hl := h.2 (Bool.or_eq_false_iff.mp hb).1
    have hr := k.2 (Bool.or_eq_false_iff.mp hb).2
    cases s with
    | left => exact hl
    | right => exact hr
    | both => exact hl

/-- Context restriction retains the types and suppresses unused slots. -/
def restrict {n : Nat} (Γ : QCtx τ n) (p : Fin n → Bool) : QCtx τ n :=
  fun i => ((Γ i).1, if p i then (Γ i).2 else .zero)

omit [HasQuantity τ] in
@[simp] theorem restrict_types {n : Nat} (Γ : QCtx τ n) (p : Fin n → Bool) :
    (restrict Γ p).types = Γ.types := rfl

/-- Restricting unused slots is an actual native weakening, not an informal
assumption that zero is a least quantity. -/
theorem weakening_restrict {n : Nat} (Γ : QCtx τ n) (p : Fin n → Bool)
    (h : ∀ i, p i = false → Usage.zero ≤ effective Γ i) : Weakening Γ (restrict Γ p) id := by
  induction Γ using inductionOn with
  | nil =>
    convert (Weakening.nil (τ := τ)) using 1
  | @snoc n Γ A q ih =>
    have ht := ih (fun i => p i.succ) (fun i => h i.succ)
    have hq : Usage.effective (if p 0 then q else .zero) (quantity A) ≤ Usage.effective q (quantity A) := by
      cases hp : p 0
      · exact h 0 hp
      · exact le_rfl
    have hw := Weakening.cons ht hq
    have he : restrict (Γ.snoc A q) p = (restrict Γ (fun i => p i.succ)).snoc A (if p 0 then q else .zero) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [he]
    convert hw using 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
end QCtx

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ] {ε : Type w} [EffectSystem ε] [HasEff Φ ε]

namespace HasType
/-- Native typing enforces exact support: zero slots are absent from syntax,
and every syntactically absent outer variable permits discarding. -/
theorem slotAllows {F : Fragment} {n : Nat} {Γ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ}
    (h : HasType F Γ e t A) (i : Fin n) : QCtx.SlotAllows (Γ i).1 (Γ i).2 (Term.uses t i) := by
  induction h with
  | var j hv =>
    constructor
    · intro hused hzero
      have hij : i = j := of_decide_eq_true hused
      subst i
      have hlinear := hv.1
      simp only [QCtx.effective, hzero, Usage.effective_zero] at hlinear
      exact hlinear
    · intro hused
      exact hv.2 i (of_decide_eq_false hused)
  | op _ _ ih => exact ih i
  | let₁ s _ _ iha ihb =>
    have ha := iha i
    have hb := ihb i.succ
    change QCtx.SlotAllows _ _ (_ || _)
    have ht := (s i).2.2.symm.allows
      (by simpa only [(s i).2.1] using ha) (by simpa only [QCtx.snoc_succ, (s i).1] using hb)
    exact ht
  | unit h => exact ⟨Bool.noConfusion, fun _ => h i⟩
  | pair s _ _ iha ihb =>
    exact (s i).2.2.allows (by simpa only [(s i).1] using iha i)
      (by simpa only [(s i).2.1] using ihb i)
  | let₂ s _ _ iha ihb =>
    exact (s i).2.2.symm.allows (by simpa only [(s i).2.1] using iha i)
      (by simpa only [QCtx.snoc_succ, (s i).1] using ihb i.succ.succ)
  | inl _ _ ih => exact ih i
  | inr _ _ ih => exact ih i
  | case _ s _ _ _ iha ihl ihr =>
    exact (s i).2.2.symm.allows (by simpa only [(s i).2.1] using iha i)
      ((by simpa only [QCtx.snoc_succ, (s i).1] using ihl i.succ : QCtx.SlotAllows _ _ _).or
        (by simpa only [QCtx.snoc_succ, (s i).1] using ihr i.succ))
  | abort _ _ ih => exact ih i
  | iter _ s _ _ _ _ iha ihb =>
    exact (s i).2.2.symm.allows (by simpa only [(s i).2.1] using iha i)
      (by simpa only [QCtx.snoc_succ, (s i).1] using ihb i.succ)

theorem unused_discardable {F : Fragment} {n : Nat} {Γ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ}
    (h : HasType F Γ e t A) {i : Fin n} (hi : Term.uses t i = false) : Usage.zero ≤ QCtx.effective Γ i :=
  (h.slotAllows i).2 hi

theorem used_nonzero {F : Fragment} {n : Nat} {Γ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ}
    (h : HasType F Γ e t A) {i : Fin n} (hi : Term.uses t i = true) : (Γ i).2 ≠ .zero :=
  (h.slotAllows i).1 hi

/-- Every quantitative derivation admits a native weakening to its raw support. -/
theorem supportWeakening {F : Fragment} {n : Nat} {Γ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ}
    (h : HasType F Γ e t A) : QCtx.Weakening Γ (QCtx.restrict Γ (Term.uses t)) id :=
  QCtx.weakening_restrict Γ (Term.uses t) (fun _ => h.unused_discardable)

end HasType
end Silmaril.Isotope.Refinement
