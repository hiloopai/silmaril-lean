module

public import Silmaril.Games.Abstract.Function.Defs

/-!
# Abstract functions: proofs

Observations compose; trap ≈ divergence is a congruence for sequencing and
forgetting the final state is not; deterministic functions have at most one
behaviour under a host; state preservation is closed under sequencing and
joins, determinism is not closed under joins.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.Function

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.AFun

universe u

variable {E : Sig.{u}} {S A B C : Type u}

theorem obsEquiv_comp {O O' : Type u} {κ : CallBeh E S B → O} (g : O → O')
    {f f' : AFun E S A B} (h : ObsEquiv κ f f') : ObsEquiv (g ∘ κ) f f' := fun s a => by
  rw [Set.image_comp, Set.image_comp, h s a]

theorem collapse_eq_ret {e : End S B} {b : B} {s : S} (h : e.collapse = .ret b s) :
    e = .ret b s := by
  cases e <;> simp_all [End.collapse]

theorem collapse_eq_abort {e : End S B} (h : e.collapse = .abort) : e = .trap ∨ e = .div := by
  cases e <;> simp_all [End.collapse]

/-- One direction of the congruence of trap ≈ divergence for sequencing. -/
theorem seq_collapse_subset {f f' : AFun E S A B} {g g' : AFun E S B C}
    (hf : ObsEquiv obsCollapse f f') (hg : ObsEquiv obsCollapse g g') (s : S) (a : A) :
    obsCollapse '' seq f g s a ⊆ obsCollapse '' seq f' g' s a := by
  rintro _ ⟨x, hx, rfl⟩
  have abort : ∀ c, obsCollapse (E := E) (S := S) (B := B) (c, End.trap) ∈ obsCollapse '' f' s a →
      ∃ y ∈ seq f' g' s a, obsCollapse y = obsCollapse (c, (End.trap : End S C)) := by
    rintro c ⟨⟨c', e'⟩, hy, he⟩
    simp only [obsCollapse, Prod.mk.injEq] at he
    obtain ⟨rfl, he⟩ := he
    rcases collapse_eq_abort (by simpa [End.collapse] using he) with rfl | rfl
    · exact ⟨_, .inl ⟨c', hy, rfl⟩, rfl⟩
    · exact ⟨_, .inr (.inl ⟨c', hy, rfl⟩), rfl⟩
  rcases hx with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c₁, b, s₁, c₂, e, h₁, h₂, rfl⟩
  · obtain ⟨y, hy, he⟩ := abort c (hf s a ▸ ⟨_, hc, rfl⟩)
    exact ⟨y, hy, he⟩
  · obtain ⟨y, hy, he⟩ := abort c (hf s a ▸ ⟨_, hc, rfl⟩)
    exact ⟨y, hy, by rw [he]; rfl⟩
  · obtain ⟨⟨c₁', e₁'⟩, hy₁, he₁⟩ : obsCollapse (c₁, End.ret b s₁) ∈ obsCollapse '' f' s a :=
      hf s a ▸ ⟨_, h₁, rfl⟩
    simp only [obsCollapse, Prod.mk.injEq] at he₁
    obtain ⟨rfl, he₁⟩ := he₁
    obtain rfl := collapse_eq_ret (by simpa [End.collapse] using he₁)
    obtain ⟨⟨c₂', e'⟩, hy₂, he₂⟩ : obsCollapse (c₂, e) ∈ obsCollapse '' g' s₁ b :=
      hg s₁ b ▸ ⟨_, h₂, rfl⟩
    simp only [obsCollapse, Prod.mk.injEq] at he₂
    obtain ⟨rfl, he₂⟩ := he₂
    exact ⟨_, .inr (.inr ⟨c₁', b, s₁, c₂', e', hy₁, hy₂, rfl⟩), by simp [obsCollapse, he₂]⟩

theorem seq_collapse {f f' : AFun E S A B} {g g' : AFun E S B C}
    (hf : ObsEquiv obsCollapse f f') (hg : ObsEquiv obsCollapse g g') :
    ObsEquiv obsCollapse (seq f g) (seq f' g') := fun s a =>
  Set.Subset.antisymm (seq_collapse_subset hf hg s a)
    (seq_collapse_subset (fun s a => (hf s a).symm) (fun s a => (hg s a).symm) s a)

/-! ## Forgetting the state is not a congruence -/

/-- Set the state to `b`. -/
def setTo (b : Bool) : AFun Sig.empty Bool PUnit PUnit := fun _ _ => {([], .ret ⟨⟩ b)}

/-- Return the state. -/
def readState : AFun Sig.empty Bool PUnit Bool := fun s _ => {([], .ret s s)}

theorem setTo_forget : ObsEquiv obsForgetState (setTo true) (setTo false) := fun s a => by
  simp [setTo, obsForgetState, End.forgetState]

theorem seq_setTo (b : Bool) (s : Bool) :
    ([], End.ret b b) ∈ seq (setTo b) readState s ⟨⟩ :=
  .inr (.inr ⟨[], ⟨⟩, b, [], .ret b b, rfl, rfl, rfl⟩)

theorem seq_setTo_inv {b s : Bool} {x : CallBeh Sig.empty Bool Bool}
    (h : x ∈ seq (setTo b) readState s ⟨⟩) : x = ([], End.ret b b) := by
  rcases h with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨c₁, b', s₁, c₂, e, h₁, h₂, rfl⟩
  · simp [setTo] at hc
  · simp [setTo] at hc
  · simp only [setTo, Set.mem_singleton_iff, Prod.mk.injEq, End.ret.injEq] at h₁
    obtain ⟨rfl, -, rfl⟩ := h₁
    simp only [readState, Set.mem_singleton_iff, Prod.mk.injEq] at h₂
    obtain ⟨rfl, rfl⟩ := h₂
    rfl

theorem forget_not_congr :
    ¬ ObsEquiv obsForgetState (seq (setTo true) readState) (seq (setTo false) readState) := by
  intro h
  have : obsForgetState ([], End.ret true true) ∈
      obsForgetState '' seq (setTo false) readState true ⟨⟩ :=
    h true ⟨⟩ ▸ ⟨_, seq_setTo true true, rfl⟩
  obtain ⟨x, hx, he⟩ := this
  rw [seq_setTo_inv hx] at he
  simp [obsForgetState, End.forgetState] at he

/-! ## Determinism under a host -/

theorem agree_consistent {h : Host E} {c₁ c₂ : List (Call E)} {e₁ e₂ : End S B}
    (hA : Agree c₁ e₁ c₂ e₂) (h₁ : Consistent h c₁) (h₂ : Consistent h c₂) :
    c₁ = c₂ ∧ e₁ = e₂ := by
  induction c₁ generalizing c₂ with
  | nil =>
    cases c₂ with
    | nil => exact ⟨rfl, hA⟩
    | cons y c₂ => exact hA.elim
  | cons x c₁ ih =>
    cases c₂ with
    | nil => obtain ⟨_, _⟩ := x; exact hA.elim
    | cons y c₂ =>
      obtain ⟨m₁, n₁⟩ := x
      obtain ⟨m₂, n₂⟩ := y
      obtain ⟨rfl, hA⟩ := hA
      have e₁' : n₁ = h m₁ := h₁ ⟨m₁, n₁⟩ List.mem_cons_self
      have e₂' : n₂ = h m₁ := h₂ ⟨m₁, n₂⟩ List.mem_cons_self
      subst e₁' e₂'
      obtain ⟨rfl, rfl⟩ := ih (hA HEq.rfl) (fun z hz => h₁ z (by simp [hz]))
        (fun z hz => h₂ z (by simp [hz]))
      exact ⟨rfl, rfl⟩

theorem det_under_subsingleton {f : AFun E S A B} (hf : Det f) (h : Host E) (s : S) (a : A) :
    (under h f s a).Subsingleton := by
  rintro ⟨c₁, e₁⟩ ⟨hx, hc₁⟩ ⟨c₂, e₂⟩ ⟨hy, hc₂⟩
  obtain ⟨rfl, rfl⟩ := agree_consistent (hf s a _ _ hx hy) hc₁ hc₂
  rfl

/-! ## Statefulness and joins -/

theorem seq_statePreserving {f : AFun E S A B} {g : AFun E S B C} (hf : StatePreserving f)
    (hg : StatePreserving g) : StatePreserving (seq f g) := by
  intro s a c b s' hx
  rcases hx with ⟨c, hc, he⟩ | ⟨c, hc, he⟩ | ⟨c₁, b₁, s₁, c₂, e, h₁, h₂, he⟩
  · simp at he
  · simp at he
  · simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    obtain rfl := hf _ _ _ _ _ h₁
    exact hg _ _ _ _ _ h₂

theorem sSup_statePreserving {F : Set (AFun E S A B)} (hF : ∀ f ∈ F, StatePreserving f) :
    StatePreserving (sSup F) := by
  intro s a c b s' hx
  rw [sSup_apply, iSup_apply] at hx
  simp only [Set.iSup_eq_iUnion, Set.mem_iUnion] at hx
  obtain ⟨⟨f, hf⟩, hx⟩ := hx
  exact hF f hf s a c b s' hx

/-- Return `b`. -/
def const (b : Bool) : AFun Sig.empty PUnit PUnit Bool := fun _ _ => {([], .ret b ⟨⟩)}

theorem const_det (b : Bool) : Det (const b) := by
  rintro s a x y hx hy
  simp only [const, Set.mem_singleton_iff] at hx hy
  subst hx hy
  rfl

theorem sup_not_det : ¬ Det (const true ⊔ const false) := by
  intro h
  have := h ⟨⟩ ⟨⟩ ([], .ret true ⟨⟩) ([], .ret false ⟨⟩) (.inl rfl) (.inr rfl)
  simp [Agree] at this

end Silmaril.Proofs.Games.Abstract.Function
