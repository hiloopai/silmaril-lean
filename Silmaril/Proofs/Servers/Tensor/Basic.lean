module

public import Silmaril.Servers.Tensor.Defs

/-!
# Proofs: the tensor of servers

Projections of tagged, swapped and reassociated traces; histories of machines with isolated
state are interleavings; the shared counter.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Tensor

open Silmaril.Servers Silmaril.Servers.Tensor

variable {A B C : Sig}

theorem left_map_inl (t : Trace A) : Trace.left (t.map (Event.inl (B := B))) = t := by
  simp only [Trace.left, List.filterMap_map]
  have : (Event.left (B := B) ∘ Event.inl (B := B) : Event A → Option (Event A)) = some := by
    funext e; cases e <;> rfl
  rw [this, List.filterMap_some]

theorem right_map_inl (t : Trace A) : Trace.right (t.map (Event.inl (B := B))) = [] := by
  simp only [Trace.right, List.filterMap_map]
  rw [List.filterMap_eq_nil_iff]; intro e _; cases e <;> rfl

theorem left_swap (t : Trace (A.tensor B)) : Trace.left (t.map Event.swap) = Trace.right t := by
  simp only [Trace.left, Trace.right, List.filterMap_map]
  congr 1; funext e; rcases e with ⟨i, r | r⟩ | ⟨i, s | s⟩ <;> rfl

theorem right_swap (t : Trace (A.tensor B)) : Trace.right (t.map Event.swap) = Trace.left t := by
  simp only [Trace.left, Trace.right, List.filterMap_map]
  congr 1; funext e; rcases e with ⟨i, r | r⟩ | ⟨i, s | s⟩ <;> rfl

theorem left_assoc (t : Trace ((A.tensor B).tensor C)) :
    Trace.left (t.map Event.assoc) = Trace.left (Trace.left t) := by
  simp only [Trace.left, List.filterMap_map, List.filterMap_filterMap]
  congr 1; funext e; rcases e with ⟨i, (r | r) | r⟩ | ⟨i, (s | s) | s⟩ <;> rfl

theorem left_right_assoc (t : Trace ((A.tensor B).tensor C)) :
    Trace.left (Trace.right (t.map Event.assoc)) = Trace.right (Trace.left t) := by
  simp only [Trace.left, Trace.right, List.filterMap_map, List.filterMap_filterMap]
  congr 1; funext e; rcases e with ⟨i, (r | r) | r⟩ | ⟨i, (s | s) | s⟩ <;> rfl

theorem right_right_assoc (t : Trace ((A.tensor B).tensor C)) :
    Trace.right (Trace.right (t.map Event.assoc)) = Trace.right t := by
  simp only [Trace.right, List.filterMap_map, List.filterMap_filterMap]
  congr 1; funext e; rcases e with ⟨i, (r | r) | r⟩ | ⟨i, (s | s) | s⟩ <;> rfl

theorem unit_nil (t : Trace Sig.unit) : t = [] := by
  rcases t with _ | ⟨⟨_, r⟩ | ⟨_, s⟩, _⟩
  · rfl
  · exact r.elim
  · exact s.elim

/-! ## Machines with isolated state -/

theorem run_nil_iff {σ : Type} (M : Machine A σ) (q q' : σ) : M.Run q [] q' ↔ q = q' :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .nil q⟩

theorem run_cons_iff {σ : Type} (M : Machine A σ) (q q'' : σ) (r : A.Req) (s : A.Resp)
    (h : History A) : M.Run q ((r, s) :: h) q'' ↔ ∃ q', M q r s q' ∧ M.Run q' h q'' :=
  ⟨fun h => by cases h with | cons hm hr => exact ⟨_, hm, hr⟩,
    fun ⟨_, hm, hr⟩ => .cons hm hr⟩

theorem tensor_run_iff {σ τ : Type} (M₁ : Machine A σ) (M₂ : Machine B τ)
    (h : History (A.tensor B)) (q₁ p₁ : σ) (q₂ p₂ : τ) :
    (Machine.tensor M₁ M₂).Run (q₁, q₂) h (p₁, p₂) ↔
      History.Routed h ∧ M₁.Run q₁ (History.left h) p₁ ∧ M₂.Run q₂ (History.right h) p₂ := by
  induction h generalizing q₁ q₂ with
  | nil =>
    simp only [History.Routed, History.left, History.right, List.filterMap_nil, List.not_mem_nil,
      false_implies, implies_true, true_and]
    rw [run_nil_iff, run_nil_iff, run_nil_iff, Prod.mk.injEq]
  | cons p h ih =>
    obtain ⟨r | r, s | s⟩ := p
    · have hR : History.Routed ((Sum.inl r, Sum.inl s) :: h : History (A.tensor B)) ↔
          History.Routed h := by simp [History.Routed]
      refine (run_cons_iff _ _ _ _ _ _).trans (Iff.trans ?_ (and_congr hR.symm
        (and_congr (run_cons_iff M₁ q₁ p₁ r s (History.left h)).symm Iff.rfl)))
      constructor
      · rintro ⟨⟨q₁', q₂'⟩, ⟨hm, he⟩, hrun⟩
        subst he
        obtain ⟨hR, h1, h2⟩ := (ih q₁' q₂').1 hrun
        exact ⟨hR, ⟨q₁', hm, h1⟩, h2⟩
      · rintro ⟨hR, ⟨q₁', hm, h1⟩, h2⟩
        exact ⟨(q₁', q₂), ⟨hm, rfl⟩, (ih q₁' q₂).2 ⟨hR, h1, h2⟩⟩
    · refine (run_cons_iff _ _ _ _ _ _).trans ⟨?_, ?_⟩
      · rintro ⟨⟨_, _⟩, hm, _⟩; exact hm.elim
      · rintro ⟨hR, _⟩; exact absurd (hR _ List.mem_cons_self) (by simp)
    · refine (run_cons_iff _ _ _ _ _ _).trans ⟨?_, ?_⟩
      · rintro ⟨⟨_, _⟩, hm, _⟩; exact hm.elim
      · rintro ⟨hR, _⟩; exact absurd (hR _ List.mem_cons_self) (by simp)
    · have hR : History.Routed ((Sum.inr r, Sum.inr s) :: h : History (A.tensor B)) ↔
          History.Routed h := by simp [History.Routed]
      refine (run_cons_iff _ _ _ _ _ _).trans (Iff.trans ?_ (and_congr hR.symm
        (and_congr Iff.rfl (run_cons_iff M₂ q₂ p₂ r s (History.right h)).symm)))
      constructor
      · rintro ⟨⟨q₁', q₂'⟩, ⟨hm, he⟩, hrun⟩
        subst he
        obtain ⟨hR, h1, h2⟩ := (ih q₁' q₂').1 hrun
        exact ⟨hR, h1, ⟨q₂', hm, h2⟩⟩
      · rintro ⟨hR, h1, ⟨q₂', hm, h2⟩⟩
        exact ⟨(q₁, q₂'), ⟨hm, rfl⟩, (ih q₁ q₂').2 ⟨hR, h1, h2⟩⟩

theorem tensor_hist_iff {σ τ : Type} (M₁ : Machine A σ) (M₂ : Machine B τ)
    (h : History (A.tensor B)) (q₁ : σ) (q₂ : τ) :
    (Machine.tensor M₁ M₂).Hist (q₁, q₂) h ↔
      History.Routed h ∧ M₁.Hist q₁ (History.left h) ∧ M₂.Hist q₂ (History.right h) := by
  constructor
  · rintro ⟨⟨p₁, p₂⟩, hr⟩
    obtain ⟨hR, h1, h2⟩ := (tensor_run_iff M₁ M₂ h q₁ p₁ q₂ p₂).1 hr
    exact ⟨hR, ⟨p₁, h1⟩, ⟨p₂, h2⟩⟩
  · rintro ⟨hR, ⟨p₁, h1⟩, ⟨p₂, h2⟩⟩
    exact ⟨(p₁, p₂), (tensor_run_iff M₁ M₂ h q₁ p₁ q₂ p₂).2 ⟨hR, h1, h2⟩⟩

end Silmaril.Proofs.Servers.Tensor

namespace Silmaril.Proofs.Servers.Tensor

open Silmaril.Servers Silmaril.Servers.Tensor

theorem counter_hist_single {q s : Nat} (h : counter.Hist q [((), s)]) : s = q := by
  obtain ⟨_, hr⟩ := h
  cases hr with | cons hm _ => exact hm.1

theorem shared_not_tensor (q₁ q₂ : Nat) :
    sharedCounter.Hist 0 ≠ (Machine.tensor counter counter).Hist (q₁, q₂) := by
  intro heq
  have h1 : sharedCounter.Hist 0 [(.inr (), .inr (0 : Nat))] := ⟨1, .cons ⟨rfl, rfl⟩ (.nil 1)⟩
  have h2 : sharedCounter.Hist 0 [(.inl (), .inl (0 : Nat)), (.inr (), .inr (1 : Nat))] :=
    ⟨2, .cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.nil 2))⟩
  rw [heq] at h1 h2
  have e1 := counter_hist_single ((tensor_hist_iff counter counter _ q₁ q₂).1 h1).2.2
  have e2 := counter_hist_single ((tensor_hist_iff counter counter _ q₁ q₂).1 h2).2.2
  omega

end Silmaril.Proofs.Servers.Tensor
