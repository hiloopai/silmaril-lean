module

public import Silmaril.Servers.Core.Defs
import Silmaril.Proofs.Servers.Core.Lin

/-!
# Proofs: the pipelining server

The pipelining server of a machine refines its atomic-handler server, and its responses on each
connection come in request order.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Core

open Silmaril.Servers

variable {A : Sig}

theorem steps_mono {S E : Type} {step step' : S → E → S → Prop}
    (h : ∀ x e y, step x e y → step' x e y) {x y : S} {l : List E} (hs : Steps step x l y) :
    Steps step' x l y := by
  induction hs with
  | nil => exact .nil _
  | cons hst _ ih => exact .cons (h _ _ _ hst) ih

theorem steps_append {S E : Type} {step : S → E → S → Prop} :
    ∀ {x y : S} {l₁ l₂ : List E}, Steps step x (l₁ ++ l₂) y →
      ∃ z, Steps step x l₁ z ∧ Steps step z l₂ y
  | _, _, [], _, hs => ⟨_, .nil _, hs⟩
  | _, _, _ :: l₁, _, hs => by
    cases hs with
    | cons hst hs =>
      obtain ⟨z, h₁, h₂⟩ := steps_append hs
      exact ⟨z, .cons hst h₁, h₂⟩

theorem erase_eq_append_cons {e : Event A} {post : Trace A} :
    ∀ {t' : List (LEvent A)} {pre : Trace A}, LEvent.erase t' = pre ++ e :: post →
      ∃ t₁ t₂, t' = t₁ ++ .ev e :: t₂ ∧ LEvent.erase t₁ = pre
  | [], pre, h => by cases pre <;> simp [LEvent.erase] at h
  | .lin i r s :: t', pre, h => by
    obtain ⟨t₁, t₂, rfl, h₁⟩ := erase_eq_append_cons (t' := t') h
    exact ⟨.lin i r s :: t₁, t₂, rfl, h₁⟩
  | .ev e' :: t', pre, h => by
    have h : e' :: LEvent.erase t' = pre ++ e :: post := h
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact ⟨[], t', rfl, rfl⟩
    | cons p pre =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, hh⟩ := h
      obtain ⟨t₁, t₂, rfl, h₁⟩ := erase_eq_append_cons (t' := t') hh
      exact ⟨.ev e' :: t₁, t₂, rfl, by simp [LEvent.erase] at h₁ ⊢; exact h₁⟩

theorem req_mono {m m' : LMon A} {t' : List (LEvent A)} (hs : Steps LMon.Step m t' m') :
    ∀ i, m.req i ≠ none → m'.req i ≠ none := by
  induction hs with
  | nil => exact fun _ h => h
  | @cons m₁ m₂ _ _ _ hst _ ih =>
    intro i hi
    apply ih
    cases hst with
    | @recv j r _ =>
      by_cases hij : i = j
      · subst hij; simp
      · simpa [hij] using hi
    | lin => exact hi
    | send => exact hi

theorem req_of_recv {m m' : LMon A} {t' : List (LEvent A)} (hs : Steps LMon.Step m t' m') :
    ∀ i r, Event.recv i r ∈ LEvent.erase t' → m'.req i ≠ none := by
  induction hs with
  | nil => exact fun _ _ h => nomatch h
  | @cons m₁ m₂ _ _ es hst hs ih =>
    intro i r hi
    cases hst with
    | @recv j r' _ =>
      rcases List.mem_cons.1 hi with hi | hi
      · cases hi
        exact req_mono hs i (by simp)
      · exact ih i r hi
    | lin => exact ih i r hi
    | send =>
      rcases List.mem_cons.1 hi with hi | hi
      · cases hi
      · exact ih i r hi

theorem answered_of_steps {m m' : LMon A} {t' : List (LEvent A)} (hs : Steps LMon.Step m t' m') :
    ∀ i, m'.req i ≠ none → m'.pending i = none → m'.ready i = none →
      (∃ s, Event.send i s ∈ LEvent.erase t') ∨
      (m.req i ≠ none ∧ m.pending i = none ∧ m.ready i = none) := by
  induction hs with
  | nil => exact fun i h₁ h₂ h₃ => Or.inr ⟨h₁, h₂, h₃⟩
  | @cons m₁ m₂ _ _ es hst _ ih =>
    intro i h₁ h₂ h₃
    rcases ih i h₁ h₂ h₃ with ⟨s, hs⟩ | ⟨g₁, g₂, g₃⟩
    · cases hst with
      | recv => exact Or.inl ⟨s, List.mem_cons_of_mem _ hs⟩
      | lin => exact Or.inl ⟨s, hs⟩
      | send => exact Or.inl ⟨s, List.mem_cons_of_mem _ hs⟩
    · cases hst with
      | @recv j r _ =>
        by_cases hij : i = j
        · subst hij; simp at g₂
        · right; simpa [hij] using And.intro g₁ (And.intro g₂ g₃)
      | @lin j r s _ =>
        by_cases hij : i = j
        · subst hij; simp at g₃
        · right; simpa [hij] using And.intro g₁ (And.intro g₂ g₃)
      | @send j s _ =>
        by_cases hij : i = j
        · subst hij; exact Or.inl ⟨s, List.mem_cons.2 (Or.inl rfl)⟩
        · right; simpa [hij] using And.intro g₁ (And.intro g₂ g₃)

theorem pipeServer_le {σ : Type} (M : Machine A σ) (q₀ : σ) : M.pipeServer q₀ ≤ M.server q₀ :=
  fun _ ⟨t', fin, hs, he⟩ => ⟨t', fin, steps_mono (fun _ _ _ h => h.1) hs, he⟩

theorem pipeServer_inOrder {σ : Type} (M : Machine A σ) (q₀ : σ) :
    (M.pipeServer q₀).Sat Sen.inOrder := by
  rintro t ⟨t', fin, hs, rfl⟩ pre post j s ht i r hr hc hlt
  obtain ⟨t₁, t₂, rfl, h₁⟩ := erase_eq_append_cons ht
  obtain ⟨z, hz, hz'⟩ := steps_append hs
  cases hz' with
  | cons hst _ =>
    have hE := hst.2 j s rfl
    have hL := (server_steps (steps_mono (fun _ _ _ h => h.1) hz)).1
    subst h₁
    have hreq := req_of_recv hL i r hr
    obtain ⟨hp, hrd⟩ := hE i hc hlt hreq
    rcases answered_of_steps hL i hreq hp hrd with h | ⟨h, _⟩
    · exact h
    · exact absurd rfl h

end Silmaril.Proofs.Servers.Core
