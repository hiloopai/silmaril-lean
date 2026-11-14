module

public import Silmaril.Servers.Reuse.Defs

/-!
# Instance reuse: proofs

For `Silmaril.Servers.Reuse.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Reuse

open Silmaril.Net.Http Silmaril.Servers.Reuse

variable {σ : Type} {O : Origin σ} {s₀ : σ}

theorem seq_pooled {s : σ} {l : Log} (h : Seq O s l) (a b : List σ) :
    Pooled O s₀ (a ++ s :: b) l := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .reuse hs ih

theorem seq_hostRuns {l : Log} (h : Seq O s₀ l) : HostRuns O s₀ l := by
  cases h with
  | nil => exact .nil _
  | cons hs hl => exact .new hs (seq_pooled (s₀ := s₀) hl [] [])

theorem fresh_pooled {l : Log} (pool : List σ) (h : Fresh O s₀ l) : Pooled O s₀ pool l := by
  induction l generalizing pool with
  | nil => exact .nil _
  | cons p l ih =>
    obtain ⟨r, resp⟩ := p
    obtain ⟨s', hs⟩ := h (r, resp) List.mem_cons_self
    exact .new hs (ih _ fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem pooled_of_inv (Inv : σ → Prop) (H : Request → Response → Prop) (h0 : Inv s₀)
    (hstep : ∀ s r resp s', Inv s → O s r resp s' → Inv s')
    (hH : ∀ s r resp s', Inv s → O s r resp s' → H r resp)
    {pool : List σ} {l : Log} (hp : Pooled O s₀ pool l) (hpool : ∀ s ∈ pool, Inv s) :
    ∀ p ∈ l, H p.1 p.2 := by
  induction hp with
  | nil => simp
  | @reuse a b s s' r resp l hs _ ih =>
    have hi : Inv s := hpool s (by simp)
    have hi' : Inv s' := hstep _ _ _ _ hi hs
    have hpool' : ∀ x ∈ a ++ s' :: b, Inv x := by
      intro x hx
      simp only [List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | hx
      · exact hpool x (by simp [hx])
      · exact hi'
      · exact hpool x (by simp [hx])
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hH _ _ _ _ hi hs
    · exact ih hpool' p hp
  | @new pool s' r resp l hs _ ih =>
    have hi' : Inv s' := hstep _ _ _ _ h0 hs
    have hpool' : ∀ x ∈ s' :: pool, Inv x := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hi'
      · exact hpool x hx
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hH _ _ _ _ h0 hs
    · exact ih hpool' p hp

theorem hostRuns_of_inv (Inv : σ → Prop) (H : Request → Response → Prop) (h0 : Inv s₀)
    (hstep : ∀ s r resp s', Inv s → O s r resp s' → Inv s')
    (hH : ∀ s r resp s', Inv s → O s r resp s' → H r resp)
    {l : Log} (hl : HostRuns O s₀ l) : ∀ p ∈ l, H p.1 p.2 :=
  pooled_of_inv Inv H h0 hstep hH hl (by simp)

theorem countResponse_one_ne_zero : countResponse 1 ≠ countResponse 0 := by decide

theorem counter_seq_iff {n : Nat} {r₁ r₂ : Request} {a b : Response} :
    Seq counter n [(r₁, a), (r₂, b)] ↔ a = countResponse n ∧ b = countResponse (n + 1) := by
  constructor
  · rintro (_ | ⟨h₁, _ | ⟨h₂, _⟩⟩)
    simp only [counter, Origin.ofFun, Prod.mk.injEq] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := h₁
    obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .cons (s' := n + 1) rfl (.cons (s' := n + 2) rfl (.nil _))

theorem counter_fresh_iff {r₁ r₂ : Request} {a b : Response} :
    Fresh counter 0 [(r₁, a), (r₂, b)] ↔ a = countResponse 0 ∧ b = countResponse 0 := by
  simp [Fresh, counter, Origin.ofFun, eq_comm]

end Silmaril.Proofs.Servers.Reuse
