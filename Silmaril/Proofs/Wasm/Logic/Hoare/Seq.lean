module

public import Silmaril.Proofs.Wasm.Logic.Hoare.Basic

/-!
# The every-run logic: sequencing

`Safe.seq` is the `[seq]`/bind rule: if `c₁` is safe with the postcondition
`seqPostK c₂ Q k` (on falling through, `c₂` is safe for `k` steps), then
`c₁ ++ c₂` is safe with `Q`, for at most `k` steps. A step of `c₁ ++ c₂` is a step
of `c₁` (`Sim.Step.split_head`), or a trap or an exception in `c₁` cutting into
`c₂`; in the latter case the trap or throw postcondition is read off the safety
of `c₁` (`Safe.trap_post`, `Safe.throw_post`).

A Silmaril addition, built on silmaril-lean's `Sim.Step.split_head`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Reading the trap and throw postconditions -/

/-- A trap inside a sequence that is safe for two steps satisfies the trap
postcondition. -/
theorem Safe.trap_post {Q : Post H} {m : Nat} {s : Store H} {f : Frame} {vs : List Val}
    {es : List Admin} (h : Safe P host Q (m + 2) ⟨s, f, vals vs ++ .trap :: es⟩) :
    Q s f .trap := by
  rcases h with ⟨o, he, hq⟩ | ⟨⟨c', hc'⟩, hs⟩
  · exact exits_trap_inv he ▸ hq
  · by_cases hne : vs ≠ [] ∨ es ≠ []
    · have hst : Step P host ⟨s, f, vals vs ++ .trap :: es⟩ ⟨s, f, [.trap]⟩ := by
        simpa using Step.trapInstrs (P := P) (host := host) (s := s) (f := f) hne
      rcases hs _ hst with ⟨o, he, hq⟩ | ⟨⟨c'', hc''⟩, -⟩
      · exact exits_trap_inv (vs := []) (rest := []) he ▸ hq
      · exact (not_step_trap hc'').elim
    · have hv : vs = [] ∧ es = [] := by simpa only [ne_eq, not_or, not_not] using hne
      have hc : Step P host ⟨s, f, [.trap]⟩ c' := by simpa [hv.1, hv.2] using hc'
      exact (not_step_trap hc).elim

/-- An exception inside a sequence that is safe for two steps satisfies the throw
postcondition. -/
theorem Safe.throw_post {Q : Post H} {m : Nat} {s : Store H} {f : Frame} {vs : List Val}
    {a : Nat} {es : List Admin} (h : Safe P host Q (m + 2) ⟨s, f, vals vs ++ throwing a ++ es⟩) :
    Q s f (.throw a) := by
  rcases h with ⟨o, he, hq⟩ | ⟨⟨c', hc'⟩, hs⟩
  · exact exits_throw_inv he ▸ hq
  · by_cases hne : vs ≠ [] ∨ es ≠ []
    · have hst : Step P host ⟨s, f, vals vs ++ throwing a ++ es⟩ ⟨s, f, throwing a⟩ :=
        Step.throwRefInstrs hne
      rcases hs _ hst with ⟨o, he, hq⟩ | ⟨⟨c'', hc''⟩, -⟩
      · exact exits_throw_inv (vs := []) (rest := []) (by simpa using he) ▸ hq
      · exact (not_step_throwing hc'').elim
    · have hv : vs = [] ∧ es = [] := by simpa only [ne_eq, not_or, not_not] using hne
      have hc : Step P host ⟨s, f, throwing a⟩ c' := by simpa [hv.1, hv.2] using hc'
      exact (not_step_throwing hc).elim

/-! ## Sequencing -/

section Seq

variable {c₂ : List Admin} {Q : Post H} {k : Nat}

/-- An exit of `c₁` in `c₁ ++ c₂`. -/
theorem seq_exit {n : Nat} {s : Store H} {f : Frame} {c₁ : List Admin} {o : Outcome}
    (hn : n ≤ k) (he : Exits o c₁) (hq : seqPostK P host c₂ Q k s f o) :
    Safe P host Q n ⟨s, f, c₁ ++ c₂⟩ := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · rw [show c₁ = vals vs from he]
    exact Safe.mono hn hq
  all_goals exact Safe.of_exits (he.append (fun _ h => Outcome.noConfusion h) c₂) hq

/-- A trap of `c₁` cutting into `c₂`. -/
theorem seq_cut_trap {n : Nat} {s : Store H} {f : Frame} {vs ws : List Val}
    {es r' : List Admin}
    (h : Safe P host (seqPostK P host c₂ Q k) (n + 1) ⟨s, f, vals vs ++ .trap :: es⟩) :
    Safe P host Q n ⟨s, f, vals ws ++ [.trap] ++ r'⟩ := by
  cases n with
  | zero => trivial
  | succ m =>
    have hq : Q s f .trap := Safe.trap_post (Q := seqPostK P host c₂ Q k) h
    exact Safe.of_exits (o := .trap) ⟨ws, r', by simp⟩ hq

/-- An exception of `c₁` cutting into `c₂`. -/
theorem seq_cut_throw {n : Nat} {s : Store H} {f : Frame} {vs ws : List Val} {a : Nat}
    {es r' : List Admin}
    (h : Safe P host (seqPostK P host c₂ Q k) (n + 1) ⟨s, f, vals vs ++ throwing a ++ es⟩) :
    Safe P host Q n ⟨s, f, vals ws ++ throwing a ++ r'⟩ := by
  cases n with
  | zero => trivial
  | succ m =>
    have hq : Q s f (.throw a) := Safe.throw_post (Q := seqPostK P host c₂ Q k) h
    exact Safe.of_exits (o := .throw a) ⟨ws, r', rfl⟩ hq

/-- One step of `c₁ ++ c₂`, given that `c₁` steps and the statement for `n`. -/
theorem seq_step {n : Nat} {s : Store H} {f : Frame} {c₁ : List Admin} {c' : Config H}
    (ih : ∀ s f c₁, Safe P host (seqPostK P host c₂ Q k) n ⟨s, f, c₁⟩ →
      Safe P host Q n ⟨s, f, c₁ ++ c₂⟩)
    (h : Safe P host (seqPostK P host c₂ Q k) (n + 1) ⟨s, f, c₁⟩)
    (hs : ∀ c', Step P host ⟨s, f, c₁⟩ c' → Safe P host (seqPostK P host c₂ Q k) n c')
    (hna : c₁.all Admin.isVal = false) (hst : Step P host ⟨s, f, c₁ ++ c₂⟩ c') :
    Safe P host Q n c' := by
  obtain ⟨vs, a, es, ha, rfl⟩ := Sim.exists_head_of_not_all hna
  have hst' : Step P host ⟨s, f, vals vs ++ a :: (es ++ c₂)⟩ c' := by simpa using hst
  rcases c' with ⟨s', f', es'⟩
  rcases Sim.Step.split_head ha hst' with ⟨ws, us, is', rfl, hu, rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, r, r', rfl, -, -, rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, x, r, r', rfl, -, -, rfl⟩
  · have h₁ : Step P host ⟨s, f, vals (ws ++ us) ++ a :: es⟩ ⟨s', f', vals ws ++ is' ++ es⟩ := by
      simpa using Sim.Step.vals_left (Sim.Step.append_right hu es) ws
    simpa using ih s' f' _ (hs _ h₁)
  · exact seq_cut_trap h
  · have h' : Safe P host (seqPostK P host c₂ Q k) (n + 1)
        ⟨s', f', vals (ws ++ us) ++ throwing x ++ es⟩ := by
      simpa [vals, Val.toAdmin] using h
    exact seq_cut_throw h'

/-- **Sequencing** (`[seq]`): `c₁ ++ c₂` is safe for `n ≤ k` steps if `c₁` is,
with `c₂` safe for `k` steps after `c₁` falls through. -/
theorem Safe.seq : ∀ {n : Nat} {s : Store H} {f : Frame} {c₁ : List Admin}, n ≤ k →
    Safe P host (seqPostK P host c₂ Q k) n ⟨s, f, c₁⟩ → Safe P host Q n ⟨s, f, c₁ ++ c₂⟩
  | 0, _, _, _, _, _ => trivial
  | n + 1, s, f, c₁, hn, h => by
    rcases h with ⟨o, he, hq⟩ | ⟨⟨c', hc'⟩, hs⟩
    · exact seq_exit hn he hq
    · refine Safe.of_step ⟨_, Sim.Step.append_right hc' c₂⟩ fun c'' hst => ?_
      exact seq_step (fun s f c₁ => Safe.seq (by omega)) (Or.inr ⟨⟨c', hc'⟩, hs⟩) hs
        hc'.not_all_isVal hst

end Seq

/-- **Sequencing** for every-run weakest preconditions. -/
theorem HWP.seq {s : Store H} {f : Frame} {c₁ c₂ : List Admin} {Q : Post H}
    (h : HWP P host s f c₁ (seqPost P host c₂ Q)) : HWP P host s f (c₁ ++ c₂) Q :=
  fun n => Safe.seq (k := n) le_rfl ((h n).post_mono fun _ _ _ => seqPost.toK n)

end Silmaril.Wasm.Logic.Hoare
