module

public import Silmaril.Wasm.Logic.Instr.Thms
public import Silmaril.Wasm.Logic.Total.Defs

/-!
# Total correctness: basic facts and sequencing

* `TSafe.post_mono` (consequence), `TSafe.exit_of_stuck`, `TSafe.step_inv`,
  `TSafe.trap_post`, `TSafe.throw_post`;
* `TSafe.seq`: if `c₁` is totally correct with `seqPostT c₂ Q`, then `c₁ ++ c₂`
  is totally correct with `Q`. By induction on the total-correctness derivation
  of `c₁`; the steps of `c₁ ++ c₂` are classified by silmaril-lean's
  `Sim.Step.split_head`, as for `Hoare.Safe.seq`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Basic facts -/

/-- **Consequence** for total correctness. -/
theorem TSafe.post_mono {Q Q' : Post H} {c : Config H} (h : TSafe P host Q c)
    (hQ : ∀ s f o, Q s f o → Q' s f o) : TSafe P host Q' c := by
  induction h with
  | exit o he hq => exact .exit o he (hQ _ _ _ hq)
  | step hp _ ih => exact .step hp ih

/-- A totally correct configuration that cannot step has exited. -/
theorem TSafe.exit_of_stuck {Q : Post H} {c : Config H} (h : TSafe P host Q c)
    (hn : ∀ c', ¬ Step P host c c') : ∃ o, Exits o c.code ∧ Q c.store c.frame o := by
  cases h with
  | exit o he hq => exact ⟨o, he, hq⟩
  | step hp _ => exact (hn _ hp.choose_spec).elim

/-- Total correctness is kept by a step. -/
theorem TSafe.step_inv {Q : Post H} {c c' : Config H} (h : TSafe P host Q c)
    (hst : Step P host c c') : TSafe P host Q c' := by
  cases h with
  | exit o he hq =>
    rcases c with ⟨s, f, code⟩
    rcases c' with ⟨s', f', code'⟩
    obtain ⟨rfl, rfl, he', -⟩ := he.step hst
    exact .exit o he' hq
  | step _ hs => exact hs c' hst

/-- A trap inside a sequence satisfies the trap postcondition. -/
theorem TSafe.trap_post {Q : Post H} {s : Store H} {f : Frame} {vs : List Val} {es : List Admin}
    (h : TSafe P host Q ⟨s, f, vals vs ++ .trap :: es⟩) : Q s f .trap := by
  by_cases hne : vs ≠ [] ∨ es ≠ []
  · have hst : Step P host ⟨s, f, vals vs ++ .trap :: es⟩ ⟨s, f, [.trap]⟩ := by
      simpa using Step.trapInstrs (P := P) (host := host) (s := s) (f := f) hne
    obtain ⟨o, he, hq⟩ := (h.step_inv hst).exit_of_stuck fun _ => not_step_trap
    exact exits_trap_inv (vs := []) (rest := []) he ▸ hq
  · have hv : vs = [] ∧ es = [] := by simpa only [ne_eq, not_or, not_not] using hne
    have h' : TSafe P host Q ⟨s, f, [.trap]⟩ := by simpa [hv.1, hv.2] using h
    obtain ⟨o, he, hq⟩ := h'.exit_of_stuck fun _ => not_step_trap
    exact exits_trap_inv (vs := []) (rest := []) he ▸ hq

/-- An exception inside a sequence satisfies the throw postcondition. -/
theorem TSafe.throw_post {Q : Post H} {s : Store H} {f : Frame} {vs : List Val} {a : Nat}
    {es : List Admin} (h : TSafe P host Q ⟨s, f, vals vs ++ throwing a ++ es⟩) :
    Q s f (.throw a) := by
  by_cases hne : vs ≠ [] ∨ es ≠ []
  · have hst : Step P host ⟨s, f, vals vs ++ throwing a ++ es⟩ ⟨s, f, throwing a⟩ :=
      Step.throwRefInstrs hne
    obtain ⟨o, he, hq⟩ := (h.step_inv hst).exit_of_stuck fun _ => not_step_throwing
    exact exits_throw_inv (vs := []) (rest := []) (by simpa using he) ▸ hq
  · have hv : vs = [] ∧ es = [] := by simpa only [ne_eq, not_or, not_not] using hne
    have h' : TSafe P host Q ⟨s, f, throwing a⟩ := by simpa [hv.1, hv.2] using h
    obtain ⟨o, he, hq⟩ := h'.exit_of_stuck fun _ => not_step_throwing
    exact exits_throw_inv (vs := []) (rest := []) (by simpa using he) ▸ hq

/-! ## Sequencing -/

section Seq

variable {c₂ : List Admin} {Q : Post H}

/-- An exit of `c₁` in `c₁ ++ c₂`. -/
theorem tseq_exit {s : Store H} {f : Frame} {c₁ : List Admin} {o : Outcome} (he : Exits o c₁)
    (hq : seqPostT P host c₂ Q s f o) : TSafe P host Q ⟨s, f, c₁ ++ c₂⟩ := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · rw [show c₁ = vals vs from he]
    exact hq
  all_goals exact .exit _ (he.append (fun _ h => Outcome.noConfusion h) c₂) hq

/-- The steps of `c₁ ++ c₂` when `c₁` steps. -/
theorem tseq_step {s : Store H} {f : Frame} {c₁ : List Admin} {c' : Config H}
    (h : TSafe P host (seqPostT P host c₂ Q) ⟨s, f, c₁⟩)
    (ih : ∀ s' f' c₁', Step P host ⟨s, f, c₁⟩ ⟨s', f', c₁'⟩ → TSafe P host Q ⟨s', f', c₁' ++ c₂⟩)
    (hna : c₁.all Admin.isVal = false) (hst : Step P host ⟨s, f, c₁ ++ c₂⟩ c') :
    TSafe P host Q c' := by
  obtain ⟨vs, a, es, ha, rfl⟩ := Sim.exists_head_of_not_all hna
  have hst' : Step P host ⟨s, f, vals vs ++ a :: (es ++ c₂)⟩ c' := by simpa using hst
  rcases c' with ⟨s', f', es'⟩
  rcases Sim.Step.split_head ha hst' with ⟨ws, us, is', rfl, hu, rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, r, r', rfl, -, -, rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, x, r, r', rfl, -, -, rfl⟩
  · have h₁ : Step P host ⟨s, f, vals (ws ++ us) ++ a :: es⟩ ⟨s', f', vals ws ++ is' ++ es⟩ := by
      simpa using Sim.Step.vals_left (Sim.Step.append_right hu es) ws
    simpa using ih s' f' _ h₁
  · have hq : Q s' f' .trap := TSafe.trap_post (Q := seqPostT P host c₂ Q) h
    exact .exit .trap ⟨ws, r', by simp⟩ hq
  · have h' : TSafe P host (seqPostT P host c₂ Q) ⟨s', f', vals (ws ++ us) ++ throwing x ++ es⟩ := by
      simpa [vals, Val.toAdmin] using h
    have hq : Q s' f' (.throw x) := TSafe.throw_post (Q := seqPostT P host c₂ Q) h'
    exact .exit (.throw x) ⟨ws, r', rfl⟩ hq

/-- **Sequencing** for total correctness. -/
theorem TSafe.seq : ∀ {c : Config H}, TSafe P host (seqPostT P host c₂ Q) c →
    TSafe P host Q ⟨c.store, c.frame, c.code ++ c₂⟩ := by
  intro c h
  induction h with
  | exit o he hq => exact tseq_exit he hq
  | @step c hp hs ih =>
    obtain ⟨c', hc'⟩ := hp
    refine .step ⟨_, Sim.Step.append_right hc' c₂⟩ fun c'' hst => ?_
    exact tseq_step (.step ⟨c', hc'⟩ hs) (fun s' f' c₁' h₁ => ih _ h₁) hc'.not_all_isVal hst

end Seq

/-- **Sequencing** for `TWP`. -/
theorem TWP.seq {s : Store H} {f : Frame} {c₁ c₂ : List Admin} {Q : Post H}
    (h : TWP P host s f c₁ (seqPostT P host c₂ Q)) : TWP P host s f (c₁ ++ c₂) Q :=
  TSafe.seq h

end Silmaril.Wasm.Logic.Hoare
