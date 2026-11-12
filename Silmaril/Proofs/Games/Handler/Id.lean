module

public import Silmaril.Games.Handler.Defs
public import Silmaril.Games.LTS.Thms

/-!
# The forwarding handler is copycat: proofs

Proofs for `Silmaril.Games.Handler.Thms`: the traces of `Handler.id E` from the
idle state are exactly the prefixes of the copycat plays `Ev.double w`.
-/

public section

namespace Silmaril.Proofs.Games.Handler

open Silmaril.Games

universe u

variable {E : Sig.{u}}

theorem run_double {w : List (Ev E)} (hw : Ev.Alternating w) :
    ∃ y, (Handler.id E).toReduction.toLTS.Run (Handler.id E).toReduction.toLTS.init (Ev.double w) y := by
  induction hw with
  | nil => exact ⟨_, .nil _⟩
  | ask m =>
    simp only [Ev.double_cons, Ev.copy_ask, Ev.double_nil, List.cons_append, List.nil_append]
    exact ⟨_, .vis (Reduction.Step.ask m) (.vis (Reduction.Step.call rfl) (.nil _))⟩
  | cons m n _ ih =>
    obtain ⟨y, hy⟩ := ih
    simp only [Ev.double_cons, Ev.copy_ask, Ev.copy_ans, List.cons_append, List.nil_append]
    exact ⟨y, .vis (Reduction.Step.ask m) (.vis (Reduction.Step.call rfl)
      (.vis (Reduction.Step.resume _ _ _ n) (.vis (Reduction.Step.ret rfl) hy)))⟩

theorem run_cons {F : Sig.{u}} {h : Handler E F} {x z : h.toReduction.toLTS.State}
    {o : Move E F} {s : List (Move E F)} (hr : h.toReduction.toLTS.Run x (o :: s) z) :
    ∃ y, Reduction.Step h.toReduction x (some o) y ∧ h.toReduction.toLTS.Run y s z := by
  cases hr with
  | tau hs _ => cases hs with | tau hc => exact (hc : False).elim
  | vis hs hr => exact ⟨_, hs, hr⟩

/-! ### The four phases of one forwarded exchange -/

private theorem id_run_idle {o : Move E E} {p : List (Move E E)}
    {y : (Handler.id E).toReduction.toLTS.State}
    (h : (Handler.id E).toReduction.toLTS.Run .idle (o :: p) y) :
    ∃ q, o = .inr (.ask q) ∧
      (Handler.id E).toReduction.toLTS.Run (.run q (Prog.lift q)) p y := by
  obtain ⟨y₁, hs, h₁⟩ := run_cons h
  cases hs with
  | ask q => exact ⟨q, rfl, h₁⟩

private theorem id_run_asked {q : E.Op} {o : Move E E} {p : List (Move E E)}
    {y : (Handler.id E).toReduction.toLTS.State}
    (h : (Handler.id E).toReduction.toLTS.Run (.run q (Prog.lift q)) (o :: p) y) :
    o = .inl (.ask q) ∧ (Handler.id E).toReduction.toLTS.Run (.wait q q Prog.pure) p y := by
  obtain ⟨y₁, hs, h₁⟩ := run_cons h
  cases hs with
  | ret hc => cases hc
  | call hc => cases hc; exact ⟨rfl, h₁⟩

private theorem id_run_called {q : E.Op} {o : Move E E} {p : List (Move E E)}
    {y : (Handler.id E).toReduction.toLTS.State}
    (h : (Handler.id E).toReduction.toLTS.Run (.wait q q Prog.pure) (o :: p) y) :
    ∃ n, o = .inl (.ans q n) ∧
      (Handler.id E).toReduction.toLTS.Run (.run q (Prog.pure n)) p y := by
  obtain ⟨y₁, hs, h₁⟩ := run_cons h
  cases hs with
  | resume _ _ _ n => exact ⟨n, rfl, h₁⟩

private theorem id_run_answered {q : E.Op} {n : E.Ar q} {o : Move E E} {p : List (Move E E)}
    {y : (Handler.id E).toReduction.toLTS.State}
    (h : (Handler.id E).toReduction.toLTS.Run (.run q (Prog.pure n)) (o :: p) y) :
    o = .inr (.ans q n) ∧ (Handler.id E).toReduction.toLTS.Run .idle p y := by
  obtain ⟨y₁, hs, h₁⟩ := run_cons h
  cases hs with
  | call hc => cases hc
  | ret hc => cases hc; exact ⟨rfl, h₁⟩

theorem double_of_run {p : List (Move E E)} {y : (Handler.id E).toReduction.toLTS.State}
    (h : (Handler.id E).toReduction.toLTS.Run (Handler.id E).toReduction.toLTS.init p y) :
    ∃ w, Ev.Alternating w ∧ p <+: Ev.double w := by
  induction hn : p.length using Nat.strong_induction_on generalizing p y with
  | _ len ih =>
  rcases p with _ | ⟨o₁, p₁⟩
  · exact ⟨[], .nil, List.prefix_refl _⟩
  obtain ⟨q, ho₁, h₁⟩ := id_run_idle h
  rw [ho₁]
  rcases p₁ with _ | ⟨o₂, p₂⟩
  · exact ⟨[.ask q], .ask q, by simp⟩
  obtain ⟨ho₂, h₂⟩ := id_run_asked h₁
  rw [ho₂]
  rcases p₂ with _ | ⟨o₃, p₃⟩
  · exact ⟨[.ask q], .ask q, by simp⟩
  obtain ⟨n, ho₃, h₃⟩ := id_run_called h₂
  rw [ho₃]
  rcases p₃ with _ | ⟨o₄, p₄⟩
  · exact ⟨[.ask q, .ans q n], .cons q n .nil, by simp⟩
  obtain ⟨ho₄, h₄⟩ := id_run_answered h₃
  rw [ho₄]
  have hlen : p₄.length < len := by rw [← hn]; simp only [List.length_cons]; omega
  obtain ⟨w, hw, hp⟩ : ∃ w, Ev.Alternating w ∧ p₄ <+: Ev.double w := ih _ hlen h₄ rfl
  exact ⟨_, .cons q n hw, by simpa using hp⟩

theorem mem_ofHandler_id {p : List (Move E E)} :
    (∃ y, (Handler.id E).toReduction.toLTS.Run (Handler.id E).toReduction.toLTS.init p y) ↔
      ∃ w, Ev.Alternating w ∧ p <+: Ev.double w := by
  constructor
  · rintro ⟨y, h⟩
    exact double_of_run h
  · rintro ⟨w, hw, hp⟩
    exact LTS.traces_of_prefix (run_double hw) hp

end Silmaril.Proofs.Games.Handler
