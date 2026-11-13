module

public import Silmaril.Wasm.Unified.Component.Core.Thms

/-!
# The trivial wrapper adds no answers

`Silmaril.Wasm.Unified.Component.obs_core_subset_wrap` shows that wrapping a core module in the
trivial component (`Silmaril.Wasm.Institution.Components.wrap`) keeps its answers. This module
proves the converse and so the exact answers of the wrapper:

* `handler_run_cons`: a run of a handler's transition system that starts with a move makes that
  move first (handlers have no internal steps);
* `two_of_lower_call`: a two-move play `ask q · ans q a` of `ofHandler h ⋙ τ` (the lower
  strategy a handler that calls below on every question) is a two-move play of `τ`: the upper
  strategy cannot call below without a visible lower move;
* `two_of_upper_call`, `two_of_upper_pure`: a two-move play of `σ ⋙ ofHandler h` at a question
  that `h` forwards (`h q = call m (pure ∘ g)`) comes from a two-move play `ask m · ans m r` of
  `σ` with `a = g r`; at a question that `h` answers at once (`h q = pure a₀`), `a = a₀`;
* **`obs_wrap`**: the answers of the trivial wrapper of `m` to a first call of export `j` are the
  answers of `m`, and, for `j` beyond the exports of `m`, a trap (`none`): `widenH` answers an
  out-of-range export with `none`;
* **`obs_wrap_eq`**, **`obs_wrap_single`**: for an export of `m` the wrapper answers exactly as
  the core module; the one-export module of `c` wrapped answers export `0` with the observations
  of `c`.

New proofs (the Games inversions are small, local to this module).
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Component

open Silmaril.Wasm.Component Silmaril.Wasm.Unified
open Silmaril.Games (Strategy Sig Move Prog Reduction Zip)

/-! ## Two-move plays through handlers -/

section TwoMoveInv

variable {E F G : Sig.{0}}

/-- A run of a handler's transition system that starts with a move makes that move first. -/
theorem handler_run_cons {h : Silmaril.Games.Handler E F} {x z : h.toReduction.toLTS.State}
    {o : Move E F}
    {s : List (Move E F)} (hr : h.toReduction.toLTS.Run x (o :: s) z) :
    ∃ y, Reduction.Step h.toReduction x (some o) y ∧ h.toReduction.toLTS.Run y s z := by
  generalize ht : o :: s = t at hr
  cases hr with
  | nil => cases ht
  | tau hst _ =>
    cases hst with
    | tau hc => exact (hc : False).elim
  | vis hst hr' =>
    cases ht
    exact ⟨_, hst, hr'⟩

/-- A legal play does not start with a lower move. -/
theorem not_legal_inl {e : Silmaril.Games.Ev E} {t : List (Move E F)} :
    ¬ Silmaril.Games.Legal (.inl e :: t) := by
  rintro ⟨y, hp⟩
  cases hp with
  | cons hs _ => cases hs

/-- A legal play does not answer its question while a lower call is pending. -/
theorem not_legal_ask_call_ans {q : F.Op} {e : Silmaril.Games.Ev E} {a : F.Ar q}
    {t : List (Move E F)} :
    ¬ Silmaril.Games.Legal (.inr (.ask q) :: .inl e :: .inr (.ans q a) :: t) := by
  rintro ⟨y, hp⟩
  cases hp with
  | cons h₁ hp₁ =>
    cases h₁
    cases hp₁ with
    | cons h₂ hp₂ =>
      cases h₂
      cases hp₂ with
      | cons h₃ _ => cases h₃

section Runs

variable {h : Silmaril.Games.Handler E F}

/-- From `idle`, a handler run starts with a question. -/
theorem run_idle {z : h.toReduction.toLTS.State} {o : Move E F} {s : List (Move E F)}
    (hr : h.toReduction.toLTS.Run .idle (o :: s) z) :
    ∃ q, o = .inr (.ask q) ∧ h.toReduction.toLTS.Run (.run q (h q)) s z := by
  obtain ⟨y, hst, hr'⟩ := handler_run_cons hr
  cases hst with
  | ask q => exact ⟨q, rfl, hr'⟩

/-- A handler running `call m k` calls `m`. -/
theorem run_call {q : F.Op} {m : E.Op} {k : E.Ar m → Prog E (F.Ar q)}
    {z : h.toReduction.toLTS.State} {o : Move E F} {s : List (Move E F)}
    (hr : h.toReduction.toLTS.Run (.run q (.call m k)) (o :: s) z) :
    o = .inl (.ask m) ∧ h.toReduction.toLTS.Run (.wait q m k) s z := by
  obtain ⟨y, hst, hr'⟩ := handler_run_cons hr
  cases hst with
  | call hc =>
    cases hc
    exact ⟨rfl, hr'⟩
  | ret hd => cases hd

/-- A handler running `pure a` answers `a`. -/
theorem run_pure {q : F.Op} {a : F.Ar q} {z : h.toReduction.toLTS.State} {o : Move E F}
    {s : List (Move E F)} (hr : h.toReduction.toLTS.Run (.run q (.pure a)) (o :: s) z) :
    o = .inr (.ans q a) := by
  obtain ⟨y, hst, -⟩ := handler_run_cons hr
  cases hst with
  | call hc => cases hc
  | ret hd =>
    cases hd
    rfl

/-- A waiting handler receives an answer. -/
theorem run_wait {q : F.Op} {m : E.Op} {k : E.Ar m → Prog E (F.Ar q)}
    {z : h.toReduction.toLTS.State} {o : Move E F} {s : List (Move E F)}
    (hr : h.toReduction.toLTS.Run (.wait q m k) (o :: s) z) :
    ∃ n, o = .inl (.ans m n) ∧ h.toReduction.toLTS.Run (.run q (k n)) s z := by
  obtain ⟨y, hst, hr'⟩ := handler_run_cons hr
  cases hst with
  | resume _ _ _ n => exact ⟨n, rfl, hr'⟩

/-- Transport a run along an equation of states. -/
theorem run_congr {x x' z : h.toReduction.toLTS.State} {s : List (Move E F)} (hx : x = x')
    (hr : h.toReduction.toLTS.Run x s z) : h.toReduction.toLTS.Run x' s z :=
  hx ▸ hr

end Runs

/-- A handler that calls on every question gives no answer without a visible lower move. -/
theorem lower_no_answer {h : Silmaril.Games.Handler E F} (hcall : ∀ q, ∃ m k, h q = .call m k)
    {q : G.Op} {a : G.Ar q} {b : Silmaril.Games.Ev F}
    {s : List (Move E F)} {t : List (Move F G)}
    (hs : .inr b :: s ∈ Strategy.ofHandler h)
    (hleg : Silmaril.Games.Legal (.inr (.ask q) :: .inl b :: t)) :
    ¬ Zip s t ([.inr (.ans q a)] : List (Move E G)) := by
  intro hz
  cases hz with
  | right c _ => exact not_legal_ask_call_ans hleg
  | sync b' _ =>
    obtain ⟨y, hr⟩ := Strategy.mem_ofHandler.mp hs
    obtain ⟨m₀, -, hr₁⟩ := run_idle hr
    obtain ⟨m, k, hmk⟩ := hcall m₀
    have hr₁' := run_congr (congrArg (Reduction.State.run (R := h.toReduction) m₀) hmk) hr₁
    exact absurd (run_call hr₁').1 (by intro h'; cases h')

/-- **The lower handler calls on every question**: a two-move play of the composite is a
two-move play of the upper strategy. -/
theorem two_of_lower_call {h : Silmaril.Games.Handler E F} (hcall : ∀ q, ∃ m k, h q = .call m k)
    {τ : Strategy F G} {q : G.Op} {a : G.Ar q}
    (hp : ([.inr (.ask q), .inr (.ans q a)] : List (Move E G)) ∈
      (Strategy.ofHandler h).comp τ) :
    ([.inr (.ask q), .inr (.ans q a)] : List (Move F G)) ∈ τ := by
  obtain ⟨s, hs, t, ht, hz⟩ := hp
  cases hz with
  | sync b _ => exact absurd (τ.legal ht) not_legal_inl
  | right c hz₁ =>
    cases hz₁ with
    | right c' _ => exact τ.of_prefix ht ⟨_, rfl⟩
    | sync b hz₂ => exact absurd hz₂ (lower_no_answer hcall hs (τ.legal ht))

/-- After the forwarded question, a two-move play of the composite comes from a two-move play
of the lower strategy. -/
theorem upper_call_tail {σ : Strategy E F} {h : Silmaril.Games.Handler F G} {q : G.Op} {m : F.Op}
    {g : F.Ar m → G.Ar q} {a : G.Ar q} {s : List (Move E F)} {t : List (Move F G)}
    {y : h.toReduction.toLTS.State} (hs : s ∈ σ)
    (hr : h.toReduction.toLTS.Run (.run q (.call m fun r => .pure (g r))) t y)
    (hz : Zip s t ([.inr (.ans q a)] : List (Move E G))) :
    ∃ r, ([.inr (.ask m), .inr (.ans m r)] : List (Move E F)) ∈ σ ∧ a = g r := by
  cases hz with
  | right c _ => exact absurd (run_call hr).1 (by intro h'; cases h')
  | sync b hz₂ =>
    show ∃ r, ([.inr (.ask m), .inr (.ans m r)] : List (Move E F)) ∈ σ ∧ a = g r
    obtain ⟨hb, hr₂⟩ := run_call hr
    cases hb
    cases hz₂ with
    | right c _ => exact absurd (run_wait hr₂) (by rintro ⟨_, h', _⟩; cases h')
    | sync b' hz₃ =>
      show ∃ r, ([.inr (.ask m), .inr (.ans m r)] : List (Move E F)) ∈ σ ∧ a = g r
      obtain ⟨n, hb', hr₃⟩ := run_wait hr₂
      cases hb'
      cases hz₃ with
      | right c _ =>
        have ha : (Sum.inr (.ans q a) : Move F G) = .inr (.ans q (g n)) := run_pure hr₃
        cases ha
        exact ⟨n, σ.of_prefix hs ⟨_, rfl⟩, rfl⟩
      | sync b'' _ => exact absurd (run_pure hr₃) (by intro h'; cases h')

/-- **The upper handler forwards the question**: a two-move play of the composite comes from a
two-move play of the lower strategy. -/
theorem two_of_upper_call {σ : Strategy E F} {h : Silmaril.Games.Handler F G} {q : G.Op}
    {m : F.Op} {g : F.Ar m → G.Ar q} (hq : h q = .call m fun r => .pure (g r)) {a : G.Ar q}
    (hp : ([.inr (.ask q), .inr (.ans q a)] : List (Move E G)) ∈
      σ.comp (Strategy.ofHandler h)) :
    ∃ r, ([.inr (.ask m), .inr (.ans m r)] : List (Move E F)) ∈ σ ∧ a = g r := by
  obtain ⟨s, hs, t, ht, hz⟩ := hp
  obtain ⟨y, hr⟩ := Strategy.mem_ofHandler.mp ht
  cases hz with
  | sync b _ => exact absurd (run_idle hr) (by rintro ⟨_, h', _⟩; cases h')
  | right c hz₁ =>
    obtain ⟨q₀, hq₀, hr₁⟩ := run_idle hr
    cases hq₀
    exact upper_call_tail hs (run_congr (congrArg (Reduction.State.run (R := h.toReduction) q) hq)
      hr₁) hz₁

/-- **The upper handler answers at once**: a two-move play of the composite carries that
answer. -/
theorem two_of_upper_pure {σ : Strategy E F} {h : Silmaril.Games.Handler F G} {q : G.Op}
    {a₀ : G.Ar q} (hq : h q = .pure a₀) {a : G.Ar q}
    (hp : ([.inr (.ask q), .inr (.ans q a)] : List (Move E G)) ∈
      σ.comp (Strategy.ofHandler h)) :
    a = a₀ := by
  obtain ⟨s, hs, t, ht, hz⟩ := hp
  obtain ⟨y, hr⟩ := Strategy.mem_ofHandler.mp ht
  cases hz with
  | sync b _ => exact absurd (run_idle hr) (by rintro ⟨_, h', _⟩; cases h')
  | right c hz₁ =>
    show a = a₀
    obtain ⟨q₀, hq₀, hr₁⟩ := run_idle hr
    cases hq₀
    have hr₁' := run_congr (congrArg (Reduction.State.run (R := h.toReduction) q) hq) hr₁
    cases hz₁ with
    | right c' _ =>
      have ha : (Sum.inr (.ans q a) : Move F G) = .inr (.ans q a₀) := run_pure (h := h) hr₁'
      cases ha
      rfl
    | sync b _ => exact absurd (run_pure (h := h) hr₁') (by intro h'; cases h')

/-- The two-move play of a handler that answers at once. -/
theorem two_ofHandler_pure {h : Silmaril.Games.Handler E F} {q : F.Op} {a : F.Ar q}
    (hq : h q = .pure a) :
    ([.inr (.ask q), .inr (.ans q a)] : List (Move E F)) ∈ Strategy.ofHandler h :=
  Strategy.mem_ofHandler.mpr ⟨_, .vis (.ask q) (.vis (.ret hq) (.nil _))⟩

/-- The one-move play of a question to a composite. -/
theorem two_comp_upper' {σ : Strategy E F} {τ : Strategy F G} {q : G.Op} {a : G.Ar q}
    (hτ : ([.inr (.ask q), .inr (.ans q a)] : List (Move F G)) ∈ τ) :
    ([.inr (.ask q), .inr (.ans q a)] : List (Move E G)) ∈ σ.comp τ :=
  ⟨[], σ.nil_mem, _, hτ, .right _ (.right _ .nil)⟩

end TwoMoveInv

/-! ## The answers of the trivial wrapper -/

variable {S : FSig}

theorem narrowH_call (n : Nat) (q : (sigN n).Op) :
    ∃ m k, narrowH n q = .call m k :=
  ⟨_, _, rfl⟩

theorem widenH_lt {n j : Nat} (h : j < n) (p : Payload) :
    widenH n (j, p) = .call (⟨j, h⟩, p) fun r => .pure r :=
  dite_eq_left h

theorem widenH_ge {n j : Nat} (h : ¬ j < n) (p : Payload) :
    widenH n (j, p) = .pure none :=
  dite_eq_right h

/-- **The answers of the trivial wrapper**: those of the module, and a trap at a missing
export. -/
theorem obs_wrap (M : PModel S) (m : UMod S) (j : Nat) (p : Payload) :
    obs M (.comp (Silmaril.Wasm.Institution.Components.wrap m), j, p) =
      obs M (.core m, j, p) ∪ {r | m.exports.length ≤ j ∧ r = none} := by
  ext r
  constructor
  · intro hr
    have hmod : ([.inr (.ask (j, p)), .inr (.ans (j, p) r)] : List (Move sigU sigU)) ∈
        Silmaril.Wasm.Institution.Components.modU (coreSem M) m := by
      rw [← Silmaril.Wasm.Institution.Components.wrapAdequate (coreSem M) m]
      exact hr
    have hup := two_of_lower_call (narrowH_call _) hmod
    by_cases hj : j < m.exports.length
    · obtain ⟨r', hr', hrr⟩ := two_of_upper_call (widenH_lt hj p) hup
      exact Or.inl ⟨hj, hrr ▸ hr'⟩
    · exact Or.inr ⟨Nat.le_of_not_lt hj, two_of_upper_pure (widenH_ge hj p) hup⟩
  · rintro (hr | ⟨hj, rfl⟩)
    · exact obs_core_subset_wrap M m j p hr
    · show _ ∈ (Silmaril.Wasm.Institution.Components.wrap m).denU (coreSem M)
      rw [Silmaril.Wasm.Institution.Components.wrapAdequate (coreSem M) m]
      exact two_comp_upper' (two_comp_upper' (two_ofHandler_pure
        (widenH_ge (Nat.not_lt.mpr hj) p)))

/-- **At an export of the module the wrapper answers exactly as the module.** -/
theorem obs_wrap_eq (M : PModel S) (m : UMod S) {j : Nat} (hj : j < m.exports.length)
    (p : Payload) :
    obs M (.comp (Silmaril.Wasm.Institution.Components.wrap m), j, p) = obs M (.core m, j, p) := by
  rw [obs_wrap]
  ext r
  exact ⟨fun h => h.elim id fun h' => absurd hj (Nat.not_lt.mpr h'.1), Or.inl⟩

/-- The wrapped one-export module of `c` answers export `0` with the observations of `c`. -/
theorem obs_wrap_single (M : PModel S) (c : S.Code) (p : Payload) :
    obs M (.comp (Silmaril.Wasm.Institution.Components.wrap (UMod.single c)), 0, p) =
      M.obs (c, p) := by
  rw [obs_wrap_eq M _ Nat.zero_lt_one, obs_single]

end Silmaril.Wasm.Unified.Component
