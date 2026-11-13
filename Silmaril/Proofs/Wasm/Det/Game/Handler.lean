module

public import Silmaril.Wasm.Det.Game.Defs
public import Silmaril.Games.Handler.Thms
public import Silmaril.Games.LTS.Thms

/-!
# Strategies of handlers are deterministic, stateless and (for strict programs) trap-strict

The transition system of a handler (`Handler.toReduction`) has no silent step, and its state
after a trace is unique (`run_det`): a call fixes its continuation, an answer resumes it. Its
Proponent moves are read off the program in control (`pmove_det`), so `ofHandler h` is
deterministic for every trap predicate. A handler starts every round afresh from `h q`, and the
state after a play ending idle is `idle` (`idle_of_path`), so it is also stateless.

`ProgStrict tE tA p`: after every answer of a call of `p` that is a trap of `tE`, the program
returns at once a result satisfying `tA`. A handler all of whose programs are strict has a
trap-strict strategy (`strict_ofHandler`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Game

open Silmaril.Games Silmaril.Wasm.Det.Game

universe u

variable {E F : Sig.{u}}

/-- The game position of a state of a handler's transition system. -/
def hpos {h : Handler E F} : h.toReduction.State → Pos E F
  | .idle => .idle
  | .run q _ => .run q
  | .wait q m _ => .wait q m

theorem no_tau {h : Handler E F} {x y : h.toReduction.State}
    (hs : Reduction.Step h.toReduction x none y) : False := by
  cases hs with
  | tau hc => exact hc

theorem step_det {h : Handler E F} {x y y' : h.toReduction.State} {l : Option (Move E F)}
    (h₁ : Reduction.Step h.toReduction x l y) (h₂ : Reduction.Step h.toReduction x l y') :
    y = y' := by
  cases h₁ with
  | ask q => cases h₂; rfl
  | tau hc => exact hc.elim
  | call hc =>
    cases h₂ with
    | call hc' =>
      have e := hc.symm.trans hc'
      cases e
      rfl
  | resume q m k n => cases h₂; rfl
  | ret hc => cases h₂; rfl

theorem lts_run_nil {L : LTS E F} (hnt : ∀ x y, L.step x none y → False) {x y : L.State}
    (hr : L.Run x [] y) : y = x := by
  generalize e : ([] : List (Move E F)) = s at hr
  induction hr with
  | nil => rfl
  | tau hs _ _ => exact (hnt _ _ hs).elim
  | vis _ _ _ => cases e

theorem lts_run_cons {L : LTS E F} (hnt : ∀ x y, L.step x none y → False) {x z : L.State}
    {o : Move E F} {s : List (Move E F)} (hr : L.Run x (o :: s) z) :
    ∃ y, L.step x (some o) y ∧ L.Run y s z := by
  generalize e : o :: s = t at hr
  induction hr with
  | nil => cases e
  | tau hs _ _ => exact (hnt _ _ hs).elim
  | vis hs hr _ =>
    cases e
    exact ⟨_, hs, hr⟩

theorem run_nil {h : Handler E F} {x y : h.toReduction.State}
    (hr : h.toReduction.toLTS.Run x [] y) : y = x :=
  lts_run_nil (fun _ _ => no_tau) hr

theorem run_cons {h : Handler E F} {x z : h.toReduction.State} {o : Move E F}
    {s : List (Move E F)} (hr : h.toReduction.toLTS.Run x (o :: s) z) :
    ∃ y, Reduction.Step h.toReduction x (some o) y ∧ h.toReduction.toLTS.Run y s z :=
  lts_run_cons (fun _ _ => no_tau) hr

theorem run_det {h : Handler E F} {x y y' : h.toReduction.State} {s : List (Move E F)}
    (h₁ : h.toReduction.toLTS.Run x s y) (h₂ : h.toReduction.toLTS.Run x s y') : y = y' := by
  induction s generalizing x with
  | nil => rw [run_nil h₁, run_nil h₂]
  | cons o s ih =>
    obtain ⟨z, hz, hr⟩ := run_cons h₁
    obtain ⟨z', hz', hr'⟩ := run_cons h₂
    cases step_det hz hz'
    exact ih hr hr'

theorem step_pos {h : Handler E F} {x y : h.toReduction.State} {o : Move E F}
    (hs : Reduction.Step h.toReduction x (some o) y) : Step (hpos x) o (hpos y) := by
  cases hs <;> constructor

theorem run_pos {h : Handler E F} {x y : h.toReduction.State} {s : List (Move E F)}
    (hr : h.toReduction.toLTS.Run x s y) : Path (hpos x) s (hpos y) := by
  induction s generalizing x with
  | nil => rw [run_nil hr]; exact .nil _
  | cons o s ih =>
    obtain ⟨z, hz, hr⟩ := run_cons hr
    exact .cons (step_pos hz) (ih hr)

theorem idle_of_path {h : Handler E F} {y : h.toReduction.State} {s : List (Move E F)}
    (hr : h.toReduction.toLTS.Run .idle s y) (hp : Path .idle s .idle) : y = .idle := by
  have e := Path.det (run_pos hr) hp
  cases y with
  | idle => rfl
  | run q c => cases e
  | wait q m k => cases e

/-- Two Proponent moves from one state are equal. -/
theorem pmove_det {h : Handler E F} {x y₁ y₂ : h.toReduction.State} {m₁ m₂ : Move E F}
    (h₁ : Reduction.Step h.toReduction x (some m₁) y₁)
    (h₂ : Reduction.Step h.toReduction x (some m₂) y₂) (hP₁ : m₁.IsP) (hP₂ : m₂.IsP) :
    m₁ = m₂ := by
  cases h₁ with
  | ask q => exact hP₁.elim
  | resume q m k n => exact hP₁.elim
  | call hc =>
    cases h₂ with
    | call hc' =>
      have e := hc.symm.trans hc'
      cases e
      rfl
    | ret hc' => cases hc.symm.trans hc'
  | ret hc =>
    cases h₂ with
    | call hc' => cases hc.symm.trans hc'
    | ret hc' =>
      have e := hc.symm.trans hc'
      cases e
      rfl

/-- The last move of a trace, from the state after its prefix. -/
theorem trace_snoc {h : Handler E F} {x z : h.toReduction.State} {s : List (Move E F)}
    {m : Move E F} (hr : h.toReduction.toLTS.Run x (s ++ [m]) z) :
    ∃ y, h.toReduction.toLTS.Run x s y ∧ Reduction.Step h.toReduction y (some m) z := by
  obtain ⟨y, hy, hm⟩ := LTS.Run.of_append hr
  obtain ⟨z', hz', hn⟩ := run_cons hm
  rw [← run_nil hn] at hz'
  exact ⟨y, hy, hz'⟩

/-- **Handlers are deterministic** (for every trap predicate). -/
theorem detMod_ofHandler (t : Traps F) (h : Handler E F) : DetMod t (Strategy.ofHandler h) := by
  intro s m₁ m₂ h₁ h₂ hP₁ hP₂ _
  obtain ⟨z₁, hr₁⟩ := Strategy.mem_ofHandler.1 h₁
  obtain ⟨z₂, hr₂⟩ := Strategy.mem_ofHandler.1 h₂
  obtain ⟨y₁, hy₁, hs₁⟩ := trace_snoc hr₁
  obtain ⟨y₂, hy₂, hs₂⟩ := trace_snoc hr₂
  cases run_det hy₁ hy₂
  exact .inl (pmove_det hs₁ hs₂ hP₁ hP₂)

/-- **Handlers are stateless** (for every trap predicate). -/
theorem statelessMod_ofHandler (t : Traps F) (h : Handler E F) :
    StatelessMod t (Strategy.ofHandler h) := by
  intro H₁ H₂ hH₁ hH₂ hi₁ hi₂ c m₁ m₂ h₁ h₂ hP₁ hP₂ _
  obtain ⟨z₁, hr₁⟩ := Strategy.mem_ofHandler.1 h₁
  obtain ⟨z₂, hr₂⟩ := Strategy.mem_ofHandler.1 h₂
  obtain ⟨y₁, hy₁, hs₁⟩ := trace_snoc hr₁
  obtain ⟨y₂, hy₂, hs₂⟩ := trace_snoc hr₂
  obtain ⟨w₁, hw₁, hc₁⟩ := LTS.Run.of_append hy₁
  obtain ⟨w₂, hw₂, hc₂⟩ := LTS.Run.of_append hy₂
  cases idle_of_path hw₁ hi₁
  cases idle_of_path hw₂ hi₂
  cases run_det hc₁ hc₂
  exact .inl (pmove_det hs₁ hs₂ hP₁ hP₂)

/-! ## Strict programs -/

/-- Binding a strict program to a pure map that sends `tA` to `tB` is strict. -/
theorem _root_.Silmaril.Wasm.Det.Game.ProgStrict.bind_pure {tE : Traps E} {A B : Type u} {tA : A → Prop} {tB : B → Prop}
    {p : Prog E A} (hp : ProgStrict tE tA p) {g : A → B} (hg : ∀ a, tA a → tB (g a)) :
    ProgStrict tE tB (p.bind fun a => .pure (g a)) := by
  induction hp with
  | pure a => exact .pure _
  | call ht _ ih =>
    refine .call (fun n hn => ?_) ih
    obtain ⟨r, hr, htr⟩ := ht n hn
    exact ⟨g r, by rw [hr]; rfl, hg r htr⟩

/-- States of a handler whose programs are strict: the program in control is strict, and a
pending call is resumed by a trap only with a trap result. -/
def SState (tE : Traps E) (tF : Traps F) {h : Handler E F} : h.toReduction.State → Prop
  | .idle => True
  | .run q c => ProgStrict tE (tF q) c
  | .wait q m k => ∀ n, ProgStrict tE (tF q) (k n) ∧ (tE m n → ∃ r, k n = .pure r ∧ tF q r)

theorem sstate_step {tE : Traps E} {tF : Traps F} {h : Handler E F}
    (hh : ∀ q, ProgStrict tE (tF q) (h q)) {x y : h.toReduction.State} {o : Move E F}
    (hs : Reduction.Step h.toReduction x (some o) y) (hx : SState tE tF x) : SState tE tF y := by
  cases hs with
  | ask q => exact hh q
  | call hc =>
    have e : _ = _ := hc
    subst e
    cases hx with
    | call ht hk => exact fun n => ⟨hk n, ht n⟩
  | resume q m k n => exact (hx n).1
  | ret _ => trivial

theorem sstate_run {tE : Traps E} {tF : Traps F} {h : Handler E F}
    (hh : ∀ q, ProgStrict tE (tF q) (h q)) {x y : h.toReduction.State} {s : List (Move E F)}
    (hr : h.toReduction.toLTS.Run x s y) (hx : SState tE tF x) : SState tE tF y := by
  induction s generalizing x with
  | nil => rw [run_nil hr]; exact hx
  | cons o s ih =>
    obtain ⟨z, hz, hr⟩ := run_cons hr
    exact ih hr (sstate_step hh hz hx)

/-- **A handler with strict programs has a trap-strict strategy.** -/
theorem strict_ofHandler {tE : Traps E} {tF : Traps F} {h : Handler E F}
    (hh : ∀ q, ProgStrict tE (tF q) (h q)) : Strict tE tF (Strategy.ofHandler h) := by
  intro s m n b hb ht
  obtain ⟨z, hr⟩ := Strategy.mem_ofHandler.1 hb
  rw [show s ++ [.inl (.ans m n), b] = (s ++ [.inl (.ans m n)]) ++ [b] by simp] at hr
  obtain ⟨y, hy, hsb⟩ := trace_snoc hr
  obtain ⟨x, hx, hsa⟩ := trace_snoc hy
  have hX := sstate_run hh hx trivial
  cases hsa with
  | resume q m' k n' =>
    obtain ⟨r, hr', htr⟩ := (hX n).2 ht
    rw [hr'] at hsb
    cases hsb with
    | call hc => cases hc
    | ret hc =>
      have e : _ = _ := hc
      cases e
      exact htr

end Silmaril.Proofs.Wasm.Det.Game
