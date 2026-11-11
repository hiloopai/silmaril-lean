module

public import Silmaril.Wasm.Game.Env.Defs
public import Silmaril.Games.LTS.Thms
public import Silmaril.Proofs.Wasm.Game.GamesAux.Basic
public import Silmaril.Proofs.Wasm.Game.Strategy.Basic

/-!
# Environments: proofs

* The plays of `K.strategy` are the events agreeing with `K`, read as upper
  moves (`mem_strategy_iff`).
* The plays of the closed program `K.strategy ≫ σ` are the upper projections
  of the plays of `σ` whose lower projection agrees with `K`
  (`mem_comp_iff`).
* Facts about the induced hosts: answers are unique, strategy-definable hosts
  are the store-preserving hosts given by partial answer functions
  (`isStrategyHost_iff`), the special hosts for no imports and the silent
  environment.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game.GamesAux Silmaril.Wasm
  Silmaril.Wasm.Execution.Core

namespace Env

variable {E : Sig.{0}} {K : Silmaril.Wasm.Game.Env E}

open Silmaril.Wasm.Game.Env

theorem Answers.unique {e : E.Op} {w w' : E.Ar e} (h : K.Answers e w) (h' : K.Answers e w') :
    w = w' := by
  unfold Silmaril.Wasm.Game.Env.Answers at h h'
  rw [h] at h'
  exact Option.some.inj h'

/-! ### Agreement -/

theorem Agrees.of_prefix {u u' : List (Ev E)} (h : K.Agrees u) (hp : u' <+: u) : K.Agrees u' := by
  induction h generalizing u' with
  | nil => rw [List.prefix_nil.1 hp]; exact .nil
  | pending e =>
    rcases u' with _ | ⟨a, _ | ⟨b, r⟩⟩
    · exact .nil
    · obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 hp; exact .pending e
    · simp at hp
  | @answered e w rest hw _ ih =>
    rcases u' with _ | ⟨a, _ | ⟨b, r⟩⟩
    · exact .nil
    · obtain ⟨h1, -⟩ := List.cons_prefix_cons.1 hp; cases h1; exact .pending e
    · obtain ⟨h1, hp1⟩ := List.cons_prefix_cons.1 hp
      obtain ⟨h2, hp2⟩ := List.cons_prefix_cons.1 hp1
      cases h1; cases h2
      exact .answered hw (ih hp2)

theorem Agrees.path {u : List (Ev E)} (h : K.Agrees u) :
    ∃ y, Silmaril.Games.Path .idle (u.map .inr : List (Move Sig.empty E)) y := by
  induction h with
  | nil => exact ⟨_, .nil _⟩
  | pending e => exact ⟨_, .cons (.ask e) (.nil _)⟩
  | answered _ _ ih =>
    obtain ⟨y, hy⟩ := ih
    exact ⟨y, .cons (.ask _) (.cons (.ret _ _) hy)⟩

theorem Agrees.snoc_ask {u : List (Ev E)} (h : K.Agrees u)
    (hp : Silmaril.Games.Path .idle (u.map .inr : List (Move Sig.empty E)) .idle) (e : E.Op) :
    K.Agrees (u ++ [.ask e]) := by
  induction h with
  | nil => exact .pending e
  | pending e' => cases hp with | cons h₁ h₂ => cases h₁; cases h₂
  | answered hw _ ih =>
    cases hp with
    | cons h₁ h₂ =>
      cases h₁
      cases h₂ with
      | cons h₃ h₄ => cases h₃; exact .answered hw (ih h₄)

/-! ### The transition system of an environment -/

theorem run_some {e : E.Op} {p : List (Move Sig.empty E)} {y : K.lts.State}
    (h : K.lts.Run (some e : K.lts.State) p y) :
    p = [] ∨ ∃ w rest, K.Answers e w ∧ p = .inr (.ans e w) :: rest ∧ K.lts.Run none rest y := by
  obtain ⟨x, hx⟩ : ∃ x : K.lts.State, some e = x := ⟨_, rfl⟩
  rw [hx] at h
  cases h with
  | nil => exact .inl rfl
  | tau hs _ => subst hx; cases hs
  | vis hs hr => subst hx; cases hs with | ans hw => exact .inr ⟨_, _, hw, rfl, hr⟩

/-- A run from the idle state is empty or starts with a question. -/
private theorem run_none_inv {p : List (Move Sig.empty E)} {y : K.lts.State}
    (h : K.lts.Run (none : K.lts.State) p y) :
    p = [] ∨ ∃ e rest, p = .inr (.ask e) :: rest ∧ K.lts.Run (some e : K.lts.State) rest y := by
  obtain ⟨x, hx⟩ : ∃ x : K.lts.State, none = x := ⟨_, rfl⟩
  rw [hx] at h
  cases h with
  | nil => exact .inl rfl
  | tau hs _ => subst hx; cases hs
  | vis hs hr => subst hx; cases hs with | ask e => exact .inr ⟨e, _, rfl, hr⟩

theorem run_none_aux : ∀ (n : Nat) (p : List (Move Sig.empty E)) (y : K.lts.State),
    p.length ≤ n → K.lts.Run (none : K.lts.State) p y → ∃ u, p = u.map .inr ∧ K.Agrees u := by
  intro n
  induction n with
  | zero =>
    intro p y hn _
    exact ⟨[], List.length_eq_zero_iff.1 (Nat.le_zero.1 hn), .nil⟩
  | succ n ih =>
    intro p y hn h
    rcases run_none_inv h with hp | ⟨e, p', hp, hr⟩
    · exact ⟨[], hp, .nil⟩
    rcases run_some hr with hrest | ⟨w, rest, hw, hrest, hr'⟩
    · exact ⟨[.ask e], by rw [hp, hrest]; rfl, .pending e⟩
    have hlen : (Sum.inr (Ev.ans e w) :: rest : List (Move Sig.empty E)).length ≤ n :=
      hrest ▸ Nat.le_of_succ_le_succ
        (hp ▸ hn : (Sum.inr (Ev.ask e) :: p' : List (Move Sig.empty E)).length ≤ n + 1)
    obtain ⟨u, hu', hu⟩ := ih rest _ (Nat.le_of_succ_le hlen) hr'
    exact ⟨.ask e :: .ans e w :: u, by rw [hp, hrest, hu']; rfl, .answered hw hu⟩

theorem run_none {p : List (Move Sig.empty E)} {y : K.lts.State}
    (h : K.lts.Run (none : K.lts.State) p y) : ∃ u, p = u.map .inr ∧ K.Agrees u :=
  run_none_aux _ p y (Nat.le_refl _) h

theorem run_of_agrees {u : List (Ev E)} (h : K.Agrees u) :
    ∃ y, K.lts.Run none (u.map .inr) y := by
  induction h with
  | nil => exact ⟨_, .nil _⟩
  | pending e => exact ⟨_, .vis (.ask e) (.nil _)⟩
  | answered hw _ ih =>
    obtain ⟨y, hy⟩ := ih
    exact ⟨y, .vis (.ask _) (.vis (.ans hw) hy)⟩

/-- A legal Opponent move after events agreeing with `K` is a question, so the play still
agrees with `K`. -/
private theorem exists_agrees_snoc {u : List (Ev E)} (hu : K.Agrees u)
    {m : Move Sig.empty E} (hl : Legal (u.map .inr ++ [m])) (hm : m.IsO) :
    ∃ u', K.Agrees u' ∧ u.map .inr ++ [m] = u'.map .inr := by
  obtain ⟨_, hpath⟩ := hl
  obtain ⟨x, hx, hxm⟩ := Silmaril.Games.Path.concat_iff.1 hpath
  cases hxm with
  | ask e => exact ⟨u ++ [.ask e], Agrees.snoc_ask hu hx e, by simp⟩
  | reply q m n => exact m.elim
  | call q m => exact m.elim
  | ret q r => exact absurd hm (by simp [Move.IsO])

theorem mem_strategy_iff {p : List (Move Sig.empty E)} :
    p ∈ K.strategy ↔ ∃ u, K.Agrees u ∧ p = u.map .inr := by
  refine ⟨fun ⟨hl, v, hv, hp⟩ => ?_, fun ⟨u, hu, hp⟩ => ?_⟩
  · show ∃ u, K.Agrees u ∧ p = u.map .inr
    obtain ⟨u, hu, hvu⟩ : ∃ u, K.Agrees u ∧ v = u.map .inr := by
      rcases hv with hv | ⟨⟨y, hy⟩, -⟩
      · exact ⟨[], .nil, hv⟩
      · obtain ⟨u, hvu, hu⟩ := run_none hy
        exact ⟨u, hu, hvu⟩
    rcases hp with hp | ⟨p₀, m, hpm, hp₀, hm⟩
    · obtain ⟨u', hu', hp'⟩ := (prefix_map_iff).1 (hvu ▸ hp)
      exact ⟨u', Agrees.of_prefix hu hu', hp'⟩
    · obtain ⟨u', hu', hp₀'⟩ := (prefix_map_iff).1 (hvu ▸ hp₀)
      have hl' : Legal (u'.map .inr ++ [m] : List (Move Sig.empty E)) := by
        rw [← hp₀', ← hpm]
        exact hl
      obtain ⟨u'', hu'', heq⟩ := exists_agrees_snoc (Agrees.of_prefix hu hu') hl' hm
      exact ⟨u'', hu'', by rw [hpm, hp₀', heq]⟩
  · obtain ⟨y, hy⟩ := run_of_agrees hu
    obtain ⟨z, hz⟩ := Agrees.path hu
    exact hp ▸ Strategy.mem_ofLTS_of_mem_traces ⟨y, hy⟩ ⟨z, hz⟩

/-- **Composition with an environment.** -/
theorem mem_comp_iff {F : Sig.{0}} {σ : Strategy E F} {p : List (Move Sig.empty F)} :
    p ∈ K.strategy.comp σ ↔ ∃ t ∈ σ, K.Agrees (lower t) ∧ p = (upper t).map .inr := by
  rw [mem_comp_empty_iff]
  refine exists_congr fun t => and_congr_right fun _ => and_congr_left fun _ => ?_
  rw [mem_strategy_iff]
  constructor
  · rintro ⟨u, hu, h⟩
    rwa [List.map_injective_iff.2 Sum.inr_injective h]
  · intro h
    exact ⟨_, h, rfl⟩

theorem Agrees.answers {u : List (Ev E)} (h : K.Agrees u) {e : E.Op} {w : E.Ar e}
    (hm : (Ev.ans e w : Ev E) ∈ u) : K.Answers e w := by
  induction h with
  | nil => simp at hm
  | pending e' => simp at hm
  | answered ha _ ih =>
    rcases List.mem_cons.mp hm with h1 | hm
    · cases h1
    · rcases List.mem_cons.mp hm with h2 | hm
      · cases h2; exact ha
      · exact ih hm

end Env

/-! ### Strategy-definable hosts -/

open Silmaril.Wasm.Game.Env in
theorem hostOf_iff (ts : List FnType) (K : Silmaril.Wasm.Game.Env (ifaceSig ts)) (h : Nat)
    (s : Store Nat) (args : List Val) (out : HostOutcome Nat) :
    hostOf ts K h s args out ↔ ∃ e, ifaceOp? ts h args = some e ∧
      match K e with
      | some w => out = .returned s (Answer.toResult (ft := ts.get e.1) w)
      | none => out = .diverged := by
  unfold hostOf Silmaril.Wasm.Game.Env.Answers
  apply exists_congr
  intro e
  apply and_congr_right
  intro _
  rcases K e with _ | w
  · constructor
    · rintro (⟨w, hw, -⟩ | ⟨-, hout⟩)
      · cases hw
      · exact hout
    · intro hout
      exact Or.inr ⟨fun w hw => (by cases hw), hout⟩
  · constructor
    · rintro (⟨w', hw, hout⟩ | ⟨hn, -⟩)
      · cases hw
        exact hout
      · exact absurd rfl (hn w)
    · intro hout
      exact Or.inl ⟨w, rfl, hout⟩

theorem isStrategyHost_iff (ts : List FnType) (host : HostSemantics Nat) :
    IsStrategyHost ts host ↔
      ∃ ans : (e : (ifaceSig ts).Op) → Option ((ifaceSig ts).Ar e),
        ∀ h s args out, host h s args out ↔ ∃ e, ifaceOp? ts h args = some e ∧
          match ans e with
          | some w => out = .returned s (Answer.toResult (ft := ts.get e.1) w)
          | none => out = .diverged := by
  constructor
  · rintro ⟨K, rfl⟩
    exact ⟨K, hostOf_iff ts K⟩
  · rintro ⟨ans, hans⟩
    refine ⟨ans, ?_⟩
    funext h s args out
    apply propext
    rw [hans, hostOf_iff ts ans]

theorem hostOf_nil (K : Silmaril.Wasm.Game.Env (ifaceSig [])) :
    hostOf [] K = (fun _ _ _ _ => False : HostSemantics Nat) := by
  funext h s args out
  apply propext
  constructor
  · rintro ⟨e, -, -⟩
    exact Fin.elim0 e.1
  · intro h
    exact h.elim

theorem throwsBelow_nil (K : Silmaril.Wasm.Game.Env (ifaceSig [])) (n : Nat) : ThrowsBelow K n :=
  fun e => Fin.elim0 e.1

theorem hostOf_silent (ts : List FnType) (h : Nat) (s : Store Nat) (args : List Val)
    (out : HostOutcome Nat) :
    hostOf ts (Silmaril.Wasm.Game.Env.silent _) h s args out ↔
      (ifaceOp? ts h args).isSome ∧ divHost h s args out := by
  unfold hostOf divHost
  constructor
  · rintro ⟨e, he, (⟨w, hw, -⟩ | ⟨-, hout⟩)⟩
    · cases hw
    · exact ⟨by simp [he], hout⟩
  · rintro ⟨hs, hout⟩
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨e, he, Or.inr ⟨fun w hw => (by cases hw), hout⟩⟩

theorem throwsBelow_silent (ts : List FnType) (n : Nat) :
    ThrowsBelow (Silmaril.Wasm.Game.Env.silent (ifaceSig ts)) n := by
  intro e w hw
  cases hw

theorem throwsBelow_mono {ts : List FnType} {K : Silmaril.Wasm.Game.Env (ifaceSig ts)} {n m : Nat}
    (h : ThrowsBelow K n) (hnm : n ≤ m) : ThrowsBelow K m := by
  intro e w hw
  have hb := h e w hw
  cases w with
  | throw a => exact Nat.lt_of_lt_of_le hb hnm
  | values vs => trivial
  | trap => trivial

end Silmaril.Proofs.Wasm.Game
