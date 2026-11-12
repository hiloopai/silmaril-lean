module

public import Silmaril.Wasm.Game.StatefulEnv.Defs
public import Silmaril.Games.LTS.Thms
public import Silmaril.Proofs.Wasm.Game.GamesAux.Basic

/-!
# Strategies of stateful environments: proofs

* The plays of `L.strategy q` are the event lists agreeing with `L` from `q`,
  read as upper moves (`mem_strategy_iff`).
* The plays of the closed program `L.strategy q ≫ σ` are the upper
  projections of the plays of `σ` whose lower projection agrees with `L` from
  `q` (`mem_comp_iff`).

Source: the same argument as `Silmaril.Proofs.Wasm.Game.Env.Basic` (stateless
environments), with the host state threaded through; new proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.SEnv

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game.GamesAux

variable {E : Sig.{0}} {L : Silmaril.Wasm.Game.SEnv E}

open Silmaril.Wasm.Game.SEnv

/-! ### Agreement -/

theorem Agrees.of_prefix {q : L.S} {u u' : List (Ev E)} (h : L.Agrees q u) (hp : u' <+: u) :
    L.Agrees q u' := by
  induction h generalizing u' with
  | nil q => rw [List.prefix_nil.1 hp]; exact .nil q
  | pending q e =>
    rcases u' with _ | ⟨a, _ | ⟨b, r⟩⟩
    · exact .nil q
    · obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 hp; exact .pending q e
    · simp at hp
  | @answered q q' e w rest hw _ ih =>
    rcases u' with _ | ⟨a, _ | ⟨b, r⟩⟩
    · exact .nil q
    · obtain ⟨h1, -⟩ := List.cons_prefix_cons.1 hp; cases h1; exact .pending q e
    · obtain ⟨h1, hp1⟩ := List.cons_prefix_cons.1 hp
      obtain ⟨h2, hp2⟩ := List.cons_prefix_cons.1 hp1
      cases h1; cases h2
      exact .answered hw (ih hp2)

theorem Agrees.path {q : L.S} {u : List (Ev E)} (h : L.Agrees q u) :
    ∃ y, Silmaril.Games.Path .idle (u.map .inr : List (Move Sig.empty E)) y := by
  induction h with
  | nil => exact ⟨_, .nil _⟩
  | pending _ e => exact ⟨_, .cons (.ask e) (.nil _)⟩
  | answered _ _ ih =>
    obtain ⟨y, hy⟩ := ih
    exact ⟨y, .cons (.ask _) (.cons (.ret _ _) hy)⟩

theorem Agrees.snoc_ask {q : L.S} {u : List (Ev E)} (h : L.Agrees q u)
    (hp : Silmaril.Games.Path .idle (u.map .inr : List (Move Sig.empty E)) .idle) (e : E.Op) :
    L.Agrees q (u ++ [.ask e]) := by
  induction h with
  | nil q => exact .pending q e
  | pending _ e' => cases hp with | cons h₁ h₂ => cases h₁; cases h₂
  | answered hw _ ih =>
    cases hp with
    | cons h₁ h₂ =>
      cases h₁
      cases h₂ with
      | cons h₃ h₄ => cases h₃; exact .answered hw (ih h₄)

/-- Answers in agreeing events are answers of `L` from some state. -/
theorem Agrees.answers {q : L.S} {u : List (Ev E)} (h : L.Agrees q u) {e : E.Op} {w : E.Ar e}
    (hm : (Ev.ans e w : Ev E) ∈ u) : ∃ q₀ q₁, L.Ans q₀ e w q₁ := by
  induction h with
  | nil => simp at hm
  | pending _ e' => simp at hm
  | answered ha _ ih =>
    rcases List.mem_cons.mp hm with h1 | hm
    · cases h1
    · rcases List.mem_cons.mp hm with h2 | hm
      · cases h2; exact ⟨_, _, ha⟩
      · exact ih hm

/-- A complete driven exchange agrees with `L`. -/
theorem Drive.agrees {q q' : L.S} {u : List (Ev E)} (h : L.Drive q u q') : L.Agrees q u := by
  induction h with
  | nil q => exact .nil q
  | cons ha _ ih => exact .answered ha ih

/-- Agreement after a driven exchange. -/
theorem Drive.append_agrees {q q' : L.S} {u v : List (Ev E)} (h : L.Drive q u q')
    (hv : L.Agrees q' v) : L.Agrees q (u ++ v) := by
  induction h with
  | nil => exact hv
  | cons ha _ ih => exact .answered ha (ih hv)

/-- Driven exchanges compose. -/
theorem Drive.append {q q' q'' : L.S} {u v : List (Ev E)} (h : L.Drive q u q')
    (hv : L.Drive q' v q'') : L.Drive q (u ++ v) q'' := by
  induction h with
  | nil => exact hv
  | cons ha _ ih => exact .cons ha (ih hv)

/-! ### The transition system of a stateful environment -/

theorem run_some {q₀ q : L.S} {e : E.Op} {p : List (Move Sig.empty E)}
    {y : (L.lts q₀).State} (h : (L.lts q₀).Run ((q, some e) : L.S × Option E.Op) p y) :
    p = [] ∨ ∃ w q' rest, L.Ans q e w q' ∧ p = .inr (.ans e w) :: rest ∧
      (L.lts q₀).Run ((q', none) : L.S × Option E.Op) rest y := by
  obtain ⟨x, hx⟩ : ∃ x : (L.lts q₀).State, (q, some e) = x := ⟨_, rfl⟩
  rw [hx] at h
  cases h with
  | nil => exact .inl rfl
  | tau hs _ => subst hx; cases hs
  | vis hs hr => subst hx; cases hs with | ans hw => exact .inr ⟨_, _, _, hw, rfl, hr⟩

/-- A run from an idle state is empty or starts with a question. -/
private theorem run_none_inv {q₀ q : L.S} {p : List (Move Sig.empty E)}
    {y : (L.lts q₀).State} (h : (L.lts q₀).Run ((q, none) : L.S × Option E.Op) p y) :
    p = [] ∨ ∃ e rest, p = .inr (.ask e) :: rest ∧
      (L.lts q₀).Run ((q, some e) : L.S × Option E.Op) rest y := by
  obtain ⟨x, hx⟩ : ∃ x : (L.lts q₀).State, (q, none) = x := ⟨_, rfl⟩
  rw [hx] at h
  cases h with
  | nil => exact .inl rfl
  | tau hs _ => subst hx; cases hs
  | vis hs hr => subst hx; cases hs with | ask _ e => exact .inr ⟨e, _, rfl, hr⟩

theorem run_none_aux {q₀ : L.S} : ∀ (n : Nat) (q : L.S) (p : List (Move Sig.empty E))
    (y : (L.lts q₀).State), p.length ≤ n →
    (L.lts q₀).Run ((q, none) : L.S × Option E.Op) p y → ∃ u, p = u.map .inr ∧ L.Agrees q u := by
  intro n
  induction n with
  | zero =>
    intro q p y hn _
    exact ⟨[], List.length_eq_zero_iff.1 (Nat.le_zero.1 hn), .nil q⟩
  | succ n ih =>
    intro q p y hn h
    rcases run_none_inv h with hp | ⟨e, p', hp, hr⟩
    · exact ⟨[], hp, .nil q⟩
    rcases run_some hr with hrest | ⟨w, q', rest, hw, hrest, hr'⟩
    · exact ⟨[.ask e], by rw [hp, hrest]; rfl, .pending q e⟩
    have hlen : (Sum.inr (Ev.ans e w) :: rest : List (Move Sig.empty E)).length ≤ n :=
      hrest ▸ Nat.le_of_succ_le_succ
        (hp ▸ hn : (Sum.inr (Ev.ask e) :: p' : List (Move Sig.empty E)).length ≤ n + 1)
    obtain ⟨u, hu', hu⟩ := ih q' rest _ (Nat.le_of_succ_le hlen) hr'
    exact ⟨.ask e :: .ans e w :: u, by rw [hp, hrest, hu']; rfl, .answered hw hu⟩

theorem run_of_agrees {q₀ q : L.S} {u : List (Ev E)} (h : L.Agrees q u) :
    ∃ y, (L.lts q₀).Run ((q, none) : L.S × Option E.Op) (u.map .inr) y := by
  induction h with
  | nil => exact ⟨_, .nil _⟩
  | pending q e => exact ⟨_, .vis (.ask q e) (.nil _)⟩
  | answered hw _ ih =>
    obtain ⟨y, hy⟩ := ih
    exact ⟨y, .vis (.ask _ _) (.vis (.ans hw) hy)⟩

/-- A legal Opponent move after events agreeing with `L` is a question, so the play still
agrees with `L`. -/
private theorem exists_agrees_snoc {q : L.S} {u : List (Ev E)} (hu : L.Agrees q u)
    {m : Move Sig.empty E} (hl : Legal (u.map .inr ++ [m])) (hm : m.IsO) :
    ∃ u', L.Agrees q u' ∧ u.map .inr ++ [m] = u'.map .inr := by
  obtain ⟨_, hpath⟩ := hl
  obtain ⟨x, hx, hxm⟩ := Silmaril.Games.Path.concat_iff.1 hpath
  cases hxm with
  | ask e => exact ⟨u ++ [.ask e], Agrees.snoc_ask hu hx e, by simp⟩
  | reply q m n => exact m.elim
  | call q m => exact m.elim
  | ret q r => exact absurd hm (by simp [Move.IsO])

/-- **The plays of a stateful environment** from state `q` are the event lists agreeing with
`L` from `q`. -/
theorem mem_strategy_iff {q : L.S} {p : List (Move Sig.empty E)} :
    p ∈ L.strategy q ↔ ∃ u, L.Agrees q u ∧ p = u.map .inr := by
  refine ⟨fun ⟨hl, v, hv, hp⟩ => ?_, fun ⟨u, hu, hp⟩ => ?_⟩
  · show ∃ u, L.Agrees q u ∧ p = u.map .inr
    obtain ⟨u, hu, hvu⟩ : ∃ u, L.Agrees q u ∧ v = u.map .inr := by
      rcases hv with hv | ⟨⟨y, hy⟩, -⟩
      · exact ⟨[], .nil q, hv⟩
      · obtain ⟨u, hvu, hu⟩ := run_none_aux _ q v y (Nat.le_refl _) hy
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
  · obtain ⟨y, hy⟩ := run_of_agrees (q₀ := q) hu
    obtain ⟨z, hz⟩ := Agrees.path hu
    exact hp ▸ Strategy.mem_ofLTS_of_mem_traces ⟨y, hy⟩ ⟨z, hz⟩

/-- **Composition with a stateful environment.** -/
theorem mem_comp_iff {F : Sig.{0}} {q : L.S} {σ : Strategy E F} {p : List (Move Sig.empty F)} :
    p ∈ (L.strategy q).comp σ ↔ ∃ t ∈ σ, L.Agrees q (lower t) ∧ p = (upper t).map .inr := by
  rw [mem_comp_empty_iff]
  refine exists_congr fun t => and_congr_right fun _ => and_congr_left fun _ => ?_
  rw [mem_strategy_iff]
  constructor
  · rintro ⟨u, hu, h⟩
    rwa [List.map_injective_iff.2 Sum.inr_injective h]
  · intro h
    exact ⟨_, h, rfl⟩

end Silmaril.Proofs.Wasm.Game.SEnv
