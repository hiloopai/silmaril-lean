module

public import Silmaril.Games.Answer.Defs
public import Silmaril.Games.Handler.Thms

/-!
# Answering machines: proofs

* `run_path`, `denotes_of_pos`: a transition system whose steps follow the legality automaton
  through a position map, and which accepts every Opponent move the automaton allows, denotes
  the strategy it generates.
* `denotes_ofAns`: an answering machine denotes its strategy.
* `ansSim`, `ansSim'`: the composite of an answering machine with the transition system of a
  handler and the answering machine of `Handler.overAns` simulate each other.
* `belowSim`, `belowSim'`: a handler below an answering machine never moves.
-/

public section

namespace Silmaril.Proofs.Games.Answer

open Silmaril.Games

universe u

variable {E F G : Sig.{u}} {σ : Type u}

/-! ## Transition systems that follow the legality automaton -/

theorem run_path {L : LTS E F} (pos : L.State → Pos E F)
    (hs : ∀ {x l y}, L.step x l y → Path (pos x) l.toList (pos y)) {x y : L.State}
    {s : List (Move E F)} (h : L.Run x s y) : Path (pos x) s (pos y) := by
  induction h with
  | nil x => exact .nil _
  | tau h₁ _ ih => exact (hs h₁).append ih
  | vis h₁ _ ih => exact (hs h₁).append ih

/-- **A transition system that follows the legality automaton and is receptive denotes its
strategy.** -/
theorem denotes_of_pos {L : LTS E F} (pos : L.State → Pos E F) (h₀ : pos L.init = .idle)
    (hs : ∀ {x l y}, L.step x l y → Path (pos x) l.toList (pos y))
    (hr : ∀ {x o p'}, Step (pos x) o p' → o.IsO → ∃ y, L.Run x [o] y) :
    L.Denotes (Strategy.ofLTS L) := by
  intro p
  constructor
  · show p ∈ L.Traces → p ∈ Strategy.ofLTS L
    intro hp
    obtain ⟨y, hy⟩ := hp
    have hl : Legal p := ⟨_, h₀ ▸ run_path pos hs hy⟩
    exact Strategy.mem_ofLTS_of_mem_traces ⟨y, hy⟩ hl
  · show p ∈ Strategy.ofLTS L → p ∈ L.Traces
    intro hp
    obtain ⟨hl, s, hs', hpre⟩ := Strategy.mem_generate.1 hp
    have hst : s ∈ L.Traces := by
      rcases hs' with rfl | ⟨h, -⟩
      · exact ⟨_, .nil _⟩
      · exact h
    rcases hpre with hpre | ⟨p₀, o, rfl, hp₀, ho⟩
    · exact LTS.traces_of_prefix hst hpre
    · show ∃ y, L.Run L.init (p₀ ++ [o]) y
      obtain ⟨x, hx⟩ : p₀ ∈ L.Traces := LTS.traces_of_prefix hst hp₀
      obtain ⟨y, hy⟩ := hl
      obtain ⟨z, hz, hzo⟩ : ∃ z, Path .idle p₀ z ∧ Step z o y := Path.concat_iff.1 hy
      have hpx : Path .idle p₀ (pos x) := h₀ ▸ run_path pos hs hx
      have hxz : pos x = z := hpx.det hz
      obtain ⟨x', hx'⟩ : ∃ x', L.Run x [o] x' := hr (hxz ▸ hzo) ho
      exact ⟨x', hx.append hx'⟩

/-! ## Answering machines denote their strategies -/

/-- The game position of a state of an answering machine. -/
def ansPos : σ × Option F.Op → Pos E F
  | (_, none) => .idle
  | (_, some q) => .run q

theorem ansPos_step {g : (q : F.Op) → σ → F.Ar q × σ} {x y : σ × Option F.Op}
    {l : Option (Move E F)} (h : LTS.AnsStep g x l y) : Path (ansPos x) l.toList (ansPos y) := by
  cases h with
  | ask s q => exact Path.single (Step.ask q)
  | ret s q => exact Path.single (Step.ret q _)

theorem ansPos_recv {g : (q : F.Op) → σ → F.Ar q × σ} {init : σ} {x : σ × Option F.Op}
    {o : Move E F} {p' : Pos E F} (h : Step (ansPos x) o p') (ho : o.IsO) :
    ∃ y, (LTS.ofAns g init : LTS E F).Run x [o] y := by
  obtain ⟨s, _ | q⟩ := x
  · cases h with
    | ask q => exact ⟨_, .vis (LTS.AnsStep.ask s q) (.nil _)⟩
  · cases h with
    | call => exact ho.elim
    | ret => exact ho.elim

theorem denotes_ofAns (g : (q : F.Op) → σ → F.Ar q × σ) (init : σ) :
    (LTS.ofAns g init : LTS E F).Denotes (Strategy.ofLTS (LTS.ofAns g init)) :=
  denotes_of_pos ansPos rfl ansPos_step ansPos_recv

/-! ## An answering machine below a handler -/

/-- The composite of an answering machine with the transition system of a handler. -/
abbrev compL (g : (q : F.Op) → σ → F.Ar q × σ) (init : σ) (h : Handler F G) : LTS E G :=
  (LTS.ofAns g init).comp h.toReduction.toLTS

/-- Simulation relation, from the composite to the answering machine of `h.overAns g`. -/
inductive AnsRel (g : (q : F.Op) → σ → F.Ar q × σ) (init : σ) (h : Handler F G) :
    (compL (E := E) g init h).State → σ × Option G.Op → Prop
  | idle (s : σ) : AnsRel g init h ((s, none), .idle) (s, none)
  | run (s₀ s : σ) (q : G.Op) (c : Prog F (G.Ar q)) : c.runAns g s = (h q).runAns g s₀ →
      AnsRel g init h ((s, none), .run q c) (s₀, some q)
  | wait (s₀ s : σ) (q : G.Op) (m : F.Op) (k : F.Ar m → Prog F (G.Ar q)) :
      (Prog.call m k).runAns g s = (h q).runAns g s₀ →
      AnsRel g init h ((s, some m), .wait q m k) (s₀, some q)

/-- The composite is simulated by the answering machine of `h.overAns g`. -/
def ansSim (g : (q : F.Op) → σ → F.Ar q × σ) (init : σ) (h : Handler F G) :
    LTS.Simulation (compL (E := E) g init h) (LTS.ofAns (h.overAns g) init) where
  R := AnsRel g init h
  init := .idle init
  step := by
    intro z z' x l hr hs
    cases hr with
    | idle s =>
      cases hs with
      | tau₁ hs => cases hs
      | tau₂ hs => cases hs
      | left e hs => cases hs
      | right g' ht =>
        cases ht with
        | ask q => exact ⟨_, .vis (LTS.AnsStep.ask s q) (.nil _), .run s s q (h q) rfl⟩
      | sync f hs ht => cases ht
    | run s₀ s q c hc =>
      cases hs with
      | tau₁ hs => cases hs
      | tau₂ hs => cases hs with | tau hc => exact (hc : False).elim
      | left e hs => cases hs
      | right g' ht =>
        cases ht with
        | @ret _ _ r hd =>
          cases hd
          have h₁ : h.overAns g q s₀ = (r, s) := hc.symm
          have hst := LTS.AnsStep.ret (E := E) (g := h.overAns g) s₀ q
          rw [h₁] at hst
          exact ⟨_, .vis hst (.nil _), .idle s⟩
      | sync f hs ht =>
        cases ht with
        | @call _ _ m k hk =>
          cases hk
          cases hs
          exact ⟨_, .nil _, .wait s₀ s q m k hc⟩
    | wait s₀ s q m k hc =>
      cases hs with
      | tau₁ hs => cases hs
      | tau₂ hs => cases hs
      | left e hs => cases hs
      | right g' ht => cases ht
      | sync f hs ht =>
        cases hs with
        | ret _ _ =>
          cases ht with
          | resume _ _ _ n => exact ⟨_, .nil _, .run s₀ _ q _ hc⟩

/-- A program run to its end in the composite. -/
theorem compL_run (g : (q : F.Op) → σ → F.Ar q × σ) (init : σ) (h : Handler F G) (q : G.Op) :
    ∀ (c : Prog F (G.Ar q)) (s : σ),
      (compL (E := E) g init h).Run ((s, none), .run q c) [.inr (.ans q (c.runAns g s).1)]
        (((c.runAns g s).2, none), .idle) := by
  intro c
  induction c with
  | pure r => exact fun s => .vis (LTS.CompStep.right _ (Reduction.Step.ret rfl)) (.nil _)
  | call m k ih =>
    intro s
    exact .tau (LTS.CompStep.sync _ (LTS.AnsStep.ask s m) (Reduction.Step.call rfl))
      (.tau (LTS.CompStep.sync _ (LTS.AnsStep.ret s m) (Reduction.Step.resume (R := h.toReduction) q m k _))
        (ih (g m s).1 (g m s).2))

/-- Simulation relation, from the answering machine of `h.overAns g` to the composite. -/
inductive AnsRel' (g : (q : F.Op) → σ → F.Ar q × σ) (init : σ) (h : Handler F G) :
    σ × Option G.Op → (compL (E := E) g init h).State → Prop
  | idle (s : σ) : AnsRel' g init h (s, none) ((s, none), .idle)
  | run (s : σ) (q : G.Op) : AnsRel' g init h (s, some q) ((s, none), .run q (h q))

/-- The answering machine of `h.overAns g` is simulated by the composite. -/
def ansSim' (g : (q : F.Op) → σ → F.Ar q × σ) (init : σ) (h : Handler F G) :
    LTS.Simulation (LTS.ofAns (h.overAns g) init) (compL (E := E) g init h) where
  R := AnsRel' g init h
  init := .idle init
  step := by
    intro x x' z l hr hs
    cases hs with
    | ask s q =>
      cases hr
      exact ⟨_, .vis (LTS.CompStep.right _ (Reduction.Step.ask q)) (.nil _), .run s q⟩
    | ret s q =>
      cases hr
      exact ⟨_, compL_run g init h q (h q) s, .idle _⟩

/-! ## A handler below an answering machine -/

/-- The composite of a handler with an answering machine above it. -/
abbrev belowL (h : Handler E F) (g : (q : G.Op) → σ → G.Ar q × σ) (init : σ) : LTS E G :=
  h.toReduction.toLTS.comp (LTS.ofAns g init)

/-- The handler stays idle. -/
def belowSim (h : Handler E F) (g : (q : G.Op) → σ → G.Ar q × σ) (init : σ) :
    LTS.Simulation (belowL h g init) (LTS.ofAns g init) where
  R z x := z = (.idle, x)
  init := rfl
  step := by
    intro z z' x l hr hs
    cases hs with
    | tau₁ hs => cases hr; cases hs
    | tau₂ hs => cases hs
    | left e hs => cases hr; cases hs
    | right g' ht =>
      cases hr
      cases ht with
      | ask s q => exact ⟨_, .vis (LTS.AnsStep.ask s q) (.nil _), rfl⟩
      | ret s q => exact ⟨_, .vis (LTS.AnsStep.ret s q) (.nil _), rfl⟩
    | sync f hs ht => cases ht

/-- The answering machine is simulated with an idle handler below it. -/
def belowSim' (h : Handler E F) (g : (q : G.Op) → σ → G.Ar q × σ) (init : σ) :
    LTS.Simulation (LTS.ofAns g init) (belowL h g init) where
  R x z := z = (.idle, x)
  init := rfl
  step := by
    intro x x' z l hr hs
    cases hr
    cases hs with
    | ask s q => exact ⟨_, .vis (LTS.CompStep.right _ (LTS.AnsStep.ask s q)) (.nil _), rfl⟩
    | ret s q => exact ⟨_, .vis (LTS.CompStep.right _ (LTS.AnsStep.ret s q)) (.nil _), rfl⟩

end Silmaril.Proofs.Games.Answer
