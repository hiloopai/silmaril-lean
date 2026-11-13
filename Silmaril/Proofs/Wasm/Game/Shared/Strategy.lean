module

public import Silmaril.Wasm.Game.Shared.Defs
public import Silmaril.Proofs.Wasm.Game.StatefulEnv.Div

/-!
# The store-passing strategy: legality, receptivity and the composite system

* `traces_legal`, `traces_receptive`, `denotes`: the transition system
  `I.shLts P` (host-free steps silent) denotes `I.shStrategy P`: its traces are
  legal (a position map), prefix closed and receptive (an idle instance accepts
  every question, a waiting one every answer, in every store).
* `silentRunning`: it takes silent steps only while running.
* `closedShD_eq_ofLTS`, `forget_closedShD`, `responds_iff`: hence
  (`DStrategy.ofLTS_comp`) the closed program `(L.dstrategy q).comp (I.shDStrategy P)`
  is the divergence-observing strategy of the composite system
  `(L.dlts q).comp (I.shLts P)`, its finite plays are `I.closedSh P L q`, and an
  answer of the closed program is a trace of the composite system.

New proofs; the shape follows `Silmaril.Proofs.Wasm.Game.{Strategy.Basic,DivAdequacy.Comp}`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Shared

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded

variable {I : Silmaril.Wasm.Game.ScalarInstance} {P : Profile}

open Silmaril.Wasm.Game.ScalarInstance

/-- Visible transitions are game steps of the positions. -/
theorem shTrans_step {x y : I.ShState} {o : Move I.shE I.shF} (h : I.ShTrans P x (some o) y) :
    Silmaril.Games.Step x.pos o y.pos := by
  cases h with
  | call f => exact .ask f
  | ucall => exact .call _ _
  | uret s' v => exact .reply _ _ _
  | oret => exact .ret _ _

/-- Silent transitions keep the position. -/
theorem shTrans_tau_pos {x y : I.ShState} (h : I.ShTrans P x none y) : y.pos = x.pos := by
  cases h
  rfl

/-- Silent transitions happen in running positions. -/
theorem shTrans_tau_run {x y : I.ShState} (h : I.ShTrans P x none y) : ∃ q, x.pos = .run q := by
  cases h
  exact ⟨_, rfl⟩

/-- The store-passing instance takes silent steps only when running. -/
theorem silentRunning (P : Profile) : (I.shLts P).SilentRunning :=
  LTS.silentRunning_of_pos (L := I.shLts P) ShState.pos rfl shTrans_step shTrans_tau_pos
    shTrans_tau_run

/-- Runs follow the positions. -/
theorem run_pos {x y : I.ShState} {p : List (Move I.shE I.shF)} (h : (I.shLts P).Run x p y) :
    Silmaril.Games.Path x.pos p y.pos :=
  LTS.path_of_run_pos (L := I.shLts P) ShState.pos shTrans_step shTrans_tau_pos h

/-- Traces are legal. -/
theorem traces_legal {p : List (Move I.shE I.shF)} (h : p ∈ (I.shLts P).Traces) : Legal p := by
  obtain ⟨y, hy⟩ := h
  exact ⟨_, run_pos hy⟩

/-- An Opponent move legal at the position of a state is a transition of the state. -/
theorem step_of_isO {y : I.ShState} {x z : Pos I.shE I.shF} {m : Move I.shE I.shF}
    (hpos : y.pos = x) (hxz : Silmaril.Games.Step x m z) (hm : m.IsO) :
    ∃ y', I.ShTrans P y (some m) y' := by
  cases y with
  | idle =>
    cases hpos
    cases hxz with
    | ask f => exact ⟨_, .call f⟩
  | running f s t =>
    cases hpos
    cases hxz <;> simp [Move.IsO] at hm
  | waiting f s t e =>
    cases hpos
    cases hxz with
    | reply _ _ n => exact ⟨_, .uret n.1 n.2⟩

/-- Traces are receptive. -/
theorem traces_receptive {p : List (Move I.shE I.shF)} {x z : Pos I.shE I.shF}
    {m : Move I.shE I.shF} (hp : p ∈ (I.shLts P).Traces) (hx : Silmaril.Games.Path .idle p x)
    (hxz : Silmaril.Games.Step x m z) (hm : m.IsO) : p ++ [m] ∈ (I.shLts P).Traces := by
  obtain ⟨y, hy⟩ := hp
  have hpos : y.pos = x := Silmaril.Games.Path.det (run_pos hy) hx
  obtain ⟨y', hy'⟩ := step_of_isO hpos hxz hm
  exact ⟨y', hy.append (LTS.Run.of_step (L := I.shLts P) hy')⟩

/-- **The transition system denotes the store-passing strategy.** -/
theorem denotes (P : Profile) : (I.shLts P).Denotes (I.shStrategy P) := by
  intro p
  constructor
  · intro hp
    exact Strategy.mem_ofLTS_of_mem_traces hp (traces_legal hp)
  · rintro ⟨hl, u, hu, hp⟩
    have hu' : u ∈ (I.shLts P).Traces := by
      rcases hu with rfl | ⟨hu, -⟩
      · exact ⟨_, .nil _⟩
      · exact hu
    rcases hp with hp | ⟨p₀, m, rfl, hp₀, hm⟩
    · exact LTS.traces_of_prefix hu' hp
    · obtain ⟨_, hpath⟩ := hl
      obtain ⟨x, hx, hxm⟩ := Silmaril.Games.Path.concat_iff.1 hpath
      exact traces_receptive (LTS.traces_of_prefix hu' hp₀) hx hxm hm

/-- The finite plays of the divergence-observing strategy are the strategy. -/
theorem forget_shDStrategy (P : Profile) : (I.shDStrategy P).forget = I.shStrategy P := rfl

/-- The composite system of the closed program. -/
abbrev ShCmp (I : Silmaril.Wasm.Game.ScalarInstance) (P : Profile) (L : SEnv I.shE) (q₀ : L.S) :
    LTS Sig.empty I.shF :=
  (L.dlts q₀).comp (I.shLts P)

/-- **The composite strategy is the strategy of the composite system.** -/
theorem closedShD_eq_ofLTS (P : Profile) (L : SEnv I.shE) (q : L.S) :
    I.closedShD P L q = DStrategy.ofLTS (ShCmp I P L q) :=
  (DStrategy.ofLTS_comp (SEnv.denotes_dlts L q) (denotes P)
    (LTS.SilentRunning.divRunning (SEnv.silentRunning_dlts L q))
    (LTS.SilentRunning.divRunning (silentRunning P))).symm

/-- The finite plays of the divergence-observing closed program are the closed program. -/
theorem forget_closedShD (P : Profile) (L : SEnv I.shE) (q : L.S) :
    (I.closedShD P L q).forget = I.closedSh P L q := by
  show (L.dstrategy q).forget.comp (I.shDStrategy P).forget = (L.strategy q).comp (I.shStrategy P)
  rw [SEnv.forget_dstrategy, forget_shDStrategy]

/-- The composite system denotes the closed program. -/
theorem cmp_denotes (P : Profile) (L : SEnv I.shE) (q : L.S) :
    (ShCmp I P L q).Denotes (I.closedSh P L q) :=
  LTS.Denotes.comp (SEnv.denotes_dlts L q) (denotes P)

/-- An answer of the closed program is a trace of the composite system. -/
theorem responds_iff {L : SEnv I.shE} {q : L.S} {f : I.shF.Op} {a : I.shF.Ar f} :
    Responds (I.closedSh P L q) f a ↔
      [.inr (.ask f), .inr (.ans f a)] ∈ (ShCmp I P L q).Traces :=
  (cmp_denotes P L q _).symm

end Silmaril.Proofs.Wasm.Game.Shared
