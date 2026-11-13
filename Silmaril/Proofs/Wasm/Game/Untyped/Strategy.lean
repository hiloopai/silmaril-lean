module

public import Silmaril.Wasm.Game.Untyped.Defs
public import Silmaril.Proofs.Wasm.Game.StatefulEnv.Div

/-!
# The untyped strategy: legality, receptivity and the composite system

* `denotes`: the transition system `U.lts P` (host-free steps silent) denotes
  `U.strategy P`: its traces are legal, prefix closed and receptive (an idle instance
  accepts every question, a waiting one every reply, in every store).
* `silentRunning`: it takes silent steps only while running.
* `closedD_eq_ofLTS`, `forget_closedD`, `responds_iff`: hence
  (`DStrategy.ofLTS_comp`) the closed program `(L.dstrategy q).comp (U.dstrategy P)` is
  the divergence-observing strategy of the composite system, with finite plays
  `U.closed P L q`.

New proofs, copied from `Silmaril.Proofs.Wasm.Game.Shared.Strategy` with the moves untyped.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Untyped

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded

variable {U : UInstance} {P : Profile}

open Silmaril.Wasm.Game.UInstance

/-- Visible transitions are game steps of the positions. -/
theorem trans_step {x y : U.State} {o : Move U.E U.F} (h : U.Trans P x (some o) y) :
    Silmaril.Games.Step x.pos o y.pos := by
  cases h with
  | call f => exact .ask f
  | ucall => exact .call _ _
  | uret a => exact .reply _ _ _
  | oret => exact .ret _ _

/-- Silent transitions keep the position. -/
theorem trans_tau_pos {x y : U.State} (h : U.Trans P x none y) : y.pos = x.pos := by
  cases h
  rfl

/-- Silent transitions happen in running positions. -/
theorem trans_tau_run {x y : U.State} (h : U.Trans P x none y) : ∃ q, x.pos = .run q := by
  cases h
  exact ⟨_, rfl⟩

/-- The untyped instance takes silent steps only when running. -/
theorem silentRunning (P : Profile) : (U.lts P).SilentRunning :=
  LTS.silentRunning_of_pos (L := U.lts P) State.pos rfl trans_step trans_tau_pos trans_tau_run

/-- Runs follow the positions. -/
theorem run_pos {x y : U.State} {p : List (Move U.E U.F)} (h : (U.lts P).Run x p y) :
    Silmaril.Games.Path x.pos p y.pos :=
  LTS.path_of_run_pos (L := U.lts P) State.pos trans_step trans_tau_pos h

/-- Traces are legal. -/
theorem traces_legal {p : List (Move U.E U.F)} (h : p ∈ (U.lts P).Traces) : Legal p := by
  obtain ⟨y, hy⟩ := h
  exact ⟨_, run_pos hy⟩

/-- An Opponent move legal at the position of a state is a transition of the state. -/
theorem step_of_isO {y : U.State} {x z : Pos U.E U.F} {m : Move U.E U.F}
    (hpos : y.pos = x) (hxz : Silmaril.Games.Step x m z) (hm : m.IsO) :
    ∃ y', U.Trans P y (some m) y' := by
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
    | reply _ _ n => exact ⟨_, .uret n⟩

/-- Traces are receptive. -/
theorem traces_receptive {p : List (Move U.E U.F)} {x z : Pos U.E U.F}
    {m : Move U.E U.F} (hp : p ∈ (U.lts P).Traces) (hx : Silmaril.Games.Path .idle p x)
    (hxz : Silmaril.Games.Step x m z) (hm : m.IsO) : p ++ [m] ∈ (U.lts P).Traces := by
  obtain ⟨y, hy⟩ := hp
  have hpos : y.pos = x := Silmaril.Games.Path.det (run_pos hy) hx
  obtain ⟨y', hy'⟩ := step_of_isO hpos hxz hm
  exact ⟨y', hy.append (LTS.Run.of_step (L := U.lts P) hy')⟩

/-- **The transition system denotes the untyped strategy.** -/
theorem denotes (P : Profile) : (U.lts P).Denotes (U.strategy P) := by
  intro p
  constructor
  · intro hp
    exact Strategy.mem_ofLTS_of_mem_traces hp (traces_legal hp)
  · rintro ⟨hl, u, hu, hp⟩
    have hu' : u ∈ (U.lts P).Traces := by
      rcases hu with rfl | ⟨hu, -⟩
      · exact ⟨_, .nil _⟩
      · exact hu
    rcases hp with hp | ⟨p₀, m, rfl, hp₀, hm⟩
    · exact LTS.traces_of_prefix hu' hp
    · obtain ⟨_, hpath⟩ := hl
      obtain ⟨x, hx, hxm⟩ := Silmaril.Games.Path.concat_iff.1 hpath
      exact traces_receptive (LTS.traces_of_prefix hu' hp₀) hx hxm hm

/-- The plays of the untyped strategy are the traces of its system. -/
theorem mem_strategy_iff {p : List (Move U.E U.F)} : p ∈ U.strategy P ↔ p ∈ (U.lts P).Traces :=
  (denotes P p).symm

/-- The finite plays of the divergence-observing strategy are the strategy. -/
theorem forget_dstrategy (P : Profile) : (U.dstrategy P).forget = U.strategy P := rfl

/-- The composite system of the closed program. -/
abbrev Cmp (U : UInstance) (P : Profile) (L : SEnv UImp) (q₀ : L.S) : LTS Sig.empty U.F :=
  (L.dlts q₀).comp (U.lts P)

/-- **The composite strategy is the strategy of the composite system.** -/
theorem closedD_eq_ofLTS (P : Profile) (L : SEnv UImp) (q : L.S) :
    U.closedD P L q = DStrategy.ofLTS (Cmp U P L q) :=
  (DStrategy.ofLTS_comp (SEnv.denotes_dlts L q) (denotes P)
    (LTS.SilentRunning.divRunning (SEnv.silentRunning_dlts L q))
    (LTS.SilentRunning.divRunning (silentRunning P))).symm

/-- The finite plays of the divergence-observing closed program are the closed program. -/
theorem forget_closedD (P : Profile) (L : SEnv UImp) (q : L.S) :
    (U.closedD P L q).forget = U.closed P L q := by
  show (L.dstrategy q).forget.comp (U.dstrategy P).forget = (L.strategy q).comp (U.strategy P)
  rw [SEnv.forget_dstrategy, forget_dstrategy]

/-- The composite system denotes the closed program. -/
theorem cmp_denotes (P : Profile) (L : SEnv UImp) (q : L.S) :
    (Cmp U P L q).Denotes (U.closed P L q) :=
  LTS.Denotes.comp (SEnv.denotes_dlts L q) (denotes P)

/-- An answer of the closed program is a trace of the composite system. -/
theorem responds_iff {L : SEnv UImp} {q : L.S} {f : U.F.Op} {a : UReply} :
    Responds (U.closed P L q) f a ↔ [.inr (.ask f), .inr (.ans f a)] ∈ (Cmp U P L q).Traces :=
  (cmp_denotes P L q _).symm

end Silmaril.Proofs.Wasm.Game.Untyped
