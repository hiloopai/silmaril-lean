module

public import Silmaril.Wasm.Game.ULink.Defs
public import Silmaril.Proofs.Wasm.Game.Untyped.Strategy

/-!
# The resolver: legality, receptivity and the composite

* `rdenotes`: the resolver system `L.rlts P` denotes `L.rstrategy P` (legal, receptive).
* `rsilentRunning`: it takes silent steps only while running.
* `compD_eq_ofLTS`, `comp_denotes`: hence the composite strategies are those of the composite
  system `(L.rlts P).comp (L.U.lts P)`.

New proofs, following `Silmaril.Proofs.Wasm.Game.Untyped.Strategy`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.ULink

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.ULink Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

variable {L : ULink} {P : Profile}

/-- Visible resolver transitions are game steps of the positions. -/
theorem rtrans_step {x y : RState} {o : Move UImp UImp} (h : L.RTrans P x (some o) y) :
    Silmaril.Games.Step (x.pos L) o (y.pos L) := by
  cases h with
  | call e => exact .ask (E := UImp) (F := UImp) e
  | callStuck e => exact .ask (E := UImp) (F := UImp) e
  | fwdCall e => exact .ask (E := UImp) (F := UImp) e
  | fwdAsk e => exact .call _ _
  | fwdAns e a => exact .reply _ _ _
  | fwdRet e a => exact .ret _ _
  | ucall => exact .call _ _
  | uret a => exact .reply _ _ _
  | oret => exact .ret _ _

/-- Silent resolver transitions keep the position. -/
theorem rtrans_tau_pos {x y : RState} (h : L.RTrans P x none y) : y.pos L = x.pos L := by
  cases h
  rfl

/-- Silent resolver transitions happen in running positions. -/
theorem rtrans_tau_run {x y : RState} (h : L.RTrans P x none y) : ∃ q, x.pos L = .run q := by
  cases h
  exact ⟨_, rfl⟩

/-- The resolver takes silent steps only when running. -/
theorem rsilentRunning (P : Profile) : (L.rlts P).SilentRunning :=
  LTS.silentRunning_of_pos (L := L.rlts P) (RState.pos L) rfl rtrans_step rtrans_tau_pos
    rtrans_tau_run

/-- Resolver runs follow the positions. -/
theorem rrun_pos {x y : RState} {p : List (Move UImp UImp)} (h : (L.rlts P).Run x p y) :
    Silmaril.Games.Path (x.pos L) p (y.pos L) :=
  LTS.path_of_run_pos (L := L.rlts P) (RState.pos L) rtrans_step rtrans_tau_pos h

theorem run_not_O {e : UCall Nat} {m : Move UImp UImp} {z : Pos UImp UImp}
    (hxz : Silmaril.Games.Step (Pos.run e) m z) (hm : m.IsO) : False := by
  cases hxz <;> simp [Move.IsO] at hm

/-- An Opponent move legal at the position of a resolver state is a transition. -/
theorem rstep_of_isO {y : RState} {x z : Pos UImp UImp} {m : Move UImp UImp}
    (hpos : y.pos L = x) (hxz : Silmaril.Games.Step x m z) (hm : m.IsO) :
    ∃ y', L.RTrans P y (some m) y' := by
  cases y with
  | idle =>
    cases hpos
    cases hxz with
    | ask e =>
      cases ht : L.target e.target with
      | none => exact ⟨_, .fwdCall e ht⟩
      | some a => exact ⟨_, .callStuck e (by simp [ht])⟩
  | running e s t =>
    cases hpos
    exact (run_not_O hxz hm).elim
  | waiting e s t e' =>
    cases hpos
    cases hxz with
    | reply _ _ n => exact ⟨_, .uret n⟩
  | stuck e =>
    cases hpos
    exact (run_not_O hxz hm).elim
  | fwd e =>
    cases hpos
    exact (run_not_O hxz hm).elim
  | fwdWait e =>
    cases hpos
    cases hxz with
    | reply _ _ n => exact ⟨_, .fwdAns e n⟩
  | fwdRet e a =>
    cases hpos
    exact (run_not_O hxz hm).elim

/-- **The resolver system denotes the provider's strategy.** -/
theorem rdenotes (P : Profile) : (L.rlts P).Denotes (L.rstrategy P) := by
  intro p
  constructor
  · intro hp
    obtain ⟨y, hy⟩ := hp
    exact Strategy.mem_ofLTS_of_mem_traces ⟨y, hy⟩ ⟨_, rrun_pos hy⟩
  · rintro ⟨hl, u, hu, hp⟩
    have hu' : u ∈ (L.rlts P).Traces := by
      rcases hu with rfl | ⟨hu, -⟩
      · exact ⟨_, .nil _⟩
      · exact hu
    rcases hp with hp | ⟨p₀, m, rfl, hp₀, hm⟩
    · exact LTS.traces_of_prefix hu' hp
    · obtain ⟨_, hpath⟩ := hl
      obtain ⟨x, hx, hxm⟩ := Silmaril.Games.Path.concat_iff.1 hpath
      obtain ⟨y, hy⟩ := LTS.traces_of_prefix hu' hp₀
      have hpos : y.pos L = x := Silmaril.Games.Path.det (rrun_pos hy) hx
      obtain ⟨y', hy'⟩ := rstep_of_isO hpos hxm hm
      exact ⟨y', hy.append (LTS.Run.of_step (L := L.rlts P) hy')⟩

/-- The composite system. -/
abbrev Cmp (L : ULink) (P : Profile) : LTS UImp L.U.F := (L.rlts P).comp (L.U.lts P)

/-- The composite system denotes the composite strategy. -/
theorem comp_denotes (P : Profile) : (Cmp L P).Denotes (L.compStrategy P) :=
  LTS.Denotes.comp (rdenotes P) (Untyped.denotes P)

/-- **The divergence-observing composite is the strategy of the composite system.** -/
theorem compD_eq_ofLTS (P : Profile) : L.compDStrategy P = DStrategy.ofLTS (Cmp L P) :=
  (DStrategy.ofLTS_comp (rdenotes P) (Untyped.denotes P)
    (LTS.SilentRunning.divRunning (rsilentRunning P))
    (LTS.SilentRunning.divRunning (Untyped.silentRunning P))).symm

end Silmaril.Proofs.Wasm.Game.ULink
