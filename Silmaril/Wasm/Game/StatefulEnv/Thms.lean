module

public import Silmaril.Wasm.Game.StatefulEnv.Defs
public import Silmaril.Wasm.Game.Strategy.Thms
import Silmaril.Proofs.Wasm.Game.StatefulEnv.Main
import Silmaril.Proofs.Wasm.Game.StatefulEnv.History
import Silmaril.Proofs.Wasm.Game.StatefulEnv.Div

/-!
# Adequacy against stateful, nondeterministic environments

This lifts the environment restriction of M2 (`Silmaril.Wasm.Game.Adequacy`):
there, environments were stateless partial answer functions `K : Env I.E`
(exactly the store-preserving Core `HostSemantics`, which has no host
state). Here an environment is a host state machine `L : SEnv I.E`
(`Silmaril.Wasm.Game.StatefulEnv.Defs`), relational in its answers, successor
states and divergence, and the operational side is Core reduction in product
with it (`SStep P L`), for an **arbitrary** silmaril profile `P`.

## Environments

* `SEnv.mem_strategy_iff`, `SEnv.mem_comp_iff`: plays of `L.strategy q` and of
  the closed program `L.strategy q ≫ σ`.
* `SEnv.strategy_ofStrategy`: every environment strategy
  `τ : Strategy Sig.empty E` is the strategy of its history machine, so the
  stateful environments are *all* environment strategies, stateful and
  nondeterministic (`closedS_ofStrategy`).
* `SEnv.strategy_ofEnv`, `SEnv.sbehavioursOf_ofEnv`: a stateless environment
  `K` is the one-state machine `ofEnv K`, with the same strategy, and with
  Core reduction under `hostOf` as product semantics.
* `SStep.core_step`, `core_step_sstep`: each product step is a Core step
  against the stateless (nondeterministic) host `L.hostAt q` of the current
  state, and conversely; for one host state the product semantics *is* Core
  reduction (`sbehavioursOf_eq_behavioursOf`).

## Adequacy (every profile)

* `sadequacy`: for a well-formed store `s`, any host state `q` and any export
  call `f`, the behaviours against the stateful host are the observations of
  the closed program `L.strategy q ≫ I.strategy P s` together with
  may-divergence (an infinite product run): terminating behaviours are
  exactly the answers (`sadequacy_answers`), and the absence of an answer is
  an infinite product run (`sdiverges_of_no_answer`).
* `closedS_after_iff`: after an answered call the closed program continues as
  the closed program at the module store **and** host state left by some
  product run of the call; so later calls are adequate, by `sadequacy` at the
  new store and host state.
* `sadequacy_strategy`: the same for an arbitrary environment strategy `τ`.
* `sadequacy_ofEnv`: at `ofEnv K` the statement is the stateless
  `adequacy_profile` (same Core behaviours, same closed program).

## Divergence read off the game (every profile)

* `SEnv.denotes_dlts`, `SEnv.forget_dstrategy`: the divergence-observing
  environment `L.dstrategy q` (a silent loop on a question `L` may leave
  unanswered) has the plays of `L.strategy q`.
* `closedSD_eq_ofLTS`: the composite `I.closedSD P s L q =
  (L.dstrategy q).comp (I.dstrategy P s)` of the two divergence-observing
  strategies is the strategy of the composite system
  (`DStrategy.ofLTS_comp`); `forget_closedSD`: its finite plays are
  `I.closedS P s L q`.
* `mem_div_closedSD_iff`: it may diverge right after `[ask f]` exactly when
  there is an infinite product run from the export call.
* `sadequacy_div`: hence the behaviours against the stateful host are
  **exactly** the observations `dcompositeObs` of the composite strategy,
  terminating behaviours and divergence alike; unlike `sadequacy`, no Core
  predicate is left on the game side.

## Remaining hypotheses

* `L.ThrowsBelow s.exns.length`: an exception answer `throw a` carries a raw
  exception address of the module's store (the game signature has no other
  name for an exception). An answer naming no existing exception leaves the
  Core configuration ill-typed (`throw_ref` of a dangling address), so
  progress and result typing fail and the product run can get stuck where the
  game has no move. Since the store only grows, the bound at the initial
  store suffices for every later state.
* Store preservation: the host answers with values, traps or exception
  addresses and cannot change the Wasm store (the store is hidden in the
  instance strategy). Hosts writing the module's memory are outside this
  fragment; see `docs/projects/games.md`.
* Scalar interfaces, as in M2.

Proofs: `Silmaril.Proofs.Wasm.Game.StatefulEnv.*`.
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core

namespace SEnv

variable {E : Sig.{0}}

/-- The plays of the strategy of a stateful environment. -/
theorem mem_strategy_iff {L : SEnv E} {q : L.S} {p : List (Move Sig.empty E)} :
    p ∈ L.strategy q ↔ ∃ u, L.Agrees q u ∧ p = u.map .inr :=
  Silmaril.Proofs.Wasm.Game.SEnv.mem_strategy_iff

/-- **Composition with a stateful environment.** -/
theorem mem_comp_iff {F : Sig.{0}} {L : SEnv E} {q : L.S} {σ : Strategy E F}
    {p : List (Move Sig.empty F)} :
    p ∈ (L.strategy q).comp σ ↔ ∃ t ∈ σ, L.Agrees q (lower t) ∧ p = (upper t).map .inr :=
  Silmaril.Proofs.Wasm.Game.SEnv.mem_comp_iff

/-- **Every environment strategy is a stateful environment**: the strategy of the history
machine of `τ` is `τ`. -/
theorem strategy_ofStrategy (τ : Strategy Sig.empty E) : (ofStrategy τ).strategy [] = τ :=
  Silmaril.Proofs.Wasm.Game.SEnv.strategy_ofStrategy τ

/-- A stateless environment is its one-state machine. -/
theorem strategy_ofEnv (K : Env E) : (ofEnv K).strategy () = K.strategy :=
  Silmaril.Proofs.Wasm.Game.SEnv.strategy_ofEnv K

/-- The host of the one-state machine of `K` is the host induced by `K`. -/
theorem hostAt_ofEnv {ts : List FnType} (K : Env (ifaceSig ts)) :
    (ofEnv K).hostAt () = hostOf ts K :=
  Silmaril.Proofs.Wasm.Game.SEnv.hostAt_ofEnv K

theorem throwsBelow_ofEnv {ts : List FnType} (K : Env (ifaceSig ts)) (n : Nat) :
    (ofEnv K).ThrowsBelow n ↔ Silmaril.Wasm.Game.ThrowsBelow K n :=
  Silmaril.Proofs.Wasm.Game.SEnv.throwsBelow_ofEnv K n

/-- **One host state: the product semantics is Core reduction** under the stateless host of
that state. -/
theorem sbehavioursOf_eq_behavioursOf {ts : List FnType} {P : Profile} {L : SEnv (ifaceSig ts)}
    [Subsingleton L.S] (q : L.S) (c : Config Nat) :
    sbehavioursOf P L q c = behavioursOf P (L.hostAt q) c :=
  Silmaril.Proofs.Wasm.Game.SEnv.sbehavioursOf_eq_behavioursOf q c

/-- For the one-state machine of `K`, the product semantics is Core reduction under
`hostOf ts K`. -/
theorem sbehavioursOf_ofEnv {ts : List FnType} {P : Profile} (K : Env (ifaceSig ts))
    (c : Config Nat) : sbehavioursOf P (ofEnv K) () c = behavioursOf P (hostOf ts K) c :=
  Silmaril.Proofs.Wasm.Game.SEnv.sbehavioursOf_ofEnv K c

end SEnv

/-- **A product step is a Core step** against the host of the current host state. -/
theorem SStep.core_step {ts : List FnType} {P : Profile} {L : SEnv (ifaceSig ts)}
    {c c' : Config Nat} {q q' : L.S} (h : SStep P L (c, q) (c', q')) :
    Execution.Core.Step P (L.hostAt q) c c' :=
  Silmaril.Proofs.Wasm.Game.SStep.core_step h

/-- **A Core step against the host of the current state is a product step.** -/
theorem core_step_sstep {ts : List FnType} {P : Profile} {L : SEnv (ifaceSig ts)}
    {c c' : Config Nat} {q : L.S} (h : Execution.Core.Step P (L.hostAt q) c c') :
    ∃ q', SStep P L (c, q) (c', q') :=
  Silmaril.Proofs.Wasm.Game.core_step_sstep h

namespace ScalarInstance

variable {I : ScalarInstance}

/-- **Game to operations, stateful host.** -/
theorem srun_of_answer {P : Profile} {s : Store Nat} {L : SEnv I.E} {q : L.S} {f : I.F.Op}
    {w : I.F.Ar f} (h : Responds (I.closedS P s L q) f w) :
    ∃ (c' : Config Nat) (q' : L.S) (r : Result),
      SSteps P L (invoke s (I.addr f.1) f.2.1, q) (c', q') ∧
      c'.code = r.toAdmin ∧ Answer.ofResult? (I.exports.get f.1) r = some w :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.srun_of_answer h

/-- **Operations to game, stateful host.** -/
theorem sanswer_of_run {P : Profile} {s : Store Nat} (hw : I.WellFormed s) {L : SEnv I.E}
    (hL : L.ThrowsBelow s.exns.length) {q q' : L.S} {f : I.F.Op} {c' : Config Nat}
    {r : Result} (run : SSteps P L (invoke s (I.addr f.1) f.2.1, q) (c', q'))
    (final : c'.code = r.toAdmin) :
    ∃ w, Answer.ofResult? (I.exports.get f.1) r = some w ∧ Responds (I.closedS P s L q) f w :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.sanswer_of_run hw hL run final

/-- **No answer is divergence, stateful host.** -/
theorem sdiverges_of_no_answer {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    {L : SEnv I.E} (hL : L.ThrowsBelow s.exns.length) {q : L.S} {f : I.F.Op}
    (hno : ∀ w, ¬ Responds (I.closedS P s L q) f w) :
    InfiniteTrace (SStep P L) (invoke s (I.addr f.1) f.2.1, q) :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.sdiverges_of_no_answer hw hL hno

/-- **M2 for stateful, nondeterministic environments, every profile.** The behaviours of an
export call against the host state machine `L` in state `q` are the observations of the
closed program `L.strategy q ≫ I.strategy P s` together with may-divergence: terminating
behaviours are exactly its answers, the absence of an answer is an infinite product run, and
divergence is a behaviour exactly when there is an infinite product run. -/
theorem sadequacy {P : Profile} {s : Store Nat} (hw : I.WellFormed s) (L : SEnv I.E)
    (hL : L.ThrowsBelow s.exns.length) (q : L.S) (f : I.F.Op) :
    sbehavioursOf P L q (invoke s (I.addr f.1) f.2.1) =
      compositeObs (I.closedS P s L q) f ∪
        {b | b = .diverges ∧ InfiniteTrace (SStep P L) (invoke s (I.addr f.1) f.2.1, q)} :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.sadequacy hw L hL q f

/-- **Terminating observations, stateful host** (both inclusions). -/
theorem sadequacy_answers {P : Profile} {s : Store Nat} (hw : I.WellFormed s) (L : SEnv I.E)
    (hL : L.ThrowsBelow s.exns.length) (q : L.S) (f : I.F.Op) (b : Behaviour Val)
    (hb : b ≠ .diverges) :
    b ∈ sbehavioursOf P L q (invoke s (I.addr f.1) f.2.1) ↔
      b ∈ compositeObs (I.closedS P s L q) f := by
  rw [sadequacy hw L hL q f]
  constructor
  · rintro (h | ⟨rfl, -⟩)
    · exact h
    · exact absurd rfl hb
  · exact Or.inl

/-- **The closed program after an answered call, stateful host**: it continues at the store
and the host state left by some product run of the call. -/
theorem closedS_after_iff {P : Profile} {s : Store Nat} {L : SEnv I.E} {q : L.S} {f : I.F.Op}
    {w : I.F.Ar f} (p : List (Move Sig.empty I.F)) :
    [.inr (.ask f), .inr (.ans f w)] ++ p ∈ I.closedS P s L q ↔
      ∃ (c' : Config Nat) (q' : L.S) (r : Result),
        SSteps P L (invoke s (I.addr f.1) f.2.1, q) (c', q') ∧
        c'.code = r.toAdmin ∧ Answer.ofResult? (I.exports.get f.1) r = some w ∧
        p ∈ I.closedS P c'.store L q' :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.closedS_after_iff p

/-- The closed program against the history machine of `τ` is `τ ≫ I.strategy P s`. -/
theorem closedS_ofStrategy (P : Profile) (s : Store Nat) (τ : Strategy Sig.empty I.E) :
    I.closedS P s (SEnv.ofStrategy τ) [] = τ.comp (I.strategy P s) := by
  unfold closedS
  rw [SEnv.strategy_ofStrategy]

/-- The closed program against the one-state machine of `K` is `I.closedWith P s K`. -/
theorem closedS_ofEnv (P : Profile) (s : Store Nat) (K : Env I.E) :
    I.closedS P s (SEnv.ofEnv K) () = I.closedWith P s K := by
  unfold closedS closedWith
  rw [SEnv.strategy_ofEnv]

/-- **M2 for an arbitrary environment strategy** `τ` (stateful, nondeterministic), every
profile: the behaviours against its history machine are the observations of `τ ≫ σ`
together with may-divergence. -/
theorem sadequacy_strategy {P : Profile} {s : Store Nat} (hw : I.WellFormed s)
    (τ : Strategy Sig.empty I.E) (hτ : (SEnv.ofStrategy τ).ThrowsBelow s.exns.length)
    (f : I.F.Op) :
    sbehavioursOf P (SEnv.ofStrategy τ) [] (invoke s (I.addr f.1) f.2.1) =
      compositeObs (τ.comp (I.strategy P s)) f ∪
        {b | b = .diverges ∧
          InfiniteTrace (SStep P (SEnv.ofStrategy τ)) (invoke s (I.addr f.1) f.2.1, [])} := by
  rw [← closedS_ofStrategy]
  exact sadequacy hw _ hτ [] f

/-- The divergence-observing composite closed program is the strategy of the composite
system of the environment and the instance. -/
theorem closedSD_eq_ofLTS (P : Profile) (s : Store Nat) (L : SEnv I.E) (q : L.S) :
    I.closedSD P s L q = DStrategy.ofLTS ((L.dlts q).comp (I.dlts P s)) :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.closedSD_eq_ofLTS P s L q

/-- The finite plays of the divergence-observing closed program are the closed program. -/
theorem forget_closedSD (P : Profile) (s : Store Nat) (L : SEnv I.E) (q : L.S) :
    (I.closedSD P s L q).forget = I.closedS P s L q :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.forget_closedSD P s L q

/-- **Divergence against a stateful host is divergence of the composite strategy** (every
profile). -/
theorem mem_div_closedSD_iff {P : Profile} {s : Store Nat} {L : SEnv I.E} {q : L.S}
    (f : I.F.Op) :
    [.inr (.ask f)] ∈ (I.closedSD P s L q).div ↔
      InfiniteTrace (SStep P L) (invoke s (I.addr f.1) f.2.1, q) :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.mem_div_closedSD_iff f

/-- **M2 for stateful, nondeterministic environments with divergence read off the game,
every profile.** The behaviours of an export call against the host state machine `L` in
state `q` are exactly the observations of the composite
`(L.dstrategy q).comp (I.dstrategy P s)` of the divergence-observing strategies. -/
theorem sadequacy_div {P : Profile} {s : Store Nat} (hw : I.WellFormed s) (L : SEnv I.E)
    (hL : L.ThrowsBelow s.exns.length) (q : L.S) (f : I.F.Op) :
    sbehavioursOf P L q (invoke s (I.addr f.1) f.2.1) = dcompositeObs (I.closedSD P s L q) f :=
  Silmaril.Proofs.Wasm.Game.ScalarInstance.sadequacy_div hw L hL q f

/-- **The stateless M2 is the one-state case**: `sadequacy` at `ofEnv K` is the statement of
`adequacy_profile`. -/
theorem sadequacy_ofEnv {P : Profile} {s : Store Nat} (hw : I.WellFormed s) (K : Env I.E)
    (hK : Silmaril.Wasm.Game.ThrowsBelow K s.exns.length) (f : I.F.Op) :
    behaviours P (hostOf I.imports K) s (I.addr f.1) f.2.1 =
      compositeObs (I.closedWith P s K) f ∪
        {b | b = .diverges ∧ Diverges P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1)} := by
  have h := sadequacy (P := P) hw (SEnv.ofEnv K) ((SEnv.throwsBelow_ofEnv K _).2 hK) () f
  rw [SEnv.sbehavioursOf_ofEnv, closedS_ofEnv] at h
  rw [behaviours_eq, h]
  congr 1
  ext b
  simp only [Set.mem_ofPred_eq]
  rw [← SEnv.hostAt_ofEnv]
  exact and_congr_right fun _ =>
    Silmaril.Proofs.Wasm.Game.SEnv.sinfinite_iff_diverges (L := SEnv.ofEnv K) () _

end ScalarInstance

end Silmaril.Wasm.Game
