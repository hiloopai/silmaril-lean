module

public import Silmaril.Wasm.Game.Shared.Defs
public import Silmaril.Wasm.Game.StatefulEnv.Thms
import Silmaril.Proofs.Wasm.Game.Shared.After
import Silmaril.Proofs.Wasm.Game.Shared.Host

/-!
# Adequacy against hosts that read and write the store

This lifts the remaining environment restriction of M2: in
`Silmaril.Wasm.Game.{Adequacy,StatefulEnv,DivAdequacy}` the host cannot read or write
the module's store. Here the store travels with the moves (`sharedSig`,
`Silmaril.Wasm.Game.Shared.Defs`, which also justifies the design), and an
environment is any stateful, nondeterministic host state machine
`L : SEnv I.shE` whose answers may change the store, subject to the host contract
read on the game (`I.ShEnvOk s L`). Every profile `P`; no determinism.

## M1: the store-passing strategy

* `denotes_shLts`, `mem_shStrategy_iff`: `I.shStrategy P` is the strategy of the
  transition system `I.shLts P` (legal, receptive traces).
* `closedShD_eq_ofLTS`, `forget_closedShD`: the divergence-observing closed
  program `I.closedShD P L q = (L.dstrategy q).comp (I.shDStrategy P)` is the
  divergence-observing strategy of the composite system, with finite plays
  `I.closedSh P L q = (L.strategy q).comp (I.shStrategy P)`.

## M2 (every profile)

* `responds_closedSh_iff`: the closed program answers the export question
  `f = ⟨j, (s, args)⟩` with `(s', w)` exactly when a product run (`ShSteps P L`:
  Core reduction, host answers continuing in the store they return) of
  `$invoke(addr j, args)` in `s` reaches a result read as `w` in the store `s'`.
  No well-formedness needed.
* `mem_div_closedShD_iff`: it may diverge right after `[ask f]` exactly when the
  call has an infinite product run.
* `shAdequacy_div`: hence, for a well-formed store and environment, the
  behaviours of the call are **exactly** the observations `shDCompositeObs` of
  the composite strategy, divergence included; `shAdequacy` is the plain-strategy
  reading (may-divergence as a Core predicate, and no answer means divergence,
  `shDiverges_of_no_answer`).
* `closedSh_after_iff`: after an answered call the closed program continues
  against `L` in the host state left by the call (stateful environments persist
  across calls; the next question carries its store).

## Every Core host (every profile)

* `shAdequacy_host`: for a host relation satisfying Core's `HostOk` (stateless
  but store-changing and nondeterministic, exactly silmaril-lean's host
  interface) and keeping host functions typed as imports (`HostKeeps`), the Core
  `behaviours P host s (addr j) args` are the observations of the closed program
  against `SEnv.ofHost I.imports host`. `hostKeeps_of_funcs`: hosts that do not
  add functions keep them.

## The store-preserving results as special cases

* `shBehavioursOf_liftSh`, `shSteps_liftSh_iff`, `shEnvOk_liftSh`: a
  store-preserving stateful environment `L : SEnv I.E` is `SEnv.liftSh L`, with the
  same product semantics and well formed when `L.ThrowsBelow s.exns.length`.
* `shDCompositeObs_liftSh`: its observations in the new game are those of the old
  closed program `I.closedSD P s L q` (`sadequacy_div`), and
  `responds_liftSh_iff`: the old closed program answers `w` exactly when the new
  one answers `(s', w)` for some store `s'`.
* `behaviours_hostOf_eq`: the stateless store-preserving M2 (`hostOf`) is the
  one-state case.

## Remaining hypotheses and gaps

* `HostKeeps`: a host may allocate new host functions only as typed imports
  (imports are named by their index in `sharedSig`); `HostOk` alone allows a
  host function of any type at any index. Scalar interfaces, as in M2.
* M3 is not restated. With store-passing on both interfaces a provider is a
  candidate environment of a consumer in the same store, but `link?`'s linked
  store has the provider's functions as Wasm functions where the consumer's
  store has host functions, so linking needs a store relation between them (and
  a linker fragment with shared memories) on top of the forward/backward
  simulations of `Silmaril.Proofs.Wasm.Game.Linking`.

Proofs: `Silmaril.Proofs.Wasm.Game.Shared.*` (new).
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core

namespace ScalarInstance

variable {I : ScalarInstance}

/-! ### M1 -/

/-- The store-passing instance system denotes its strategy. -/
theorem denotes_shLts (P : Profile) : (I.shLts P).Denotes (I.shStrategy P) :=
  Silmaril.Proofs.Wasm.Game.Shared.denotes P

/-- The plays of the store-passing strategy are the traces of its system. -/
theorem mem_shStrategy_iff {P : Profile} {p : List (Move I.shE I.shF)} :
    p ∈ I.shStrategy P ↔ p ∈ (I.shLts P).Traces :=
  (denotes_shLts P p).symm

/-- **The closed program is the strategy of the composite system.** -/
theorem closedShD_eq_ofLTS (P : Profile) (L : SEnv I.shE) (q : L.S) :
    I.closedShD P L q = DStrategy.ofLTS ((L.dlts q).comp (I.shLts P)) :=
  Silmaril.Proofs.Wasm.Game.Shared.closedShD_eq_ofLTS P L q

/-- The finite plays of the divergence-observing closed program are the closed program. -/
theorem forget_closedShD (P : Profile) (L : SEnv I.shE) (q : L.S) :
    (I.closedShD P L q).forget = I.closedSh P L q :=
  Silmaril.Proofs.Wasm.Game.Shared.forget_closedShD P L q

/-! ### M2 -/

/-- **Answers are product runs, with the final store** (every profile). -/
theorem responds_closedSh_iff {P : Profile} {L : SEnv I.shE} {q : L.S} {f : I.shF.Op}
    {s' : Store Nat} {w : Answer (I.exports.get f.1)} :
    Responds (I.closedSh P L q) f (s', w) ↔
      ∃ (c' : Config Nat) (q' : L.S) (r : Result),
        ShSteps P L (invoke f.2.1 (I.addr f.1) f.2.2.1, q) (c', q') ∧ c'.code = r.toAdmin ∧
          c'.store = s' ∧ Answer.ofResult? (I.exports.get f.1) r = some w :=
  Silmaril.Proofs.Wasm.Game.Shared.responds_iff_run

/-- **Divergence against a store-changing host is divergence of the composite** (every
profile). -/
theorem mem_div_closedShD_iff {P : Profile} {L : SEnv I.shE} {q : L.S} (f : I.shF.Op) :
    [.inr (.ask f)] ∈ (I.closedShD P L q).div ↔
      InfiniteTrace (ShStep P L) (invoke f.2.1 (I.addr f.1) f.2.2.1, q) :=
  Silmaril.Proofs.Wasm.Game.Shared.mem_div_closedShD_iff f

/-- **M2 for stateful, nondeterministic, store-changing environments, divergence read off the
game, every profile.** The behaviours of the export call `f = ⟨j, (s, args)⟩` against the
host state machine `L` in state `q` are exactly the observations of the composite
`(L.dstrategy q).comp (I.shDStrategy P)`. -/
theorem shAdequacy_div {P : Profile} {L : SEnv I.shE} {f : I.shF.Op} (hw : I.WellFormed f.2.1)
    (hL : I.ShEnvOk f.2.1 L) (q : L.S) :
    shBehavioursOf P L q (invoke f.2.1 (I.addr f.1) f.2.2.1) =
      shDCompositeObs (I.closedShD P L q) f :=
  Silmaril.Proofs.Wasm.Game.Shared.shAdequacy_div hw hL q

/-- **M2 for store-changing environments, plain strategies, every profile.** -/
theorem shAdequacy {P : Profile} {L : SEnv I.shE} {f : I.shF.Op} (hw : I.WellFormed f.2.1)
    (hL : I.ShEnvOk f.2.1 L) (q : L.S) :
    shBehavioursOf P L q (invoke f.2.1 (I.addr f.1) f.2.2.1) =
      shCompositeObs (I.closedSh P L q) f ∪
        {b | b = .diverges ∧ InfiniteTrace (ShStep P L) (invoke f.2.1 (I.addr f.1) f.2.2.1, q)} :=
  Silmaril.Proofs.Wasm.Game.Shared.shAdequacy hw hL q

/-- **No answer is divergence**, against a store-changing host. -/
theorem shDiverges_of_no_answer {P : Profile} {L : SEnv I.shE} {f : I.shF.Op}
    (hw : I.WellFormed f.2.1) (hL : I.ShEnvOk f.2.1 L) {q : L.S}
    (hno : ∀ s' w, ¬ Responds (I.closedSh P L q) f (s', w)) :
    InfiniteTrace (ShStep P L) (invoke f.2.1 (I.addr f.1) f.2.2.1, q) :=
  Silmaril.Proofs.Wasm.Game.Shared.shDiverges_of_no_answer hw hL hno

/-- **The closed program after an answered call** continues against the environment in the
host state left by some product run of the call. -/
theorem closedSh_after_iff {P : Profile} {L : SEnv I.shE} {q : L.S} {f : I.shF.Op}
    {s' : Store Nat} {w : Answer (I.exports.get f.1)} (p : List (Move Sig.empty I.shF)) :
    [.inr (.ask f), .inr (.ans f (s', w))] ++ p ∈ I.closedSh P L q ↔
      ∃ (c' : Config Nat) (q' : L.S) (r : Result),
        ShSteps P L (invoke f.2.1 (I.addr f.1) f.2.2.1, q) (c', q') ∧ c'.code = r.toAdmin ∧
          c'.store = s' ∧ Answer.ofResult? (I.exports.get f.1) r = some w ∧
          p ∈ I.closedSh P L q' :=
  Silmaril.Proofs.Wasm.Game.Shared.closedSh_after_iff p

/-! ### Every Core host -/

/-- A `HostOk` host keeping host functions typed is a well-formed shared environment. -/
theorem shEnvOk_ofHost {host : HostSemantics Nat} (hok : HostOk host) (hk : I.HostKeeps host)
    (s₀ : Store Nat) : I.ShEnvOk s₀ (SEnv.ofHost I.imports host) :=
  Silmaril.Proofs.Wasm.Game.Shared.shEnvOk_ofHost hok hk s₀

/-- Hosts preserving the functions of the store keep host functions typed. -/
theorem hostKeeps_of_funcs {host : HostSemantics Nat}
    (h : ∀ hh s vs s' r, host hh s vs (.returned s' r) → s'.funcs = s.funcs) :
    I.HostKeeps host :=
  Silmaril.Proofs.Wasm.Game.Shared.hostKeeps_of_funcs h

/-- **M2 for every Core host, every profile.** For a host relation satisfying Core's host
contract `HostOk` (it may read and write the store, nondeterministically) and keeping host
functions typed as imports, the Core behaviours of the export call `f = ⟨j, (s, args)⟩` are
exactly the observations of the closed program against the host as a shared environment. -/
theorem shAdequacy_host {P : Profile} {host : HostSemantics Nat} (hok : HostOk host)
    (hk : I.HostKeeps host) {f : I.shF.Op} (hw : I.WellFormed f.2.1) :
    behaviours P host f.2.1 (I.addr f.1) f.2.2.1 =
      shDCompositeObs (I.closedShD P (SEnv.ofHost I.imports host) ()) f := by
  rw [Silmaril.Proofs.Wasm.Game.Shared.behaviours_eq_shBehavioursOf hok hk hw]
  exact shAdequacy_div hw (shEnvOk_ofHost hok hk _) ()

/-! ### Store-preserving environments as a special case -/

/-- A store-preserving environment throwing existing exceptions is a well-formed shared
environment. -/
theorem shEnvOk_liftSh {s : Store Nat} {L : SEnv I.E} (hL : L.ThrowsBelow s.exns.length) :
    I.ShEnvOk s (SEnv.liftSh L) :=
  Silmaril.Proofs.Wasm.Game.Shared.shEnvOk_liftSh hL

/-- **The old store-preserving observations are the new ones at the lifted environment.** -/
theorem shDCompositeObs_liftSh {P : Profile} {s : Store Nat} (hw : I.WellFormed s) (L : SEnv I.E)
    (hL : L.ThrowsBelow s.exns.length) (q : L.S) (f : I.F.Op) :
    shDCompositeObs (I.closedShD P (SEnv.liftSh L) q) (shOp s f) =
      dcompositeObs (I.closedSD P s L q) f := by
  rw [← sadequacy_div hw L hL q f, ← Silmaril.Proofs.Wasm.Game.Shared.shBehavioursOf_liftSh]
  exact (shAdequacy_div (f := shOp s f) hw (shEnvOk_liftSh hL) q).symm

/-- **The old closed program answers `w` exactly when the new one answers `(s', w)`** for some
final store `s'`. -/
theorem responds_liftSh_iff {P : Profile} {s : Store Nat} (hw : I.WellFormed s) {L : SEnv I.E}
    (hL : L.ThrowsBelow s.exns.length) {q : L.S} {f : I.F.Op} {w : I.F.Ar f} :
    Responds (I.closedS P s L q) f w ↔
      ∃ s', Responds (I.closedSh P (SEnv.liftSh L) q) (shOp s f) (s', w) := by
  constructor
  · intro h
    obtain ⟨c', q', r, run, final, hr⟩ := srun_of_answer h
    have run' := Silmaril.Proofs.Wasm.Game.Shared.shSteps_liftSh_iff.2 run
    exact ⟨c'.store, responds_closedSh_iff.2 ⟨c', q', r, run', final, rfl, hr⟩⟩
  · rintro ⟨s', h⟩
    obtain ⟨c', q', r, run, final, -, hr⟩ := responds_closedSh_iff.1 h
    have run' := Silmaril.Proofs.Wasm.Game.Shared.shSteps_liftSh_iff.1 run
    obtain ⟨w', hw', hresp⟩ := sanswer_of_run hw hL run' final
    have hww : w' = w := Option.some.inj (hw'.symm.trans hr)
    exact hww ▸ hresp

/-- **The stateless store-preserving M2 is the one-state, store-preserving case.** -/
theorem behaviours_hostOf_eq {P : Profile} {s : Store Nat} (hw : I.WellFormed s) (K : Env I.E)
    (hK : ThrowsBelow K s.exns.length) (f : I.F.Op) :
    behaviours P (hostOf I.imports K) s (I.addr f.1) f.2.1 =
      shDCompositeObs (I.closedShD P (SEnv.liftSh (SEnv.ofEnv K)) ()) (shOp s f) := by
  rw [behaviours_eq, ← SEnv.sbehavioursOf_ofEnv, ← Silmaril.Proofs.Wasm.Game.Shared.shBehavioursOf_liftSh]
  exact shAdequacy_div (f := shOp s f) hw (shEnvOk_liftSh ((SEnv.throwsBelow_ofEnv K _).2 hK)) ()

end ScalarInstance

/-- The lifted environment has the product behaviours of the store-preserving one. -/
theorem shBehavioursOf_liftSh {ts : List FnType} {P : Profile} {L : SEnv (ifaceSig ts)}
    (q : L.S) (c : Config Nat) : shBehavioursOf P (SEnv.liftSh L) q c = sbehavioursOf P L q c :=
  Silmaril.Proofs.Wasm.Game.Shared.shBehavioursOf_liftSh q c

/-- The product runs of the lifted environment are those of the store-preserving one. -/
theorem shSteps_liftSh_iff {ts : List FnType} {P : Profile} {L : SEnv (ifaceSig ts)}
    {x y : Config Nat × L.S} : ShSteps P (SEnv.liftSh L) x y ↔ SSteps P L x y :=
  Silmaril.Proofs.Wasm.Game.Shared.shSteps_liftSh_iff

end Silmaril.Wasm.Game
