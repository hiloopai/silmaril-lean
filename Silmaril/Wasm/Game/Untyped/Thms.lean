module

public import Silmaril.Wasm.Game.Untyped.Defs
public import Silmaril.Wasm.Game.Shared.Thms
import Silmaril.Proofs.Wasm.Game.Untyped.View
import Silmaril.Proofs.Wasm.Game.Untyped.Example

/-!
# The untyped shared-store game: adequacy for every host and arbitrary interfaces

This lifts the scalar-interface restriction of the Wasm game semantics, at every
Core 3.0 profile and with no determinism. Moves carry raw values and the store
(`untypedSig`, `Silmaril.Wasm.Game.Untyped.Defs`, which also justifies the design);
typing is store-relative well-formedness of moves (`UCall.CallsHost`,
`UInstance.CallOk`, `UReply.OkFor`, `UEnvOk`), so reference-typed parameters and
results (`funcref`, `externref`, GC and exception references) are covered by the same
statements as numbers.

## M1

* `UInstance.denotes_lts`, `mem_strategy_iff`: `U.strategy P` is the strategy of
  `U.lts P`; `closedD_eq_ofLTS`, `forget_closedD`: the closed program
  `(L.dstrategy q).comp (U.dstrategy P)` is the divergence-observing strategy of the
  composite system, with finite plays `U.closed P L q`.

## M2 (every profile)

* `responds_closed_iff`: answers `⟨s', r⟩` are the finite product runs to `r` in `s'`;
  `mem_div_closedD_iff`: divergence after `[ask f]` is an infinite product run.
* `uAdequacy_div`: **for every environment and every export question**, the
  behaviours are exactly the observations of the composite, divergence included. No
  well-formedness: answers carry raw results, so no result-typing step is needed.
* `uAdequacy`, `uDiverges_of_no_answer`: for a well-typed call and a well-formed
  environment, no answer is divergence (progress).
* `responds_ok`: rely/guarantee: if the environment satisfies the host contract on
  the imports, the instance satisfies it on its exports (typed store extending the
  caller's, result typed in the final store at the declared results).
* `closed_after_iff`: host state persists across calls.
* Store growth: `UReply.OkFor.extend`, `UEnvOk.mono`, `resultTyped_extend`.

## Every Core host, without `HostKeeps`

* `uEnvOk_uOfHost`: every `HostOk` host is a well-formed untyped environment.
* `uAdequacy_host`: **for every `HostOk` host** (it may read and write the store,
  allocate host functions of any type, and be nondeterministic), the Core behaviours
  of a well-typed invocation are the observations of the closed untyped program.
  `ScalarInstance.uAdequacy_host` is the case of a scalar instance at a well-formed
  store: the `HostKeeps` hypothesis of `shAdequacy_host` is not needed in the untyped
  game.

## The typed games as views

* `ScalarInstance.mem_shStrategy_iff_erase`: a typed play is a play of the typed shared
  strategy exactly when its erasure is a play of the untyped strategy (every profile,
  no well-formedness).
* `ScalarInstance.shDCompositeObs_eq_erase`: for a well-formed store and environment,
  the observations of the typed shared closed program are those of the untyped one
  against the erased environment; `ScalarInstance.dcompositeObs_eq_erase`: likewise for
  the store-hiding stateful game of `Silmaril.Wasm.Game.StatefulEnv` (through
  `SEnv.liftSh`).

## Worked example

`UntypedExample`: `exRelay` exports `relay : [externref] → [externref]` calling the
import `env.pass : [externref] → [externref]` on its argument (no scalar type:
`relay_not_scalar`). Against the reference-echoing host `echoHost` (`echoHost_ok`), the
closed untyped program answers every call `relay v` with `v` in the same store
(`relay_responds`, every profile, every value `v`), and for a `v` typed `externref`
in the instantiated store this is a Core behaviour and an observation of the
composite strategy (`relay_observes`); `relay_extern_host` instantiates it at the
internalised host reference `extern (host 7)`.

## Gaps

* M3 (linking) is not restated for the untyped game.
* `UEnvOk` constrains answers only; that a well-typed host call has an outcome
  (the first half of `HostOk`) is not needed, since an unanswered call is silent.
* Export names `U.X` are arbitrary; the untyped instance does not check that an
  export question invokes an existing function (ill-typed questions get whatever
  Core does; `uAdequacy_div` holds for them too).

Proofs: `Silmaril.Proofs.Wasm.Game.Untyped.*` (new).
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

/-! ### Store growth -/

/-- **Store growth preserves result typing.** -/
theorem resultTyped_extend {s s' : Store Nat} {r : Result} {ts : List CValType}
    (he : Extend s s') (h : ResultTyped s r ts) : ResultTyped s' r ts :=
  Silmaril.Proofs.Wasm.Game.Untyped.resultTyped_extend he h

/-- A reply stays well typed when its store grows. -/
theorem UReply.OkFor.extend {s s' : Store Nat} {rs : Ty (.list .val)} {a : UReply}
    (h : a.OkFor s rs) (hs' : StoreOk s') (he : Extend a.store s') :
    (⟨s', a.result⟩ : UReply).OkFor s rs :=
  Silmaril.Proofs.Wasm.Game.Untyped.okFor_extend h hs' he

/-- Well-formedness of environments is inherited by later stores. -/
theorem UEnvOk.mono {s₀ s₁ : Store Nat} {L : SEnv UImp} (he : Extend s₀ s₁) (hL : UEnvOk s₀ L) :
    UEnvOk s₁ L :=
  Silmaril.Proofs.Wasm.Game.Untyped.uEnvOk_mono he hL

/-- **Every `HostOk` host is a well-formed untyped environment**, from every store. -/
theorem uEnvOk_uOfHost {host : HostSemantics Nat} (hok : HostOk host) (s₀ : Store Nat) :
    UEnvOk s₀ (SEnv.uOfHost host) :=
  Silmaril.Proofs.Wasm.Game.Untyped.uEnvOk_uOfHost hok s₀

namespace UInstance

variable {U : UInstance}

/-! ### M1 -/

/-- The untyped instance system denotes its strategy. -/
theorem denotes_lts (P : Profile) : (U.lts P).Denotes (U.strategy P) :=
  Silmaril.Proofs.Wasm.Game.Untyped.denotes P

/-- The plays of the untyped strategy are the traces of its system. -/
theorem mem_strategy_iff {P : Profile} {p : List (Move U.E U.F)} :
    p ∈ U.strategy P ↔ p ∈ (U.lts P).Traces :=
  Silmaril.Proofs.Wasm.Game.Untyped.mem_strategy_iff

/-- **The closed program is the strategy of the composite system.** -/
theorem closedD_eq_ofLTS (P : Profile) (L : SEnv UImp) (q : L.S) :
    U.closedD P L q = DStrategy.ofLTS ((L.dlts q).comp (U.lts P)) :=
  Silmaril.Proofs.Wasm.Game.Untyped.closedD_eq_ofLTS P L q

/-- The finite plays of the divergence-observing closed program are the closed program. -/
theorem forget_closedD (P : Profile) (L : SEnv UImp) (q : L.S) :
    (U.closedD P L q).forget = U.closed P L q :=
  Silmaril.Proofs.Wasm.Game.Untyped.forget_closedD P L q

/-! ### M2 -/

/-- **Answers are product runs, with the final store** (every profile, every environment). -/
theorem responds_closed_iff {P : Profile} {L : SEnv UImp} {q : L.S} {f : U.F.Op} {a : UReply} :
    Responds (U.closed P L q) f a ↔
      ∃ (c' : Config Nat) (q' : L.S),
        USteps P L (invoke f.store (U.addr f.target) f.args, q) (c', q') ∧
          c'.code = a.result.toAdmin ∧ c'.store = a.store :=
  Silmaril.Proofs.Wasm.Game.Untyped.responds_iff_run

/-- **Divergence is divergence of the composite** (every profile, every environment). -/
theorem mem_div_closedD_iff {P : Profile} {L : SEnv UImp} {q : L.S} (f : U.F.Op) :
    [.inr (.ask f)] ∈ (U.closedD P L q).div ↔
      InfiniteTrace (UStep P L) (invoke f.store (U.addr f.target) f.args, q) :=
  Silmaril.Proofs.Wasm.Game.Untyped.mem_div_closedD_iff f

/-- **M2 for the untyped game, divergence read off the game, every profile.** For every
stateful, nondeterministic, store-changing environment `L` and every export question
`f = ⟨x, s, args⟩` (any raw arguments, any store), the behaviours of `$invoke(U.addr x, args)`
in `s` against `L` are exactly the observations of `(L.dstrategy q).comp (U.dstrategy P)`. -/
theorem uAdequacy_div {P : Profile} (f : U.F.Op) (L : SEnv UImp) (q : L.S) :
    uBehavioursOf P L q (invoke f.store (U.addr f.target) f.args) =
      uDCompositeObs (U.closedD P L q) f :=
  Silmaril.Proofs.Wasm.Game.Untyped.uAdequacy_div f L q

/-- **No answer is divergence**, for a well-typed call and a well-formed environment. -/
theorem uDiverges_of_no_answer {P : Profile} {L : SEnv UImp} {f : U.F.Op}
    {ps rs : Ty (.list .val)} (hq : U.CallOk f ps rs) (hL : UEnvOk f.store L) {q : L.S}
    (hno : ∀ a, ¬ Responds (U.closed P L q) f a) :
    InfiniteTrace (UStep P L) (invoke f.store (U.addr f.target) f.args, q) :=
  Silmaril.Proofs.Wasm.Game.Untyped.uDiverges_of_no_answer hq hL hno

/-- **M2 for the untyped game, plain strategies, every profile.** -/
theorem uAdequacy {P : Profile} {L : SEnv UImp} {f : U.F.Op} {ps rs : Ty (.list .val)}
    (hq : U.CallOk f ps rs) (hL : UEnvOk f.store L) (q : L.S) :
    uBehavioursOf P L q (invoke f.store (U.addr f.target) f.args) =
      uCompositeObs (U.closed P L q) f ∪
        {b | b = .diverges ∧ InfiniteTrace (UStep P L) (invoke f.store (U.addr f.target) f.args, q)} :=
  Silmaril.Proofs.Wasm.Game.Untyped.uAdequacy hq hL q

/-- **Rely/guarantee for the host contract**: if the environment answers well-typed host
calls as `HostOk` requires, every answer of the instance to a well-typed export call is a
typed store extending the caller's, with a result typed at the declared results relative to
that store. -/
theorem responds_ok {P : Profile} {L : SEnv UImp} {f : U.F.Op} {ps rs : Ty (.list .val)}
    (hq : U.CallOk f ps rs) (hL : UEnvOk f.store L) {q : L.S} {a : UReply}
    (h : Responds (U.closed P L q) f a) : a.OkFor f.store rs :=
  Silmaril.Proofs.Wasm.Game.Untyped.responds_ok hq hL h

/-- **The closed program after an answered call** continues against the environment in the
host state left by some product run of the call. -/
theorem closed_after_iff {P : Profile} {L : SEnv UImp} {q : L.S} {f : U.F.Op} {a : UReply}
    (p : List (Move Sig.empty U.F)) :
    [.inr (.ask f), .inr (.ans f a)] ++ p ∈ U.closed P L q ↔
      ∃ (c' : Config Nat) (q' : L.S),
        USteps P L (invoke f.store (U.addr f.target) f.args, q) (c', q') ∧
          c'.code = a.result.toAdmin ∧ c'.store = a.store ∧ p ∈ U.closed P L q' :=
  Silmaril.Proofs.Wasm.Game.Untyped.closed_after_iff p

/-! ### Every Core host -/

/-- **M2 for every Core host, every profile, no `HostKeeps`.** For a host relation satisfying
Core's host contract `HostOk`, the Core behaviours of a well-typed invocation (a typed store,
an existing function, arguments typed in that store, references included) are exactly the
observations of the closed untyped program against the host. -/
theorem uAdequacy_host {P : Profile} {host : HostSemantics Nat} (hok : HostOk host) {f : U.F.Op}
    {ps rs : Ty (.list .val)} (hq : U.CallOk f ps rs) :
    behaviours P host f.store (U.addr f.target) f.args =
      uDCompositeObs (U.closedD P (SEnv.uOfHost host) ()) f := by
  rw [Silmaril.Proofs.Wasm.Game.Untyped.behaviours_eq_uBehavioursOf hok hq]
  exact uAdequacy_div f (SEnv.uOfHost host) ()

end UInstance

/-! ### The typed games as views -/

namespace ScalarInstance

variable {I : ScalarInstance}

/-- **The typed shared strategy is the untyped strategy read on typed plays** (every profile,
no well-formedness). -/
theorem mem_shStrategy_iff_erase {P : Profile} {p : List (Move I.shE I.shF)} :
    p ∈ I.shStrategy P ↔ p.map I.eraseMove ∈ I.toU.strategy P :=
  Silmaril.Proofs.Wasm.Game.Untyped.mem_shStrategy_iff_erase

/-- The typed product behaviours are the untyped ones against the erased environment. -/
theorem shBehavioursOf_eq_erase {P : Profile} {L : SEnv I.shE} {f : I.shF.Op}
    (hw : I.WellFormed f.2.1) (hL : I.ShEnvOk f.2.1 L) (q : L.S) :
    shBehavioursOf P L q (invoke f.2.1 (I.addr f.1) f.2.2.1) =
      uBehavioursOf P L.erase q (invoke f.2.1 (I.addr f.1) f.2.2.1) :=
  Silmaril.Proofs.Wasm.Game.Untyped.shBehavioursOf_eq_erase hw hL q

/-- **The typed shared observations are the untyped ones** of the erased environment, at a
well-formed store and against a well-formed typed environment (every profile). -/
theorem shDCompositeObs_eq_erase {P : Profile} {L : SEnv I.shE} {f : I.shF.Op}
    (hw : I.WellFormed f.2.1) (hL : I.ShEnvOk f.2.1 L) (q : L.S) :
    shDCompositeObs (I.closedShD P L q) f = uDCompositeObs (I.toU.closedD P L.erase q) (I.eraseF f) := by
  rw [← shAdequacy_div hw hL q, shBehavioursOf_eq_erase hw hL q]
  exact UInstance.uAdequacy_div (U := I.toU) (I.eraseF f) L.erase q

/-- **The store-hiding stateful game is a view too**: its observations are those of the
untyped game against the erased lifted environment (every profile). -/
theorem dcompositeObs_eq_erase {P : Profile} {s : Store Nat} (hw : I.WellFormed s) (L : SEnv I.E)
    (hL : L.ThrowsBelow s.exns.length) (q : L.S) (f : I.F.Op) :
    dcompositeObs (I.closedSD P s L q) f =
      uDCompositeObs (I.toU.closedD P (SEnv.liftSh L).erase q) (I.eraseF (shOp s f)) := by
  rw [← shDCompositeObs_liftSh hw L hL q f]
  exact shDCompositeObs_eq_erase (f := shOp s f) hw (shEnvOk_liftSh hL) q

/-- **M2 for every Core host at a scalar instance, without `HostKeeps`**: at a well-formed
store, the Core behaviours of an export call under any `HostOk` host (which may add host
functions of any type) are the observations of the closed untyped program. -/
theorem uAdequacy_host {P : Profile} {host : HostSemantics Nat} (hok : HostOk host)
    {f : I.shF.Op} (hw : I.WellFormed f.2.1) :
    behaviours P host f.2.1 (I.addr f.1) f.2.2.1 =
      uDCompositeObs (I.toU.closedD P (SEnv.uOfHost host) ()) (I.eraseF f) :=
  UInstance.uAdequacy_host hok (Silmaril.Proofs.Wasm.Game.Untyped.callOk_of_wellFormed hw)

end ScalarInstance

/-! ### Worked example -/

namespace UntypedExample

/-- **The relay module's functions have no scalar type.** -/
theorem relay_not_scalar :
    exRelayS.funcs.map (fun fi => FnType.ofDefType? fi.type) = [none, none] :=
  Silmaril.Proofs.Wasm.Game.UntypedExample.relay_not_scalar

/-- The export `relay` is the function at address `1`. -/
theorem relay_addr : exportFuncAddrs exRelayPrep.1.frame.module = [1] :=
  Silmaril.Proofs.Wasm.Game.UntypedExample.t_addrs

/-- The instantiated store is typed. -/
theorem exRelayS_ok : StoreOk exRelayS := Silmaril.Proofs.Wasm.Game.UntypedExample.exRelayS_ok

/-- The reference-echoing host satisfies Core's host contract. -/
theorem echoHost_ok : HostOk echoHost := Silmaril.Proofs.Wasm.Game.UntypedExample.echoHost_ok

/-- The call `relay v` in the instantiated store. -/
abbrev relayQ (v : Val) : exRelayU.F.Op := ⟨(), exRelayS, [v]⟩

/-- **The game passes references through the import and back**: for every profile and every
value `v`, the closed untyped program against `echoHost` answers `relay v` with `v`, in the
same store. -/
theorem relay_responds (P : Profile) (v : Val) :
    Responds (exRelayU.closed P (SEnv.uOfHost echoHost) ()) (relayQ v) ⟨exRelayS, .values [v]⟩ := by
  obtain ⟨fi₀, fi₁, t, x, y, h⟩ := Silmaril.Proofs.Wasm.Game.UntypedExample.shape
  have run := Silmaril.Proofs.Wasm.Game.UntypedExample.run_relay (P := P) h v
  exact Silmaril.Proofs.Wasm.Game.Untyped.responds_of_run (U := exRelayU) (relayQ v)
    (c' := ⟨exRelayS, {}, vals [v]⟩) (r := .values [v])
    (Silmaril.Proofs.Wasm.Game.Untyped.uSteps_of_steps run) rfl

/-- `relay v` is a well-typed call when `v` is an `externref` of the instantiated store. -/
theorem relay_callOk {v : Val} (hv : ValOk exRelayS v (.refv (.ref true (.abs .extern)))) :
    exRelayU.CallOk (relayQ v) (Ty.ofList [.refv (.ref true (.abs .extern))])
      (Ty.ofList [.refv (.ref true (.abs .extern))]) := by
  obtain ⟨fi₀, fi₁, t, x, y, h⟩ := Silmaril.Proofs.Wasm.Game.UntypedExample.shape
  have hf : exRelayS.funcs[1]? = some fi₁ := by rw [h.funcs]; rfl
  have hargs : List.Forall₂ (ValOk exRelayS) [v]
      (Ty.ofList [.refv (.ref true (.abs .extern))] : Ty (.list .val)).toList := by
    rw [Ty.toList_ofList]
    exact .cons hv .nil
  exact ⟨exRelayS_ok, fi₁, hf, h.ty₁, hargs⟩

/-- **Adequacy on the example**: for an `externref` `v` of the instantiated store, returning
`v` is a Core behaviour of `relay v` under `echoHost` and an observation of the composite
untyped strategy, which equal each other (every profile). -/
theorem relay_observes (P : Profile) {v : Val}
    (hv : ValOk exRelayS v (.refv (.ref true (.abs .extern)))) :
    (Result.values [v]).toBehaviour ∈ behaviours P echoHost exRelayS 1 [v] ∧
      behaviours P echoHost exRelayS 1 [v] =
        uDCompositeObs (exRelayU.closedD P (SEnv.uOfHost echoHost) ()) (relayQ v) := by
  have heq := UInstance.uAdequacy_host (P := P) echoHost_ok (relay_callOk hv)
  have hobs : (Result.values [v]).toBehaviour ∈
      uDCompositeObs (exRelayU.closedD P (SEnv.uOfHost echoHost) ()) (relayQ v) := by
    have hforget : (exRelayU.closedD P (SEnv.uOfHost echoHost) ()).toStrategy =
        exRelayU.closed P (SEnv.uOfHost echoHost) () :=
      UInstance.forget_closedD (U := exRelayU) P (SEnv.uOfHost echoHost) ()
    refine Or.inl ⟨⟨exRelayS, .values [v]⟩, ?_, rfl⟩
    rw [hforget]
    exact relay_responds P v
  exact ⟨heq ▸ hobs, heq⟩

/-- The internalised host reference `extern (host 7)` is an `externref` in every store. -/
theorem extern_host_ok (s : Store Nat) :
    ValOk s (.ref (.extern (.host 7))) (.refv (.ref true (.abs .extern))) :=
  .ref (.sub (.extern (.host 7) (by simp)) (.ref (.abs _)) (.refNull .heapRefl))

/-- **The example at a concrete reference.** -/
theorem relay_extern_host (P : Profile) :
    (Result.values [.ref (.extern (.host 7))]).toBehaviour ∈
      uDCompositeObs (exRelayU.closedD P (SEnv.uOfHost echoHost) ())
        (relayQ (.ref (.extern (.host 7)))) := by
  have h := relay_observes P (extern_host_ok exRelayS)
  exact h.2 ▸ h.1

end UntypedExample

end Silmaril.Wasm.Game
