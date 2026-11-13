module

public import Silmaril.Wasm.Game.ULink.Defs
public import Silmaril.Wasm.Game.Untyped.Thms
import Silmaril.Proofs.Wasm.Game.ULink.Example
import Silmaril.Proofs.Wasm.Game.ULink.Inf
import Silmaril.Proofs.Wasm.Game.ULink.Obs
import Silmaril.Proofs.Wasm.Game.ULink.Setup
import Silmaril.Proofs.Wasm.Game.ULink.Callback

/-!
# Static linking in the untyped shared-store game: M3

For a link `L : ULink` over one store (`Silmaril.Wasm.Game.ULink.Defs`, which also explains why
the linker is semantic): the linked module `L.U`, run in the real store, is the composite
`(L.rstrategy P).comp (L.U.strategy P)` of the provider (the resolver, which runs the provider
functions in the real store) and the consumer (the same instance run in the stubbed store),
with the store relation applied to the moves (`L.stubUp`: upper moves carry stubbed stores).
Every profile; no determinism.

* `link_eq_comp`: **finite plays**: for plays whose stores have the link's layout
  (`L.LayoutPlay`), `p ∈ L.U.strategy P ↔ p.map L.stubUp ∈ L.compStrategy P`.
* `link_div_eq_comp`: **divergence**: `p ∈ (L.U.dstrategy P).div ↔
  p.map L.stubUp ∈ (L.compDStrategy P).div`, where the composite is the divergence-observing
  composite of `Silmaril.Games` (`compD_eq_ofLTS`: hidden infinite chatter between provider and
  consumer is divergence).
* `link_inf_eq_comp`: **infinite plays**: for a set `I` of plays with the layout,
  `I ∈ (L.U.dstrategy P).inf ↔ List.map L.stubUp '' I ∈ (L.compDStrategy P).inf`; an infinite run
  of either system is matched stage by stage by the other's simulation (dependent choice), and
  `stubUp` is injective on plays with the layout. `link_dstrategy_eq_comp` collects the three
  components: the full `DStrategy` equality up to `stubUp`, on plays with the layout.

## Closed programs: no per-play hypothesis

The layout is an invariant of closed programs (`Silmaril.Proofs.Wasm.Game.ULink.{Closed,Obs}`):
for a well-typed export call `f` (`L.U.CallOk f ps rs`) from a store with the layout whose
stubbed functions exist (`L.StubsIn`), against an environment satisfying the untyped host
contract `UEnvOk f.store Lenv` and allocating no stub codes (`L.EnvNoStub Lenv`), every
environment answer is to a well-typed call (the run invariant of the untyped game), so its store
extends the caller's (`Extend` keeps the provider code, `layout_extend`) and has no stub codes.

* `link_closed_obs`: **end-to-end M3**: the observations of the closed linked program
  `(Lenv.dstrategy q).comp (L.U.dstrategy P)` for `f` are those of the closed composite
  `L.compClosedD P Lenv q = (Lenv.dstrategy q).comp ((L.rdstrategy P).comp (L.U.dstrategy P))`
  for the stubbed question `L.stubQ f`, divergence included;
* `link_behaviours`: so are the Core-level behaviours (product semantics) of the linked call;
* `link_host`: **for every `HostOk` host** allocating no stub codes, the Core behaviours
  `behaviours P host` of the linked call are the observations of host ∘ provider ∘ consumer.

## The link of a `link?` setup

`Linking.Setup.toULink` (`Silmaril.Proofs.Wasm.Game.ULink.Setup`): for a setup of silmaril-lean's
`link?`, the semantic link of the shared world `S.sharedI` with the setup's stub set. Its
stubbed store is the setup's consumer-with-stubs store (`toULink_stubS`: `stubS S.sc = S.scs`),
and the shared store has the layout (`toULink_layout`, `toULink_stubsIn`), so
`Linking.Setup.ulink_behaviours`: the Core behaviours of the shared world are the observations
of environment ∘ provider ∘ consumer, the consumer asked in **the setup's consumer store**
`S.scs`.

Beyond silmaril-lean's `link?`: the consumer may keep imports that the provider does not
resolve (**partial linking**: such calls are forwarded by the resolver and are imports of the
linked module), and the consumer may import the provider's **memories, tables and globals**
(they are objects of the one store that every move carries). The provider may itself have
imports (its callouts are moves of the composite's lower interface), and references (including
function references to either side) may cross the interface: a callback into consumer code from
the provider runs inside the provider's run, in the real store.

The proofs are a forward simulation of the composite by the linked module (`≤`,
`Silmaril.Proofs.Wasm.Game.ULink.Forward`: consumer steps are linked steps by silmaril-lean's
`withFuncs` family lemmas; provider steps are linked steps in the consumer's callout context)
and a backward one (`≥`, `Silmaril.Proofs.Wasm.Game.ULink.Backward`: a linked step inside the
provider's code is a provider step, by inversion at the first non-value,
`Silmaril.Proofs.Wasm.Game.ULink.{Inv,Fill}`), both divergence-sensitive (each silent step is
matched by at least one silent step, or by none while a measure decreases).

## Worked example (`ULinkExample`)

`exProv` exports its memory and `set` (`i32.store 42` at address `0`); `exCons` imports both and
exports `run` (`call set; i32.load 0`). Both are validated and allocated by the spec's
`prepare?` into one store `exS` (kernel evaluation). `linked_play`: the linked module answers
`run` with `i32 42` in the written store `exS'`; `comp_play`: so does the composite of provider
and consumer (in the stubbed stores), every profile; `run_behaviour`: Core reduction agrees,
under every host.

## Worked example: partial linking and a callback (`ULinkCallback`)

`exApply` exports `apply : [(ref null $cb)] → [i32]` (`local.get 0; call_ref`); `exUse` imports a
host function `env.host` that the provider does not provide (**partial link**: `cbLink` stubs
`apply` only) and `apply`, and exports `run = ref.func cb; call apply` with `cb = call env.host`.
Allocated by `prepare?` into one store `cbS` after the host function (kernel evaluation).
`linked_play`: for every profile, value `v` and store `s'`, the linked module answers `run` by
asking the host (from the **callback** `cb`, three frames deep inside `apply`) and returning its
answer; `comp_play`: the composite has the same play through `stubUp` (the consumer's call of
`apply` is a question to the provider, which calls back consumer code in the shared store, and
the unresolved host import is a lower move of the composite).

## Gaps

* The play-level statements (`link_eq_comp`, `link_div_eq_comp`, `link_inf_eq_comp`) are for
  plays whose stores have the link's layout. The closed statements (`link_closed_obs`,
  `link_behaviours`, `link_host`) need no per-play hypothesis, only a well-typed call from a
  store with the layout and an environment satisfying `UEnvOk` and `EnvNoStub`; they compare
  the observations of one export call (answers' results and divergence), not whole closed plays
  over several calls, nor answer stores (the linked answer store `s` and the composite's
  `stubS s`).
* `EnvNoStub` is a hypothesis on the environment (it may not allocate a host function whose
  code is a stub code); stub codes are not made fresh.
* The linker is semantic. The bridge to `link?` (`Linking.Setup.toULink`) identifies the stores
  (`stubS S.sc = S.scs`, layout of `S.sc`) and states M3 for the shared world `S.sharedI`; it
  does not connect to the syntactically linked module `S.linkedI` (store `S.sl`), which the
  existing step A of `Silmaril.Wasm.Game.Linking` does in the scalar game, and no syntactic Silmaril
  linker for memories, tables or globals is given.
* The worked examples run the forwarding path of the resolver only through the provider's
  callouts (the callback's host call is asked by the provider); a consumer's own direct host
  call (`fwd`) is covered by the theorems but not exercised by an example.
* The resolver may also leave any stub call unanswered (`callStuck`, a state with no
  transition); this only adds the question itself, which receptiveness requires anyway, and
  keeps the resolver receptive without a typing hypothesis. (Not stated as a separate lemma;
  `link_eq_comp` and `link_div_eq_comp` hold with it.)

Proofs: `Silmaril.Proofs.Wasm.Game.ULink.*` (new).
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

namespace ULink

variable {L : ULink}

/-- The resolver system denotes the provider's strategy. -/
theorem rdenotes (P : Profile) : (L.rlts P).Denotes (L.rstrategy P) :=
  Silmaril.Proofs.Wasm.Game.ULink.rdenotes P

/-- **The divergence-observing composite is the strategy of the composite system.** -/
theorem compD_eq_ofLTS (P : Profile) :
    L.compDStrategy P = DStrategy.ofLTS ((L.rlts P).comp (L.U.lts P)) :=
  Silmaril.Proofs.Wasm.Game.ULink.compD_eq_ofLTS P

/-- `unstubS` inverts stubbing on stores with the layout. -/
theorem unstub_stub {s : Store Nat} (h : L.Layout s) : L.unstubS (L.stubS s) = s :=
  Silmaril.Proofs.Wasm.Game.ULink.unstub_stub h

/-- **M3 in the untyped game, finite plays, every profile**: the linked module's strategy is
the composite of the provider's and the consumer's, with the store relation on the moves. -/
theorem link_eq_comp {P : Profile} {p : List (Move UImp L.U.F)} (hl : L.LayoutPlay p) :
    p ∈ L.U.strategy P ↔ p.map L.stubUp ∈ L.compStrategy P :=
  Silmaril.Proofs.Wasm.Game.ULink.link_eq_comp hl

/-- **M3 in the untyped game, divergence, every profile.** -/
theorem link_div_eq_comp {P : Profile} {p : List (Move UImp L.U.F)} (hl : L.LayoutPlay p) :
    p ∈ (L.U.dstrategy P).div ↔ p.map L.stubUp ∈ (L.compDStrategy P).div :=
  Silmaril.Proofs.Wasm.Game.ULink.link_div_eq_comp hl

/-- **M3 in the untyped game, infinite plays, every profile**: for a set of plays with the
layout, it is an infinite play of the linked module exactly when its stubbed image is one of
the composite. -/
theorem link_inf_eq_comp {P : Profile} {I : Set (List (Move UImp L.U.F))}
    (hl : ∀ p ∈ I, L.LayoutPlay p) :
    I ∈ (L.U.dstrategy P).inf ↔ List.map L.stubUp '' I ∈ (L.compDStrategy P).inf :=
  Silmaril.Proofs.Wasm.Game.ULink.link_inf_eq_comp hl

/-- **M3 in the untyped game, all three components of the divergence-observing strategies**:
finite plays, divergences and infinite plays, on plays with the layout, up to `stubUp`. -/
theorem link_dstrategy_eq_comp (P : Profile) :
    (∀ p, L.LayoutPlay p → (p ∈ (L.U.dstrategy P).toStrategy ↔
        p.map L.stubUp ∈ (L.compDStrategy P).toStrategy)) ∧
      (∀ p, L.LayoutPlay p → (p ∈ (L.U.dstrategy P).div ↔ p.map L.stubUp ∈ (L.compDStrategy P).div)) ∧
      ∀ I : Set (List (Move UImp L.U.F)), (∀ p ∈ I, L.LayoutPlay p) →
        (I ∈ (L.U.dstrategy P).inf ↔ List.map L.stubUp '' I ∈ (L.compDStrategy P).inf) :=
  ⟨fun _ hl => link_eq_comp hl, fun _ hl => link_div_eq_comp hl, fun _ hl => link_inf_eq_comp hl⟩

/-! ### Closed programs -/

/-- An environment that never changes the functions of the store allocates no stub codes. -/
theorem envNoStub_of_funcs {Lenv : SEnv UImp}
    (h : ∀ q e a q', Lenv.Ans q e a q' → a.store.funcs = e.store.funcs) : L.EnvNoStub Lenv :=
  fun q e a q' hans hns b fi k hb hc => hns b fi k (h q e a q' hans ▸ hb) hc

/-- **Store growth keeps the layout**, when no stub-coded host function appears. -/
theorem layout_extend {s s' : Store Nat} (hl : L.Layout s) (hin : L.StubsIn s) (he : Extend s s')
    (hns : L.NoStub s') : L.Layout s' :=
  Silmaril.Proofs.Wasm.Game.ULink.layout_extend hl hin he hns

/-- The closed composite is the strategy of the closed composite system. -/
theorem compClosedD_eq_ofLTS (P : Profile) (Lenv : SEnv UImp) (q : Lenv.S) :
    L.compClosedD P Lenv q = DStrategy.ofLTS ((Lenv.dlts q).comp ((L.rlts P).comp (L.U.lts P))) :=
  Silmaril.Proofs.Wasm.Game.ULink.compClosedD_eq_ofLTS P Lenv q

/-- **End-to-end M3 in the untyped game, every profile, no per-play hypothesis.** For a
well-typed export call `f` from a store with the link's layout, against an environment
satisfying the untyped host contract and allocating no stub codes, the observations of the
closed linked program are those of the closed composite (environment ∘ provider ∘ consumer)
for the stubbed question, divergence included. -/
theorem link_closed_obs {P : Profile} {f : L.U.F.Op} {ps rs : Ty (.list .val)}
    (hq : L.U.CallOk f ps rs) (hl : L.Layout f.store) (hin : L.StubsIn f.store) {Lenv : SEnv UImp}
    (hL : UEnvOk f.store Lenv) (hns : L.EnvNoStub Lenv) (q : Lenv.S) :
    uDCompositeObs (L.U.closedD P Lenv q) f = uDCompositeObs (L.compClosedD P Lenv q) (L.stubQ f) :=
  Silmaril.Proofs.Wasm.Game.ULink.link_closed_obs ⟨hq, hL, hns, hin, hl⟩

/-- **End-to-end M3, Core behaviours**: the behaviours of the linked call against the
environment (product semantics) are the observations of the closed composite. -/
theorem link_behaviours {P : Profile} {f : L.U.F.Op} {ps rs : Ty (.list .val)}
    (hq : L.U.CallOk f ps rs) (hl : L.Layout f.store) (hin : L.StubsIn f.store) {Lenv : SEnv UImp}
    (hL : UEnvOk f.store Lenv) (hns : L.EnvNoStub Lenv) (q : Lenv.S) :
    uBehavioursOf P Lenv q (invoke f.store (L.U.addr f.target) f.args) =
      uDCompositeObs (L.compClosedD P Lenv q) (L.stubQ f) := by
  rw [UInstance.uAdequacy_div f Lenv q]
  exact link_closed_obs hq hl hin hL hns q

/-- **End-to-end M3 for every Core host**: for a host satisfying Core's host contract and
allocating no stub codes, the Core behaviours of a well-typed linked call from a store with the
layout are the observations of host ∘ provider ∘ consumer. -/
theorem link_host {P : Profile} {host : HostSemantics Nat} (hok : HostOk host)
    (hns : L.EnvNoStub (SEnv.uOfHost host)) {f : L.U.F.Op} {ps rs : Ty (.list .val)}
    (hq : L.U.CallOk f ps rs) (hl : L.Layout f.store) (hin : L.StubsIn f.store) :
    behaviours P host f.store (L.U.addr f.target) f.args =
      uDCompositeObs (L.compClosedD P (SEnv.uOfHost host) ()) (L.stubQ f) := by
  rw [UInstance.uAdequacy_host hok hq]
  exact link_closed_obs hq hl hin (uEnvOk_uOfHost hok f.store) hns ()

end ULink

/-! ### The link of a `link?` setup -/

namespace Linking.Setup

variable (S : Setup)

/-- The linked module of the semantic link of a setup is its shared world. -/
theorem toULink_U : S.toULink.U = S.sharedI.toU := rfl

/-- **The stubbed shared store is the setup's consumer-with-stubs store.** -/
theorem toULink_stubS : S.toULink.stubS S.sc = S.scs :=
  Silmaril.Proofs.Wasm.Game.ULink.toULink_stubS S

/-- The shared store has the layout of the semantic link. -/
theorem toULink_layout (hS : S.Scalar) : S.toULink.Layout S.sc :=
  Silmaril.Proofs.Wasm.Game.ULink.toULink_layout S hS

/-- The stubbed functions are functions of the shared store. -/
theorem toULink_stubsIn : S.toULink.StubsIn S.sc :=
  Silmaril.Proofs.Wasm.Game.ULink.toULink_stubsIn S

/-- **M3 for the shared world of a `link?` setup**: for a well-typed call of a linked export in
the shared store, the Core behaviours against an environment satisfying the untyped host
contract and allocating no stub codes are the observations of environment ∘ provider ∘
consumer, the consumer being asked in the setup's consumer-with-stubs store `S.scs`. -/
theorem ulink_behaviours {P : Profile} (hS : S.Scalar) {f : S.toULink.U.F.Op}
    (hf : f.store = S.sc) {ps rs : Ty (.list .val)} (hq : S.toULink.U.CallOk f ps rs)
    {Lenv : SEnv UImp} (hL : UEnvOk f.store Lenv) (hns : S.toULink.EnvNoStub Lenv) (q : Lenv.S) :
    uBehavioursOf P Lenv q (invoke f.store (S.toULink.U.addr f.target) f.args) =
      uDCompositeObs (S.toULink.compClosedD P Lenv q) ⟨f.target, S.scs, f.args⟩ := by
  have hl : S.toULink.Layout f.store := hf ▸ toULink_layout S hS
  have hin : S.toULink.StubsIn f.store := hf ▸ toULink_stubsIn S
  have hQ : S.toULink.stubQ f = ⟨f.target, S.scs, f.args⟩ := by
    rw [← toULink_stubS, ← hf]
    rfl
  rw [← hQ]
  exact ULink.link_behaviours hq hl hin hL hns q

end Linking.Setup

namespace ULinkExample

/-- `run` is the function at address `1` of the linked store. -/
theorem run_addr : exportFuncAddrs consPrep.1.frame.module = [1] :=
  Silmaril.Proofs.Wasm.Game.ULinkExample.t_addrs

/-- The linked store has the link's layout. -/
theorem exS_layout : exLink.Layout exS := Silmaril.Proofs.Wasm.Game.ULinkExample.exS_layout

/-- **The linked module answers `run` with `i32 42`** in the store where `set` wrote, every
profile. -/
theorem linked_play (P : Profile) :
    [.inr (.ask runQ), .inr (.ans runQ runA)] ∈ exLink.U.strategy P :=
  Silmaril.Proofs.Wasm.Game.ULinkExample.linked_play

/-- **The composite of provider and consumer answers `run` with `i32 42`**, every profile: the
consumer's call of `set` is a question to the provider, whose answer carries the store with the
shared memory written, which the consumer then reads. -/
theorem comp_play (P : Profile) :
    [.inr (.ask (exLink.stubQ runQ)), .inr (.ans (exLink.stubQ runQ) (exLink.stubR runA))] ∈
      exLink.compStrategy P :=
  Silmaril.Proofs.Wasm.Game.ULinkExample.comp_play

/-- **Core agrees**: under every host, `$invoke(run)` may return `i32 42`, every profile. -/
theorem run_behaviour (P : Profile) (host : HostSemantics Nat) :
    (Result.values [.num ⟨.int .i32, 42⟩]).toBehaviour ∈ behaviours P host exS 1 [] :=
  Silmaril.Proofs.Wasm.Game.ULinkExample.run_behaviour host

end ULinkExample

namespace ULinkCallback

/-- The linked store has the layout of the partial link. -/
theorem cbS_layout : cbLink.Layout cbS := Silmaril.Proofs.Wasm.Game.ULinkCallback.cbS_layout

/-- `cb` and `run` are the functions at addresses `2` and `3` of the linked store. -/
theorem run_addr : exportFuncAddrs usePrep.1.frame.module = [2, 3] :=
  Silmaril.Proofs.Wasm.Game.ULinkCallback.t_addrs

/-- **Partial linking with a callback, linked module**: for every profile, host answer value
`v` and store `s'`, the linked module answers `run` by asking the host import (from the callback
`cb`, called by the provider's `apply`) and returning its answer. -/
theorem linked_play (P : Profile) (s' : Store Nat) (v : Val) :
    runPlay ⟨s', .values [v]⟩ ∈ cbLink.U.strategy P :=
  Silmaril.Proofs.Wasm.Game.ULinkCallback.linked_play s' v

/-- **Partial linking with a callback, composite**: the composite of the provider and the
consumer has the same play through `stubUp`, when the host's store has the layout. -/
theorem comp_play (P : Profile) {s' : Store Nat} (hs' : cbLink.Layout s') (v : Val) :
    (runPlay ⟨s', .values [v]⟩).map cbLink.stubUp ∈ cbLink.compStrategy P :=
  Silmaril.Proofs.Wasm.Game.ULinkCallback.comp_play hs' v

/-- The example at the linked store itself. -/
theorem comp_play_cbS (P : Profile) (v : Val) :
    (runPlay ⟨cbS, .values [v]⟩).map cbLink.stubUp ∈ cbLink.compStrategy P :=
  comp_play P cbS_layout v

end ULinkCallback

end Silmaril.Wasm.Game
