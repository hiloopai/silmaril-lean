module

public import Silmaril.Wasm.Component.Reference.LinkedGRound.Defs
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound.Sess
import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound.Back

/-!
# A session round of a linked component with an abstract exporter: theorems

**Scope.** Every profile `P`; the reference machine over `core3P P` under `linkHost impl` (any
host state type and host functions); a `LinkedG` whose exporter is given by reference data `d`
at a placement `pl`, meeting R1 (`Frame`), R2 (`Fwd`), R5 (`Resume`) and R6 (`Bounded`); the
importer at an instance index `ii` outside the exporter's block.

**Proved (proof-internal, in `Proofs.….LinkedGRound`): one session round, forward.**

* `call_stepB` (`Step`): one import call answered by **any** exporter step on the lifted
  arguments: a returning step is `call_ret` with the importer's frame (`FrameG`: its thread in
  instance `ii`, which may leave, the export instances' thread tables reusable) re-established
  from the arena prefixes of `CallExt`, and the results checked; a trapping step is a trapped
  end with the parts related at the trapped core store (`TrapAtG`). A step answering a flat
  payload has no end of R2, so does not occur.
* `rounds_fwdB` (`Rounds`): the importer's core activation along a round of `LinkedG.SessSpec`
  (its instance path, the component import calls related by `ImpRel` and answered by an
  `ExpRun` of the exporter), iterating `call_stepB` with `LInvG.reach_fwd`, is a run without
  host events or `internal` traps to the importer's result (`LInvG` and `FrameG` again), or to
  a trapped end (arguments that do not lift, by `nest_trap_argsG`; an exporter step answering a
  trap).
* `call_atG` (`CallG`): `call_atLKTS` from **any** configuration ready for the host, the
  importer's instance at any index `ii` (not `[{}, ιe, ιi]`), with the return from any later
  store keeping the call's records at their indices.
* `linkCall_fwdB` (`Call`): **a `LinkedG.SessSpec` round from a configuration between calls
  (`ReadyB`) is a top-level call of the reference machine** (`Calls`): a round answering results
  is a resolved call ending between calls (`ReadyB` at the exporter's state and the importer's
  store after the round, the next call id); a round answering a trap is a trapped call (no
  `internal` fault) and `ReadyB` holds at its `resumeCfg` (R5, `lready_trapG`). The ends: the
  return, results of the importer that do not lift, a trap of the importer's core activation,
  and the trapped ends of the round. `ReadyB` carries the between-calls invariant `LReadyG`
  (`Ready`: `LReady` of `Linked2` with the exporter's half replaced by `d.Hold`).
* `sessL_fwdB` (`Sess`): **every `LinkedG.SessSpec` session from the stores of a `ReadyB`
  configuration is a resumable session (`SessCalls`)** from it, with the reference images of
  its outcomes.

**Proved (public, below): the read-back gap of R3, and its correction** (`Defs`).

* `locked_modify_step`, `locked_core_step`: a locked-down configuration with a non-empty
  control chain still steps, may unlock (a `modify`) and may change its core store (a core
  step). So the machine lemma suggested in #864 for the read-back, that a locked-down store stays
  locked with its core store fixed along a run, is **false** for non-empty control chains; R3's
  middle case, which may be witnessed by such a configuration (`Ends`' trapped branch), says
  nothing about the rest of the run.
* The correction `RefData.BwdT`: in R3's middle case a locked-down end has an empty control
  chain, so the middle case passes through returns only (`endsT_unlocked`), trapped runs being
  R3's third case. `BwdT.bwd`: it implies R3. `Simple.expSpec_refAdeqT`: a simple exporter
  meets R1, R2, the corrected R3, R4, R5 and R6 (its middle case is a return); `RefAdeqT.refAdeqB`.

**Not claimed** (what remains):

* **`ReadyB` after instantiation**, hence `LinkedG.sess_specToRef` from the empty configuration:
  the instantiation of `LinkedG.toRef` (R4 for the exporter, then the importer's instantiation
  after the exporter's instances: `instL_lrun` of `Linked2` with the exporter abstracted), and
  the static facts `StatB` there (the importer's lifted exports, its ownership of its
  functions, the trampolines `tr k` of the wiring).
* **`Linked2` as an instance**: `Linked2.toG` with `Simple.expSpec_refAdeqB`, which needs
  `ReadyB` from `Linked2`'s `ReadyL` (its `Rel4` under the renaming `gL` split into the
  importer's `PartRel` and the exporter's `SHold` under `h0`).
* **The read-back** (`linkCall_inv`, `sess_refToSpec`, `sessObs_eq`) against the corrected R3,
  then `LinkedG.toExp_refAdeq` and `LinkedN.sessAdequacy_full`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Engine
open Silmaril.Wasm.Numerics (Profile)

/-- **A locked-down configuration may unlock** (proved): a `modify` in focus applies its update
whatever the lockdown flag. -/
theorem locked_modify_step {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
    {dispatch : Call E → Canon.P E σ (Ret E)} (m : Machine.Config E σ) {th : Option ThreadId}
    {k : Unit → Canon.P E σ (Ret E)} {segs : List (Seg E σ)} {rest : List (Activation E σ)}
    (hc : m.ctl = ⟨th, .prog (.op (S := Canon.Eff E σ)
      (.modify fun s => { s with lockdown := false }) k), segs⟩ :: rest) :
    Machine.Step prof hr dispatch m .tau
      { m with
        store := { m.store with lockdown := false }
        ctl := ⟨th, .prog (k ()), segs⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound.locked_modify_step m hc

/-- **A locked-down configuration may change its core store** (proved): an internal step of a
running core activation in focus, whatever the lockdown flag. -/
theorem locked_core_step {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
    {dispatch : Call E → Canon.P E σ (Ret E)} (m : Machine.Config E σ) {th : Option ThreadId}
    {ct ct' : E.Thread (CanonHost E)} {c' : E.Store (CanonHost E)}
    {k : List FlatValue → Canon.P E σ (Ret E)} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} (hc : m.ctl = ⟨th, .core ct k, segs⟩ :: rest)
    (hs : E.status m.core ct = .running) (hi : E.Internal (m.core, ct) (c', ct')) :
    Machine.Step prof hr dispatch m .core
      { m with core := c', ctl := ⟨th, .core ct' k, segs⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound.locked_core_step m hc hs hi

/-- **The corrected R3 implies R3** (proved). -/
theorem ExpSpec.RefData.BwdT.bwd {P : Profile} {e : ExpSpec} {d : e.RefData P} (h : d.BwdT) :
    d.Bwd :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound.bwdT_bwd h

/-- **`RefAdeqT` implies `RefAdeqB`** (proved). -/
theorem ExpSpec.RefAdeqT.refAdeqB {P : Profile} {e : ExpSpec} (h : e.RefAdeqT P) :
    e.RefAdeqB P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound.refAdeqT_refAdeqB h

/-- **A simple exporter meets R1, R2, the corrected R3, R4, R5 and R6** (proved, every
profile), under the hypotheses of `Simple.expSpec_refAdeqB`. -/
theorem Simple.expSpec_refAdeqT (P : Profile) {c : Simple} (hc : c.Good) (hi : c.Inst)
    {I : Silmaril.Wasm.Game.ScalarInstance} (hI : c.mod.IsInst I)
    (hS : Linked2.ModSplitOk c.mod.mod) (hN : ∀ x ∈ c.exports, ∀ n, x.name ≠ tag "t" n) :
    (Simple.expSpec c I).RefAdeqT P :=
  Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound.simple_refAdeqT P hc hi hI hS hN

end Silmaril.Wasm.Component.Reference
