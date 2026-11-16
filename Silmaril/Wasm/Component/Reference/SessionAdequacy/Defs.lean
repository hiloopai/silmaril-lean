module

public import Silmaril.Wasm.Component.Reference.Adequacy.Defs

/-!
# Resumable-session adequacy of the component IR: definitions

`Adequacy` (#669) compares the IR with the reference machine through `RefPubEquiv`, and gets
only the trap-last plays of the IR: after a trap, REF locks the whole store down
(`Machine.trapCfg`, `lockdown := true`; REF asserts `not lockdown` in `Store.invoke`), so no
further top-level call runs, while the IR strategy of a core instance keeps its store and
answers further calls (`Silmaril.Games.Abstract.StratSession`: a Wasm trap aborts the current
call, not the instance).

This module defines a **resumable reference session**, a session extension of REF's
single-run semantics that matches that Wasm session reading:

* a session is a sequence of top-level export calls `0, 1, …`, each run by the reference
  machine (`Calls`, at component choice profile `prof`);
* a resolved call continues from the configuration it ends in, as in `SeqCalls`;
* a trapped call ends that call, and the next call starts from `resumeCfg m mT`: the
  configuration `m` before the trapped call, with the **core store** (and host state) that the
  trapped configuration `mT` holds. The Core (Wasm) store, with every memory, global and table
  write the trapped call made, persists. The component-level bookkeeping of the aborted call
  (its task, thread and caller records, the instance's thread table, the nesting depth) and
  the `lockdown` flag are discarded with the call.

This is an explicit **modelling choice**, not REF: REF itself locks the store down after a
trap and accepts no further call. `resumeCfg` and `SessCalls` are defined from reference
machine runs only (no IR, no strategy).

`RefSessEquiv P prof c c'`: the same export types, and for every typed sequence of calls the
same session outcomes (`sessObs`: for each call, its results or a trap).

Scope and non-claims (`SessionAdequacy.Thms`):

* `Simple` components, float-free (`Simple.FloatFree`), in the fragment `Simple.Adequate`;
* terminating outcomes only: `Comp.den` has finite plays, so divergence (and deadlock and
  cancellation, which never occur here) are not compared. The infinite case belongs to the
  game-level infinite closure (`StratSession.threadS`'s `inf` component) and is a later step;
* not contextual full abstraction: the observer is a host calling exports in sequence;
* the parser from bytes to `Comp` (and to `Simple`) is not involved; its correctness is a
  separate obligation.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

section Session

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}

/-- **Resuming after a trapped call** (the session extension of REF; REF itself locks down):
the configuration `m` before the call, with the core store and host state of the trapped
configuration `mT`. -/
def resumeCfg (m mT : Machine.Config E σ) : Machine.Config E σ :=
  { m with core := mT.core, host := mT.host }

/-- **A resumable session** of top-level calls `k, k + 1, …` of the function values `f` on
`args` from `m`, with the outcome of each call: `some rs` for a call resolving with results
`rs`, `none` for a trapped call, after which the session resumes from `resumeCfg`. -/
inductive SessCalls (prof : ProfileKind) (h : Host E σ) :
    Machine.Config E σ → Nat → List (FuncId × List Val) → List (Option (List Val)) →
    Prop where
  | nil (m : Machine.Config E σ) (k : Nat) : SessCalls prof h m k [] []
  | ret {m m₁ : Machine.Config E σ} {k : Nat} {f : FuncId} {args rs : List Val}
      {cs : List (FuncId × List Val)} {outs : List (Option (List Val))} :
      Calls prof h.hr h.dispatch m ⟨k⟩ f args m₁ (.resolved (some rs)) →
      SessCalls prof h m₁ (k + 1) cs outs →
      SessCalls prof h m k ((f, args) :: cs) (some rs :: outs)
  | trap {m m₁ : Machine.Config E σ} {k : Nat} {f : FuncId} {args : List Val}
      {cs : List (FuncId × List Val)} {outs : List (Option (List Val))} :
      Calls prof h.hr h.dispatch m ⟨k⟩ f args m₁ .trap →
      SessCalls prof h (resumeCfg m m₁) (k + 1) cs outs →
      SessCalls prof h m k ((f, args) :: cs) (none :: outs)

/-- **The outcomes of a resumable session**: instantiate `c` from the empty store, then call
the exports named in `calls` in order (top-level calls `0, 1, …`) as a resumable session. -/
def sessBehaviours (prof : ProfileKind) (h : Host E σ) (σ0 : σ) (c : CompAst E.Module)
    (calls : List (String × List Val)) : Set (List (Option (List Val))) :=
  {outs | ∃ m₀ inst es fs,
    InstResult.instance m₀ inst es ∈ instBehaviours prof h (initConfig σ0) c [] ∧
    calls.mapM (fun q => es.lookup q.1) = some fs ∧
    SessCalls prof h m₀ 0 (fs.zip (calls.map Prod.snd)) outs}

end Session

/-! ## The specification of sessions (no machine, no strategy)

The canonical-ABI specification of a session on one instance: the Core store is threaded
through returned calls (`RetAt`) and trapped calls (`TrapAt`) alike. -/

section SessSpec

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

/-- The flat results of a Core result, as `coreAt` reads them. -/
def coreRes : Result → Option (List Flat)
  | .values vs => vs.mapM toFlat?
  | _ => none

/-- **A trapped call** of export `x` on `vs` from the store `s`: the lowered arguments run
host-free to a result whose lift traps (a Core trap, an uncaught exception, or results the IR
lift rejects), leaving the store `s'`. -/
structure TrapAt (P : Profile) (c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance)
    (x : SimpleExport) (vs : List IVal) (s s' : Store Nat) : Prop where
  typed : ValTy.checkList x.ty.params vs = true
  run : ∃ (t' : Thread) (res : Result),
    Silmaril.Wasm.Game.Reach P
      (s, Thread.invokeFlat (I.addrs.getD x.core 0) (lowerArgs x.ty.params vs)) (s', t') ∧
    Silmaril.Wasm.Game.ResultAt s' t' res ∧ liftOutcome x.ty (coreRes res) = .traps

/-- **Sessions of the specification** from the store `s` to the store `s'`: returned and
trapped calls threading the store, with the IR results of each call (`none` for a trap). -/
inductive SessSpec (P : Profile) (c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance) :
    Store Nat → List (SimpleExport × List IVal) → List (Option (List IVal)) → Store Nat →
    Prop where
  | nil (s : Store Nat) : SessSpec P c I s [] [] s
  | ret {s s₁ s₂ : Store Nat} {x : SimpleExport} {vs ws : List IVal}
      {cs : List (SimpleExport × List IVal)} {outs : List (Option (List IVal))} :
      RetAt P c I x vs s ws s₁ → SessSpec P c I s₁ cs outs s₂ →
      SessSpec P c I s ((x, vs) :: cs) (some ws :: outs) s₂
  | trap {s s₁ s₂ : Store Nat} {x : SimpleExport} {vs : List IVal}
      {cs : List (SimpleExport × List IVal)} {outs : List (Option (List IVal))} :
      TrapAt P c I x vs s s₁ → SessSpec P c I s₁ cs outs s₂ →
      SessSpec P c I s ((x, vs) :: cs) (none :: outs) s₂

end SessSpec

/-- Session outcomes of IR values, as reference values. -/
def refOuts (outs : List (Option (List IVal))) :
    List (Option (List Silmaril.Wasm.Component.Value.Val)) :=
  outs.map (Option.map (List.map toRefVal))

/-- The IR play of a session: each call `(j, vs)` answered by its results, or by a trap
(`none`). -/
def sessMoves (c : Simple) :
    List (Fin c.exports.length × List IVal) → List (Option (List IVal)) →
    List (Silmaril.Games.Move (sigN 0) (sigN c.toComp.exports.length))
  | (j, vs) :: cs, o :: os =>
    .inr (.ask (⟨j, by simp [Simple.toComp]⟩, .vals vs)) ::
      .inr (.ans (m := (⟨j, by simp [Simple.toComp]⟩, .vals vs)) (o.map .vals)) ::
      sessMoves c cs os
  | _, _ => []

/-- **The session observations** of calling the exports `calls` of `c` (by index, on IR
values) as a resumable session on the reference machine. -/
noncomputable def sessObs (P : Profile) (prof : ProfileKind) (c : Simple)
    (calls : List (Fin c.exports.length × List IVal)) :
    Set (List (Option (List Silmaril.Wasm.Component.Value.Val))) :=
  sessBehaviours prof (refHost P) () c.toRef
    (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal))

/-- **The resumable-session equivalence**, on the reference machine only: the same export
types, and for every typed sequence of calls the same session outcomes. Export names are not
compared: the IR calls exports by position. -/
structure RefSessEquiv (P : Profile) (prof : ProfileKind) (c c' : Simple) : Prop where
  len : c.exports.length = c'.exports.length
  ty : ∀ j : Fin c.exports.length, c'.exports[Fin.cast len j].ty = c.exports[j].ty
  obs : ∀ calls : List (Fin c.exports.length × List IVal), TypedCalls c calls →
    sessObs P prof c calls = sessObs P prof c' (castCalls len calls)

end Silmaril.Wasm.Component.Reference
