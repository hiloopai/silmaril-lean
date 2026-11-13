module

public import Silmaril.Wasm.Component.Wiring.Defs

/-!
# Canonical-ABI adapters and wiring programs

A component instance (or an export) gets each function it needs from the
current environment through an `Impl`: a *chain* of adapters ending in a
*target`. The chain is read from the consumer (top) down to the provider:

* `Adapter.lift ft` (`canon lift`): offers a component function of type `ft`
  on top of a core function of type `ft.flat`. Arguments are type checked and
  lowered on the way down; results are lifted on the way up.
* `Adapter.lower ft` (`canon lower`): offers a core function of type `ft.flat`
  on top of a component function of type `ft`. Arguments are lifted (this may
  trap), results are type checked and lowered.
* `Adapter.canon ft`: a *fused* `lower ∘ lift` (core caller, core callee):
  arguments and results are canonicalised by `canonFlat` (lift then lower).
* `Adapter.check ft`: a fused `lift ∘ lower` (component caller and callee):
  arguments and results are type checked.
* `Adapter.flatCheck ps rs`: a core-to-core type check; this is what
  `canon ft` becomes when all types of `ft` are trivially represented.

A target is a call of an environment function (`Target.call r`) or a known
constant answer (`Target.const res`, a statically known handler).

`Impl.prog e im : Payload → Prog sigU (Option Payload)` is the program of an
`Impl` over an environment of `e` functions, and `implsH` collects a list of
`Impl`s into a `Handler`. Payloads of the wrong kind and calls out of range
trap.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games
open Silmaril.Wasm (NumType)

/-- Canonical-ABI adapters (see the module documentation). -/
inductive Adapter where
  | lift (ft : FuncTy)
  | lower (ft : FuncTy)
  | canon (ft : FuncTy)
  | check (ft : FuncTy)
  | flatCheck (params results : List NumType)
  deriving Repr, Inhabited, DecidableEq

namespace Adapter

/-- The transformation of arguments, on their way down. -/
def down : Adapter → Payload → Option Payload
  | .lift ft, .vals vs => (checkLower ft.params vs).map .flat
  | .lower ft, .flat xs => (liftArgs ft.params xs).map .vals
  | .canon ft, .flat xs => (canonFlat ft.params xs).map .flat
  | .check ft, .vals vs => (checkVals ft.params vs).map .vals
  | .flatCheck ps _, .flat xs => (checkFlat ps xs).map .flat
  | _, _ => none

/-- The transformation of results, on their way up. -/
def up : Adapter → Payload → Option Payload
  | .lift ft, .flat ys => (liftArgs ft.results ys).map .vals
  | .lower ft, .vals ws => (checkLower ft.results ws).map .flat
  | .canon ft, .flat ys => (canonFlat ft.results ys).map .flat
  | .check ft, .vals ws => (checkVals ft.results ws).map .vals
  | .flatCheck _ rs, .flat ys => (checkFlat rs ys).map .flat
  | _, _ => none

end Adapter

/-- What a wiring program ends with. -/
inductive Target where
  /-- Call function `r` of the environment. -/
  | call (r : Nat)
  /-- Answer a statically known result. -/
  | const (res : Option Payload)
  deriving Repr, BEq, Inhabited

/-- A wiring program: adapters (consumer first), then a target. -/
structure Impl where
  /-- The adapters, from the consumer down. -/
  chain : List Adapter
  /-- The target. -/
  target : Target
  deriving Repr, BEq, Inhabited

/-- Run a chain of adapters around the continuation `k` (which performs the
target). A trap in an argument transformation answers `none` at once. -/
def runChain {E : Sig.{0}} : List Adapter → (Payload → Prog E (Option Payload)) → Payload →
    Prog E (Option Payload)
  | [], k, a => k a
  | ad :: c, k, a =>
    match ad.down a with
    | none => .pure none
    | some a' => (runChain c k a').bind fun r => .pure (r.bind ad.up)

/-- The program of a target over an environment of `e` functions (calls out
of range trap). -/
def Target.prog (e : Nat) : Target → Payload → Prog sigU (Option Payload)
  | .call r, a => if r < e then .call (r, a) (fun n => .pure n) else .pure none
  | .const res, _ => .pure res

/-- The program of a wiring `Impl` over an environment of `e` functions. -/
def Impl.prog (e : Nat) (im : Impl) : Payload → Prog sigU (Option Payload) :=
  runChain im.chain (im.target.prog e)

/-- The handler offering the functions implemented by the `Impl`s `ims` over
an environment of `e` functions (an index without an `Impl` traps). -/
def implsH (e : Nat) (ims : List Impl) : Handler sigU sigU := fun q =>
  match ims[q.1]? with
  | some im => im.prog e q.2
  | none => .pure none

/-- `implsH` at an interface of `t` functions. -/
def implsN (e : Nat) (ims : List Impl) (t : Nat) : Handler sigU (sigN t) := fun q =>
  implsH e ims (q.1.val, q.2)

/-- Substitution of wiring: an `Impl` over an environment of `σ.length`
functions becomes an `Impl` over the environment in which function `r` is
implemented by `σ[r]`. The chains are concatenated (consumer first); a call out
of range becomes a trap. -/
def Impl.subst (σ : List Impl) (im : Impl) : Impl :=
  match im.target with
  | .call r =>
    match σ[r]? with
    | some im' => ⟨im.chain ++ im'.chain, im'.target⟩
    | none => ⟨im.chain, .const none⟩
  | .const _ => im

/-- An `Impl` only calls functions below `e`. -/
def Impl.Scoped (e : Nat) (im : Impl) : Prop :=
  match im.target with
  | .call r => r < e
  | .const _ => True

/-- All `Impl`s of `σ` only call functions below `e`. -/
def ScopedList (e : Nat) (σ : List Impl) : Prop := ∀ im ∈ σ, im.Scoped e

/-- Forward the first `e` functions; the others trap. -/
def maskH (e : Nat) : Handler sigU sigU := fun q => (Target.call q.1).prog e q.2

/-- Direct forwarding of function `r`. -/
abbrev Impl.fwd (r : Nat) : Impl := ⟨[], .call r⟩

/-- The trapping `Impl`. -/
abbrev Impl.trap : Impl := ⟨[], .const none⟩

end Silmaril.Wasm.Component
