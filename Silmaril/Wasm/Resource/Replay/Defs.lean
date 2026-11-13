module

public import Silmaril.Wasm.Resource.Handle.Defs
public import Silmaril.Wasm.Resource.Check.Defs
public import Silmaril.Wasm.Verify.Refute.Defs
public import Silmaril.Wasm.Spec.Run.Defs

@[expose] public section

/-!
# Replaying environment answers on real modules

A computable refuter for protocol sentences whose counterexamples go **through environment
answers** (use after free, double free), run by kernel evaluation.

* `RMove`: a move with plain indices (export/import number, Core arguments, behaviour);
  `RMove.ofEvent` reads a Wasm event this way.
* `Script`: the environment, as answer values for the `k`-th callout `h args`.
* `runTo? fuel c`: run silmaril-lean's verified interpreter (`runI`, deterministic profile
  `profile refOracle`, no host) from the configuration `c`; if it stops at a host-call redex
  (`decompose?`), the stopped configuration, the redex context, callee, host function and
  arguments.
* `replayFrom I sc fuel n k c`: up to `n` callouts from `c`. At each callout `h args` whose
  arguments are typed by import `h`, record `ask h args`; if the scripted answer `vs` is typed by
  the result types of import `h` and of the called host function, record `ans h (returns vs)`,
  plug `vs` into the redex context (the configuration of silmaril-lean's `resumeResult`) and go on.
* `replayExport I sc fuel n j k`: the call of export `j` with candidate arguments `k`, then
  `replayFrom` from `$invoke`.
* `replayRefute I sc fuel n bad`: the first replay (exports in order, candidates `0`, `1`) that
  `bad` flags.

Classifiers on recorded moves: `clientEvN` (client handle protocol, imports by number) and
`obEvN` (ownership protocol, `NRoles` by number; `NRoles.toOB` the roles of an interface).
`clientReplay?`, `obReplay?`: the refuters on modules, with the scripts `clientScript`,
`obScript` (an allocation returns the fresh `i32` handle `7 + k`, other imports return
nothing).

Soundness (`Silmaril.Wasm.Resource.Replay.Thms`): every recorded replay is the play of the
instance's strategy, for every profile admitting the deterministic steps of the refuter.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game Silmaril.Wasm.Verify Silmaril.Wasm.Spec

/-- A move with plain indices. -/
inductive RMove where
  /-- Export `j` is called with `args`. -/
  | call (j : Nat) (args : List Val)
  /-- Export `j` answers `b`. -/
  | ret (j : Nat) (b : Behaviour Val)
  /-- Import `h` is called with `args`. -/
  | ask (h : Nat) (args : List Val)
  /-- Import `h` answers `b`. -/
  | ans (h : Nat) (b : Behaviour Val)

/-- A Wasm event read with plain indices. -/
def RMove.ofEvent {X : WIface} : WEvent X → RMove
  | .inr (.ask j a) => .call j.val a
  | .inr (.ans j b) => .ret j.val b
  | .inl (.ask i a) => .ask i.val a
  | .inl (.ans i b) => .ans i.val b

/-- The environment: the answer values to the `k`-th callout `h args`. -/
abbrev Script := Nat → Nat → List Val → List Val

/-- Run the interpreter from `c`; if it stops at a host-call redex, the stopped configuration and
the redex. -/
def runTo? (fuel : Nat) (c : Config Nat) : Option (Config Nat × Ctx × Nat × Nat × List Val) :=
  let d := (Exec.runI refOracle fuel c).1
  (decompose? d.store d.code).map fun x => (d, x)

/-- Values typed by the results of an optional type. -/
def resultsOk : Option FnType → List Val → Bool
  | some ft, vs => typedB ft.results vs
  | none, _ => false

/-- Arguments typed by the parameters of import `h`. -/
def argsOk (I : ScalarInstance) (h : Nat) (args : List Val) : Bool :=
  match I.imports[h]? with
  | some ft => typedB ft.params args
  | none => false

/-- An answer typed by import `h` and by the host function at address `a`. -/
def ansOk (I : ScalarInstance) (s : Store Nat) (a h : Nat) (vs : List Val) : Bool :=
  resultsOk I.imports[h]? vs && resultsOk (funcType? s a) vs

/-- **The replay** of up to `n` callouts from `c` (the `k`-th callout first). -/
def replayFrom (I : ScalarInstance) (sc : Script) (fuel : Nat) :
    Nat → Nat → Config Nat → List RMove
  | 0, _, _ => []
  | n + 1, k, c =>
    match runTo? fuel c with
    | none => []
    | some (d, E, a, h, args) =>
      if argsOk I h args then
        if ansOk I d.store a h (sc k h args) then
          .ask h args :: .ans h (.returns (sc k h args)) ::
            replayFrom I sc fuel n (k + 1) ⟨d.store, d.frame, E.fill (vals (sc k h args))⟩
        else [.ask h args]
      else []

/-- The replay of the call of export `j` with candidate arguments `k`. -/
def replayExport (I : ScalarInstance) (sc : Script) (fuel n : Nat) (j : Fin I.exports.length)
    (k : Nat) : List RMove :=
  .call j.val (candArgs k (I.exports.get j).params) ::
    replayFrom I sc fuel n 0 (invoke I.store (I.addr j) (candArgs k (I.exports.get j).params))

/-- **The replay refuter**: the first replay flagged by `bad`. -/
def replayRefute (I : ScalarInstance) (sc : Script) (fuel n : Nat) (bad : List RMove → Bool) :
    Option (List RMove) :=
  ((List.finRange I.exports.length).flatMap fun j =>
    [replayExport I sc fuel n j 0, replayExport I sc fuel n j 1]).find? bad

/-! ## Client handles -/

/-- The client classifier on recorded moves (imports `ia`, `iu`, `if_` by number). -/
def clientEvN (ia iu if_ : Nat) : RMove → HEv Val
  | .ans i b => if i = ia then HEv.allocOf b else .skip
  | .ask i a => if i = iu then HEv.useOf a else if i = if_ then HEv.freeOf a else .skip
  | _ => .skip

/-- A replay rejected by the client protocol. -/
def clientBad (ia iu if_ : Nat) (rs : List RMove) : Bool :=
  !(handleProto Val .client).acceptsB (rs.map (clientEvN ia iu if_))

/-- The client script: `alloc` returns the fresh handle `7 + k`, other imports nothing. -/
def clientScript (ia : Nat) : Script := fun k h _ =>
  if h = ia then [Val.i32 (BitVec.ofNat 32 (7 + k))] else []

/-- **The client replay refuter** on a module, with up to `n` callouts. -/
def clientReplay? (m : Module) (ia iu if_ n : Nat) : Option (List RMove) :=
  replayRefute (instOf m) (clientScript ia) refFuel n (clientBad ia iu if_)

/-! ## Ownership -/

/-- Ownership roles by number (`OBRoles` with plain indices). -/
structure NRoles where
  /-- Imports returning a new owned handle. -/
  alloc : Nat → Bool
  /-- Imports using their handle argument. -/
  use : Nat → Bool
  /-- Imports dropping their (owned) handle argument. -/
  free : Nat → Bool
  /-- Imports taking ownership of their handle argument. -/
  give : Nat → Bool
  /-- Exports whose handle argument is borrowed for the call. -/
  lend : Nat → Bool
  /-- Exports whose handle argument is owned by the program from then on. -/
  take : Nat → Bool

/-- The ownership roles of an interface given by number. -/
def NRoles.toOB {Ty : Type} {X : Iface Ty} (r : NRoles) : OBRoles X where
  alloc i := r.alloc i.val
  use i := r.use i.val
  free i := r.free i.val
  give i := r.give i.val
  lend j := r.lend j.val
  take j := r.take j.val

/-- The ownership classifier on recorded moves. -/
def obEvN (r : NRoles) : RMove → OEv Val
  | .ans i b => if r.alloc i then OEv.ofRes .alloc b else .skip
  | .ask i a =>
    if r.use i then OEv.ofArgs .use a else if r.free i then OEv.ofArgs .free a
    else if r.give i then OEv.ofArgs .give a else .skip
  | .call j a =>
    if r.lend j then OEv.ofArgs .lend a else if r.take j then OEv.ofArgs .take a else .skip
  | .ret _ _ => .endCall

/-- A replay rejected by the ownership protocol. -/
def obBad (r : NRoles) (rs : List RMove) : Bool :=
  !(obProto Val).acceptsB (rs.map (obEvN r))

/-- The ownership script: allocations return the fresh handle `7 + k`, other imports nothing. -/
def obScript (r : NRoles) : Script := fun k h _ =>
  if r.alloc h then [Val.i32 (BitVec.ofNat 32 (7 + k))] else []

/-- **The ownership replay refuter** on a module, with up to `n` callouts. -/
def obReplay? (m : Module) (r : NRoles) (n : Nat) : Option (List RMove) :=
  replayRefute (instOf m) (obScript r) refFuel n (obBad r)

end Silmaril.Wasm.Resource
