module

public import Silmaril.Wasm.Game.DivAdequacy.Defs
public import Silmaril.Wasm.Game.Instantiate.Defs
public import Silmaril.Games.Inst.Defs
public import Silmaril.Wasm.Behaviour.Semantics.Core

/-!
# Modules with a start function: the instantiation phase

A start function runs during instantiation, after segment initialisation and
before any export call. It may call imports, trap, throw or diverge. The
strategy of a module with a start function therefore has an
**instantiation phase**, which is the instantiation phase of
`Silmaril.Games.Inst`: the module's game is over the signature
`I.F.withInst (Behaviour Val)`, whose extra question `inst` is answered
`ready` or `fail b` (`b` the trap or uncaught exception of the start
function), and whose divergence after `[askInst]` is divergence of the start
function.

## Instances before their start function

`instantiateOnce? s m xas = some (s', f, st)` performs allocation and segment
initialisation and *returns* the start function `st = m.start` instead of
running it (`instantiateOnce?_start`). `IsInstanceStart m mt I start` is
`IsInstance` with the start function allowed: `I.store` is the store before
the start function runs and `start` is the start function's **address**
(`none` exactly when the module has no start function). `StartTyped s a`
says the function at `a` has the type `startType = [] → []`.

## The instantiable system of an instance

`I.instSys P s start : InstSystem I.E I.F (Behaviour Val)`
(`Silmaril.Games.Inst.InstSystem`):

* the instantiation run is the single-threaded machine running the start
  thread `startThread start` from the store `s` (the pending invocation
  `$invoke(a, [])`, or the finished empty thread when there is no start
  function), host-free steps silent, callouts played as import calls
  (`CallsOut`), answers resumed with `resumeResult` (`resumeK`);
* it is ready, leaving its store, when the thread returns `values []`, and
  fails with `traps`/`throws a` when it traps or throws (`StartFailed`);
* export calls then run from the persisted store exactly as the
  divergence-observing instance system `I.dlts` does.

The system is the case `t₀ = startThread start` of `I.instSysT P s t₀`, whose
instantiation runs an arbitrary thread `t₀` (used for the spec's
`$instantiate` configuration in `Silmaril.Wasm.Game.SpecInst`); likewise
`instStrategyT`, `closedInstLTST`, `closedInstT`, and `StartsToT` (the thread
returns at a store).

`I.instStrategy P s start = DStrategy.ofInst (I.instSys P s start)` is the
divergence-observing strategy of the instance including its start phase.
Against an environment `K` the closed program is the composite system
`I.closedInstLTS P s start K` (the environment's `K.dlts` below the
instantiable system) and its strategy `I.closedInst P s start K`.

## Core readings

* `startConfig s start`: the Core configuration of the start phase;
  `StartsTo P host s start s'`: the start phase returns at the store `s'`;
  `startBehaviours P host s start`: its closed-world behaviours
  (`behaviours P host s a []` for a start function at `a`, `{returns []}`
  without one).
* `instObs δ`: the instantiation observations of a strategy with an
  instantiation phase (`returns []` when ready, `b` when failing with `b`,
  `diverges` when diverging); `obsAfterInst δ f`: the observations of the
  export call `f` right after a successful instantiation.
* `liftMove`: the moves of `E ↠ F` as moves of `E ↠ F.withInst R` (export
  calls are `some q`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-- The type `[] → []` of a start function. -/
def startType : FnType := ⟨[], []⟩

/-- The function at address `a` of `s` has the start type `[] → []`. -/
def StartTyped (s : Store Nat) (a : Nat) : Prop :=
  ∃ fi : FuncInst Nat, s.funcs[a]? = some fi ∧ Expand fi.type startType.toComp

/-- `I` is the instance of the module `m` (of validated type `mt`) against fresh host
functions for its imports, **before its start function runs**; `start` is the address of the
start function, if the module has one (see the module docstring). -/
structure IsInstanceStart (m : Module) (mt : CModuleType) (I : ScalarInstance)
    (start : Option Nat) : Prop where
  valid : validate? m = some mt
  funcImports : ∀ xt ∈ mt.imports, ∃ d, xt = .func d
  importTypes : List.Forall₂ (fun d ft => FnType.ofDefType? d = some ft)
    (CExternType.funcs mt.imports) I.imports
  instantiated : ∃ (f : Frame) (st : Option FuncIdx),
    instantiateOnce? (importStore (CExternType.funcs mt.imports)) m
        ((List.range mt.imports.length).map ExternAddr.func) = some (I.store, f, st) ∧
      exportFuncAddrs f.module = I.addrs ∧
      Option.Rel (fun x a => f.module.funcs[x.toNat]? = some a) st start
  exportTypes : List.Forall₂
    (fun a ft => ∃ fi : FuncInst Nat, I.store.funcs[a]? = some fi ∧
      FnType.ofDefType? fi.type = some ft) I.addrs I.exports

/-! ## Lifting moves to the instantiable signature -/

/-- An event of `F` as an event of `F.withInst R` (export questions are `some q`). -/
def liftEv {F : Sig.{0}} {R : Type} : Ev F → Ev (F.withInst R)
  | .ask q => .ask (some q)
  | .ans q r => .ans (m := some q) r

/-- A move of `E ↠ F` as a move of `E ↠ F.withInst R`. -/
def liftMove {E F : Sig.{0}} {R : Type} : Move E F → Move E (F.withInst R) :=
  Sum.map id liftEv

/-! ## The start phase in Core -/

/-- The start thread: the pending invocation of the start function, or the finished empty
thread when there is none. -/
def startThread : Option Nat → Thread
  | none => .active {} []
  | some a => .pending a []

/-- The Core configuration of the start phase at store `s`. -/
def startConfig (s : Store Nat) (start : Option Nat) : Config Nat := (startThread start).config s

/-- The start phase returns at the store `s'`. -/
def StartsTo (P : Profile) (host : HostSemantics Nat) (s : Store Nat) (start : Option Nat)
    (s' : Store Nat) : Prop :=
  ∃ c', Steps P host (startConfig s start) c' ∧ c'.code = (Result.values []).toAdmin ∧
    c'.store = s'

/-- The start thread failed: it trapped, or threw an uncaught exception. -/
def StartFailed (c : Store Nat × Thread) (b : Behaviour Val) : Prop :=
  (ResultAt c.1 c.2 .trap ∧ b = .traps) ∨ ∃ a, ResultAt c.1 c.2 (.throw a) ∧ b = .throws a

/-- The instantiation thread `t₀` returns `values []` at the store `s'`, starting from the
store `s`. -/
def StartsToT (P : Profile) (host : HostSemantics Nat) (s : Store Nat) (t₀ : Thread)
    (s' : Store Nat) : Prop :=
  ∃ c', Steps P host (t₀.config s) c' ∧ c'.code = (Result.values []).toAdmin ∧ c'.store = s'

/-- The closed-world behaviours of the start phase. -/
def startBehaviours (P : Profile) (host : HostSemantics Nat) (s : Store Nat)
    (start : Option Nat) : Set (Behaviour Val) :=
  behavioursOf P host (startConfig s start)

/-- The instantiation observations of a strategy with an instantiation phase. -/
def instObs {E F : Sig.{0}} (δ : DStrategy E (F.withInst (Behaviour Val))) :
    Set (Behaviour Val) :=
  {b | b = .returns [] ∧ δ.InstReady} ∪ {b | δ.InstFails b} ∪
    {b | b = .diverges ∧ δ.InstDiverges}

/-- The observations of the export call `f` of a closed strategy with an instantiation
phase, right after a successful instantiation: the behaviours of its answers, and
`diverges` when it may diverge after the question. -/
def obsAfterInst {ts : List FnType}
    (δ : DStrategy Sig.empty ((ifaceSig ts).withInst (Behaviour Val)))
    (f : (ifaceSig ts).Op) : Set (Behaviour Val) :=
  {b | ∃ w, [askInst, ansInst .ready, askEx f, ansEx f w] ∈ δ.toStrategy ∧
      b = Answer.toBehaviour (ft := ts.get f.1) w} ∪
    {b | b = .diverges ∧ [askInst, ansInst .ready, askEx f] ∈ δ.div}

namespace ScalarInstance

variable (I : ScalarInstance)

/-- The continuation resuming the thread `t` at store `s` with the answer to `e`. -/
noncomputable def resumeK (s : Store Nat) (t : Thread) (e : I.E.Op) :
    I.E.Ar e → Store Nat × Thread :=
  fun v => (s, resumeResult s t (Answer.toResult (ft := I.imports.get e.1) v))

/-- The thread is stopped at a callout played as the import call `e`. -/
def CallsOut (c : Store Nat × Thread) (e : I.E.Op) : Prop :=
  ∃ h args, CalloutAt c.1 c.2 h args ∧ I.importOp? h args = some e

/-- **The instantiable system of an instance whose instantiation runs the thread `t₀`** from
the store `s`: the instantiation phase runs `t₀` (for the spec's instantiation, the thread of the
configuration of `$instantiate`, segment initialisation followed by `call start`), host-free steps
silent, callouts played as import calls; it is ready, leaving its store, when the thread returns
`values []`, and fails when it traps or throws. Export calls then run from the persisted store. -/
noncomputable def instSysT (P : Profile) (s : Store Nat) (t₀ : Thread) :
    InstSystem I.E I.F (Behaviour Val) where
  IConf := Store Nat × Thread
  State := Store Nat
  Conf _ := Store Nat × Thread
  istart := (s, t₀)
  istep := InternalP P
  icall c e k := I.CallsOut c e ∧ k = I.resumeK c.1 c.2 e
  iready c s' := ResultAt c.1 c.2 (.values []) ∧ s' = c.1
  ifail c b := StartFailed c b
  start q s' := (s', I.initThread q)
  step := fun {_} => InternalP P
  call := fun {_} c e k => I.CallsOut c e ∧ k = I.resumeK c.1 c.2 e
  done := fun {q} c v s' =>
    ∃ r, ResultAt c.1 c.2 r ∧ Answer.ofResult? (I.exports.get q.1) r = some v ∧ s' = c.1

/-- **The instantiable system of an instance** at store `s` with start function `start`
(see the module docstring): the start thread `startThread start`. -/
noncomputable def instSys (P : Profile) (s : Store Nat) (start : Option Nat) :
    InstSystem I.E I.F (Behaviour Val) :=
  I.instSysT P s (startThread start)

/-- The strategy of an instance whose instantiation runs the thread `t₀`, divergence
observed. -/
noncomputable def instStrategyT (P : Profile) (s : Store Nat) (t₀ : Thread) :
    DStrategy I.E (I.F.withInst (Behaviour Val)) :=
  DStrategy.ofInst (I.instSysT P s t₀)

/-- **The strategy of an instance including its start phase**, divergence observed. -/
noncomputable def instStrategy (P : Profile) (s : Store Nat) (start : Option Nat) :
    DStrategy I.E (I.F.withInst (Behaviour Val)) :=
  DStrategy.ofInst (I.instSys P s start)

/-- The closed program whose instantiation runs the thread `t₀`, as a transition system. -/
noncomputable def closedInstLTST (P : Profile) (s : Store Nat) (t₀ : Thread)
    (K : Env I.E) : LTS Sig.empty (I.F.withInst (Behaviour Val)) :=
  K.dlts.comp (I.instSysT P s t₀).toLTS

/-- The closed program whose instantiation runs the thread `t₀`, divergence observed. -/
noncomputable def closedInstT (P : Profile) (s : Store Nat) (t₀ : Thread)
    (K : Env I.E) : DStrategy Sig.empty (I.F.withInst (Behaviour Val)) :=
  DStrategy.ofLTS (I.closedInstLTST P s t₀ K)

/-- The closed program including the start phase, as a transition system: the environment
below the instantiable system. -/
noncomputable def closedInstLTS (P : Profile) (s : Store Nat) (start : Option Nat)
    (K : Env I.E) : LTS Sig.empty (I.F.withInst (Behaviour Val)) :=
  I.closedInstLTST P s (startThread start) K

/-- **The closed program including the start phase**, divergence observed. -/
noncomputable def closedInst (P : Profile) (s : Store Nat) (start : Option Nat)
    (K : Env I.E) : DStrategy Sig.empty (I.F.withInst (Behaviour Val)) :=
  DStrategy.ofLTS (I.closedInstLTS P s start K)

end ScalarInstance

end Silmaril.Wasm.Game
