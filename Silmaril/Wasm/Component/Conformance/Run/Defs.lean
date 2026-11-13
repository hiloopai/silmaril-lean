module

public import Silmaril.Wasm.Component.Conformance.Host.Defs
public import Silmaril.Wasm.Component.Conformance.Valid.Defs

/-!
# Running components on the reference machine, for conformance scripts

The executable pieces a `.wast` runner needs, over the copied reference machine with the
concrete Core 3.0 engine `core3 neverFail` and its interpreter `core3Exec neverFail` (the
embedder of `Reference.Example`), the specification limits and quirks, the host instances of
`Conformance.Host` (wasmtime's `.wast` linker: `hostImpl`, host state `HostSt`), no ready
host waitables, and the deterministic first-alternative oracle:

* `validate c`: the executable validator `checkCore3?` at `features` (`Conformance.Valid`);
* `instantiate fuel reg c ct`: root instantiation of `c` (of validated type `ct`) with the
  root arguments `linkArgs` builds from the host namespace (`reg`: the instances registered
  so far) in a fresh store (REF `Store()`), run for at most `fuel` steps, classified as an instance (configuration and
  function exports), a trap (with its reason), or `stuck` (out of fuel, deadlock, an
  `internal` model fault, or no `instantiated` report);
* `invoke fuel m k f args`: top-level call `k` of function `f` on `args` from configuration
  `m`, then internal steps and host ticks until the call has resolved (`callUntil`, which is
  `Machine.runTopCall` stopping at the call's result, and resolving deferred host calls,
  `resolvePending`, when nothing else can happen), classified as returned values, a
  cancellation, a trap (with its reason), a deadlock, or `stuck`;
* `funcType? m f`: the WIT type of a function value, which the runner needs to read and
  compare values by case and label names.

Each result keeps the configuration reached, so a script can call the same instance again
(after a trap the store is locked down, which is how REF poisons an instance). Instantiation
uses the copied machine's `Machine.run`; `callUntil` is new, and `Run.Thms` proves that its
trace is a run of the machine relation (`callUntil_sound`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Conformance

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon

/-- A machine configuration of the runner. -/
abbrev Cfg : Type := Config Eng HostSt

/-- No host waitable is ever ready. -/
def noReady : HostReady HostSt := fun _ _ => false

/-- The specification embedder over `core3 neverFail` with wasmtime's `.wast` host. -/
def emb : Embedder Eng HostSt :=
  { X := core3Exec Silmaril.Wasm.SingleThreaded.neverFail, hr := noReady, host := hostImpl }

/-- Deferred host calls are queued. -/
def hasPending (st : HostSt) : Bool := !st.pending.isEmpty

/-- The deterministic first-alternative oracle. -/
abbrev oracle : Oracle Eng := Oracle.first

/-- The seeded pseudo-random oracle (`nondet` profile), for runs on which `oracle` makes no
progress: its `earlyReturn` is always `false` and its scheduling picks always `0`, so a thread
that yields in a loop waiting for another one can be resumed forever. -/
abbrev lcgOracle (seed : Nat) : Oracle Eng := Oracle.lcg seed

/-- The wait sites at which `eagerOracle` returns early: the waits for an event or a
resolution (K1, K3-K8). At the yield sites (`thread.yield`, callback `YIELD`,
`yield-then-resume`: K2, K9, K12), whose condition always holds, and at suspensions and host
threads (K10, K11, K13) it blocks, so a yield still lets other threads run. -/
def eagerSite : Runtime.WaitSite → Bool
  | .enterBackpressure | .callbackWait | .waitableSetWait | .syncCopy | .syncCancelCopy
  | .syncLower | .syncSubtaskCancel => true
  | _ => false

/-- The answers of `eagerOracle`: `earlyReturn` at an `eagerSite` is `true` (a wait whose
condition already holds returns at once), every other choice is the first alternative of the
`nondet` profile. -/
def eagerAnswer : (k : ChoiceKind) → k.Resp
  | .earlyReturn site => eagerSite site
  | k => firstAnswer .nondet k

/-- **The eager oracle** (`nondet` profile, stateless): REF's `Thread.wait_until` with
`DETERMINISTIC_PROFILE = False` returns without blocking when its condition already holds and
`random.randint(0,1)` is 1; this oracle takes that branch at every wait for an event or a
resolution (`eagerSite`), which is what wasmtime does (it does not suspend a task whose wait is
already satisfied), and blocks at yields. `Oracle.first` (the deterministic
profile) always blocks. -/
def eagerOracle : Oracle Eng where
  prof := .nondet
  State := Unit
  state := ()
  answer := fun st _ k => (eagerAnswer k, st)

/-- The first trap reason of a trace. -/
def trapReason? (ls : List (Label Eng HostSt)) : Option TrapReason :=
  ls.findSome? fun | .trap r => some r | _ => none

/-- The result of instantiating a component. -/
inductive InstOutcome where
  | instance (m : Cfg) (exports : List (String × FuncId))
    (items : List (String × Instantiate.ItemVal Eng))
  | trap (r : Option TrapReason)
  | stuck (why : String)

/-- Instantiate `c` of type `ct` with linked root arguments from a fresh store whose host
state has the registered instances `reg` and the `resource1` destructor counters `drops`
(wasmtime keeps them in its linker), for at most `fuel` steps. -/
def instantiate (fuel : Nat) (reg : List (String × HostItem)) (c : RefComponent)
    (ct : Reference.ComponentType) (drops : Nat × Nat := (0, 0)) : InstOutcome :=
  let m₀ : Cfg := Config.init CStore.empty
    { registered := reg, drops := drops.1, lastDrop := drops.2 }
  match hostStep? emb.hr (.run (instantiateLinkedProg c ct)) m₀ with
  | none => .stuck "instantiation event not enabled"
  | some (_, m₁) =>
    let r := Machine.run emb.hr emb.dispatch emb.X oracle fuel m₁
    match trapReason? r.labels with
    | some (.internal msg) => .stuck s!"internal fault: {msg}"
    | some t => .trap (some t)
    | none =>
      if r.outcome = .trap then .trap none
      else if r.config.hostInControl && !r.config.store.lockdown then
        match (traceObs r.labels).findSome? decodeInstantiated? with
        | some (_, es) => .instance r.config es r.config.host.lastExports
        | none => .stuck s!"no instantiation report (outcome {reprStr r.outcome})"
      else .stuck s!"instantiation did not finish (outcome {reprStr r.outcome})"

/-- The result of a top-level call. -/
inductive CallResult where
  | returned (vs : List Value.Val)
  | cancelled
  | trap (r : Option TrapReason)
  | deadlock
  | stuck (why : String)

section Drivers

variable {E : CoreEngine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)]
  (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E)) (X : E.Exec) (o : Oracle E)
  (pend : σ → Bool) (resolve : P E σ (Ret E))

/-- Top-level call `c` has resolved and the host is in control. -/
def callDone (c : CallId) (m : Config E σ) : Bool := m.hostInControl && (m.result? c).isSome

/-- `Machine.runTopLoop` (internal steps, and a host `tick` whenever `wantsTick`) that stops as
soon as `callDone c`, and that, when neither is possible but the host has deferred work
(`pend` of the host state), runs the host program `resolve` (`HostEvent.run`): a `.wast` `invoke` returns when its result is available, while
`runTopLoop`, like `run_tests.py`, drives every ready thread to quiescence (which never comes
when a resolved task keeps yielding). The outcome of a stop is `outcomeOf`. -/
def untilLoop (c : CallId) : Nat → o.State → Config E σ → List (Label E σ) →
    RunResult E σ o.State
  | 0, st, m, acc =>
    { outcome := if !callDone c m &&
          ((step? dispatch X (o.at st) m).isSome || wantsTick hr m || pend m.host) then .outOfFuel
        else outcomeOf hr m,
      config := m, state := st, labels := acc.reverse }
  | n + 1, st, m, acc =>
    if callDone c m then
      { outcome := outcomeOf hr m, config := m, state := st, labels := acc.reverse }
    else
      match step? dispatch X (o.at st) m with
      | some (l, st', m') => untilLoop c n st' m' (l :: acc)
      | none =>
        if wantsTick hr m then
          match hostStep? hr .tick m with
          | some (l, m') => untilLoop c n st m' (l :: acc)
          | none => { outcome := outcomeOf hr m, config := m, state := st, labels := acc.reverse }
        else if pend m.host then
          match hostStep? hr (.run resolve) m with
          | some (l, m') => untilLoop c n st m' (l :: acc)
          | none => { outcome := outcomeOf hr m, config := m, state := st, labels := acc.reverse }
        else { outcome := outcomeOf hr m, config := m, state := st, labels := acc.reverse }

/-- Issue top-level call `c` of `f` on `args` (`HostEvent.invoke`), then `untilLoop`; `none`
if the invoke is not enabled. The invoke label heads the trace. -/
def callUntil (fuel : Nat) (c : CallId) (f : FuncId) (args : List Value.Val) (m : Config E σ) :
    Option (RunResult E σ o.State) :=
  (hostStep? hr (.invoke c f args) m).map fun (l, m') =>
    untilLoop hr dispatch X o pend resolve c fuel o.state m' [l]

end Drivers

/-- The result of top-level call `k` in a run of `callUntil`. After the call, a store holding
more handles than the capacity `wasmtime.set-max-table-capacity` set is a trap
(`capacityTrap`, `Conformance.Host`). -/
def classify {τ : Type} (k : Nat) (r : RunResult Eng HostSt τ) : CallResult :=
  if overCapacity r.config.store r.config.host then .trap (some capacityTrap) else
  match trapReason? r.labels with
  | some (.internal msg) => .stuck s!"internal fault: {msg}"
  | some t => .trap (some t)
  | none =>
    match r.config.result? ⟨k⟩ with
    | some (some vs) => .returned vs
    | some none => .cancelled
    | none =>
      match r.outcome with
      | .trap => .trap none
      | .deadlock => .deadlock
      | .outOfFuel => .stuck "out of fuel"
      | out => .stuck s!"unresolved (outcome {reprStr out})"

/-- Top-level call `k` of `f` on `args` from `m`, at most `fuel` steps of `callUntil` with
oracle `o` (default `oracle`); the result (`classify`) and the configuration reached (`m`
itself when the call could not be issued). -/
def invoke (fuel : Nat) (m : Cfg) (k : Nat) (f : FuncId) (args : List Value.Val)
    (o : Oracle Eng := oracle) : CallResult × Cfg :=
  match callUntil emb.hr emb.dispatch emb.X o hasPending resolvePending fuel ⟨k⟩ f args m with
  | none => (.stuck "invoke event not enabled", m)
  | some r => (classify k r, r.config)

/-- The WIT type of function value `f` in `m`. -/
def funcType? (m : Cfg) (f : FuncId) : Option (WIT.FuncType Empty RtId) :=
  (m.store.func? f).map CFuncInst.ft

end Silmaril.Wasm.Component.Conformance
