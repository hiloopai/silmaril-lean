module

public import Silmaril.Containers.Executor.Defs
public import Silmaril.Containers.Outcome.Defs
public import Silmaril.Wasi.Comp.Defs
public import Silmaril.Wasi.Host.Defs

/-! # A synchronous WIT component and an independent one-invocation runner

Experimental, model backed: no component binary or native Wasm engine is claimed.
`sample(false)` asks the host for a Boolean and negates it; `sample(true)` traps.
The named component uses the existing `Wasi.Body` operational semantics. The runner below
has its own states and a silent negate step; its simulation is proved in `Thms`.
-/

@[expose] public section
namespace Silmaril.Containers.SyncComponent

open Silmaril.Wasm.Component (Val Iface)
open Silmaril.Wasi (FnName World nsig Body BProg Host)
open Silmaril.Games (Sig Move)

def imports : Iface := [("choose", ⟨[], [.bool]⟩)]
def exports : Iface := [("sample", ⟨[.bool], [.bool]⟩)]
def chooseName : FnName := ⟨"silmaril:examples/choice", "choose"⟩
def sampleName : FnName := ⟨"silmaril:examples/sampler", "sample"⟩
def world : World := ⟨{chooseName}, {sampleName}⟩
def chooseOp : (nsig world.imports).Op := (⟨chooseName, rfl⟩, [])
def sampleOp (trap : Bool) : (nsig world.exports).Op := (⟨sampleName, rfl⟩, [.bool trap])
def values (r : Option Bool) : Option (List Val) := r.map fun b => [.bool b]

def afterChoice : Option (List Val) → BProg world.imports
  | some [.bool b] => .pure (values (some (!b)))
  | _ => .pure none

/-- Dynamically malformed arguments/answers trap, as in the existing component interface.
The supported invocation/host contract below supplies typed arguments and Boolean answers. -/
def body : Body world.imports world.exports := fun q => match q.2 with
  | [.bool false] => .call chooseOp afterChoice
  | _ => .pure none

/-- A fixed synchronous event alphabet for this WIT world, without streams/futures. -/
inductive Event where
  | call (trap : Bool)
  | choose
  | chosen (b : Bool)
  | returned (r : Option Bool)
  deriving DecidableEq, Repr

def Event.isExport : Event → Bool
  | .call _ | .returned _ => true
  | _ => false

def Event.move (trap : Bool) : Event → Move (nsig world.imports) (nsig world.exports)
  | .call b => .inr (.ask (sampleOp b))
  | .choose => .inl (.ask chooseOp)
  | .chosen b => .inl (.ans chooseOp (values (some b)))
  | .returned r => .inr (.ans (sampleOp trap) (values r))

def Event.host : Event → Option (Move Sig.empty (nsig world.imports))
  | .choose => some (.inr (.ask chooseOp))
  | .chosen b => some (.inr (.ans chooseOp (values (some b))))
  | _ => none

def Event.closed (trap : Bool) : Event → Option (Move Sig.empty (nsig world.exports))
  | .call b => some (.inr (.ask (sampleOp b)))
  | .returned r => some (.inr (.ans (sampleOp trap) (values r)))
  | _ => none

inductive Phase where
  | idle | started | waiting
  | computing (b : Bool)
  | result (r : Option Bool)
  | finished (r : Option Bool)

/-- Independent source execution, including an actual internal computation step. -/
inductive Step : Bool → Phase → Option Event → Phase → Prop where
  | start (trap : Bool) : Step trap .idle (some (.call trap)) .started
  | request : Step false .started (some .choose) .waiting
  | reply (trap b : Bool) : Step trap .waiting (some (.chosen b)) (.computing b)
  | negate (trap b : Bool) : Step trap (.computing b) none (.result (some (!b)))
  | trap : Step true .started none (.result none)
  | ret (trap : Bool) (r : Option Bool) :
      Step trap (.result r) (some (.returned r)) (.finished r)

inductive Run (trap : Bool) : List Event → Phase → Prop where
  | nil : Run trap [] .idle
  | snoc {t s s' e} : Run trap t s → Step trap s e s' → Run trap (t ++ e.toList) s'

/-- Relate source phases to the existing component's operational states. -/
def componentState (trap : Bool) : Phase → Silmaril.Wasi.CSt world.imports world.exports
  | .idle | .finished _ => .idle
  | .started => .run (sampleOp trap) (body (sampleOp trap))
  | .waiting => .wait (sampleOp trap) chooseOp afterChoice
  | .computing b => .run (sampleOp trap) (afterChoice (values (some b)))
  | .result r => .run (sampleOp trap) (.pure (values r))

abbrev ClosedHost := Host Sig.empty world.imports

def hostPlay (b : Bool) : List (Move Sig.empty (nsig world.imports)) :=
  [.inr (.ask chooseOp), .inr (.ans chooseOp (values (some b)))]

/-- Legal host strategies enforce turns/pending questions. This additional contract enforces
the WIT result shape. No trap or malformed value is an admitted host answer. -/
def TypedAnswers (t : List Silmaril.Wasi.WEv) : Prop :=
  ∀ e ∈ t, ∃ b, e = .imp chooseName [] (values (some b))

/-- Safety alone cannot require a host to answer. One-shot availability supplies a complete
execution witness, not eventual delivery, scheduling fairness or engine progress. -/
def Admitted (host : ClosedHost) : Prop :=
  (Silmaril.Wasi.hostSat TypedAnswers).holds host ∧ ∃ b, hostPlay b ∈ host

/-- The same export specification is read on component plays, linked plays and containers:
normal mode returns a Boolean; trap mode returns the defined guest trap. -/
def ReturnOK (args : List Val) (r : Option (List Val)) : Prop :=
  (args = [.bool true] → r = none) ∧
  (args = [.bool false] → ∃ b, r = values (some b))

def GoodEvent : Silmaril.Wasi.WEv → Prop
  | .ret _ args r => ReturnOK args r
  | _ => True

def GoodEvents (t : List Silmaril.Wasi.WEv) : Prop := ∀ e ∈ t, GoodEvent e

/-- The loose typed host permits either Boolean independently on each call. -/
def looseHost : ClosedHost := Silmaril.Wasi.ofPred TypedAnswers
  ⟨by simp [TypedAnswers], fun _ _ hp ht e he => ht e (hp.subset he)⟩

def completedTrace (trap : Bool) (choice : Bool) : List Event :=
  if trap then [.call true, .returned none]
  else [.call false, .choose, .chosen choice, .returned (some (!choice))]

/-- Defined guest outcome, separately from the runner's reporting exit status. -/
def guestOutcome : Option Bool → Outcome UB
  | none => .trapped 0
  | some _ => .exited 0

/-- The model runner reports a guest trap with status 70. The `returned none` event preserves
the defined guest trap; it is not host UB or a guest normal exit. -/
def reportCode : Option Bool → UInt8
  | none => 70
  | some _ => 0

def report (t : List Event) (r : Option Bool) : Beh Event :=
  .done (t.filter Event.isExport) (.exited (reportCode r))

/-- Explicit more-UB observation policy. Default guest traps stay defined; selecting this
policy replaces their terminal reporting outcome with UB. It never masks existing host UB. -/
def trapPolicy : Adapter Event Event := ⟨fun b => match b with
  | .done t stop => if .returned none ∈ t then .done t (.undefined .unmodeled) else .done t stop
  | b => b⟩

/-- Complete source executions compatible with the actual host strategy, plus a waiting
behavior in normal mode. Finite-play host strategies do not assert eventual delivery, even
when a reply is available. The model is one invocation. -/
def source (host : ClosedHost) (trap : Bool) : Model Event := fun b =>
  (∃ t r, Run trap t (.finished r) ∧ t.filterMap Event.host ∈ host ∧ b = report t r) ∨
  (trap = false ∧ b = .blocked [.call false])

/-- Independently defined by the existing linked component's plays and their typed export
observations. Source-machine runs do not occur in this definition. -/
def linked (host : ClosedHost) (trap : Bool) : Model Event := fun b =>
  (∃ r, [.inr (.ask (sampleOp trap)), .inr (.ans (sampleOp trap) (values r))] ∈
    Silmaril.Wasi.link host (Silmaril.Wasi.ofBody body) ∧
    b = .done [.call trap, .returned r] (.exited (reportCode r))) ∨
  (trap = false ∧ [.inr (.ask (sampleOp trap))] ∈
    Silmaril.Wasi.link host (Silmaril.Wasi.ofBody body) ∧ b = .blocked [.call false])

/-- The transferred partial export spec; waiting is not a successful return. -/
def Reports (trap : Bool) (b : Beh Event) : Prop :=
  (∃ r, ReturnOK [.bool trap] (values r) ∧
    b = .done [.call trap, .returned r] (.exited (reportCode r))) ∨
  (trap = false ∧ b = .blocked [.call false])

def runtime : Runtime (Unit × ClosedHost × Bool) (ClosedHost × Bool) Event where
  load i := .ok i.2
  sem p := source p.1 p.2
  obs := Eq

/-- Supported guest is this fixed synchronous component body, not an arbitrary Boolean
program or a binary. The context supplies its typed Boolean argument. -/
def executor : Executor Unit ClosedHost Bool (ClosedHost × Bool) Event Event where
  runtime := runtime
  supported _ := True
  valid _ := ∀ trap : Bool, Silmaril.Wasm.Component.checkVals exports[0]!.2.params [.bool trap] =
    some [.bool trap]
  admits _ host _ := Admitted host
  linked _ host trap := linked host trap
  observe := Adapter.id

end Silmaril.Containers.SyncComponent
