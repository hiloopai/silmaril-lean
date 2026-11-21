module

public import Silmaril.Semantics.Behaviour.Thms

/-! A source-level candidate for SQLite 3.54.1's `sqlite3_mutex_leave` wrapper.
The observation stops at the call to `xMutexLeave`, not at its reply. -/

@[expose] public section

namespace Silmaril.Machine.SqliteMutex

open Behaviour

abbrev Handle := BitVec 64

inductive Request where
  | leave (mutex : Handle)
  deriving DecidableEq, Repr

/-- A linked handler would return void. Its effects are not part of this boundary. -/
def Reply : Request → Type
  | .leave _ => Unit

/-- Evidence comes from the calling context, not from pointer bits. -/
structure Context where
  live : Handle → Prop
  ownedByCaller : Handle → Prop
  leaveInstalled : Prop

def Context.Admits (env : Context) (mutex : Handle) : Prop :=
  mutex = 0#64 ∨ (env.live mutex ∧ env.ownedByCaller mutex ∧ env.leaveInstalled)

inductive Boundary where
  | callerReturn
  | handlerEntry
  deriving DecidableEq, Repr

inductive Fault where
  | data | fetch | divide | undefinedFlag | unsupported | validation
  deriving DecidableEq, Repr

/-- `returned` here means end of the fragment. `Boundary` distinguishes
function return from transfer to a handler. -/
abbrev Obs := Observable Request Boundary Empty Unit Fault

def candidate (mutex : Handle) : Obs :=
  if mutex = 0#64 then ⟨[], .returned .callerReturn⟩
  else ⟨[.leave mutex], .returned .handlerEntry⟩

def contract (env : Context) : Observable.Contract Handle Request Boundary Empty Unit Fault where
  pre := env.Admits
  post mutex obs := obs = candidate mutex

end Silmaril.Machine.SqliteMutex
