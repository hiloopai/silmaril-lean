module

public import Silmaril.Servers.Core.Defs

@[expose] public section

/-!
# Liveness: every request is eventually answered

The core's sentences (`Silmaril.Servers.Sen`) are properties of finite traces: they say what a
server may do (partial correctness), never that it does anything. Liveness needs infinite
observations, so it is a separate kind of sentence:

* `ITrace A`: an infinite observation: at each instant an event or nothing;
* `ISen A`: a property of infinite observations; **`ISen.answered`**: every request received is
  eventually answered;
* `ITrace.prefix u n`: the finite trace of the first `n` instants, so a finite-trace sentence
  holds of an infinite observation when it holds of all its prefixes (`ISen.always`);
* `Machine.IRun M q₀`: an infinite run of the atomic-handler server of `M`
  (`Machine.server`): at each instant it idles or takes a step (a request received, a handler
  run, a response sent);
* `IRun.Fair`: **weak fairness**, per request: a handler run that stays enabled is eventually
  taken, and a computed response that stays ready is eventually sent;
* `Machine.Total`: in every state, the handler can answer every request.

The pipelining server (`Machine.pipeServer`: responses in request order on each connection)
has its own runs (`Machine.PRun`) and fairness (`PRun.Fair`): a response is *sendable* when it
is ready and every earlier request on its connection has been answered (`PRun.SendEnabled`),
and weak fairness asks that a response that stays sendable is eventually sent.

The theorems (`Silmaril.Servers.Live.Thms`): the fair runs of the atomic-handler server, and of
the pipelining server, of a total machine answer every request; every prefix of every run is a
trace of the server, so it satisfies the server's safety sentences too; and fair runs exist:
for every stream of requests on a connection there is a fair run that receives them all.

A Silmaril addition.
-/

namespace Silmaril.Servers

variable {A : Sig} {σ : Type}

/-- **An infinite observation**: at each instant, an event or nothing. -/
abbrev ITrace (A : Sig) : Type := Nat → Option (Event A)

/-- **A sentence about infinite observations.** -/
abbrev ISen (A : Sig) : Type := ITrace A → Prop

/-- The finite trace of the first `n` instants. -/
def ITrace.prefix (u : ITrace A) (n : Nat) : Trace A := (List.range n).filterMap u

/-- **Every request is eventually answered.** -/
def ISen.answered : ISen A :=
  fun u => ∀ n i r, u n = some (.recv i r) → ∃ m s, n < m ∧ u m = some (.send i s)

/-- A finite-trace sentence holds of every prefix. -/
def ISen.always (φ : Sen A) : ISen A := fun u => ∀ n, φ (u.prefix n)

/-- In every state, the handler can answer every request. -/
def Machine.Total (M : Machine A σ) : Prop := ∀ q r, ∃ s q', M q r s q'

/-- **An infinite run of the atomic-handler server**: at each instant it idles (`none`) or takes
a step of `Machine.serverStep`. -/
structure Machine.IRun (M : Machine A σ) (q₀ : σ) where
  /-- The state at each instant: the machine's and the linearization monitor's. -/
  st : Nat → σ × LMon A
  /-- The step taken at each instant, if any. -/
  ev : Nat → Option (LEvent A)
  init : st 0 = (q₀, LMon.init A)
  step : ∀ n, (ev n = none ∧ st (n + 1) = st n) ∨
    ∃ e, ev n = some e ∧ M.serverStep (st n) e (st (n + 1))

namespace Machine.IRun

variable {M : Machine A σ} {q₀ : σ}

/-- What an environment observes of a run. -/
def obs (ρ : M.IRun q₀) : ITrace A := fun n =>
  match ρ.ev n with
  | some (.ev e) => some e
  | _ => none

/-- The handler run on the request `i` is enabled at instant `n`. -/
def LinEnabled (ρ : M.IRun q₀) (i : ReqId) (n : Nat) : Prop :=
  ∃ r, (ρ.st n).2.pending i = some r ∧ ∃ s q', M (ρ.st n).1 r s q'

/-- **Weak fairness**: an action that stays enabled from some instant on is eventually taken. -/
def Fair (ρ : M.IRun q₀) : Prop :=
  (∀ i n, (∀ m, n ≤ m → ρ.LinEnabled i m) → ∃ m, n ≤ m ∧ ∃ r s, ρ.ev m = some (.lin i r s)) ∧
  (∀ i n, (∀ m, n ≤ m → (ρ.st m).2.ready i ≠ none) →
    ∃ m, n ≤ m ∧ ∃ s, ρ.ev m = some (.ev (.send i s)))

end Machine.IRun

/-- The fair observations of the atomic-handler server of `M`. -/
def Machine.fairObs (M : Machine A σ) (q₀ : σ) : ISen A :=
  fun u => ∃ ρ : M.IRun q₀, ρ.Fair ∧ ρ.obs = u

/-! ## The pipelining server -/

/-- **An infinite run of the pipelining server** (`Machine.pipeServer`): at each instant it
idles or takes a step of `Machine.pipeStep`. -/
structure Machine.PRun (M : Machine A σ) (q₀ : σ) where
  /-- The state at each instant. -/
  st : Nat → σ × LMon A
  /-- The step taken at each instant, if any. -/
  ev : Nat → Option (LEvent A)
  init : st 0 = (q₀, LMon.init A)
  step : ∀ n, (ev n = none ∧ st (n + 1) = st n) ∨
    ∃ e, ev n = some e ∧ M.pipeStep (st n) e (st (n + 1))

namespace Machine.PRun

variable {M : Machine A σ} {q₀ : σ}

/-- A run of the pipelining server is a run of the atomic-handler server. -/
def toIRun (ρ : M.PRun q₀) : M.IRun q₀ where
  st := ρ.st
  ev := ρ.ev
  init := ρ.init
  step n := (ρ.step n).imp id fun ⟨e, he, hs⟩ => ⟨e, he, hs.1⟩

/-- What an environment observes of a run. -/
def obs (ρ : M.PRun q₀) : ITrace A := ρ.toIRun.obs

/-- The response to `i` may be sent at instant `n`: it is ready, and every earlier request on
its connection has been answered. -/
def SendEnabled (ρ : M.PRun q₀) (i : ReqId) (n : Nat) : Prop :=
  (ρ.st n).2.ready i ≠ none ∧ (ρ.st n).2.EarlierAnswered i

/-- **Weak fairness of the pipelining server**: a handler run that stays enabled is eventually
taken, and a response that stays sendable (ready, every earlier request on its connection
answered) is eventually sent. -/
def Fair (ρ : M.PRun q₀) : Prop :=
  (∀ i n, (∀ m, n ≤ m → ρ.toIRun.LinEnabled i m) →
    ∃ m, n ≤ m ∧ ∃ r s, ρ.ev m = some (.lin i r s)) ∧
  (∀ i n, (∀ m, n ≤ m → ρ.SendEnabled i m) →
    ∃ m, n ≤ m ∧ ∃ s, ρ.ev m = some (.ev (.send i s)))

end Machine.PRun

/-- The fair observations of the pipelining server of `M`. -/
def Machine.pipeFairObs (M : Machine A σ) (q₀ : σ) : ISen A :=
  fun u => ∃ ρ : M.PRun q₀, ρ.Fair ∧ ρ.obs = u

end Silmaril.Servers
