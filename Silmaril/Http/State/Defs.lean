module

@[expose] public section

/-!
# HTTP servers with state: atomic handlers, hosts, histories and linearizability

See `docs/projects/http-servers.md` (section "State models"). This module is the trace
vocabulary that the state models of `Silmaril.Http.State.{Component, OwnedFs, SharedFs}` share.
It depends on Lean core only and is generic in the request and response types; the HTTP
instances take `Silmaril.Net.Http.Request` and `Response`.

## Histories

A **history** (`Hist`) is what an observer of a server sees: request `i` arrives with `r`
(`Ev.call i r`), and later the response `s` to request `i` is issued (`Ev.ret i s`). Request
identities are explicit, so a second request may arrive before the first is answered, and
responses may be issued in any order. Connections are not modelled here: a request identity
is all that relates a response to its request.

## Atomic handlers and sequential runs

An **atomic handler** `Atomic σ Req Resp` is a relation: in state `s`, request `r` may be
answered `resp` with next state `s'` (nondeterministic, partial: no answer at all is allowed).
`Silmaril.Net.Http.Origin σ` is exactly `Atomic σ Request Response`. `Legal A s L s'`: the
operations `L` (identity, request, response) run one after another from `s` end in `s'`.

## Linearizability and serializability

`L` **explains** `H` (`Explains`): `L` is a legal sequential run, each operation of `L` is a
request of `H` (with its request), each response of `H` is the response of the operation of
`L` with its identity, and identities are not repeated. Operations of `L` may be requests of
`H` that are still pending (they took effect, the response is not out yet), as in Herlihy and
Wing's completions.

* `Serializable A s₀ H`: some `L` explains `H`;
* `Linearizable A s₀ H` (Herlihy and Wing, 1990): some `L` explains `H` and respects real
  time (`RealTime`): if the response to `a` was issued before request `b` arrived
  (`RetBeforeCall`), then `a` comes before `b` in `L` (`Before`).

## Hosts

A **server** (`Server`) is a state type, an atomic handler, an **environment** relation on
states (what others may do to the state between handler runs: nothing for component state,
edits of a shared file system for `SharedFs`) and an initial state. Its host (`Step`,
`Server.Reach`) is a machine over configurations (`Conf`: the state, the log of handler runs
so far, the history so far) with four steps:

* `arrive`: a request with a fresh identity arrives;
* `run`: some request that has arrived and not run yet is handled **atomically** (one handler
  run, between other steps: a Wasm component instance is single-threaded, and a synchronous
  `wasi:http` handler runs to completion);
* `respond`: the response of a run that has not been answered yet is issued;
* `env`: the environment changes the state.

The host may run pending requests in any order, and answer runs in any order. The log of runs
is internal (it is not observed); `Server.Hists M H` says `H` is the history of a reachable
configuration.

## Sentences, satisfaction, refinement, abstraction

A **sentence** (`Sen`) is a property of histories; a server **satisfies** it (`Server.Sat`)
when every history does. **Refinement** (`Server.Refines`) is inclusion of histories. An
**abstraction** `Abstraction M B t₀` relates a server to an atomic specification `B` with
initial state `t₀`: an invariant of `M`'s states, an abstraction function `α` onto `B`'s
states, every handler run simulated by `B`, environment steps invisible to `α`. It is how one
state model is read as another (a file-backed store as an in-memory store, a file server whose
files nobody else changes as a stateless function).

## Per-request instances

`wasmtime serve` instantiates the component afresh for each request, so state kept inside
the component does not survive. `Server.perRequest A s₀` is that host: every request is
handled by `A` from `s₀` (`Atomic.fresh`), and there is no persistent state.

A Silmaril addition.
-/

namespace Silmaril.Http.State

open scoped List

/-- **An event of a server's history**: request `id` arrives with `r`, or the response `s` to
request `id` is issued. -/
inductive Ev (Req Resp : Type) where
  /-- Request `id` arrives with the request `r`. -/
  | call (id : Nat) (r : Req)
  /-- The response `s` to request `id` is issued. -/
  | ret (id : Nat) (s : Resp)
deriving DecidableEq, Repr

/-- A history: the events observed so far, in order. -/
abbrev Hist (Req Resp : Type) : Type := List (Ev Req Resp)

/-- An operation of a sequential run: a request identity, its request and its response. -/
structure Op (Req Resp : Type) where
  /-- The request identity. -/
  id : Nat
  /-- The request. -/
  req : Req
  /-- The response. -/
  resp : Resp
deriving DecidableEq, Repr

/-- **An atomic handler**: in state `s`, request `r` may be answered `resp` with next state `s'`. -/
def Atomic (σ Req Resp : Type) : Type := σ → Req → Resp → σ → Prop

variable {σ τ Req Resp : Type}

/-- The atomic handler of a step function. -/
def Atomic.ofFun (f : σ → Req → Resp × σ) : Atomic σ Req Resp :=
  fun s r resp s' => f s r = (resp, s')

/-- The stateless handler that answers `r` as `A` does from `s₀` (a fresh instance per
request). -/
def Atomic.fresh (A : Atomic σ Req Resp) (s₀ : σ) : Atomic Unit Req Resp :=
  fun _ r resp _ => ∃ s', A s₀ r resp s'

/-- The stateless handler of a relation between requests and responses. -/
def Atomic.ofRel (R : Req → Resp → Prop) : Atomic Unit Req Resp := fun _ r resp _ => R r resp

/-- **A legal sequential run**: the operations `L`, one after another from `s`, end in `s'`. -/
def Legal (A : Atomic σ Req Resp) : σ → List (Op Req Resp) → σ → Prop
  | s, [], s' => s = s'
  | s, o :: L, s'' => ∃ s', A s o.req o.resp s' ∧ Legal A s' L s''

/-- Request `i` has arrived in `H`. -/
def Called (H : Hist Req Resp) (i : Nat) : Prop := ∃ r, Ev.call i r ∈ H

/-- Request `i` has been answered in `H`. -/
def Returned (H : Hist Req Resp) (i : Nat) : Prop := ∃ s, Ev.ret i s ∈ H

/-- The response to `a` was issued before request `b` arrived. -/
def RetBeforeCall (H : Hist Req Resp) (a b : Nat) : Prop :=
  ∃ s r, [Ev.ret a s, Ev.call b r] <+ H

/-- An operation of identity `a` comes before one of identity `b` in `L`. -/
def Before (L : List (Op Req Resp)) (a b : Nat) : Prop :=
  ∃ x y, x.id = a ∧ y.id = b ∧ [x, y] <+ L

/-- **`L` explains `H`** as a sequential run of `A` from `s₀`. -/
structure Explains (A : Atomic σ Req Resp) (s₀ : σ) (H : Hist Req Resp)
    (L : List (Op Req Resp)) : Prop where
  /-- `L` is a legal sequential run from `s₀`. -/
  legal : ∃ s, Legal A s₀ L s
  /-- Identities are not repeated. -/
  nodup : (L.map Op.id).Nodup
  /-- Each operation is a request of `H`, with its request. -/
  called : ∀ o ∈ L, Ev.call o.id o.req ∈ H
  /-- Each response of `H` is the response of the operation with its identity. -/
  answered : ∀ i s, Ev.ret i s ∈ H → ∃ o ∈ L, o.id = i ∧ o.resp = s

/-- `L` respects the real-time order of `H`. -/
def RealTime (H : Hist Req Resp) (L : List (Op Req Resp)) : Prop :=
  ∀ a b, RetBeforeCall H a b → ∀ y ∈ L, y.id = b → Before L a b

/-- **Serializability**: some sequential run of `A` from `s₀` explains `H`. -/
def Serializable (A : Atomic σ Req Resp) (s₀ : σ) (H : Hist Req Resp) : Prop :=
  ∃ L, Explains A s₀ H L

/-- **Linearizability** (Herlihy and Wing): some sequential run of `A` from `s₀` explains `H`
and respects its real-time order. -/
def Linearizable (A : Atomic σ Req Resp) (s₀ : σ) (H : Hist Req Resp) : Prop :=
  ∃ L, Explains A s₀ H L ∧ RealTime H L

/-- **A well-formed history**: identities are not reused, each request is answered at most
once, and only after it arrived. -/
structure WellFormed (H : Hist Req Resp) : Prop where
  /-- One request per identity. -/
  callUnique : ∀ i r r', Ev.call i r ∈ H → Ev.call i r' ∈ H → r = r'
  /-- One response per identity. -/
  retUnique : ∀ i s s', Ev.ret i s ∈ H → Ev.ret i s' ∈ H → s = s'
  /-- A response is to a request that arrived. -/
  retCalled : ∀ i s, Ev.ret i s ∈ H → Called H i

/-! ## Hosts -/

/-- A configuration of a host: the state, the (internal) log of handler runs, the history. -/
structure Conf (σ Req Resp : Type) where
  /-- The state. -/
  st : σ
  /-- The handler runs so far, in order (not observed). -/
  log : List (Op Req Resp)
  /-- The history so far. -/
  hist : Hist Req Resp

/-- **A step of the host** of the handler `A` with environment `E`. -/
inductive Step (A : Atomic σ Req Resp) (E : σ → σ → Prop) :
    Conf σ Req Resp → Conf σ Req Resp → Prop
  /-- A request with a fresh identity arrives. -/
  | arrive {c : Conf σ Req Resp} {i : Nat} {r : Req} : ¬ Called c.hist i →
      Step A E c { c with hist := c.hist ++ [.call i r] }
  /-- A request that arrived and has not run is handled atomically. -/
  | run {c : Conf σ Req Resp} {i : Nat} {r : Req} {resp : Resp} {s' : σ} :
      Ev.call i r ∈ c.hist → i ∉ c.log.map Op.id → A c.st r resp s' →
      Step A E c { c with st := s', log := c.log ++ [⟨i, r, resp⟩] }
  /-- The response of a run that has not been answered is issued. -/
  | respond {c : Conf σ Req Resp} {o : Op Req Resp} : o ∈ c.log → ¬ Returned c.hist o.id →
      Step A E c { c with hist := c.hist ++ [.ret o.id o.resp] }
  /-- The environment changes the state. -/
  | env {c : Conf σ Req Resp} {s' : σ} : E c.st s' → Step A E c { c with st := s' }

/-- **A server**: a state type, an atomic handler, an environment and an initial state. -/
structure Server (Req Resp : Type) : Type 1 where
  /-- The state. -/
  σ : Type
  /-- The atomic handler. -/
  handler : Atomic σ Req Resp
  /-- What others may do to the state between handler runs. -/
  env : σ → σ → Prop
  /-- The initial state. -/
  init : σ

/-- The reachable configurations of a server's host. -/
inductive Server.Reach (M : Server Req Resp) : Conf M.σ Req Resp → Prop
  /-- The initial configuration: initial state, no runs, no events. -/
  | init : M.Reach ⟨M.init, [], []⟩
  /-- A step from a reachable configuration. -/
  | step {c c' : Conf M.σ Req Resp} : M.Reach c → Step M.handler M.env c c' → M.Reach c'

/-- The histories of a server. -/
def Server.Hists (M : Server Req Resp) (H : Hist Req Resp) : Prop :=
  ∃ c, M.Reach c ∧ c.hist = H

/-- A server whose state nobody else changes (component state). -/
def Server.closed (A : Atomic σ Req Resp) (s₀ : σ) : Server Req Resp :=
  ⟨σ, A, fun _ _ => False, s₀⟩

/-- **A fresh instance per request** (as `wasmtime serve` runs a `wasi:http` component). -/
def Server.perRequest (A : Atomic σ Req Resp) (s₀ : σ) : Server Req Resp :=
  Server.closed (A.fresh s₀) ()

/-! ## Sentences, satisfaction, refinement -/

/-- **A sentence**: a property of histories. -/
abbrev Sen (Req Resp : Type) : Type := Hist Req Resp → Prop

/-- **Satisfaction**: every history of the server has the property. -/
def Server.Sat (M : Server Req Resp) (φ : Sen Req Resp) : Prop := ∀ H, M.Hists H → φ H

/-- **Refinement**: every history of `M` is a history of `N`. -/
def Server.Refines (M N : Server Req Resp) : Prop := ∀ H, M.Hists H → N.Hists H

/-- **An abstraction** of the server `M` onto the atomic specification `B` from `t₀`. -/
structure Abstraction (M : Server Req Resp) (B : Atomic τ Req Resp) (t₀ : τ) where
  /-- An invariant of `M`'s states. -/
  inv : M.σ → Prop
  /-- The abstraction function. -/
  α : M.σ → τ
  inv_init : inv M.init
  α_init : α M.init = t₀
  inv_handler : ∀ s r resp s', inv s → M.handler s r resp s' → inv s'
  inv_env : ∀ s s', inv s → M.env s s' → inv s'
  /-- Each handler run (from an invariant state) is a run of `B`. -/
  sim : ∀ s r resp s', inv s → M.handler s r resp s' → B (α s) r resp (α s')
  /-- Environment steps (from an invariant state) are invisible to `α`. -/
  env_hidden : ∀ s s', inv s → M.env s s' → α s' = α s

/-- The identity abstraction of a closed server. -/
def Abstraction.closed (A : Atomic σ Req Resp) (s₀ : σ) :
    Abstraction (Server.closed A s₀) A s₀ where
  inv _ := True
  α := id
  inv_init := trivial
  α_init := rfl
  inv_handler _ _ _ _ _ _ := trivial
  inv_env _ _ _ h := h.elim
  sim _ _ _ _ _ h := h
  env_hidden _ _ _ h := h.elim

end Silmaril.Http.State
