# HTTP servers: one framework for Wasm components, processes and containers

This page describes a framework for stating and proving properties of HTTP servers, whatever
runs them: a Wasm component in the wasi:http proxy world, a Linux process on sockets, a
container, or a CGI program run once per request. The aim is to compare implementations by
refinement: for example, a Wasm server refines a Linux server's specification. The code is in
the `Servers` region (`Silmaril/Servers/…`, see [regions.toml](../../regions.toml)). It builds
on the HTTP semantics of `Silmaril.Net.Http` ([HTTP](http.md)) and follows the style of the CLI
institution `Silmaril.Cli.Institution` ([CLI](cli.md)).

Statuses follow [HTTP](http.md):

- **Proved** means that a theorem is stated in a `Thms` header and depends only on the
  standard axioms.
- **Checked** means that the behaviour is evaluated on examples.
- **Defined** means that definitions exist without theorems.
- **Planned** means that nothing exists yet.

No module uses `sorry`, `native_decide` or extra axioms.

Build the modules with `lake build Silmaril.Servers.Core.Thms Silmaril.Servers.Http.Thms
Silmaril.Servers.Examples.Counter.Thms`.

## Traces: the platform-neutral core

`Silmaril.Servers.Core` gives the interface that every instance shares.

### The server institution (Proved)

| Notion | Lean | Reading |
| --- | --- | --- |
| interface (signature) | `Sig` (`Req`, `Resp`) | what a request and a response are |
| request identity | `ReqId` (`conn`, `seq`) | the connection and the position on it |
| event, trace | `Event.recv i r`, `Event.send i s`, `Trace A` | requests received and responses sent, in order |
| sentence | `Sen A := Trace A → Prop` | a trace property |
| model | `Model A` (`Tr : Trace A → Prop`) | the traces an environment can observe of a server |
| satisfaction | `Model.Sat M φ` | every trace of `M` satisfies `φ` |
| refinement | `Model.Refines M N`, that is `M ≤ N` | trace inclusion |
| morphism `A ⟶ B` | `Hom` (`req : B.Req → A.Req`, `resp : B.Resp → A.Resp`) | what the coarser view `A` sees of `B` |

Sentences translate forwards (`Hom.sen`) and models reduce backwards (`Hom.mod`). The
satisfaction condition holds (`Hom.sat_sen_iff`), and the interfaces form a category, so this
is an institution (`inst : Sig ⥤ Room`, `classic`) in the sense of Goguen and Burstall (1992).

Models contain finite observations only. They describe safety (partial correctness): a server
that never answers satisfies every sentence about responses. Liveness and fairness are not
modelled yet.

### Traces with overlapping requests (Defined)

A second request may arrive before the first one is answered. It may arrive on the same
connection (HTTP/1.1 pipelining, HTTP/2 streams) or on another connection (concurrent
clients). A request is identified by its connection and its position there (`ReqId`). A trace
is **well formed** (`Sen.WF`) when no identity is received twice and every response answers an
open request. Well-formedness is checked by a monitor (`WMon`) over the trace.

### The readings people reason with (Defined)

| Reading | Lean | Meaning |
| --- | --- | --- |
| atomic, functional | `Sen.atomic R`, `Sen.ofFun f` | each response is allowed by `R` for its request (or is `f` of it) |
| sequential specification | `History A`, `SeqSpec A`, `Machine A σ`, `Machine.Hist` | request/response pairs of atomic handler runs; a state machine. `Silmaril.Net.Http.Origin σ` is a machine |
| linearizable | `Sen.lin S` | the trace is explained by atomic handler runs placed between each request and its response (linearization points `LEvent.lin`, checked by the monitor `LMon`). Their sequence is a history in `S` (Herlihy and Wing 1990). Pending requests may or may not have run |
| sequentially consistent | `Sen.sc S` | some reordering of the trace that keeps each connection's order is linearizable, so the order across connections is not observed (Lamport 1979) |
| in-order responses | `Sen.inOrder` | on each connection, responses come in request order (RFC 9112 §9.3.2) |
| sequential use | `Sen.Sequential`, `Trace.seq` | each request is answered before the next one arrives |

Three server models are operational:

- `Machine.server M q₀` is the **atomic-handler server**. Requests arrive in any order. The
  handler runs atomically on any pending request, and computed responses are sent in any order.
- `Machine.pipeServer M q₀` is the **pipelining server**. It works the same way, but sends a
  response only when every earlier request on its connection has been answered.
- `Model.ofFun f` is the **function server**. Its traces are the well-formed traces in which
  every response is `f` of its request.

### Theorems (Proved, `Silmaril/Servers/Core/Thms.lean`)

- **The operational and declarative readings agree.** `Machine.server_tr_iff` proves that the
  traces of the atomic-handler server are exactly the linearizable traces, so
  `Machine.server_sat_lin` holds. Linearizable traces are well formed (`Sen.wf_of_lin`).
- **Atomic specifications lift.** A stateless machine allows exactly the pointwise histories
  (`Machine.hist_ofRel`). On well-formed traces, linearizability with respect to a stateless
  specification is the atomic sentence (`Sen.lin_pointwise_iff`, `Sen.lin_ofRel_iff`). So the
  function server is the atomic-handler server of its function (`Model.ofFun_eq_server`).
- **Sequential use forces the linearization.** A sequential use is linearizable exactly when its
  history is in the specification (`Sen.lin_seq_iff`).
- **Pipelining.** The pipelining server refines the atomic-handler server
  (`Machine.pipeServer_refines`). So it is linearizable (`Machine.pipeServer_sat_lin`), and it
  answers in order (`Machine.pipeServer_sat_inOrder`).
- **Linearizable implies sequentially consistent** (`Sen.sc_of_lin`).
- **Refinement is trace inclusion, and the lifts preserve it.** `Model.sat_of_refines`,
  `Model.Refines.trans`, `Sen.atomic_mono`, `Sen.lin_mono`, `Sen.sc_mono` and
  `Machine.server_mono` cover the basic cases. By `Model.sat_lin_of_refines_server`, every
  model that refines a machine's atomic-handler server is linearizable with respect to that
  machine. This is how an implementation, such as a component or a process, is meant to be
  verified: prove that it refines the atomic-handler server of its specification.
- **Morphisms.** `Hom.sen_atomic` proves that the atomic sentence translates to the atomic
  sentence of the projected relation. A trace that is linearizable for a translated
  specification maps to a linearizable trace (`Hom.lin_trace`). So the reducts of linearizable
  models are linearizable (`Hom.mod_sat_lin`).

### The HTTP instance (Proved, `Silmaril/Servers/Http`)

`Http.sig` uses the RFC 9110 `Request` and `Response` of `Silmaril.Net.Http`. Coarser and
finer views are morphisms:

- `Http.status : statusSig ⟶ sig`, which keeps only the status code;
- `Http.path : pathSig ⟶ sig`, which keeps only the path and query;
- `Http.final : sig ⟶ exchSig`, which goes from interim and final responses to the final one.

An origin server (`Origin σ`) is a machine (`Http.machine`), and its trace sentence is
`Http.originSen`. The stateless origin of a web is linearizable exactly when every response is
the web's answer (`Http.originSen_ofTargets_iff`, `Http.server_ofTargets_tr_iff`). The
resource store of `Silmaril.Net.Http` has a linearizable atomic-handler server
(`Http.store_sat`). Status sentences read at the full interface (`Http.sen_allStatus`).

### Example (Proved, `Silmaril/Servers/Examples/Counter`)

The counter machine answers with the number of requests it has already handled. Two of its
traces are proved:

- In `overlap`, two requests on different connections overlap and are answered out of arrival
  order. The trace is linearizable (`overlap_lin`).
- In `early`, a single request is answered `1`. The trace is not linearizable
  (`early_not_lin`).

### Open

- Liveness: every request is eventually answered, under fairness.
- Interim responses and streamed bodies as events in their own right. Today a response is one
  atomic event, and `Http.exchSig` only groups interim responses with the final one.
- Connection events (open, close, half close) and their effect on pending requests.
- The converse of `Hom.lin_trace` (reflection of linearizability along morphisms) and a
  comorphism between the CLI institution and this one (one CLI run per request, as in CGI).
- Proving that the declarative linearizability used here (`Sen.lin`, linearization points) is
  equivalent to the Herlihy–Wing definition (a real-time-order-respecting permutation).

## References

- J. A. Goguen and R. M. Burstall. Institutions: abstract model theory for specification and
  programming. *Journal of the ACM* 39(1), 1992.
- M. P. Herlihy and J. M. Wing. Linearizability: a correctness condition for concurrent
  objects. *ACM Transactions on Programming Languages and Systems* 12(3), 1990.
- L. Lamport. How to make a multiprocessor computer that correctly executes multiprocess
  programs. *IEEE Transactions on Computers* C-28(9), 1979.
- RFC 9110, HTTP Semantics; RFC 9112, HTTP/1.1 (§9.3.2, pipelining).
