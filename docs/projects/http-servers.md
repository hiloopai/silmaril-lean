# HTTP servers: one framework for Wasm components, processes and containers

This page describes a framework for stating and proving properties of HTTP servers, whatever
runs them: a Wasm component in the wasi:http proxy world, a Linux process on sockets, a
container, or a CGI program run once per request. The aim is to compare implementations by
refinement: for example, a Wasm server refines a Linux server's specification. The code is in
the `Servers` region (`Silmaril/Servers/…`, see [regions.toml](../../regions.toml)). It builds
on the HTTP semantics of `Silmaril.Net.Http` ([HTTP](http.md)) and follows the style of the CLI
institution `Silmaril.Cli.Institution` ([CLI](cli.md)).

## Summary and status

A platform-neutral core gives HTTP servers an institution: interfaces, specifications as
sentences over request/response traces (a second request may arrive before the first is
answered), servers as trace sets, refinement as trace inclusion. Atomic, functional,
linearizable and sequentially consistent readings are proved to lift into it. `wasi:http`
components, state models (component state, a filesystem the server alone edits, a shared
filesystem) and Linux, container and CGI platforms are all read as models of the core.

- **Proved:** the core institution and its morphisms; linearizability equal to Herlihy–Wing;
  per-connection and sequentially consistent readings, with serializability from sequential
  consistency; one fresh-instance-per-request model that the WASI, state and platform readings
  are instances of; liveness under weak fairness; HTTP/1.1 framing round trips; platform logs
  as core models, with platform refinement equal to core refinement; socket events of the Linux
  process model; the `hello` module and the `hello`, `route`, `echo` and `greet` specifications
  for every host; the file-backed store component refines state models (b) and (a); the
  shared-file store is linearizable on keys nobody else touches; the `hello` component refines a
  Linux server loop.
- **Tested:** six components (`hello`, `route`, `echo`, `greet`, `store`, `static`) pass 54
  conformance checks against `wasmtime serve` 49.0.2 (`tests/servers`); the script skips when
  no runtime is present.
- **Open** (frozen tasks, results stated conditionally): `Task.wasmRuns`, `Task.binRuns` and
  `Task.staticRuns` (the binaries run the Lean bodies), `Task.loopSentPrefix` (the converse
  refinement for the Linux loop), `Task.wire1Mono`, `Task.specTableCountsConns`,
  `Task.serializable_sc`. Also open: bodies longer than 4096 octets (the components write in one
  `blocking-write-and-flush`, which wasmtime limits to 4096 octets), a comorphism to the CLI
  institution, concurrent wasi:http 0.3 handlers, and comparing the runtime with the Lean
  components rather than with the specifications.

The page has one section per part: the platform-neutral core (traces), the WASI instance, the
state models and a survey with the design of the other instances. Statuses follow
[HTTP](http.md):

- **Proved** means that a theorem is stated in a `Thms` header and depends only on the
  standard axioms.
- **Checked** means that the behaviour is evaluated on examples.
- **Defined** means that definitions exist without theorems.
- **Planned** means that nothing exists yet.

No module uses `sorry`, `native_decide` or extra axioms.

## How the parts fit together

The core (`Silmaril.Servers.Core`) is the shared interface: interfaces `Sig`, traces with
request identities, sentences, models as trace sets, refinement as trace inclusion, and
morphisms, forming an institution. The other parts were written against smaller local
vocabularies and are related to the core as follows.

| Part | Its vocabulary | Relation to the core | Status |
| --- | --- | --- | --- |
| Traces (`Core`, `Http`, `Examples.Counter`) | the core | it is the core | Proved |
| WASI (`Exchange`, `Calls`, `WasiHttp`, `WasiExamples`, `WasiCore`, `WasiBinaries`) | exchange servers: sets of core `History`s over the core `Sig` | lifted into core models by `Exchange.seqUse` and `Exchange.fresh`, with linearizability and refinement of `Machine.server` proved (`fresh_refines_server`, `hello_fresh`, `echo_fresh_lin`); the module of `hello` too (`helloBin_fresh`), and liveness through `Machine.fresh_total` (`hello_live`, `helloBin_live`) | Proved |
| State models (`State`, `State.{Component,OwnedFs,SharedFs}`, `State.Traces`) | histories `Ev.call`/`Ev.ret`, `Atomic σ`, Herlihy–Wing `Linearizable`, `Abstraction` | identified with the core by `State.Traces`: a history is a core trace with one connection per request (`toTrace`), `Atomic σ` is `Machine (sig Req Resp) σ` by definition, Herlihy–Wing linearizability is `Sen.lin` (`linearizable_iff_lin`), the closed host is `Machine.server` (`closed_model_tr_iff`), and an abstraction gives refinement of `Machine.server` (`Abstraction.model_refines`); every trace-level result of (a), (b) and (c) is restated as a core sentence (`State.Sentences`) | Proved |
| File-backed store component (`WasiFs`, `WasiFs.Kv`) | a `wasi:http` component over `wasi:filesystem`, read as a state-model server | refines the file store of state model (b) (`wasiStoreSmall_refines`), its core model refines the core server of its specification (`wasiStore_model_refines`), and through (b) it refines the component-state key-value store of (a) on targets in origin form (`wasiStoreSmall_kv`); its read-only filesystem answers satisfy the `Silmaril.Wasi` filesystem theory (`storeHost_fsOk`) | Proved |
| Shared files and the static server as components (`WasiFs.Shared`, `WasiFs.Static`) | the same component over files others change; a static file server component | the store is linearizable on the keys nobody else touches (`wasiShared_linearizable_on`); the static server refines (b)'s static server, given the open `Task.staticRuns` | Proved (static: conditional) |
| Reducts (`State.Reduct`) | servers read through maps of requests and responses | the histories of `M.mapResp g` are those of `M` with responses mapped (`Server.hists_mapResp`) | Proved |
| Connections on state histories (`State.Conn`) | `Sen.perConn`, `Model.perConn`, `Sen.sc` on `toTrace` | `Sen.sc` gives serializability (`sc_serializable`); a fresh instance per request is an instance per connection on one request per connection (`perRequest_model_iff`) | Proved |
| Connections (`Conn`) | the core | per-connection sentences and models over the core's traces, sequential consistency (`Sen.sc`) | Proved |
| Connection events (`Sessions`) | connection traces `CTrace` (`connect`, `close`, core events) | erasing connection events maps well-formed connection traces onto exactly the well-formed core traces (`CSen.wf_erase`, `CSen.exists_of_wf`), so core sentences and refinement mean the same with connections (`Model.withConns_sat_iff`, `Model.withConns_refines_iff`) | Proved |
| Platforms (`Reuse`, `Cgi`, `Platform`, `Wire1`, `Sockets`, `Compare`) | `Platform T` with `view`, `Refines`, sequential `Log`s and per-connection `ConnLog`s | a `Log` is a core `History` (`log_eq_history`); `Platform.model` reads a platform's logs as a core `Model` and `Refines` is exactly core refinement (`refines_iff_model`); `Platform.connModel` reads per-connection traces as core traces with identities ⟨connection, index⟩, and `Refines` gives core refinement (`connModel_refines`) | Proved |
| Fresh instance per request (`PerRequest`) | the core | one model, `Machine.perRequest M q₀`; `Exchange.fresh`, `State.Server.perRequest` and `Reuse.Fresh` are instances of it (`Exchange.fresh_eq_perRequest`, `State.perRequest_model_tr_iff`, `Reuse.fresh_eq_hist`), and so is the platform `Platform.fresh` (`Platform.fresh_model_tr_iff`) | Proved |
| Liveness (`Live`) | infinite observations `ITrace`, sentences `ISen` | a separate kind of sentence over infinite runs of `Machine.server` and `Machine.pipeServer`; every finite prefix of a run is a core trace (`Machine.IRun.prefix_tr`, `Machine.PRun.prefix_tr`) | Proved |
| A Linux server loop (`LinuxHello`) | a `UserIsa` whose instruction steps are the loop's transitions, run by LPS with its own `accept`, `read`, `sendto` and `close` | its socket traces are a `SockSem` (`Sockets.sockSemNet`), so it is an implementation of `Platform.linux`; it serves hello (`serves`), so the hello component refines it (`wasi_refines_loop`) | Proved; the converse is conditional on `Task.loopSentPrefix` |
| Timed socket traces (`Timed`) | socket traces read as core traces by the event that completes each request and exchange | `timedModel` is a core `Model`; for a monotone framing each connection's receptions and sendings are its per-connection log (`recvsOn_timed`, `sendsOn_timed`), with the cross-connection order of the socket events | Proved; `Wire1.framing` monotone is `Task.wire1Mono` |
| HTTP/1.1 exchanges (`WireExch`) | interim responses and close-delimited final responses on the wire | values of `Http.exchSig` (interim responses, final); `framingC` is a `Platform.Framing` | Proved |

Every part is now read in the core. What remains outside it is listed under "Open" in each
section: in particular the CLI institution is not yet related to this one by a comorphism, and
the runtime conformance tests compare a binary with the specs, not with the Lean components.

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
that never answers satisfies every sentence about responses. Liveness and fairness are a
separate kind of sentence, over infinite runs (below, "Liveness").

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
- **The converse, for morphisms that see every response.** When `h.resp` is surjective (as for
  `Http.status`, `Http.path` and `Http.final`), a trace whose view is linearizable for `S` is
  linearizable for the translation `h.seq S` (`Hom.lin_of_trace`, `Hom.lin_trace_iff`). So
  linearizability translates along the morphism (`Hom.sen_lin`), and a model satisfies the
  translated sentence exactly when its reduct is linearizable (`Hom.sat_lin_iff`). The
  annotated trace of the finer view takes each handler run's request from the monitor and its
  response from the response sent later to the same identity, or any preimage if none is sent;
  without surjectivity this last choice can fail, since a handler run whose response is never
  sent still counts in the history.
- **The linearization monitor's invariant** (`LMon.Inv`: a pending request was received and has
  no response ready; a ready response answers a received request) holds initially and is kept
  by every step (`LMon.inv_init`, `LMon.Inv.step`).

### Connections and sequential consistency (Proved, `Silmaril/Servers/Conn`)

Readings that look at one connection at a time: `Sen.perConn φ` (the events of every
connection satisfy `φ`), `Sen.connSeq` (each client waits for every response before its next
request, while connections overlap), and `Model.perConn N`, an instance of `N` per connection
(a process forked per connection, a keep-alive connection bound to one Wasm instance).

- **Sequential consistency from a merge.** If some sequential use with the same events on every
  connection has its history in `S`, the trace is sequentially consistent with respect to `S`
  (`Sen.sc_of_merge`). Sequential consistency only looks at the connections one by one
  (`Sen.sc_congr`).
- **Strictly weaker than linearizability.** `counterTrace` answers request 0 of connection 0
  with `1`, and only then request 0 of connection 1 arrives and is answered `0`. For the
  counter it is sequentially consistent (`counter_sc`: swap the connections) but not
  linearizable (`counter_not_lin`: real time forbids the swap).
- **Pipelining per connection.** In-order responses are a per-connection property
  (`Sen.inOrder_of_perConn`). With a pipelining instance of a machine per connection, every
  connection answers in order (`Model.perConn_pipe_inOrder`) and is linearizable on its own
  (`Model.perConn_pipe_lin`).
- **Without state, an instance per connection is one server.** For a stateless machine, an
  instance per connection refines the shared atomic-handler server (`Model.perConn_ofRel`), so
  it is linearizable and sequentially consistent. `Model.perConn_mono` and `Model.perConn_sat`
  give monotonicity and the transfer of sentences.

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
(`Http.store_sat`). Status sentences read at the full interface (`Http.sen_allStatus`). The
three views see every response (`Http.status_resp_surjective`, `Http.path_resp_surjective`,
`Http.final_resp_surjective`), so linearizability translates along them: a server's status
codes are linearizable for `S` exactly when the server is linearizable for `S` read on status
codes (`Http.sat_lin_status`).

### A fresh instance per request (Proved, `Silmaril/Servers/PerRequest`)

A host that handles every request with a fresh instance (CGI, `wasmtime serve` for a 0.2
proxy component, Spin, Fastly Compute) has one model over the core:
`Machine.perRequest M q₀`, the atomic-handler server of the stateless machine
`Machine.fresh M q₀`, which answers every request as `M` answers it from `q₀`.

- Its traces are the well-formed traces in which every response is an answer of `M` from `q₀`,
  however the requests overlap (`Machine.perRequest_tr_iff`). It is linearizable
  (`Machine.perRequest_sat_lin`), a sequential use is a trace exactly when every exchange is an
  answer from `q₀` (`Machine.perRequest_seq_iff`), and it is monotone in the answers
  (`Machine.perRequest_mono`). For a stateless machine it is the atomic-handler server
  (`Machine.perRequest_ofRel`).
- **Instances.** The `wasi:http` reading `Exchange.fresh M` is `(Exchange.machine M).perRequest ()`
  (`Exchange.fresh_eq_perRequest`, an equality of models). The core traces of the state models'
  host `State.Server.perRequest A s₀` are the traces of `A.machine.perRequest s₀` with one
  connection per request (`State.perRequest_model_tr_iff`). The sequential logs of fresh
  instances `Reuse.Fresh O s₀` are the histories of `Machine.fresh` (`Reuse.fresh_eq_hist`), so
  they are the sequential uses of the model (`Reuse.fresh_seq_iff`); the logs of one reused
  instance `Reuse.Seq` are the histories of the origin read as a machine (`Reuse.seq_iff`).
- **The platforms.** The core model of the platform `Platform.fresh σ` (a handler with instance
  state run on a fresh instance per request, observed as sequential logs) has exactly the
  sequential uses of `(Http.machine O).perRequest s₀` (`Platform.fresh_model_tr_iff`), so it
  refines it and is linearizable for `Machine.fresh` (`Platform.fresh_model_refines`,
  `Platform.fresh_model_sat_lin`). Likewise `Platform.seq σ` (one reused instance) has exactly
  the sequential uses of the origin's atomic-handler server (`Platform.seq_model_tr_iff`,
  `Platform.seq_model_refines`). Its logs are the histories of `Machine.fresh`
  (`Platform.fresh_view_iff`) and of the origin (`Platform.seq_view_iff`).

### Liveness (Proved, `Silmaril/Servers/Live`)

The core's sentences are about finite traces and say only what a server may do. Liveness is a
separate kind of sentence, over infinite observations (`ITrace A`: at each instant an event or
nothing; `ISen A`).

- `ISen.answered`: every request received is eventually answered.
- `Machine.IRun M q₀`: an infinite run of the atomic-handler server (it idles or takes a step
  at each instant). `IRun.Fair` is weak fairness per request: a handler run that stays enabled
  is eventually taken, and a ready response that stays ready is eventually sent.
  `Machine.Total M`: the handler can answer every request in every state.
- **`Machine.IRun.answered`**: fair runs of a total machine answer every request
  (`Machine.fairObs_answered` for the fair observations). The proof is that a pending request
  stays pending until its handler run, and a ready response stays ready until it is sent.
- Safety and liveness together: every prefix of a run's observation is a trace of the server
  (`Machine.IRun.prefix_tr`), so a run satisfies every sentence the server satisfies at every
  prefix (`Machine.IRun.always_of_sat`), in particular linearizability
  (`Machine.IRun.always_lin`).
- Function servers and relations that answer every request are total (`Machine.ofFun_total`,
  `Machine.ofRel_total`), and so is a fresh instance per request of a machine that can answer
  every request from its initial state (`Machine.fresh_total`).
- **The pipelining server.** `Machine.PRun M q₀` is an infinite run of the pipelining server.
  A response is *sendable* when it is ready and every earlier request on its connection has
  been answered (`PRun.SendEnabled`); `PRun.Fair` asks that a handler run that stays enabled is
  eventually taken and that a response that stays sendable is eventually sent.
  **`Machine.PRun.answered`**: fair runs of the pipelining server of a total machine answer
  every request (`Machine.pipeFairObs_answered`). The proof is by strong induction on the
  position of the request on its connection: each earlier request that ever arrives is
  answered, by induction, and stays answered, so from some instant on the response stays
  sendable and fairness sends it. Every prefix is a trace of the pipelining server
  (`Machine.PRun.prefix_tr`), so a run answers in order at every prefix
  (`Machine.PRun.always_inOrder`).
- **Fair runs exist** (`Machine.exists_fair`). For a total machine and every stream of requests
  on a connection, the run that receives the `k`-th request at instant `3k`, runs the handler
  on it at `3k + 1` and sends the response at `3k + 2` is weakly fair, both as a run of the
  pipelining server and as a run of the atomic-handler server. So the fair observations are
  not empty (`Machine.fairObs_nonempty`, `Machine.pipeFairObs_nonempty`), and the liveness
  theorems are not vacuous. Fair runs for streams of requests on several connections at once
  are not constructed.

Liveness is relative to the host: the theorems assume a weakly fair scheduler.

### Connection events (Proved, `Silmaril/Servers/Sessions`)

The core's traces carry the connection of each request but not the connections themselves.
`CEvent A` adds them: a connection is opened (`connect c`), closed by either side
(`close c`), or a core event happens on it (`ev e`); `CTrace.erase` forgets the connection
events.

- **Well formed** (`CSen.WF`, the monitor `CMon`): each connection is opened once and closed at
  most once (`Phase`: `fresh`, `live`, `closed`); requests are received and answered only on
  live connections, as the core's monitor allows. A request still open when its connection
  closes is never answered.
- **Nothing is lost.** The core trace of a well-formed connection trace is well formed
  (`CSen.wf_erase`), and every well-formed core trace is the core trace of one
  (`CSen.exists_of_wf`: open every connection it uses first). So for a model whose traces are
  well formed, `M.withConns` (its traces with connections) satisfies the lift of a core
  sentence exactly when `M` satisfies it (`Model.withConns_sat_iff`), and refinement is the
  same with and without connections (`Model.withConns_refines_iff`).
- **Graceful close** (`CSen.graceful`): a connection is closed only once every request received
  on it has been answered. **`CSen.graceful_answered`**: a well-formed graceful trace that
  closes every connection it opens answers every request. `Model.graceful M` is the graceful
  part of `M.withConns` (`Model.graceful_refines`, `Model.graceful_sat`).

The socket events of the Linux platform (`SockEv.accept`, `SockEv.close`) are the same events
at the level of octets; reading them as `CEvent`s is not done yet.

### Example (Proved, `Silmaril/Servers/Examples/Counter`)

The counter machine answers with the number of requests it has already handled. Two of its
traces are proved:

- In `overlap`, two requests on different connections overlap and are answered out of arrival
  order. The trace is linearizable (`overlap_lin`).
- In `early`, a single request is answered `1`. The trace is not linearizable
  (`early_not_lin`).

### Open

- Interim responses and streamed bodies as events in their own right. Today a response is one
  atomic event, and `Http.exchSig` only groups interim responses with the final one.
- Half close, and server models that react to connection events (a pipelining server per
  connection that abandons the open requests of a closed connection); reading the socket events
  of the Linux platform as connection traces.
- Reflection of linearizability along morphisms whose response map is not surjective, and a
  comorphism between the CLI institution and this one (one CLI run per request, as in CGI).
- Liveness of the `wasi:http` example components (their machines are total, so
  `Machine.fresh_total` applies once a component's per-request runs are read as a fair host),
  and fair runs for request streams on several connections at once.

## WASI: `wasi:http` components as servers (`Silmaril.Servers.{Exchange,Calls,WasiHttp,WasiExamples,WasiCore,WasiBinaries}`)

### Exchange servers and their lifts to the core (`Silmaril.Servers.Exchange`)

The WASI reading is first stated over **exchange servers**: each request and its response form
one atomic exchange, and a server is a set of exchange sequences, that is a set of core
histories (`History`). A specification is a core sequential specification (`SeqSpec`).

| Part | Status |
| --- | --- |
| `Iface` (the core's `Sig`), exchanges, `Model I` (sets of histories), `Sen I` (`SeqSpec I`), `Sat`, `each R`, `ofFun`, `ofRel` | Defined |
| Refinement as inclusion (`Refines.sat`, `Refines.trans`); `sat_each_iff`; `ofFun_refines_iff` | Proved |
| Interface morphisms `Hom I J` (read requests, write responses), `Hom.lift`, `Hom.pull`, the satisfaction condition `Hom.sat_lift_iff`, `Hom.lift_mono` | Proved |
| **Lift 1, one instance used sequentially** (`seqUse M`: core traces that answer each request before the next, on fresh identities): linearizable for every specification `M` satisfies (`seqUse_sat_lin`, from the core's `Sen.lin_seq_iff`) | Proved |
| **Lift 2, a fresh instance per request** (`fresh M`: well-formed core traces with any overlap, each request and its response a one-exchange trace of `M`, as `wasmtime serve` runs a 0.2 proxy component): `each R` gives the atomic sentence (`fresh_sat_atomic`), refinement of the atomic-handler server of `R` (`fresh_refines_server`) and linearizability (`fresh_sat_lin`); a server refining `ofFun f` refines the core's function server `Model.ofFun f` (`fresh_ofFun_refines`) | Proved |
| Both lifts preserve refinement (`seqUse_mono`, `fresh_mono`) | Proved |

The exchange-server `Hom` points the other way from the core's `Hom` (it writes responses
forwards); relating the two is open.

### The `wasi:http` proxy world

A `wasi:http/proxy` component exports `wasi:http/incoming-handler.handle(request:
incoming-request, response-out: response-outparam)`. The host calls it once per incoming
request. The slice in `Silmaril.Servers.WasiHttp` was checked by hand against the vendored
`specs/wasi/0.2.12/http/{proxy,handler,types}.wit` and `specs/wasi/0.2.12/io/streams.wit`:

| Function | Name in Lean |
| --- | --- |
| `incoming-handler.handle` (export) | `handleF` |
| `[method]incoming-request.method`, `[method]incoming-request.path-with-query` | `reqMethod`, `reqPath` |
| `[method]incoming-request.consume`, `[method]incoming-body.stream` | `reqConsume`, `inStream` |
| `[constructor]fields`, `[constructor]outgoing-response` | `newFields`, `newResp` |
| `[method]outgoing-response.set-status-code`, `[method]outgoing-response.body` | `setStatus`, `respBody` |
| `[method]outgoing-body.write`, `[static]outgoing-body.finish` | `bodyWrite`, `bodyFinish` |
| `[static]response-outparam.set` | `outSet` |
| `wasi:io/streams` `[method]output-stream.blocking-write-and-flush`, `[resource-drop]output-stream` | `streamWrite`, `streamDrop` (`Silmaril.Wasi.Theory`) |
| `wasi:io/streams` `[method]input-stream.blocking-read` | `inRead` |

The names and value encodings follow the existing WASI theories (`Silmaril.Wasi.Theory`,
`Silmaril.Wasi.Versions.Net`): unversioned 0.2 interface names, handles as `u32`, `result` and
`option` as variants, strings as records of `char`s.

### Components read as HTTP servers

Components are bodies of `Silmaril.Wasi.Comp`: one program over the imports for each export
call, with **uninterpreted** imports. Every answer of the host is a possible play, so a
statement about all plays holds for every host.

- **Calls are atomic** (`Silmaril.Servers.Calls`). A body runs one export call at a time, so
  every play is a sequence of complete runs of export calls, followed by at most one call in
  progress. This is the shape theorem `calls_of_mem`. Its corollary `sat_each` reduces a
  specification `each R` to one complete run of one call. `mem_model_single` gives the
  converse: a single answered run is a trace, so specifications are not vacuous. `runP` runs a
  program over a concrete host (`leads_runP`). **Proved.**
- **The response of a call** (`respOf o`) is the response passed to
  `response-outparam.set(o, ok(rh))`. Its status is the last accepted `set-status-code` on
  `rh`, which defaults to `200` as the WIT says. Its header section is the lines accepted by
  `fields.append` on the fields that `rh` was constructed from, in order. Its content is the
  bytes written to the output streams of `rh`'s body, and that body must be finished. Only the
  host's answers are read. A failed or ill-typed answer to an operation of the response, or to
  any `fields.append` of the call, makes the response unobservable.
- **`set` may be called once.** It consumes the outparam, so a second `set` of the same
  outparam makes the response unobservable (`oSet_twice`).
- **The request of a call** is any request (`Silmaril.Net.Http.Request`) consistent with what
  the host answered on the request handle: the `method` and `path-with-query` answers
  (`ReqOk`), and the `fields.get` and `fields.entries` answers on the headers resources taken
  from the request with `incoming-request.headers` (`HdrOk`): the request's values for that
  field name, compared case-insensitively, and its whole header section. The rest of the
  request (authority, content) is left open, so a specification must hold for every request
  consistent with the answers.
- **Linked systems.** `linkServer η σ` is the server read from `Silmaril.Wasi.link η σ`, the
  component over a host `η` with any lower interface: the exchanges of the component's calls
  in the plays behind the link. It refines `wasiServer σ` (`linkServer_refines`,
  `linkServerB_refines`), so every specification of the component holds over every host
  (`link_sat_of`, `link_satB_of`). An answered run over a concrete implementation is a trace of
  the body linked over that concrete host (`mem_linkServer`), so the linked servers are not
  vacuous. **Proved.**
- **Binaries.** `Runs σ h`: every play of the strategy `σ` is a play of the body `h`. A
  strategy that runs `h` refines `h` as a server, alone and linked over any host
  (`runs_refines`, `runs_refinesB`, `runs_link`). **Proved.**
- `wasiServer σ : Exchange.Model httpIface` is the component `σ` read as a server of
  `Silmaril.Net.Http` requests and responses (RFC 9110 §6). `httpIface` is the core's `Http.sig` (`httpIface_eq`). **Defined.**
- `wasiServerB σ` also reads request bodies (`BodyOk`). After every prefix of a call, the bytes
  delivered by `blocking-read` on the streams of the bodies consumed from the request are a
  prefix of the request's content, and they are all of it once a read answers `closed`. It
  refines `wasiServer σ` (`wasiServerB_refines`), so the specifications proved for
  `wasiServer` carry over (`hello_satB`). **Proved.**

### Example servers

| Server | Specification | Status |
| --- | --- | --- |
| `answer o resp`, the shared response code (fields, `fields.append` of each header line of `resp`, outgoing response, status, body, `set`, write, drop, finish) | For every host, no response or exactly `resp`, header lines included (`answer_run`, through `addFields_run` for the appends). Over a host whose answers succeed, exactly `resp` (`answer_ok`, in the proofs). | Proved |
| `hello` | Every exchange is `200 hello` with the header `content-type: text/plain` (`hello_sat`), so `hello` refines the server of the constant function (`hello_refines`). Every request answered `200 hello` is a trace (`hello_answers`). | Proved |
| `route` | Every exchange is answered from the route table on the path-with-query: `/` gives `200 home`, `/hello` gives `200 hello` and anything else gives `404 not found` (`route_sat`, `route_refines`). Every request answered from the table is a trace (`route_answers`). | Proved |
| `greet` (take the request's headers with `headers()`, read `x-name` with `fields.get`, answer `200 hello <first value>`, or `200 hello world` without one; `500` when `headers()` is not answered with a handle) | Every exchange is the greeting of the request's `x-name` values, or `500` (`greet_sat`); the value comes from the header answers of the reading (`HdrOk`), tied to the request. Every request answered with its greeting is a trace (`greet_answers`). | Proved |
| `echo` (consume the body, read until `closed` at most `echoFuel` times, answer `200` with the bytes read, else `500`) | Every exchange of `wasiServerB (ofBody echo)` is `200` with the request's content, or `500` (`echo_sat`). The proof is an induction over the read loop that carries `BodyOk` along the prefixes of the call. | Proved |
| `hello`, `route`, `greet`, `echo` over the reference host `refHost` (`serveRef`) | `hello` on `/`, `route` on `/`, `/hello` and `/missing`, `greet` with and without `x-name`, and `echo` on a `POST` with content `abc` | Checked |
| Liveness, through `Machine.fresh_total`: with a fresh instance per request (`freshM`), `hello`, `route` and `greet` can answer every request (`hello_total`, `route_total`, `greet_total`, from the non-vacuity theorems), so every weakly fair run of a host serving them answers every request it receives, and every prefix of the run satisfies the safety specification (`hello_live`, `route_live`, `greet_live`) | | Proved |
| The reference host's answers have the WIT result types (`refHost_ty`), so a response over it is a trace over typed hosts (`serve_memTy`) | | Proved |
| `hello`, `route` with a fresh instance per request, in the concurrent core: they refine the core's function servers (`hello_fresh`, `route_fresh`); `echo` is linearizable for its specification (`echo_fresh_lin`); `hello` used sequentially is linearizable (`hello_seq_lin`) | | Proved |
| `hello`, `route`, `greet`, `echo` linked over every host (`hello_link`, `route_link`, `greet_link`, `echo_link`); a response over the reference host is a trace of the example linked over the concrete reference host (`serve_link`, `hello_link_answers`) | | Proved |
| Any strategies that run the bodies (`Runs`) satisfy the specifications, alone and linked over every host: `wasm_sat` under `Task.wasmRuns σh σr σe` | | Conditional results proved |
| The core modules of the components, read by a denotation (below): the module of `hello` runs the body `hello` over typed hosts (`hello_runsTy`) | | Proved |
| The modules of `route`, `echo` and `greet` run their bodies over typed hosts (`Task.binRuns`; `binRuns_sat` gives their specifications under it) | | Open (conditional results proved) |
| A server as a web of the outgoing theories (`webOf`): the client theories `Net.httpTh`/`httpTh3 (webOf f)` see the status of `f`'s answer to a `GET` (`webOf_pathV`, `route_web_missing`) | | Proved |

The examples are Lean programs over the imports, in the shape of a component after lifting.
The order of `answer` (`set` before the body is written) is the one the `wasi:http`
documentation recommends, so that a host can stream the body.

### The components

`tests/servers/wasi-http/{common,hello,route,echo,greet}.wat` are the same four servers as core
Wasm modules: `common.wat` holds the imports, the memory, a bump allocator (`cabi_realloc`) and
`answer`, and each server file holds its export
`wasi:http/incoming-handler@0.2.12#handle`. Every export makes the import calls of its Lean
body, in the same order and with the same arguments, and takes the same branches on the
answers (`hOf`: the handle of an `ok`, else `0`). `tests/servers/wasi-http/build.sh` wraps each
in a module, gives it the component type of `tests/servers/wasi-http/world.wit` (which imports
`wasi:http/types@0.2.12` and `wasi:io/streams@0.2.12` and exports
`wasi:http/incoming-handler@0.2.12`, over the WIT in `specs/wasi/0.2.12`) with
`wasm-tools component embed` and makes the component with `wasm-tools component new`. The
flake's `http-test` shell pins the tools (`nix develop .#http-test`: wasmtime 49.0.2,
wasm-tools 1.261.0, curl).

The binaries differ from the bodies in a few places, none of which changes the import calls
over a typed host: `route` compares the UTF-8 bytes of the path, where the Lean reading maps
each `char` to an octet (`octet`, which maps a `char` above `U+00FF` to `0xFF` so that no
non-ASCII path reads as an ASCII one); `greet` has no `500` path, since `headers()` always
answers a handle; and `blocking-write-and-flush` accepts at most 4096 bytes, so for a longer
`echo` body the host fails the write, which the reading counts as no response.

### The components' code (`Silmaril.Servers.{WasiCore,WasiBinaries}`)

`Silmaril.Wasi.compModel` reads a component of the component IR as a WASI model, but the IR's
canonical-ABI adapters are flat (no linear memory), so they cannot lift the strings and lists
these components pass through memory. `WasiCore` instead gives a core module the denotation
of a body over the proxy imports:

| Part | Lean | Status |
| --- | --- | --- |
| The modules: `helloCore`, `routeCore`, `echoCore`, `greetCore`, read at elaboration time from the very `.wat` files the conformance test builds, by the Core 3 WAT frontend of `wat3!` (`wat3_files!`) | `Silmaril.Servers.WasiBinaries.Defs` | Defined |
| The denotation `coreBody m fuel`: a fresh instance per call (globals, one memory, active data), a big-step interpreter of a core fragment in continuation-passing style (constants, locals, globals, integer arithmetic and comparisons, loads and stores, `memory.size`/`grow`/`copy`, structured control, direct calls; anything else traps), at most `fuel` steps, whose import calls are the body's moves | `run`, `coreBody` | Defined |
| The canonical ABI of the slice's 16 imports (`glue`): flat arguments lifted from memory (strings must be ASCII), answers lowered into flat results or through the return pointer with the canonical layouts, host strings and lists copied into memory allocated by the module's `cabi_realloc` | `glue`, `Low`, `lower` | Defined |
| Memory as a log of writes, so that a handle stored and loaded back is the same value without arithmetic (`wordAt`) | `Wr`, `byteAt` | Defined |
| Typed hosts: `AnsTy f n`, the answer has the WIT result type of `f`; `RunsTy σ h`, every play of `σ` with typed answers is a play of `ofBody h`; `wasiServerTy σ`, the reading over typed hosts | | Defined |
| A body that simulates `h` on typed answers runs `h` over typed hosts (`sim_runsTy`), and then refines `h` as a server (`runsTy_refines`, `runsTy_refinesB`) | `Silmaril.Servers.WasiCore.Thms` | Proved |
| **`hello`**: the module simulates the body (`hello_sim`), so it runs it over typed hosts (`hello_runsTy`), answers `200 hello` with its header (`helloBin_sat`), refines the core's function server with a fresh instance per request (`helloBin_fresh`), answers every request over the reference host (`helloBin_serveRef`, `helloBin_answers`) and is live over a fair host (`helloBin_live`) | `Silmaril.Servers.WasiBinaries.Thms` | Proved |
| `route`, `echo`, `greet`: their denotations over the reference host give the expected responses on the requests above | `routeBin_ref_*`, `echoBin_ref`, `greetBin_ref_*` | Checked |
| `route`, `echo`, `greet` run their bodies over typed hosts | `Task.binRuns` | Open |

The proof for `hello` computes each next import call of the denotation in the kernel
(`kernel_rfl`), with the host's answers as variables, and splits the answers only where the
module reads them (the handles of `outgoing-response.body` and `outgoing-body.write`), so it has
four paths and checks in about 4 s. `route`, `echo` and `greet` depend on host data of
unbounded size (the path's bytes, the body's chunks, the list of header values), which this
evaluation does not cover; they need lemmas about the interpreter on symbolic memory.

What the denotation assumes: hosts are typed (a runtime only gives answers of the WIT result
types, and a trapping host ends the instance, which the bodies do not model); each call of
`handle` runs on a fresh instance, as `wasmtime serve` runs a 0.2 proxy component; the payload
of an `error-code` from `outgoing-body.finish` is not written into memory; and the component
wrapper made by `wasm-tools component new` is taken to be the canonical-ABI adapters of `glue`.
That `run` and `glue` agree with the Core 3.0 game semantics (`Silmaril.Wasm.Game`) and the
reference canonical ABI (`Silmaril.Wasm.Component.Reference`) on modules of the fragment is not
proved; the kernel-reducible verified interpreter of `Silmaril.Wasm.Verify.Kernel` and the
canonical-ABI soundness results of the reference machine are the parts such a proof would use.

### Conformance against a runtime

`tests/servers/wasi-http-conformance.sh` builds the six components (or takes `HELLO_WASM`,
`ROUTE_WASM`, `ECHO_WASM`, `GREET_WASM`, `STORE_WASM`, `STATIC_WASM`, checking only those
given), serves each with `wasmtime serve` and compares the
responses to the specifications: `hello` on `/` and `/anything` (status, content and
`content-type`), `route` on `/`, `/hello` and `/missing`, `echo` on a `GET` and on `POST`s of 3
and 3000 bytes, and `greet` without `x-name`, with one and with two values. The
runtime is pinned (`WASMTIME_VERSION`, default `49.0.2`; `any` accepts every version). It
skips cleanly when `wasmtime`, `curl`, or both the components and `wasm-tools`, are missing.
Run as `nix develop .#http-test -c tests/servers/wasi-http-conformance.sh`, the 12 checks of
these four pass on wasmtime 49.0.2.

The same harness serves the filesystem servers of the state models (section "State models"),
`tests/servers/wasi-http/{store,static}.wat` (with `fs-imports.wat` and `fs.wat`, world
`fs-server` of `world.wit`, which also imports `wasi:filesystem/{types,preopens}@0.2.12`), with
`wasmtime serve -S cli --dir DIR::data` over a fresh directory. All 54 checks of the whole run
(hello, route, echo, greet, store and static) pass on wasmtime 49.0.2, with the one known gap
below printed and not counted:

- **store** (`storeBody`, state model (b)): `GET`, `HEAD`, `PUT` (`201`, then `204`), `DELETE`
  (`204`, then `404`), `OPTIONS`, `405` for `POST` and `PATCH`, `501` for an unknown method; the
  query is part of the key; the files it writes are named `keyName` (`/a` is `k2f61`); a
  200000-octet `PUT` (several reads of the request body) lands in its file;
- **store over shared files** (state model (c)): the harness writes and removes key files
  between requests; an untouched key keeps its value, a changed key is read as it was left,
  and a file of no key is never written;
- **static** (`staticAnswer (docRoot "data")`): nested files, `.` and empty components and a
  query, `..` (sent with `--path-as-is`) and the preopen itself and a directory answered `404`,
  `HEAD`, `405` with `Allow: GET, HEAD`; then a file changed and one removed by another writer.

One known gap is printed and not counted: a `GET` of the 200000-octet file returns no content,
because `answer` writes the whole content with one `blocking-write-and-flush`, which `wasi:io`
0.2 limits to 4096 octets (wasmtime traps: "Buffer too large for blocking-write-and-flush").
The reference host of the Lean reading (`refHost`) accepts any length, so the Lean results
(`run_spec` and the others) say nothing about this limit; a `GET` of 4096 octets passes. The
same limit applies to `echo`. Fixing it means writing in chunks of at most 4096 octets, in the
WAT and in the Lean `answer` (and its proofs), and giving the reference host the limit.

### Not modelled yet

- Headers added to a response after its construction (`outgoing-response.headers`),
  `fields.set`, `delete` and `from-list`, trailers and `send-informational`.
- Liveness of `echo`: it may answer `500` when the host delivers the body in more than
  `echoFuel` reads, and it has no non-vacuity theorem for every request (it is checked on one
  request), so `Machine.fresh_total` is not applied to it. Liveness is relative to a weakly
  fair host; that the host's own runs (a `wasmtime serve` process) are fair is not modelled.
- Resource drops other than the output stream's.
- Concurrent export calls. A body runs one call at a time. The host may also run several
  instances, which gives concurrency across instances.
- A host-side theory of `wasi:http` (which answers a host may give, e.g. that a second `set`
  traps) to strengthen the linked statements beyond "every host".
- That the modules of `route`, `echo` and `greet` run their bodies (`Task.binRuns`), and that
  the fragment denotation agrees with Core 3.0 and the reference canonical ABI (see above).
- The equality of `Silmaril.Wasi.ofBody` with `Silmaril.Games.Strategy.ofHandler` is still
  open (see [More Wasm](wasm-wasi.md)).

## State models

Modules `Silmaril.Servers.State.*`. This section covers where a server keeps its
state and what can be proved about the histories a client observes in each case. All servers
here have the same interface: requests and responses of `Silmaril.Net.Http`
(`Request = Message RequestLine`, `Response = Message Status`, RFC 9110 §6). Only the state
model changes from one server to the next.

### The shared vocabulary (`Silmaril.Servers.State`)

| Notion | Lean | Status |
| --- | --- | --- |
| History: request `i` arrives with `r` (`Ev.call i r`), its response `s` is issued (`Ev.ret i s`). A second request may arrive before the first response, and responses may come in any order | `Ev`, `Hist` | defined |
| Atomic handler: a relation between state, request, response and next state (`Net.Http.Origin σ` is the HTTP case) | `Atomic`, `Atomic.ofFun`, `Atomic.fresh`, `Atomic.ofRel` | defined |
| Sequential runs; serializability; linearizability (Herlihy and Wing 1990: a sequential run of the handler explains the history and respects real time; pending requests may be included) | `Legal`, `Explains`, `Serializable`, `Linearizable`, `RealTime` | defined |
| Server: state, handler, environment (what others do to the state between runs), initial state. Its host takes requests with fresh identities, runs any pending request atomically and answers runs in any order | `Server`, `Step`, `Server.Reach`, `Server.Hists` | defined |
| Sentences (history properties), satisfaction, refinement (history inclusion) | `Sen`, `Server.Sat`, `Server.Refines` | defined |
| Abstraction of a server onto an atomic specification: invariant, abstraction function, handler runs simulated, environment invisible | `Abstraction` | defined |
| A server with an abstraction is **linearizable** with respect to the abstract specification, and **refines** the closed server of it | `Abstraction.sat_linearizable`, `Abstraction.refines` | proved |
| Every history is well formed; each response in a linearizable history is an answer of the specification to its request; linearizability is transported along simulations; refinement preserves satisfaction | `Server.sat_wellFormed`, `Linearizable.answer`, `Linearizable.map`, `Server.Refines.sat` | proved |
| With a fresh instance per request (as `wasmtime serve` and Spin run components), each response is an answer from the initial state | `Server.perRequest`, `perRequest_answer` | proved |

The linearization in these proofs is the order in which the host runs its handlers. For this
order to exist, each handler run must be atomic: the host runs one request at a time. That is
the case for a synchronous `wasi:http` handler on one instance. The host may still choose
which pending request to run next, so overlapping requests, out-of-order responses and
requests that are never answered are all covered.

### The state models in the core (`Silmaril.Servers.State.Traces`, Proved)

The state models' vocabulary is read in the core, so that the core is the one vocabulary:

- A history is a core trace with **one connection per request**: `Ev.call i r` is
  `Event.recv ⟨i, 0⟩ r` and `Ev.ret i s` is `Event.send ⟨i, 0⟩ s` (`toTrace`, injective,
  `toTrace_injective`). The state histories do not model connections, so this reading adds no
  order. `Server.model M` is the core model of a state server.
- `Atomic σ Req Resp` is `Machine (sig Req Resp) σ` by definition (`atomic_eq_machine`); at HTTP
  it is `Machine Http.sig σ` and `Origin σ` (`atomic_eq_http`, `atomic_eq_origin`).
- **Herlihy–Wing linearizability is the linearization-point sentence**: for a history whose core
  trace is well formed, `Linearizable A s₀ H ↔ Sen.lin (A.machine.Hist s₀) (toTrace H)`
  (`linearizable_iff_lin`; the direction from the core needs no hypothesis,
  `linearizable_of_lin`). One direction replays the history on the host, running the
  operations of the sequential run up to the one of each response just before it (each has
  arrived, by the real-time order); the other goes through the host's own linearizability.
- **The closed host is the core's atomic-handler server**, on traces with one connection per
  request (`closed_model_tr_iff`), by a forward and a backward simulation (arrive is `recv`,
  run is a linearization point, respond is `send`).
- **An abstraction gives core refinement**: a state server with an abstraction onto `B` refines
  `B.machine.server t₀` (`Abstraction.model_refines`), so it is linearizable in the core
  (`Abstraction.model_sat_lin`) and, at HTTP, satisfies the origin's trace sentence
  `Http.originSen` (`Abstraction.model_sat_originSen`). Refinement of state servers is
  refinement of their core models (`Server.Refines.model`).

### The results as core sentences (`Silmaril.Servers.State.Sentences`, Proved)

Every trace-level result of (a), (b), (c) and of the file-backed store component is restated
one by one about the core model `Server.model M`. Three bridges do the work:

- `model_refines_server`: a state server that refines `Server.closed A s₀` has a core model that
  refines `A.machine.server s₀` (from `Server.Refines.model` and `closed_model_tr_iff`), so it
  satisfies `A`'s linearizability sentence (`model_sat_lin`);
- `model_sat_atomic`: a statement about the calls and returns of every history is a core atomic
  sentence of the model;
- `model_sat_distinct`: distinct answers to distinct requests are the core sentence
  `Sen.distinct`.

| Result | Core restatement | Kind |
| --- | --- | --- |
| `counter_linearizable` | `Component.counter_model_refines`, `counter_model_sat_lin` | refinement, `Sen.lin` |
| `kv_linearizable` | `Component.kv_model_refines`, `kv_model_sat_origin` | refinement, `Http.originSen` |
| `counter_distinct`, `decimalCounter_distinct` | `Component.counter_model_distinct`, `decimalCounter_model_distinct` | `Sen.distinct` |
| `perRequest_counter` | `Component.perRequest_counter_model` | `Sen.ofFun fun _ => f 0` |
| `perRequest_kv_get` | `Component.perRequest_kv_get_model` | `Sen.atomic` |
| `fileStore_refines`, `fileStore_linearizable` | `OwnedFs.fileStore_model_refines`, `fileStore_model_sat_origin` | refinement of `kv.machine.server`, `Http.originSen` |
| `static_refines`, `static_answer` | `OwnedFs.static_model_refines`, `static_model_sat` | refinement, `Sen.ofFun (staticAnswer loc fs₀)` |
| `static_safe`, `static_untouched`, `store_safe` | `SharedFs.static_model_safe`, `static_model_untouched`, `store_model_safe` | `Sen.atomic` |
| `store_refines`, `store_linearizable` | `SharedFs.store_model_refines`, `store_model_sat_origin` | refinement, `Http.originSen` |
| `store_refines_on`, `store_linearizable_on` | `SharedFs.store_model_refines_on`, `store_model_sat_lin_on` | refinement of `(kvOn K).machine.server`, `Sen.lin` |
| `wasiStore_refines`, `wasiStore_linearizable`, `wasiStoreSmall_refines` | `WasiFs.wasiStore_model_refines`, `wasiStore_model_sat_lin`, `wasiStoreSmall_model_refines` | refinement, `Sen.lin` |

The results about states rather than traces (`fileStore_frame`, `wasiStore_frame`,
`Abstraction.reach_inv`) and the run-level checks of `WasiFs` have no trace reading and are not
restated.

### (a) State inside the component (`Silmaril.Servers.State.Component`)

The state lives in the instance's memory and globals, and nobody else changes it
(`Server.closed`).

| Server | Claim | Lean | Status |
| --- | --- | --- | --- |
| Counter: the `n`-th run answers `f n` (`counter`; `httpCounter render`: `200` with `render n`) | Linearizable with respect to its handler; for injective `f`, distinct requests get distinct answers however they overlap | `counter_linearizable`, `counter_distinct`, `httpCounter_distinct` | proved |
| The HTTP counter that answers in decimal (`httpCounter decimal`) | `decimal` is injective (its characters are `Nat.toDigits 10 n`), so distinct requests get distinct answers, with no hypothesis left | `decimal_injective`, `decimalCounter_distinct` | proved |
| Key-value store: `Net.Http.storeStep` (`GET`, `HEAD`, `PUT`, `DELETE`, `OPTIONS` per RFC 9110 §9.3) | Linearizable with respect to `storeStep` | `kv_linearizable` | proved |
| The same components with a fresh instance per request | The counter always answers `f 0`; the store answers every `GET` from its initial contents, so component state does not persist | `perRequest_counter`, `perRequest_kv_get` | proved |


### (b) WASI over a file system that the server alone edits (`Silmaril.Servers.State.OwnedFs`)

The state is the contents of the files under the preopened directories, in the CLI file
model (`Silmaril.Cli.Fs`: rooted paths to contents, as a WASI preopen gives them). The files
are host state, so they survive a fresh instance per request.

| Server | Claim | Lean | Status |
| --- | --- | --- | --- |
| Static file server (`GET`/`HEAD` the file the target names or `404`, else `405` with `Allow: GET, HEAD`) | Refines the stateless server of the initial files; each request `r` is answered `staticAnswer loc fs₀ r` | `static_refines`, `static_answer` | proved |
| Document root: the path before `?`, without empty and `.` components, under a preopen; `..` names nothing | Names only files under its preopen, never with `..` | `docRoot_safe`; three `#guard` examples | proved, checked |
| File-backed key-value store (`fileStoreStep`: `storeStep` written against the file `enc t` of each key) | For an injective layout, a step through `view enc` is a `storeStep`; the store **refines the component-state store** of state model (a) and is linearizable; the frame invariant `Frame` holds (only key files are written) | `fileStoreStep_view`, `fileStore_refines`, `fileStore_linearizable`, `fileStore_frame` | proved |

### (c) WASI over a file system that others may change (`Silmaril.Servers.State.SharedFs`)

The same servers, with an environment `E : Fs → Fs → Prop` that may change files between
handler runs. Runs stay atomic with respect to the environment, as when files are read and
written whole and replaced atomically. An environment that interleaves inside a handler run
is not modelled.

| Claim | Lean | Status |
| --- | --- | --- |
| Safety, for any environment that keeps an invariant `I` of the files: each response of the static server is its answer with some files satisfying `I`; the histories are linearizable with respect to that loose specification | `static_safe`, `static_linearizable` | proved |
| Safety of the store for any environment: each response is a `storeStep` answer from some store | `store_safe` | proved |
| Functional correctness for untouched files: a request whose file the environment never touches is answered as with the initial files | `static_untouched` | proved |
| An environment that never touches key files (it may change any other file in the preopen): the store refines the component-state store and is linearizable | `store_refines`, `store_linearizable` | proved |
| A store where the environment may change the files of the keys outside `K` (and any other file): linearizable with respect to `kvOn K`, the key-value store on the keys of `K` (requests on keys of `K` are atomic `storeStep`s of one store; requests on other keys get some `storeStep` answer and leave `K` alone), and it refines that server; on all keys `kvOn` is `kv` | `store_linearizable_on`, `store_refines_on`, `kvOn_true` | proved |

### (b) as a WASI component (`Silmaril.Servers.WasiFs`)

State model (b) run as a component. `storeBody` is a component of the `wasi:http` proxy world
(`Silmaril.Servers.WasiHttp`) that also imports `wasi:filesystem` 0.2: `get-directories`,
`open-at`, `read`, `write`, `unlink-file-at`. It keeps the representation of each target in the
file `keyName` of its path-with-query (`k` and the octets in hexadecimal, `n` for none) under
the preopen. `GET`/`HEAD` open and `read` the file whole (`404` on `error(no-entry)`). `PUT`
reads the request body as `echo` does, checks whether the file exists, opens it with `create`
and `truncate`, and `write`s the body (`204`/`201`). `DELETE` uses `unlink-file-at`
(`204`/`404`). `OPTIONS` gives `204`, `POST`/`CONNECT`/`TRACE`/`PATCH` give `405`, other methods
`501`. A body of `2^64 - 1` octets or more is answered `413`, since a `read` length is a `u64`.

The host `storeHost root q fs` answers the `wasi:http` imports as the reference host for `q`.
The read-only filesystem calls go to **the existing `wasi:filesystem` host**
`Silmaril.Wasi.Versions.FsMore.fsImplV v2` over `treeOf [root] fs'`. `treeOf` reads the CLI
files `Silmaril.Cli.Fs` as a `wasi:filesystem` tree: the preopen is a directory, and each file
`⟨root, rel⟩` is a file node at `root :: rel`. Here `fs'` is the files at that point of the
call. The mutating calls change the files (`mutAns`, `mutUpd`). `replay` is the files after a
call. The component read as a server, `wasiStore root fs₀`, runs one complete call of `handle`
per request, atomically (`storeHandler`). The files are host state, so a fresh instance per
request keeps them.

| Claim | Lean | Status |
| --- | --- | --- |
| Every request, for files shorter than `2^64 - 1` octets: the run of `handle` makes the response of `specStep` and leaves its files (`fileStoreStep (keyFile root)` without header fields; `413` for a body too long to read back) | `run_spec` | proved |
| The component's server refines `specStore` and is linearizable with respect to `specStep`, however the host orders overlapping requests; only key files change | `wasiStore_refines`, `wasiStore_linearizable`, `wasiStore_frame` | proved |
| On requests shorter than `2^64 - 1` octets it **refines the file store `fileStore (keyFile root)` of state model (b)**, read without header fields (`fileStoreNF`) | `wasiStoreSmall_refines` | proved |
| Every read-only filesystem answer of the host passes the 0.2 theory `FsMore.fsThV v2` over the tree of the files at that point | `storeHost_fsOk` | proved |
| A `GET` of a file and of a missing file, a `PUT` that creates a file (and the file after it), a `DELETE` | `get_ref`, `get_missing_ref`, `put_ref`, `put_files_ref`, `delete_ref` (by `decide`) | checked |

The component sends no header fields, so the comparison is with `fileStore` through `noFields`
(`Atomic.mapResp`). It differs from `fileStore` only in the `Allow` field of the `OPTIONS` and
`405` answers. `tests/servers/wasi-http/store.wat` is the same program in WAT (it makes the same
import calls in the same order); it passes the conformance harness (section "Conformance
against a runtime"), except for contents longer than 4096 octets. Not proved: that the host's
mutating calls satisfy a `wasi:filesystem` theory (`FsMut` checks the tree's shape, not
contents), and that `storeBody` is the reading of `store.wasm` (as `Task.wasmRuns` for the
proxy examples).

### The store component as the key-value store (`Silmaril.Servers.WasiFs.Kv`, Proved)

`keyFile root` depends on the path-with-query only, so targets that differ only in their scheme
or authority share a file: the store is the key-value store of (a) on targets **in origin
form** (`originForm t`: the path-with-query alone; `normReq r`: the request with its target in
origin form; `viewN root fs`: the store the files hold on such targets).

| Claim | Lean | Status |
| --- | --- | --- |
| The file names are injective (`k` and two hexadecimal digits per octet, or `n`); two targets share a file exactly when they have the same path-with-query; on targets in origin form the layout is injective | `keyName_injective`, `keyFile_eq_iff`, `keyFile_injOn` | proved |
| A step of the file store, seen through `viewN`, is a `storeStep` of the request in origin form | `fileStoreStep_viewN` | proved |
| **History lemma for the `noFields` reduct**: the histories of `fileStoreNF` are those of the file store on short requests with responses read through `noFields` (an instance of `Server.hists_mapResp`) | `fileStoreNF_hists` | proved |
| On short requests the component refines the closed server of `kvNF` (`kv` on short requests, read through `normReq` and `noFields`) from `viewN root fs₀`, and is linearizable with respect to it | `wasiStoreSmall_refines_kv`, `wasiStoreSmall_linearizable_kv` | proved |
| **Every history of the component, its targets in origin form, is a history of the component-state store `kvServer (viewN root fs₀)` of state model (a) with responses read without header fields** | `wasiStoreSmall_kv` | proved |

### Reducts (`Silmaril.Servers.State.Reduct`, Proved)

`Server.comap f g M` reads a server through a map of requests `f` and a map of responses `g`
(`Atomic.comap`); `Server.mapResp g` maps only the responses. `Server.hists_comap`: every
history of the reduct, its requests mapped by `f`, is a history of `M` with its responses mapped
by `g` (a forward simulation of hosts with the same states and runs). `Server.hists_mapResp`:
the histories of `M.mapResp g` are exactly those of `M` with responses mapped by `g`, so
refinement is preserved (`Server.Refines.mapResp`).

### (c) as a WASI component (`Silmaril.Servers.WasiFs.Shared`, Proved)

`wasiShared root fs₀ E` is the store component, on short requests, over files that an
environment `E` changes between handler runs (as the harness does). For an `E` that keeps the
files short:

| Claim | Lean | Status |
| --- | --- | --- |
| Whatever the other writers do, each response is `specStep`'s answer to its request from some files; the histories are linearizable with respect to that safety specification | `wasiShared_safe`, `wasiShared_linearizable_safe` | proved |
| When the other writers never touch the files of the keys of `K` (`keyOn root K`; any other file, including other keys' files, may change), the component is linearizable with respect to `kvOnNF K`, the store on the keys of `K` (`SharedFs.kvOn`), read on targets in origin form and without header fields, and refines its closed server; on all keys `kvOnNF` is `kvNF` | `wasiShared_linearizable_on`, `wasiShared_refines_on`, `kvOnNF_true` | proved |

### The static file server as a component (`Silmaril.Servers.WasiFs.Static`)

`staticBody` is the static file server written over the store's world and host, the program of
`tests/servers/wasi-http/static.wat`: `method()`; for `GET`/`HEAD`, `path-with-query()`, the
name `staticName` (the components of `docRoot`, joined by `/`), `get-directories`, `open-at` and
one `read`: `200` with the contents (none for `HEAD`), `404` for no name or any error; other
methods `405` with `Allow: GET, HEAD` (observed: the `wasi:http` reading keeps header fields).

| Claim | Lean | Status |
| --- | --- | --- |
| The run of `handle` answers `staticAnswer (docRoot root) fs q` and leaves the files, for short files with no file at the preopen itself | `Task.staticRuns root` | open |
| Given that task, the component refines the static file server `staticServer (docRoot root) fs₀` of (b); over files that others change keeping an invariant `I`, each response is the answer of some files satisfying `I`, and the histories are linearizable with respect to `staticSafe` of (c) | `wasiStatic_refines_of`, `wasiStaticShared_safe_of`, `wasiStaticShared_linearizable_of` | proved (conditional) |
| A nested file through `.` and empty components with a query, `..`, the preopen, a directory, a missing file, `HEAD`, a `DELETE` answered `405` with its `Allow` field; on six requests the run answers `staticAnswer` and leaves the files | `#guard`s in `Static/Thms.lean` | checked |

### State histories read per connection (`Silmaril.Servers.State.Conn`, Proved)

Read through `toTrace`, every request of a state history is alone on its connection, so the
core's per-connection readings (`Silmaril.Servers.Conn`) say:

| Claim | Lean | Status |
| --- | --- | --- |
| Connection `i` of `toTrace H` is the trace of request `i`'s events; a per-connection sentence holds when it holds for every request | `onConn_toTrace`, `perConn_toTrace` | proved |
| **Sequential consistency of the trace gives serializability of the history**: `Sen.sc` may reorder connections freely, and each request is its own connection | `sc_serializable` | proved |
| Linearizability gives sequential consistency (for a well-formed trace) | `linearizable_sc` | proved |
| The converse of `sc_serializable` | `Task.serializable_sc` | open |
| **A fresh instance per request is an instance per connection** of the component-state server, and on traces with one request per connection the two models are equal | `perRequest_perConn`, `perConn_perRequest`, `perRequest_model_iff` | proved |

### State models as signatures and morphisms

The three models are servers over the same request and response types that differ in their
state (`Server.σ`) and their environment (`Server.env`). An `Abstraction` is a morphism from a
server to an atomic specification: it maps states and keeps every handler run. Its two
consequences, linearizability and refinement, are how the models are compared:

* file-backed store (b) → component-state store (a): `view enc` (`fileStore_refines`);
* store over shared files whose keys are untouched (c) → component-state store (a): `view enc`
  (`store_refines`);
* static server over owned files (b) → stateless server: the constant map, invariant `fs = fs₀`
  (`static_refines`);
* static server over shared files (c) → its safety specification: the constant map, the
  environment's invariant (`static_linearizable`);
* store over shared files whose keys outside `K` others change (c) → the store on `K`:
  `restrictKeys K ∘ view enc` (`store_refines_on`);
* fresh instance per request → stateless server `Atomic.fresh` (`perRequest_answer`);
* the `wasi:http` store component over `wasi:filesystem` → the file store (b) without header
  fields: the identity on files, invariant "files shorter than `2^64 - 1` octets, non-key files
  as initially" (`wasiStoreSmall_refines`, above);
* that file store without header fields → the component-state store (a) on targets in origin
  form: `viewN root` (`wasiStoreSmall_refines_kv`); with the reduct lemma, its histories are
  `kvServer`'s (`wasiStoreSmall_kv`);
* the store component over shared files whose keys of `K` are untouched (c) → the store on `K`:
  `restrictKeys K ∘ viewN root` (`wasiShared_refines_on`);
* the static component → the static server (b): the identity on files, invariant `fs = fs₀`
  (`wasiStatic_refines_of`, given `Task.staticRuns`).

In each case a client cannot tell the concrete server from the abstract one. For example, a
key-value store kept in a file and one kept in a component's memory have the same histories.

### Open

* Asynchronous handlers (`wasi:http` 0.3, where handler runs of one instance can interleave at
  `await` points): runs are no longer atomic, and linearizability needs linearization points
  inside runs.
* Connections and pipelining: read in the core (`State.Traces`), every request of these
  histories is alone on its connection, and the per-connection readings are connected
  (`State.Conn`); the converse `Task.serializable_sc` is open. The per-connection,
  sequential-consistency and connection-event readings exist in the core
  (`Silmaril.Servers.Conn`, `Silmaril.Servers.Sessions`), but the state models' hosts do not
  place several requests on one connection (pipelining is not modelled in the state
  vocabulary).
* Done for the file-backed store (`Silmaril.Servers.WasiFs`): connecting handler runs to
  component executions and the file model to the `wasi:filesystem` theories; the shared-file
  model (c) as a component (`WasiFs.Shared`).
* `Task.staticRuns`: the run proof of the static component (the store's `run_spec` analogue);
  it needs the `FsMore` reading of `open-at` on a path of several components.
* That `store.wasm` and `static.wasm` run `storeBody` and `staticBody` (as `Task.wasmRuns`).
* Contents longer than 4096 octets (one `blocking-write-and-flush`, see "Conformance against a
  runtime"), and reads shorter than the file (a host may return fewer octets than asked; the
  components read once).
* A theory of the mutating filesystem calls with contents.

## Survey: frameworks, formalizations and the other instances

### Frameworks for Wasm HTTP applications

| Framework | Interface the application implements | Instances per request | Notes |
| --- | --- | --- | --- |
| `wasi:http` 0.2, world `proxy` [1] | export `incoming-handler.handle(request: incoming-request, response-out: response-outparam)`; bodies are `wasi:io` streams | "A host may arbitrarily reuse or not reuse component instance … a component must be able to handle 0..N calls to `handle`" (`specs/wasi/0.2.12/http/proxy.wit`) | The response is sent by `response-outparam.set` and "execution [may] continue after the response has been sent" (`handler.wit`). The response is issued before `handle` returns. |
| `wasi:http` 0.3, world `service` [1] | export `handler.handle: async func(request) -> result<response, error-code>`; bodies are component-model `stream<u8>` | as 0.2. In addition, "Hosts may concurrently invoke this `handler` interface multiple times, even when previous requests have yet to finish processing", unless the guest applies backpressure (`specs/wasi/0.3.2/http/worlds.wit`) | `middleware` world: a service that also imports `handler`, so components chain |
| `wasmtime serve` [2] | either world | at most `--max-instance-reuse-count` requests per instance: 1 by default for 0.2 components (a fresh instance per request), 128 for 0.3 ones, with at most `--max-instance-concurrent-reuse-count` (16 by default) at once for 0.3 [2] | No TLS option. The intended pinned conformance runtime. |
| Spin [3] | its HTTP trigger, whose entry point is the `wasi:http` incoming handler (Spin 2.0, 2023-11-03, "standardized on wasi-http"); also a WAGI executor | a new instance per request for 0.2 handlers; 0.3 handlers are reused, by default up to 128 requests per instance and 16 at once (`crates/trigger-http`) [3]. Persistent state goes through host key-value or SQL interfaces | Routes by path to components (manifest `spin.toml`) |
| wasmCloud [4] | the exported `wasi:http` handler | per host policy | In wasmCloud 2, "the host matches the request's hostname to a workload, takes an instance of its component, and calls the exported `wasi:http` handler" (`ARCHITECTURE.md`); in wasmCloud 1 an HTTP server *provider* (a host-side plugin) made that call |
| Fastly Compute [5] | Compute host calls (`witx`) and component SDKs | a new instance per request by default: "The default behavior for Viceroy (and Fastly Compute) is to launch a new WASM instance for each inbound HTTP request" (Viceroy 0.14.0, 2025-08-08). Reuse is opt-in *by the guest*: an instance that calls the `http_downstream` `next_request` host call is handed further requests (`reuse_or_spawn_guest`, at most `NEXT_REQ_PENDING_MAX = 5` waiting instances in Viceroy v0.22.0). "Sessions" were renamed "sandboxes" in 0.18.0 (2026-05-21) [5] | Viceroy is the local test runtime. Guest-driven reuse is a *pull* shape: the instance runs its own request loop, like the Linux shape below |
| NGINX Unit [6] | application type `wasm-wasi-component`: `wasi:http/proxy@0.2.0` (Unit 1.32.0, 27 Feb 2024, `CHANGES`) | per Unit's configuration | A web server hosting components; the repository was archived in October 2025, last release 1.35.0 (3 Sep 2025) |
| WAGI [7] (repository archived; last release v0.8.1, 2022-06-15) | a WASI *command* (a core module, entry point `_start` by default): CGI 1.1 meta-variables in the environment, the path and then each `&`-separated query item as arguments (`build_argv`), the whole body buffered on stdin, the CGI response on stdout | one run per request: `handle_request` builds a fresh WASI context, store and instance for every request; modules are compiled once at start-up | "WAGIs are not handled as 'processes', they are executed internally with multi-threading"; "some CGI env vars are rewritten to remove local FS information"; extra `X_*` variables (`X_MATCHED_ROUTE`, `X_FULL_URL`, ...); a `location` header must be a full URL; no NPH mode (`docs/architecture.md`) [7] |
| CGI/1.1 (RFC 3875) [8] | a program: meta-variables (§4.1), body on stdin (§4.2), response on stdout (§6) | one run per request | The ancestor of WAGI. The same shape as `Silmaril.Cli` behaviours. |
| Others | Envoy's proxy-wasm ABI [9]: HTTP filters inside a proxy, called per stream (`proxy_on_request_headers`, `proxy_on_response_headers`, ..., ABI v0.2.1); WasmEdge's socket extension (`wasmedge_wasi_socket::TcpListener`, `bind` then `accept` in a loop) and Wasmer's WASIX ("sockets (socket, bind, connect)", threads, `fork`) [10], POSIX-style sockets inside Wasm, so the *Linux-process* shape below; `wasi:sockets` (also vendored here); containerd's runwasi [11]: its Wasmtime shim (`containerd-shim-wasmtime` v0.6.1) serves a `wasi:http/proxy` component behind the container interface, "heavily inspired by wasmtime serve", with a fresh store and instance per request (`http_proxy.rs`); Cloudflare Workers [33]: Wasm instantiated from JavaScript (`WebAssembly.instantiate()`) inside the Workers runtime, whose `fetch` handler is JavaScript; "WASI support is experimental ... with only some syscalls implemented" | varies; fresh per request for runwasi's `wasi:http` path | Most fit one of the three shapes below |

**Checked against pinned releases** (on 2026-11-13, from the release sources): Wasmtime v50.0.1
(`src/commands/serve.rs`: `DEFAULT_WASIP2_MAX_INSTANCE_REUSE_COUNT = 1`,
`DEFAULT_WASIP3_MAX_INSTANCE_REUSE_COUNT = 128`,
`DEFAULT_WASIP3_MAX_INSTANCE_CONCURRENT_REUSE_COUNT = 16`); Spin v4.3.0
(`crates/trigger-http/src/{lib,server}.rs`: the same defaults, applied to 0.3 handlers only)
and the Spin v2.0.0 release notes; wasmCloud v2.12.1 (`ARCHITECTURE.md`); Viceroy v0.22.0
(`CHANGELOG.md`); NGINX Unit `CHANGES` at its archived head; the vendored `wasi:http` WIT
(`specs/wasi/0.2.12/http/proxy.wit`, `specs/wasi/0.3.2/http/worlds.wit`) for the two quotes
in the first rows. Earlier text said that Spin accepted plain `wasi:http` handlers only from
2.6, that `wasmtime serve` has "no limits", and that wasmCloud 2 uses an HTTP provider; these
were corrected. Rechecked later the same day: the Fastly row against Viceroy v0.22.0
(`CHANGELOG.md`, entry 0.14.0, and `src/execute.rs`, tag commit `cbc9c978`), which corrected
"reusable sessions" to guest-driven reuse through `next_request`; the WAGI row against WAGI
v0.8.1 (`docs/architecture.md`, `src/handlers.rs`: per-request store and instance,
`build_argv`); and the Others row against proxy-wasm `spec` (`abi-versions/v0.2.1`, commit
`bf6919b`), runwasi `containerd-shim-wasmtime/v0.6.1`
(`crates/containerd-shim-wasmtime/src/{instance,http_proxy}.rs`), and the WasmEdge, WASIX and
Cloudflare Workers documentation pages (not versioned; read on 2026-11-13). Earlier text did
not say that Fastly reuse is requested by the guest, nor that runwasi serves `wasi:http`
components itself.

The three shapes are as follows. In the first, **a handler per request** is called by the host
with a request and gives back a response: `wasi:http`, Spin, wasmCloud, Fastly, Unit, proxy-wasm.
In the second, **a program per request** reads the request from its environment and stdin and
writes the response on stdout: CGI, WAGI. In the third, **a long-running process with
sockets** does its own HTTP framing: Linux servers, containers, WasmEdge or WASIX, and
`wasi:sockets`. For the first two shapes, the host decides how requests map to instances. For
the third, the server's own code decides.

### Formalizations of HTTP and of servers

- **Here.** RFC 9110 semantics, RFC 9112 HTTP/1.1 framing and chunked coding, RFC 9113 HTTP/2
  with RFC 7541 HPACK ([HTTP](http.md)). Also origin servers as relations
  (`Silmaril.Net.Http.Origin`: safety, idempotence, `HEAD` as `GET`, a resource store), TCP's
  byte-stream service and datagram channels (`Silmaril.Net.{Tcp,Channel}`), and the
  `wasi:http` theories (`Silmaril.Wasi.Versions.{Http3,HttpBody,HttpOver}`).
- **Verified networked servers with interaction trees.** Koh et al. [12] verify a C "swap"
  server with VST and CompCert against an interaction-tree implementation model. That model is
  in turn proved against a linear "one client at a time" specification, and the server runs on
  CertiKOS. A network refinement relates the linear specification to what concurrent clients
  observe, which is the atomic-to-concurrent lift of the core here. Li, Pierce and Zdancewic
  [13] derive testers from nondeterministic interaction-tree models of a fragment of HTTP/1.1
  and find RFC violations in Apache and Nginx. Li's dissertation [14] develops this testing by
  dualizing the specification. Interaction trees: Xia et al. [15].
- **Verified distributed systems.** IronFleet [16] (refinement from implementation to a
  state-machine specification, including the key-value server IronKV) and Verdi [17]
  (verified system transformers over network semantics). The style of refinement used there is
  trace inclusion modulo refinement mappings (Abadi and Lamport [18]).
- **Correctness conditions.** Linearizability (Herlihy and Wing [19]) and sequential
  consistency (Lamport [20]) are the readings of the core's `Sen.lin` and `Sen.sc`.
- **Sockets and file systems.** Netsem [21] gives a rigorous, test-validated specification of
  TCP, UDP and the sockets API. It is the natural reference for the socket events of the
  Linux-process instance. SibylFS [22] specifies POSIX file systems as an executable oracle,
  the reference for the general-file-system state model.
- **Verified HTTPS components and parsers.** Project Everest [23] (a verified HTTPS stack:
  miTLS, HACL\*, EverCrypt) and EverParse [24] (verified parsers for message formats).
- **The web as a whole.** Formal models of web security reason about browsers, servers and
  attackers: Akhawe et al. [25], and Fett, Küsters and Schmitz [26] (a Dolev-Yao model of the
  web infrastructure). Featherweight Firefox [27] and the verified browser kernel Quark [28]
  are on the client side. HTTP request smuggling, a disagreement about message boundaries
  between two HTTP/1.1 parsers, is found by differential fuzzing in T-Reqs [29]. The planned
  smuggling-freedom theorem of [HTTP](http.md) is the formal counterpart.
- **Wasm itself.** Mechanized Wasm semantics: Watt [30], WasmCert [31], Iris-Wasm [32]. The
  component model and WASI here are in [Wasm components](wasm-components.md) and
  [More Wasm](wasm-wasi.md).

No published work found here verifies a `wasi:http` component end to end, or relates two
deployments of one HTTP server (component, process, container) by refinement. That comparison
is the target of this page.

### Design: the instances and refinement between them

**Platforms** (`Silmaril.Servers.Platform`, defined). A platform `P : Platform T` gives three
things: its implementations (`Impl`), what is observed of their runs (`Obs`, `runs`), and how
an observation is read as HTTP traces of type `T` (`reads`, a relation). `P.view i` is the set
of traces of `i`. For sequential logs (`T = Log`, a core `History` of `Http.sig`) it is the core
model `Platform.model P i` (the logs used one request at a time on fresh identities,
`Exchange.seqUse`), and `refines_iff_model` (proved) says that `Refines` is exactly refinement
of these models; `Exchange.seqUse_refines_iff` is the underlying fact. For per-connection
traces, `Platform.connModel P i` is the set of well-formed core traces that answer in request
order on each connection and whose events are the exchanges, the `k`-th on connection `c`
with identity `⟨c, k⟩` (`Explains`); `connModel_refines` (proved) carries refinement over.
`Refines P Q i j` is trace inclusion across platforms. `Refines.sat` (proved)
transports every trace specification from `j` to `i`. `Refines.map` (proved) keeps refinement
under a change of observation.

| Instance | Lean | Implementation | Observation read as HTTP | Status |
| --- | --- | --- | --- | --- |
| Handler with instance state, one reused instance | `Platform.seq σ` | an origin `Origin σ` with its initial state | its runs (`Reuse.Seq`), one exchange at a time | defined |
| … a fresh instance per request (CGI, Spin, Fastly, `wasmtime serve` 0.2) | `Platform.fresh σ` | same | each exchange a run from the initial state (`Reuse.Fresh`) | defined |
| … under a host that pools instances (`wasi:http`'s contract) | `Platform.host σ` | same | runs of a pool of instances, any request to any idle or new instance (`Reuse.HostRuns`) | defined |
| CGI or WAGI script | `Platform.cgi g` | a `Silmaril.Cli.Spec` and the initial files | one run per request on the files the previous run left (`Cgi.origin`) | defined |
| Linux process over sockets | `Platform.linux fr` | a socket semantics `Input → List SockEv → Prop` and the launch invocation | the connections accepted and, per connection, requests framed from the octets received paired in order with responses framed from the octets sent (`connLog`, RFC 9112 §9.3) | defined; HTTP/1.1 framing `Wire1.framing` with round trips proved (interim responses and close-delimited bodies in `WireExch`); socket semantics of a process-model program `Sockets.sockSem`, over every network `Sockets.sockSemNet`; a hello loop `LinuxHello.L` proved to serve hello |
| `wasi:http` component, fresh instance per request | `Compare.wasi` | a component body over the proxy imports | each exchange a one-exchange trace of the component (`wasiServer`) | defined; hello compared with Linux (below) |
| Container | `Platform.container fr` | a socket semantics and a `Container` (image of layers with whiteouts, entry point, arguments, environment, roots) | the process platform at `Container.launch`, whose files are the image's (`container_view`, by definition) | defined |

The theorems proved in `Servers.Reuse`, `Servers.Cgi` and `Servers.Platform` (each `Thms`
header lists them):

- **Correct for every reachable state means correct for every host**
  (`Reuse.hostRuns_of_inv`, `Platform.host_sat_of_inv`). Suppose an invariant of the instance
  state holds initially, is kept by every step, and makes every step answer within `H`. Then
  every exchange of every pooling policy is in `H`. `seq_hostRuns` and `fresh_hostRuns`
  (`seq_refines_host`, `fresh_refines_host` as platform refinements) show that reuse of one
  instance and a fresh instance per request are both pooling policies.
- **The reuse policy is observable for state kept in the instance**
  (`Reuse.counter_policy_matters`). A counter answers `0, 1` on one reused instance and
  `0, 0` with fresh ones. So a `wasi:http` component may not promise anything that depends on
  instance state; such state must live behind an import (a key-value store, the files).
- **CGI**: refining the program refines the server (`Cgi.origin_mono`: CLI refinement lifts).
  A program that leaves the files respects safe methods (`respectsSafe_of_keepsFiles`). The
  status rules of RFC 3875 §6.2 and §6.3.3 are checked on examples.
- **A cross-platform equivalence** (`Platform.cgi_hello_equiv_host`). Take the hello CGI
  script on any files, and a stateless component answering the constant web under any pooling
  host. Each refines the other. Both have exactly the logs in which every exchange answers
  `helloResponse`, with `HEAD` answered without content (`cgi_hello_iff`, `web_host_iff`).

**HTTP/1.1 on the wire** (`Silmaril.Servers.Wire1`, proved). `toRequest` and `toResponse` read
an `Http1` head and framed body as RFC 9110 messages (method by `Method.ofToken`, the target
as path-with-query, content the body's payload, the framing fields `Content-Length` and
`Transfer-Encoding` dropped). `framing` reads a connection's octets as consecutive requests and
one response per request, each read with its request's method. Round trips:
`requests_encode` (requests with valid heads and fitting bodies, sent back to back, are read
back exactly), `responses_encode`, and `connLog_encode` (the exchanges of such a connection
are the pairs). Not covered here: interim responses (read as the response) and close-delimited
response bodies, which `WireExch` below reads; `CONNECT` tunnels; absolute-form targets.

**Socket events of a process** (`Silmaril.Servers.Sockets`, proved). The Linux process model
(`Silmaril.Process.LPS`) records runs as raw system-call histories whose byte events carry a
trace channel, `connChannel ix = ix + 3` for the `ix`-th accepted connection. `ofRecords`
reads bytes read and written on connection channels as `recv`/`send` and successful
`accept`/`accept4` calls as `accept`s in order; `sockSem` is the socket semantics of a
launched program (its finite runs, `HStar`). `connLog_byteTrace`: the exchanges of every
connection, under any framing, are framed from the bytes on its channel.

- **The `k`-th accept is channel `k + 3`.** `accept4Spec_ok`: a successful LPS `accept`
  advances the connection counter by one, takes the head of the network queue, emits nothing
  and installs a connected socket on channel `connIx + 3`. `connIx_hstar`: along every run of
  a table that counts connections (`CountsConns`: only successful accepts move the counter),
  the counter is the number of accepts so far, so `kth_accept_channel`: the `k`-th accept of a
  run started at counter `0` is the connection of channel `k + 3`. That LPS's whole table
  counts connections is the frozen `Task.specTableCountsConns` (a pass over its arms).
- **`close` and `recvfrom`.** `ofRecordsC` also reads `close`: the descriptors that accepts
  returned map to their connections, and a successful `close` of one is a `close` event; the
  octets, hence the exchanges, are unchanged (`connLog_ofRecordsC`). `closeSpec_ok`,
  `recvfromSpec_ok`, `recvmsgSpec_ok`: a `close` emits no byte event, and a `recvfrom` or
  `recvmsg` that returns emits nothing and changes nothing (LPS declines both on a socket), so
  reading their records as nothing is exact; bytes are read from the events of whatever call
  delivers them.
- **The network is the environment's choice.** `sockSem` fixes the connection queue with the
  invocation, so it cannot satisfy a hypothesis such as `ServesHello` that asks for every
  sequence of requests. `sockSemNet` ranges over every queue (LPS's `ProcInput.net`) and reads
  `close`; over the constant queue it has the exchanges of `sockSem`
  (`sockSemNet_const_connLog`).

**A Linux hello server loop** (`Silmaril.Servers.LinuxHello`, proved, one direction
conditional). A loop that accepts on a listening socket handed over at start (descriptor 3,
as with socket activation), reads until the client's `FIN`, frames what it read as HTTP/1.1
requests, answers each leading request whose method is neither `HEAD` nor `CONNECT` with
`helloWire`, sends with `sendto(…, MSG_NOSIGNAL)` until done and closes. The loop is a
`UserIsa` whose instruction steps are its transitions in Lean and whose memory is a 4 KiB
input buffer and a 4 KiB window on the pending output: it is a program of the process model,
not a compiled binary. The system calls are LPS's own: `serverTable` holds the four arms of
LPS's generic table, and since the loop traps only with their numbers its runs are the same
under the whole table (`L_eq_full`).

- **`serves`**: `ServesHello L inp` for every invocation, through `sockSemNet` and LPS's
  `accept4Spec`, `readSpec` (chunks of at most 4096 octets, then `FIN`) and `sendtoSpec`
  (chunks of at most 4096). With `Compare.wasi_refines_linux`: **`wasi_refines_loop`**, the
  hello component refines this process on logs on the wire. This discharges, for this loop,
  the hypothesis the previous comparison left open.
- **`hello_prefix_err`**: no strict prefix of `helloWire`'s octets frames as a response, after
  any octets (a head read inside such a prefix is `helloWire`'s whole head, by soundness and
  completeness of the head grammar, and the 5 body octets are missing). Hence
  **`onlyHello_of_sentPrefix`**: any socket semantics whose connections each send a prefix of
  the hello responses their received octets call for (`SentPrefix`) only says hello, short
  sends included.
- Open: `Task.loopSentPrefix`, that the loop satisfies `SentPrefix`. It is an invariant over
  every run LPS allows (failed accepts, short reads and sends, resets, `EPIPE`), the descriptor
  table and the channel of each connection. Under it, `only_of_task` and `hello_equiv_loop`:
  the loop and the hello component are equivalent on logs on the wire.

**Core traces from socket timing** (`Silmaril.Servers.Timed`, proved for monotone framings).
`connModel` fixes only the order on each connection. `timed fr tr` reads the order the socket
events give: a request is received at the event that completes its octets, a response sent
at the event that completes its exchange (or its request, if the server answered early), each
with identity ⟨connection, index⟩. For a framing that never takes back what it has read
(`Mono`), the receptions of each connection are its requests in order (`recvsOn_timed`) and its
sendings are its exchanges' responses in order (`sendsOn_timed`): the timed trace holds
exactly the per-connection logs, plus the cross-connection order. `timedModel` is the core
model of a socket semantics read this way, monotone in the socket semantics
(`timedModel_mono`). That `Wire1.framing` is monotone is the frozen `Task.wire1Mono`.

**Interim responses and close-delimited bodies** (`Silmaril.Servers.WireExch`, proved).
`parseExch` reads, after a request, any `1xx` responses other than `101` as interim and then
the final response (RFC 9110 §15.2); a final response delimited by closing the connection
(RFC 9112 §6.3 rule 8) counts only once the server has closed it. `exchanges` gives
`Http.exchSig` values (interim responses, final response), `framingC` the final responses as a
`Platform.Framing`, and `connLogX` the exchanges of a connection of a socket trace, closed when
the trace has the server's `close`. Round trips: `exchanges_encode` (interim responses and
fitting finals, back to back), `exchanges_encode_close` (a last close-delimited response is
read once the connection is closed) and `exchanges_encode_open` (and not before).

**Hello, Wasm against Linux, end to end** (`Silmaril.Servers.Compare`, proved, conditional on the
Linux side). `wasi_hello_iff`: the logs of the hello component are those answering every
request `200 hello`. `wasi_refines_linux`: on logs whose requests are on the wire (`wireLog`:
readings of wire requests that read back, methods other than `HEAD` and `CONNECT`), the hello
component refines every Linux process that, for any such requests received back to back on
one connection, sends `helloWire` (`200 OK`, `content-type: text/plain`, `content-length: 5`, `hello`) for each in some run
(`ServesHello`). The proof goes through the component's `wasi:http` calls, the HTTP/1.1 round
trips and the merge of connection logs. `linux_refines_wasi`: a process whose every exchange
answers `200 hello` (`OnlyHello`) refines the component on all logs. `hello_equiv` combines
them, `wasi_refines_linux_model` states the first in the server institution, and `helloSock`, a
reference hello server at the socket level, satisfies both hypotheses
(`hello_equiv_helloSock`). Two findings: HTTP/1.1 cannot carry every request a component may be
given, and the hello component answers `HEAD` with content, which an HTTP/1.1 client reads as
no body (RFC 9112 §6.3), so the comparison is restricted to `wireLog`. The loop of
`Silmaril.Servers.LinuxHello` satisfies `ServesHello` under LPS's semantics (above); no
compiled binary is proved to.

How refinement between the other instances is stated:

- **A Wasm server refines a Linux server's specification.** Both are read into one trace type.
  A Linux server is observed per connection (`List ConnId × ConnLog`), and `toLogs` reads that
  as the sequential logs that merge its connections (`Merge`, an interleaving that keeps each
  connection's order). Then "component `c` under every `wasi:http` host refines Linux server
  `p`" is `Refines (Platform.host σ) (Platform.map toLogs (Platform.linux fr)) c p`. A
  specification of the Linux server stated as a property of merged logs then holds of the
  component. This is sequential consistency over connections, the core's `Sen.sc`. The
  converse direction, a Linux server refining a component's specification, is stated the same
  way.
- **A container refines the process it packages** by definition (`container_view`). The
  content of a container claim is the image: a theorem about the process on inputs whose files
  satisfy an invariant applies to every image whose files (`Image.fs`) satisfy it.
- **CGI against a handler.** `Platform.cgi g` is `Platform.seq` of the script's origin
  (`cgi_view`, by definition). A CGI script and a component therefore compare on `Log`
  directly, as in the hello equivalence.

Planned, in order of cost:

1. `Task.loopSentPrefix`: the run invariant of the hello loop (every LPS outcome of its four
   calls), which completes the equivalence of the loop and the hello component. Then the
   same for a compiled binary, through an ISA of the process model instead of the loop's own
   `UserIsa`. Netsem [21] is the reference for what the kernel may do.
2. `Task.wire1Mono` (HTTP/1.1 framing never takes back what it read), which makes the timed
   reading of HTTP/1.1 socket traces exact; and `Task.specTableCountsConns`.
3. Concurrent instance reuse (the 0.3 `service` world). An exchange is then no longer atomic
   at the instance. The linearizability reading of the core is the specification, with the
   component's `backpressure` as the opt-out.
4. Finer observations than whole exchanges: streaming bodies (the 0.2 `response-outparam`
   sends the response before `handle` returns), and connection-level errors and timeouts.
   Interim responses and close-delimited bodies are read (`WireExch`), but not yet from the
   component side.

### References for the survey

1. WebAssembly/wasi-http, the `wasi:http` proposal. https://github.com/WebAssembly/wasi-http.
   The vendored WIT is `specs/wasi/0.2.12/http` and `specs/wasi/0.3.2/http`.
2. Wasmtime CLI options, `wasmtime serve`. https://docs.wasmtime.dev/cli-options.html;
   source `src/commands/serve.rs` at release v50.0.1,
   https://github.com/bytecodealliance/wasmtime/blob/v50.0.1/src/commands/serve.rs
3. Spin documentation, https://spinframework.dev/v3/http-trigger; release v4.3.0,
   https://github.com/spinframework/spin/tree/v4.3.0/crates/trigger-http; v2.0.0 release
   notes, https://github.com/spinframework/spin/releases/tag/v2.0.0
4. wasmCloud documentation, https://wasmcloud.com/docs; `ARCHITECTURE.md` at v2.12.1,
   https://github.com/wasmCloud/wasmCloud/blob/v2.12.1/ARCHITECTURE.md
5. Fastly Compute, https://docs.fastly.com/products/compute; Viceroy release v0.22.0,
   https://github.com/fastly/Viceroy/tree/v0.22.0 (`CHANGELOG.md`, `src/execute.rs`)
6. NGINX Unit configuration, `wasm-wasi-component`, https://unit.nginx.org/configuration/;
   `CHANGES`, https://github.com/nginx/unit/blob/master/CHANGES
7. WAGI, the WebAssembly Gateway Interface, release v0.8.1.
   https://github.com/deislabs/wagi/tree/v0.8.1 (`docs/architecture.md`,
   `docs/writing_modules.md`, `src/handlers.rs`)
8. D. Robinson, K. Coar. *The Common Gateway Interface (CGI) Version 1.1*. RFC 3875, 2004.
9. proxy-wasm ABI specification, `abi-versions/v0.2.1`.
   https://github.com/proxy-wasm/spec/tree/bf6919b/abi-versions/v0.2.1
10. WasmEdge, "Socket networking: server",
    https://wasmedge.org/docs/develop/rust/socket_networking/server/; WASIX,
    https://wasix.org/docs
11. containerd runwasi, release `containerd-shim-wasmtime/v0.6.1`.
    https://github.com/containerd/runwasi/tree/containerd-shim-wasmtime/v0.6.1
12. N. Koh, Y. Li, Y. Li, L. Xia, L. Beringer, W. Honoré, W. Mansky, B. C. Pierce,
    S. Zdancewic. *From C to Interaction Trees: Specifying, Verifying, and Testing a Networked
    Server*. CPP 2019. https://arxiv.org/abs/1811.11911
13. Y. Li, B. C. Pierce, S. Zdancewic. *Model-Based Testing of Networked Applications*.
    ISSTA 2021. https://arxiv.org/abs/2102.00378
14. Y. Li. *Testing by Dualization*. PhD dissertation, University of Pennsylvania, 2022.
    https://arxiv.org/abs/2210.01047
15. L. Xia, Y. Zakowski, P. He, C. Hur, G. Malecha, B. C. Pierce, S. Zdancewic. *Interaction
    Trees: Representing Recursive and Impure Programs in Coq*. POPL 2020.
16. C. Hawblitzel, J. Howell, M. Kapritsos, J. R. Lorch, B. Parno, M. L. Roberts, S. Setty,
    B. Zill. *IronFleet: Proving Practical Distributed Systems Correct*. SOSP 2015.
17. J. R. Wilcox, D. Woos, P. Panchekha, Z. Tatlock, X. Wang, M. D. Ernst, T. Anderson.
    *Verdi: A Framework for Implementing and Formally Verifying Distributed Systems*. PLDI 2015.
18. M. Abadi, L. Lamport. *The Existence of Refinement Mappings*. TCS 82(2), 1991.
19. M. P. Herlihy, J. M. Wing. *Linearizability: A Correctness Condition for Concurrent
    Objects*. TOPLAS 12(3), 1990.
20. L. Lamport. *How to Make a Multiprocessor Computer That Correctly Executes Multiprocess
    Programs*. IEEE Trans. Computers C-28(9), 1979.
21. S. Bishop, M. Fairbairn, H. Mehnert, M. Norrish, T. Ridge, P. Sewell, M. Smith,
    K. Wansbrough. *Engineering with Logic: Rigorous Test-Oracle Specification and Validation
    for TCP/IP and the Sockets API*. JACM 66(1), 2019.
22. T. Ridge, D. Sheets, T. Tuerk, A. Giugliano, A. Madhavapeddy, P. Sewell. *SibylFS: Formal
    Specification and Oracle-Based Testing for POSIX and Real-World File Systems*. SOSP 2015.
23. K. Bhargavan et al. *Everest: Towards a Verified, Drop-in Replacement of HTTPS*.
    SNAPL 2017.
24. T. Ramananandro et al. *EverParse: Verified Secure Zero-Copy Parsers for Authenticated
    Message Formats*. USENIX Security 2019.
25. D. Akhawe, A. Barth, P. E. Lam, J. Mitchell, D. Song. *Towards a Formal Foundation of Web
    Security*. CSF 2010.
26. D. Fett, R. Küsters, G. Schmitz. *An Expressive Model for the Web Infrastructure:
    Definition and Application to the BrowserID SSO System*. IEEE S&P 2014.
27. A. Bohannon, B. C. Pierce. *Featherweight Firefox: Formalizing the Core of a Web
    Browser*. WebApps 2010.
28. D. Jang, Z. Tatlock, S. Lerner. *Establishing Browser Security Guarantees through Formal
    Shim Verification*. USENIX Security 2012.
29. B. Jabiyev, S. Sprecher, K. Onarlioglu, E. Kirda. *T-Reqs: HTTP Request Smuggling with
    Differential Fuzzing*. CCS 2021.
30. C. Watt. *Mechanising and Verifying the WebAssembly Specification*. CPP 2018.
31. C. Watt, X. Rao, J. Pichon-Pharabod, M. Bodin, P. Gardner. *Two Mechanisations of
    WebAssembly 1.0*. FM 2021.
32. X. Rao, A. L. Georges, M. Legoupil, C. Watt, J. Pichon-Pharabod, P. Gardner, L. Birkedal.
    *Iris-Wasm: Robust and Modular Verification of WebAssembly Programs*. PLDI 2023.
33. Cloudflare Workers, "WebAssembly (Wasm)",
    https://developers.cloudflare.com/workers/runtime-apis/webassembly/

## Building

```
lake build Silmaril.Servers.Core.Thms Silmaril.Servers.Http.Thms \
  Silmaril.Servers.Examples.Counter.Thms Silmaril.Servers.Exchange.Thms \
  Silmaril.Servers.Calls.Thms Silmaril.Servers.WasiHttp.Thms \
  Silmaril.Servers.WasiExamples.Thms Silmaril.Servers.State.Thms \
  Silmaril.Servers.State.Component.Thms Silmaril.Servers.State.OwnedFs.Thms \
  Silmaril.Servers.State.SharedFs.Thms Silmaril.Servers.Reuse.Thms \
  Silmaril.Servers.Cgi.Thms Silmaril.Servers.Platform.Thms \
  Silmaril.Servers.Conn.Thms Silmaril.Servers.WasiFs.Thms \
  Silmaril.Servers.Wire1.Thms Silmaril.Servers.Sockets.Thms Silmaril.Servers.Compare.Thms \
  Silmaril.Servers.State.Traces.Thms Silmaril.Servers.PerRequest.Thms Silmaril.Servers.Live.Thms \
  Silmaril.Servers.State.Sentences.Thms Silmaril.Servers.Sessions.Thms \
  Silmaril.Servers.WasiCore.Thms Silmaril.Servers.WasiBinaries.Thms \
  Silmaril.Servers.State.Reduct.Thms Silmaril.Servers.State.Conn.Thms \
  Silmaril.Servers.WasiFs.Kv.Thms Silmaril.Servers.WasiFs.Shared.Thms \
  Silmaril.Servers.WasiFs.Static.Thms \
  Silmaril.Servers.LinuxHello.Thms Silmaril.Servers.Timed.Thms Silmaril.Servers.WireExch.Thms
```

Every module builds in under 15 s; the slowest are the run proofs of `WasiFs`, the proof that the
`hello` module runs its body (`Silmaril.Proofs.Servers.WasiBinaries.Hello`, kernel evaluation)
and `Silmaril.Servers.WasiExamples.Thms`, whose checks over the reference host are evaluated by
`decide`. `Silmaril.Servers.WasiBinaries.Defs` reads `tests/servers/wasi-http/*.wat` when it is
elaborated; Lake does not track those files, so a change to them needs that module rebuilt. The
conformance harness runs with
`nix develop .#http-test -c tests/servers/wasi-http-conformance.sh`, and skips cleanly without
`wasmtime`, `curl`, or both the components and `wasm-tools`.

## References for the core

- J. A. Goguen and R. M. Burstall. Institutions: abstract model theory for specification and
  programming. *Journal of the ACM* 39(1), 1992.
- M. P. Herlihy and J. M. Wing. Linearizability: a correctness condition for concurrent
  objects. *ACM Transactions on Programming Languages and Systems* 12(3), 1990.
- L. Lamport. How to make a multiprocessor computer that correctly executes multiprocess
  programs. *IEEE Transactions on Computers* C-28(9), 1979.
- RFC 9110, HTTP Semantics; RFC 9112, HTTP/1.1 (§9.3.2, pipelining).
