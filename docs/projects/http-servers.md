# HTTP servers: one framework for Wasm components, processes and containers

This page describes a framework for stating and proving properties of HTTP servers, whatever
runs them: a Wasm component in the wasi:http proxy world, a Linux process on sockets, a
container, or a CGI program run once per request. The aim is to compare implementations by
refinement: for example, a Wasm server refines a Linux server's specification. The code is in
the `Servers` region (`Silmaril/Servers/…`, see [regions.toml](../../regions.toml)). It builds
on the HTTP semantics of `Silmaril.Net.Http` ([HTTP](http.md)) and follows the style of the CLI
institution `Silmaril.Cli.Institution` ([CLI](cli.md)).

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
| WASI (`Exchange`, `Calls`, `WasiHttp`, `WasiExamples`) | exchange servers: sets of core `History`s over the core `Sig` | lifted into core models by `Exchange.seqUse` and `Exchange.fresh`, with linearizability and refinement of `Machine.server` proved (`fresh_refines_server`, `hello_fresh`, `echo_fresh_lin`) | Proved |
| State models (`State`, `State.{Component,OwnedFs,SharedFs}`, `State.Traces`) | histories `Ev.call`/`Ev.ret`, `Atomic σ`, Herlihy–Wing `Linearizable`, `Abstraction` | identified with the core by `State.Traces`: a history is a core trace with one connection per request (`toTrace`), `Atomic σ` is `Machine (sig Req Resp) σ` by definition, Herlihy–Wing linearizability is `Sen.lin` (`linearizable_iff_lin`), the closed host is `Machine.server` (`closed_model_tr_iff`), and an abstraction gives refinement of `Machine.server` (`Abstraction.model_refines`) | Proved |
| File-backed store component (`WasiFs`) | a `wasi:http` component over `wasi:filesystem`, read as a state-model server | refines the file store of state model (b) (`wasiStoreSmall_refines`); its read-only filesystem answers satisfy the `Silmaril.Wasi` filesystem theory (`storeHost_fsOk`) | Proved |
| Connections (`Conn`) | the core | per-connection sentences and models over the core's traces, sequential consistency (`Sen.sc`) | Proved |
| Platforms (`Reuse`, `Cgi`, `Platform`) | `Platform T` with `view`, `Refines`, sequential `Log`s and per-connection `ConnLog`s | `Platform.view` is to become a core `Model`; `Log` is a `History`, `ConnLog` a trace with identities (connection, index) | Open |
| Fresh instance per request (`PerRequest`) | the core | one model, `Machine.perRequest M q₀`; `Exchange.fresh`, `State.Server.perRequest` and `Reuse.Fresh` are instances of it (`Exchange.fresh_eq_perRequest`, `State.perRequest_model_tr_iff`, `Reuse.fresh_eq_hist`) | Proved |
| Liveness (`Live`) | infinite observations `ITrace`, sentences `ISen` | a separate kind of sentence over infinite runs of `Machine.server`; every finite prefix of a run is a core trace (`Machine.IRun.prefix_tr`) | Proved |

`Platform.fresh` (platforms) is not yet stated as an instance of `Machine.perRequest`; it is
the next one, together with `Platform.view` as a core `Model`.

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
(`Http.store_sat`). Status sentences read at the full interface (`Http.sen_allStatus`).

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

Liveness is relative to the host: the theorem assumes a weakly fair scheduler.

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
- Connection events (open, close, half close) and their effect on pending requests.
- The converse of `Hom.lin_trace` (reflection of linearizability along morphisms) and a
  comorphism between the CLI institution and this one (one CLI run per request, as in CGI).
- Liveness beyond the atomic-handler server: fair runs of the pipelining server, and liveness
  of the `wasi:http` example components (their machines are total, so `Machine.fresh_total`
  applies once a component's per-request runs are read as a fair host). That fair runs exist
  for every machine is not proved.

## WASI: `wasi:http` components as servers (`Silmaril.Servers.{Exchange,Calls,WasiHttp,WasiExamples}`)

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
| `echo` (consume the body, read until `closed` at most `echoFuel` times, answer `200` with the bytes read, else `500`) | Every exchange of `wasiServerB (ofBody echo)` is `200` with the request's content, or `500` (`echo_sat`). The proof is an induction over the read loop that carries `BodyOk` along the prefixes of the call. | Proved |
| `hello`, `route`, `echo` over the reference host `refHost` (`serveRef`) | `hello` on `/`, `route` on `/`, `/hello` and `/missing`, and `echo` on a `POST` with content `abc` | Checked |
| `hello`, `route` with a fresh instance per request, in the concurrent core: they refine the core's function servers (`hello_fresh`, `route_fresh`); `echo` is linearizable for its specification (`echo_fresh_lin`); `hello` used sequentially is linearizable (`hello_seq_lin`) | | Proved |
| `hello`, `route`, `echo` linked over every host (`hello_link`, `route_link`, `echo_link`); a response over the reference host is a trace of the example linked over the concrete reference host (`serve_link`, `hello_link_answers`) | | Proved |
| The WAT binaries run the bodies: `Task.wasmRuns σh σr σe`, with `wasm_sat` giving the three specifications for the binaries' denotations, alone and linked over every host, under that task | | Open (conditional results proved) |
| A server as a web of the outgoing theories (`webOf`): the client theories `Net.httpTh`/`httpTh3 (webOf f)` see the status of `f`'s answer to a `GET` (`webOf_pathV`, `route_web_missing`) | | Proved |

The examples are Lean programs over the imports, in the shape of a component after lifting.
The order of `answer` (`set` before the body is written) is the one the `wasi:http`
documentation recommends, so that a host can stream the body.

### The components

`tests/servers/wasi-http/{common,hello,route,echo}.wat` are the same three servers as core Wasm
modules: `common.wat` holds the imports, the memory, a bump allocator (`cabi_realloc`) and
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

The binaries differ from the bodies in two places, neither of which changes the import calls:
`route` compares the UTF-8 bytes of the path, where the Lean reading maps each `char` to an
octet (`octet`, which maps a `char` above `U+00FF` to `0xFF` so that no non-ASCII path reads as
an ASCII one); and `blocking-write-and-flush` accepts at most 4096 bytes, so for a longer
`echo` body the host fails the write, which the reading counts as no response.

That the components' denotations run the bodies is open (`Task.wasmRuns`). Stating it needs a
denotation of these binaries as strategies over the proxy imports (for example through
`Silmaril.Wasi.compModel` of a decoded component and a core semantics), which is not defined
here yet.

### Conformance against a runtime

`tests/servers/wasi-http-conformance.sh` builds the three components (or takes `HELLO_WASM`,
`ROUTE_WASM`, `ECHO_WASM`), serves each with `wasmtime serve` and compares the responses to the
specifications: `hello` on `/` and `/anything` (status, content and `content-type`), `route` on
`/`, `/hello` and `/missing`, and `echo` on a `GET` and on `POST`s of 3 and 3000 bytes. The
runtime is pinned (`WASMTIME_VERSION`, default `49.0.2`; `any` accepts every version). It
skips cleanly when `wasmtime`, `curl`, or both the components and `wasm-tools`, are missing.
Run as `nix develop .#http-test -c tests/servers/wasi-http-conformance.sh`, all 9 checks pass on
wasmtime 49.0.2.

### Not modelled yet

- Headers added to a response after its construction (`outgoing-response.headers`),
  `fields.set`, `delete` and `from-list`, trailers and `send-informational`. Liveness is not
  covered:
  `echo` may answer `500` when the host delivers the body in more than `echoFuel` reads, and
  only `hello` and `route` have non-vacuity theorems (`echo` is checked on one request).
- Resource drops other than the output stream's.
- Concurrent export calls. A body runs one call at a time. The host may also run several
  instances, which gives concurrency across instances.
- A host-side theory of `wasi:http` (which answers a host may give, e.g. that a second `set`
  traps) to strengthen the linked statements beyond "every host".
- A denotation of the WAT components, so that `Task.wasmRuns` can be stated about them and
  proved.
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

So the results of (a), (b) and (c) below carry over to the core through `Server.Refines.model`
and `closed_model_tr_iff` (for example, the file-backed store's refinement of the
component-state store becomes refinement of the core's atomic-handler server of `storeStep`);
they are not restated one by one.

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

Header fields are not observed by the `wasi:http` reading, so the comparison is with
`fileStore` through `noFields` (`Atomic.mapResp`). It differs from `fileStore` only in the
`Allow` field of the `OPTIONS` and `405` answers. `keyFile root` depends on the
path-with-query only, so targets that differ only in their scheme or authority share a file.
Its injectivity on paths, which `fileStore_refines` would need to continue to the
component-state store, is not proved. Also not proved: that the
host's mutating calls satisfy a `wasi:filesystem` theory (`FsMut` checks the tree's shape, not
contents), and that `storeBody` is the reading of a Wasm binary (it is written as a program
over the imports, like the other examples).

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
  as initially" (`wasiStoreSmall_refines`, below).

In each case a client cannot tell the concrete server from the abstract one. For example, a
key-value store kept in a file and one kept in a component's memory have the same histories.

### Open

* Asynchronous handlers (`wasi:http` 0.3, where handler runs of one instance can interleave at
  `await` points): runs are no longer atomic, and linearizability needs linearization points
  inside runs.
* Connections and pipelining: read in the core (`State.Traces`), every request of these
  histories is alone on its connection. The per-connection and sequential-consistency readings
  exist in the core (`Silmaril.Servers.Conn`), but they are not yet connected to these histories.
* Done for the file-backed store (`Silmaril.Servers.WasiFs`): connecting handler runs to
  component executions and the file model to the `wasi:filesystem` theories. Not done: the
  static file server, the shared-file models (c) as components, and a theory of the mutating
  filesystem calls with contents.

## Survey: frameworks, formalizations and the other instances

### Frameworks for Wasm HTTP applications

| Framework | Interface the application implements | Instances per request | Notes |
| --- | --- | --- | --- |
| `wasi:http` 0.2, world `proxy` [1] | export `incoming-handler.handle(request: incoming-request, response-out: response-outparam)`; bodies are `wasi:io` streams | "A host may arbitrarily reuse or not reuse component instance … a component must be able to handle 0..N calls to `handle`" (`specs/wasi/0.2.12/http/proxy.wit`) | The response is sent by `response-outparam.set` and "execution [may] continue after the response has been sent" (`handler.wit`). The response is issued before `handle` returns. |
| `wasi:http` 0.3, world `service` [1] | export `handler.handle: async func(request) -> result<response, error-code>`; bodies are component-model `stream<u8>` | as 0.2. In addition, "Hosts may concurrently invoke this `handler` interface multiple times, even when previous requests have yet to finish processing", unless the guest applies backpressure (`specs/wasi/0.3.2/http/worlds.wit`) | `middleware` world: a service that also imports `handler`, so components chain |
| `wasmtime serve` [2] | either world | instantiates the component for each request. Reuse is off by default for 0.2 components and on by default for 0.3 ones [2] | For development: no TLS and no limits [2]. The intended pinned conformance runtime. |
| Spin [3] | its HTTP trigger, or a plain `wasi:http` incoming handler (since Spin 2.6) | a new instance per request. Persistent state goes through host key-value or SQL interfaces [3] | Routes by path to components (manifest `spin.toml`) |
| wasmCloud [4] | `wasi:http/incoming-handler` | per host policy | An HTTP server *provider* (a host-side plugin) calls `handle` on the component |
| Fastly Compute [5] | Compute host calls (`witx`) and component SDKs | a new instance per request by default. Viceroy 0.14.0 (2025-08-08) added experimental host calls for reusable sessions [5] | Viceroy is the local test runtime |
| NGINX Unit [6] | application type `wasm-wasi-component`: `wasi:http/proxy` (Unit 1.32 and later) | per Unit's configuration | Production web server hosting components |
| WAGI [7] | a WASI *command*: CGI 1.1 meta-variables in the environment, query parameters as arguments, the body on stdin, the CGI response on stdout | one run per request | Executed in-process, not as an OS process. It rewrites CGI variables that would reveal the host file system and adds `X_*` variables [7] |
| CGI/1.1 (RFC 3875) [8] | a program: meta-variables (§4.1), body on stdin (§4.2), response on stdout (§6) | one run per request | The ancestor of WAGI. The same shape as `Silmaril.Cli` behaviours. |
| Others | Envoy's proxy-wasm ABI [9] (HTTP filters inside a proxy); WasmEdge's socket extension and Wasmer's WASIX [10] (POSIX-style sockets inside Wasm, so the *Linux-process* shape below); `wasi:sockets` (also vendored here); containerd's runwasi [11] (Wasm workloads behind the container interface); Cloudflare Workers (Wasm inside V8 isolates driven by a JavaScript `fetch` handler) | varies | Most fit one of the three shapes below |

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
of traces of `i`. That set is meant as a model of the core server institution once `T` is the
core's trace type; this identification is not yet made. `Refines P Q i j` is trace inclusion across platforms. `Refines.sat` (proved)
transports every trace specification from `j` to `i`. `Refines.map` (proved) keeps refinement
under a change of observation.

| Instance | Lean | Implementation | Observation read as HTTP | Status |
| --- | --- | --- | --- | --- |
| Handler with instance state, one reused instance | `Platform.seq σ` | an origin `Origin σ` with its initial state | its runs (`Reuse.Seq`), one exchange at a time | defined |
| … a fresh instance per request (CGI, Spin, Fastly, `wasmtime serve` 0.2) | `Platform.fresh σ` | same | each exchange a run from the initial state (`Reuse.Fresh`) | defined |
| … under a host that pools instances (`wasi:http`'s contract) | `Platform.host σ` | same | runs of a pool of instances, any request to any idle or new instance (`Reuse.HostRuns`) | defined |
| CGI or WAGI script | `Platform.cgi g` | a `Silmaril.Cli.Spec` and the initial files | one run per request on the files the previous run left (`Cgi.origin`) | defined |
| Linux process over sockets | `Platform.linux fr` | a socket semantics `Input → List SockEv → Prop` and the launch invocation | the connections accepted and, per connection, requests framed from the octets received paired in order with responses framed from the octets sent (`connLog`, RFC 9112 §9.3) | defined; the framing `fr` is a parameter |
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

1. The HTTP/1.1 instance of `Framing`, from `Silmaril.Net.Http1.Framing`. It is blocked on
   mapping its request and response heads to `Silmaril.Net.Http.Request` and `Response` (a
   planned row of [HTTP](http.md)). With it, a theorem that
   `connLog` of the encodings of a log gives back that log (framing round trip per
   connection).
2. The socket semantics of a Linux binary: `SockEv` read off the `accept`, `read`, `write` and
   `close` system calls of `Silmaril.Process` traces. Netsem [21] is the reference for what the
   kernel may do (partial reads and writes, `EAGAIN`).
3. Concurrent instance reuse (the 0.3 `service` world). An exchange is then no longer atomic
   at the instance. The linearizability reading of the core is the specification, with the
   component's `backpressure` as the opt-out.
4. Finer observations than whole exchanges: interim responses, streaming bodies (the 0.2
   `response-outparam` sends the response before `handle` returns), and connection-level
   errors and timeouts.

### References for the survey

1. WebAssembly/wasi-http, the `wasi:http` proposal. https://github.com/WebAssembly/wasi-http.
   The vendored WIT is `specs/wasi/0.2.12/http` and `specs/wasi/0.3.2/http`.
2. Wasmtime CLI options, `wasmtime serve`. https://docs.wasmtime.dev/cli-options.html
3. Spin documentation. https://spinframework.dev
4. wasmCloud documentation, HTTP server provider. https://wasmcloud.com/docs
5. Fastly Compute, https://docs.fastly.com/products/compute; Viceroy and its changelog,
   https://github.com/fastly/Viceroy
6. NGINX Unit configuration, `wasm-wasi-component`. https://unit.nginx.org/configuration/
7. WAGI, the WebAssembly Gateway Interface. https://github.com/deislabs/wagi (see
   `docs/architecture.md`, `docs/writing_modules.md`)
8. D. Robinson, K. Coar. *The Common Gateway Interface (CGI) Version 1.1*. RFC 3875, 2004.
9. proxy-wasm ABI specification. https://github.com/proxy-wasm/spec
10. WasmEdge sockets, https://wasmedge.org/docs/; WASIX, https://wasix.org
11. containerd runwasi. https://github.com/containerd/runwasi
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

## Building

```
lake build Silmaril.Servers.Core.Thms Silmaril.Servers.Http.Thms \
  Silmaril.Servers.Examples.Counter.Thms Silmaril.Servers.Exchange.Thms \
  Silmaril.Servers.Calls.Thms Silmaril.Servers.WasiHttp.Thms \
  Silmaril.Servers.WasiExamples.Thms Silmaril.Servers.State.Thms \
  Silmaril.Servers.State.Component.Thms Silmaril.Servers.State.OwnedFs.Thms \
  Silmaril.Servers.State.SharedFs.Thms Silmaril.Servers.Reuse.Thms \
  Silmaril.Servers.Cgi.Thms Silmaril.Servers.Platform.Thms \
  Silmaril.Servers.Conn.Thms Silmaril.Servers.WasiFs.Thms
```

Every module builds in under 8 s; the slowest are the run proofs of `WasiFs` and
`Silmaril.Servers.WasiExamples.Thms`, whose checks over the reference host are evaluated by
`decide`. The conformance harness runs with
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
