# HTTP servers: specifications across platforms

This page describes a framework for specifying and verifying HTTP servers, whatever runs
them: Wasm components, Linux processes, containers or anything else. Servers are compared by
refinement. The platform-neutral core describes what a server does as traces of exchanges.
Each platform is an instance: its programs are read as models of the core. This page records
what is defined, proved, checked and open. Its statuses are those of
[the HTTP page](http.md):

- **Proved** means that a theorem is stated in a `Thms` header and depends only on the standard axioms.
- **Checked** means that the behaviour is evaluated on examples by `decide` or `rfl`.
- **Defined** means that definitions exist without theorems.
- **Planned** means that nothing exists yet.

No part of this tree uses `sorry`, `native_decide` or extra axioms. All modules are in the
`Servers` region (`Silmaril/Servers`, proofs in `Silmaril/Proofs/Servers`).

## Atomic servers: `Silmaril.Servers.Basic`

In the simplest reading, each request and its response form one **atomic exchange**, and a
server is the set of exchange sequences it can take part in. The module is minimal. It is the
interface that the WASI instance below is stated against. A trace semantics where a second
request may arrive before the first response is beyond this module.

| Part | Status |
| --- | --- |
| Interfaces `Iface` (requests, responses), exchanges, servers `Model I` as sets of exchange traces | Defined |
| Specifications `Sen I` (trace predicates), satisfaction `Sat`, `each R` (every exchange related by `R`) | Defined |
| Refinement as trace inclusion; it preserves satisfaction (`Refines.sat`) and is transitive | Proved |
| Servers as functions (`ofFun f`): `ofFun f` refines `ofRel R` iff `R q (f q)` for every `q` (`ofFun_refines_iff`) | Proved |
| Interface morphisms `Hom I J` (read requests, write responses), the lift of servers, the pullback of specifications and the satisfaction condition (`Hom.sat_lift_iff`), monotonicity of the lift | Proved |

## WASI HTTP servers: `Silmaril.Servers.{Calls,WasiHttp,WasiExamples}`

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
  `rh`, which defaults to `200` as the WIT says. Its content is the bytes written to the
  output streams of `rh`'s body, and that body must be finished. Only the host's answers are
  read. A failed or ill-typed answer to an operation of the response makes the response
  unobservable. Header fields are not observed.
- **The request of a call** is any request (`Silmaril.Net.Http.Request`) consistent with what
  the host answered on the request handle (`ReqOk`): the `method` and `path-with-query`
  answers. The rest of the request is left open, so a specification must hold for every
  request consistent with the answers.
- `wasiServer σ : Model httpIface` is the component `σ` read as a server of
  `Silmaril.Net.Http` requests and responses (RFC 9110 §6). **Defined.**
- `wasiServerB σ` also reads request bodies (`BodyOk`). After every prefix of a call, the bytes
  delivered by `blocking-read` on the streams of the bodies consumed from the request are a
  prefix of the request's content, and they are all of it once a read answers `closed`. It
  refines `wasiServer σ` (`wasiServerB_refines`), so the specifications proved for
  `wasiServer` carry over (`hello_satB`). **Proved.**

### Example servers

| Server | Specification | Status |
| --- | --- | --- |
| `answer o resp`, the shared response code (fields, outgoing response, status, body, `set`, write, drop, finish) | For every host, no response or exactly `resp` (`answer_run`). Over a host whose answers succeed, exactly `resp` (`answer_ok`, in the proofs). | Proved |
| `hello` | Every exchange is `200 hello` (`hello_sat`), so `hello` refines the server of the constant function (`hello_refines`). Every request answered `200 hello` is a trace (`hello_answers`). | Proved |
| `route` | Every exchange is answered from the route table on the path-with-query: `/` gives `200 home`, `/hello` gives `200 hello` and anything else gives `404 not found` (`route_sat`, `route_refines`). Every request answered from the table is a trace (`route_answers`). | Proved |
| `echo` (consume the body, read until `closed` at most `echoFuel` times, answer `200` with the bytes read, else `500`) | Every exchange of `wasiServerB (ofBody echo)` is `200` with the request's content, or `500` (`echo_sat`). The proof is an induction over the read loop that carries `BodyOk` along the prefixes of the call. | Proved |
| `hello`, `route`, `echo` over the reference host `refHost` (`serveRef`) | `hello` on `/`, `route` on `/`, `/hello` and `/missing`, and `echo` on a `POST` with content `abc` | Checked |
| A server as a web of the outgoing theories (`webOf`): the client theories `Net.httpTh`/`httpTh3 (webOf f)` see the status of `f`'s answer to a `GET` (`webOf_pathV`, `route_web_missing`) | | Proved |

The examples are Lean programs over the imports, in the shape of a component after lifting,
not Wasm binaries. The order of `answer` (`set` before the body is written) is the one the
`wasi:http` documentation recommends, so that a host can stream the body.

### Conformance against a runtime

`tests/servers/wasi-http-conformance.sh` serves components with `wasmtime serve` and compares
their responses to the specifications (`HELLO_WASM`, `ROUTE_WASM`, and an optional
`WASMTIME_VERSION` pin). It skips cleanly when `wasmtime`, `curl` or the components are
missing. No component binaries exist yet, so the harness has not been run against a runtime.

### Not modelled yet

- Request and response headers, trailers and `send-informational`. Liveness is not covered:
  `echo` may answer `500` when the host delivers the body in more than `echoFuel` reads, and
  only `hello` and `route` have non-vacuity theorems (`echo` is checked on one request).
- The once-only rule of `response-outparam.set`, and resource drops other than the output
  stream's.
- Concurrent export calls. A body runs one call at a time. The host may also run several
  instances, which gives concurrency across instances.
- Statements over linked systems (`Silmaril.Wasi.link η σ` for a host `η`). They follow from
  the statements over all plays, as in `Silmaril.Wasi.Examples`, but are not written out.
- Compiling the examples to Wasm components (in WAT or through the component tools of this
  repository) and running the conformance harness on them.
- The equality of `Silmaril.Wasi.ofBody` with `Silmaril.Games.Strategy.ofHandler` is still
  open (see [More Wasm](wasm-wasi.md)).

## Building

```
lake build Silmaril.Servers.Basic.Thms Silmaril.Servers.Calls.Thms \
  Silmaril.Servers.WasiHttp.Thms Silmaril.Servers.WasiExamples.Thms
```
