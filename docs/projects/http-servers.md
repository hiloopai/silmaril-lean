# HTTP servers: a framework for specifying and comparing them

This page covers the verification of HTTP servers, whether they run as Wasm components under
`wasi:http`, as Linux processes, as containers or on another platform. It builds on the HTTP
formalization in `Silmaril.Net` ([HTTP](http.md)), the WASI theories ([More Wasm](wasm-wasi.md))
and the CLI work ([CLI](cli.md)). Statuses follow [HTTP](http.md): **proved** (a theorem in a
`Thms` header that depends only on the standard axioms), **checked** (evaluated on examples),
**defined**, **planned**. No part of this tree uses `sorry`, `native_decide` or extra axioms.

## State models

Region `Http`, modules `Silmaril.Http.State.*`. This section covers where a server keeps its
state and what can be proved about the histories a client observes in each case. All servers
here have the same interface: requests and responses of `Silmaril.Net.Http`
(`Request = Message RequestLine`, `Response = Message Status`, RFC 9110 §6). Only the state
model changes from one server to the next.

### The shared vocabulary (`Silmaril.Http.State`)

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

### (a) State inside the component (`Silmaril.Http.State.Component`)

The state lives in the instance's memory and globals, and nobody else changes it
(`Server.closed`).

| Server | Claim | Lean | Status |
| --- | --- | --- | --- |
| Counter: the `n`-th run answers `f n` (`counter`; `httpCounter render`: `200` with `render n`) | Linearizable with respect to its handler; for injective `f`, distinct requests get distinct answers however they overlap | `counter_linearizable`, `counter_distinct`, `httpCounter_distinct` | proved |
| Key-value store: `Net.Http.storeStep` (`GET`, `HEAD`, `PUT`, `DELETE`, `OPTIONS` per RFC 9110 §9.3) | Linearizable with respect to `storeStep` | `kv_linearizable` | proved |
| The same components with a fresh instance per request | The counter always answers `f 0`; the store answers every `GET` from its initial contents, so component state does not persist | `perRequest_counter`, `perRequest_kv_get` | proved |

The decimal rendering `decimal` is defined. Its injectivity, which `httpCounter_distinct`
assumes, is not proved.

### (b) WASI over a file system that the server alone edits (`Silmaril.Http.State.OwnedFs`)

The state is the contents of the files under the preopened directories, in the CLI file
model (`Silmaril.Cli.Fs`: rooted paths to contents, as a WASI preopen gives them). The files
are host state, so they survive a fresh instance per request.

| Server | Claim | Lean | Status |
| --- | --- | --- | --- |
| Static file server (`GET`/`HEAD` the file the target names or `404`, else `405` with `Allow: GET, HEAD`) | Refines the stateless server of the initial files; each request `r` is answered `staticAnswer loc fs₀ r` | `static_refines`, `static_answer` | proved |
| Document root: the path before `?`, without empty and `.` components, under a preopen; `..` names nothing | Names only files under its preopen, never with `..` | `docRoot_safe`; three `#guard` examples | proved, checked |
| File-backed key-value store (`fileStoreStep`: `storeStep` written against the file `enc t` of each key) | For an injective layout, a step through `view enc` is a `storeStep`; the store **refines the component-state store** of state model (a) and is linearizable; the frame invariant `Frame` holds (only key files are written) | `fileStoreStep_view`, `fileStore_refines`, `fileStore_linearizable`, `fileStore_frame` | proved |

### (c) WASI over a file system that others may change (`Silmaril.Http.State.SharedFs`)

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
| A store where the environment changes some key files: linearizable on the untouched keys | | planned |

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
* fresh instance per request → stateless server `Atomic.fresh` (`perRequest_answer`).

In each case a client cannot tell the concrete server from the abstract one. For example, a
key-value store kept in a file and one kept in a component's memory have the same histories.

### Open

* Asynchronous handlers (`wasi:http` 0.3, where handler runs of one instance can interleave at
  `await` points): runs are no longer atomic, and linearizability needs linearization points
  inside runs.
* Connections and pipelining (HTTP/1.1 answers requests on one connection in order) are not part
  of these histories. Per-connection order would make a sequential-consistency variant possible.
* Connecting the handler runs to component executions (the `wasi:http` incoming handler and its
  bodies as streams), and the file model to the `wasi:filesystem` theories in `Silmaril.Wasi`.
* Partially shared key files (see the planned row above).

References: M. P. Herlihy and J. M. Wing, *Linearizability: a correctness condition for
concurrent objects*, ACM TOPLAS 12(3), 1990; RFC 9110 (HTTP semantics).
