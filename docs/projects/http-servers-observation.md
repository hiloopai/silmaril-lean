# HTTP servers: observation, refinement, hosts, contexts and independent endpoints

This page is a follow-up to [HTTP servers](http-servers.md) (the `Servers` region). It adds
seven topics to that framework. They use its core (`Silmaril.Servers.Core`: interfaces,
request/response traces, models as trace sets, refinement as trace inclusion) and do not set
up a competing one. Its runtime counterpart, testing the `dice` component under replayable
host policies, is in [`tests/servers/policies`](../../tests/servers/policies/README.md).

## Summary and status

| Topic | Module | Status |
| --- | --- | --- |
| Observations after initialization | `Silmaril.Servers.Observe` | Proved |
| Host interpretations and quantifiers | `Silmaril.Servers.Hosts` | Proved |
| Contextual equivalence and the HTTP reading | `Silmaril.Servers.Context` | Proved |
| `wasi:http` components, hosts as contexts | `Silmaril.Servers.WasiContext` | Proved |
| Independent endpoints (tensor, routing, state isolation) | `Silmaril.Servers.Tensor` | Proved |
| Example: dice over a random host | `Silmaril.Servers.Examples.Dice` | Proved |
| Problem shapes, evidence kinds, registered problems | `Silmaril.Servers.Problems` | Proved; one problem open |
| HTTP/1.1 implementations (#158) as servers | `Silmaril.Servers.Http1Bridge` | Proved |

No module uses `sorry`, `native_decide` or a new axiom. `#print axioms` on the registered
solutions shows `propext`, `Classical.choice` and `Quot.sound` at most.

## Observations after initialization (`Observe`)

The core reads a server as the traces it can be seen doing, and assumes it is up. An
observation (`Obs A`) is one of three things:

* `initFail`: initialization failed;
* `run t`: the server is running after the finite trace `t`;
* `stop t`: the server stopped (exited or crashed) after `t`.

A behaviour (`Beh A`) is a set of observations. It is *healthy* when its running traces are
prefix closed and a server that stopped after `t` was running after `t`.

* **Orientation.** `Beh.Refines I S` puts the implementation first and is `I ⊆ S`.
  Observational equivalence is equality, which is refinement both ways
  (`Beh.eq_iff_refines`).
* **Preorder and quotient.** Implementations of any kind with a denotation `d : ι → Beh A`
  are preordered by refinement (`implPreorder d`). Their antisymmetric quotient is
  `Quotient (obsSetoid d)` with the order `Norm.partialOrder d`. Classes are their normalized
  trace languages: `norm d` is injective (`norm_injective`), and `norm_le_iff` says the order
  is inclusion.
* **Safety, liveness, may and must.** `Must` (every observation) is preserved by refinement,
  and so are `InitSafe` and `NoStop`. `May` (some observation) goes the other way. The empty
  behaviour refines everything and cannot initialize (`empty_refines`,
  `not_canInit_empty`), so refinement alone is a safety relation.
* **Divergence and termination.** All observations are finite. A handler that never answers
  shows up only as a running trace with a pending request, which is also how a slow server
  looks. A test timeout therefore records a bound, not divergence. Eventual answers are
  liveness properties: they stay in `Silmaril.Servers.Live`, over infinite runs and fairness.
* **Link to the core.** `Beh.ofModel M` is the behaviour of a core model that always
  initializes, and `traces (ofModel M) = M`. Refinement of `ofModel`s is core refinement.
  On healthy behaviours, a trace sentence holds of every observation exactly when the core
  model satisfies it (`must_sen_iff`, `must_ofModel_iff`).

## Host interpretations (`Hosts`)

An open server `Open H A := H → Beh A` has one behaviour per host strategy. Every claim says
how it quantifies over a set of hosts `Hs`:

| claim | meaning |
| --- | --- |
| `RefinesAt Hs C D` | for every host, the same one on both sides, `C η ⊆ D η` |
| `EquivAt Hs C D` | for every host, `C η = D η` |
| `MustAll Hs C φ` | every observation under every host satisfies `φ` (demonic) |
| `MaySome Hs C φ` | some observation under some host satisfies `φ` (angelic) |
| `MayAll Hs C φ` | under every host, some observation satisfies `φ` |

What is proved about these quantifiers:

* `MustAll` and `MaySome` are the `Must` and `May` of the merged behaviour `under Hs C`.
* Refinement of merged behaviours is strictly weaker than `RefinesAt`
  (`under_not_refinesAt`: it lets the two sides use different hosts).
* A `MustAll` over more hosts gives one over fewer hosts (`MustAll.anti`).
* One observation that violates `φ` under one host of `Hs` refutes `MustAll Hs C φ`
  (`not_mustAll_of_witness`). A passing run proves nothing beyond its own host.

There are three kinds of host for an import with calls `Q` and answers `R`. All three embed
into `Stateful`.

* `Pure Q R`: a deterministic function.
* `Oracle R`: user nondeterminism, the `k`-th call answered by `o k`. A seeded family
  `seeded gen` is one host per seed.
* `Stateful σ Q R`: an effectful, stateful environment. It is deterministic given its state,
  so every run can be replayed from the initial state (`Stateful.answers`, `pure_answers`,
  `oracle_answers`, `answers_append`).

## Contextual equivalence and the HTTP reading (`Context`, `WasiContext`)

A language with contexts (`Lang`) observes each closed program: `run K c`. A **reading**
(`Reading`) fixes, for each environment `x`, a context `ctx x`, and a map `read` from what that
closed program is observed doing to an HTTP behaviour. These two fields are the exact
assumptions:

* **Lift.** If two components are contextually equivalent on the contexts the reading uses,
  their HTTP behaviours are equal in every environment (`Reading.equivAt_of_ctxEquivOn`). If
  `read` is monotone, contextual refinement gives HTTP refinement
  (`Reading.refinesAt_of_ctxRefinesOn`).
* **Not a theorem.** An arbitrary projection of components is not preserved
  (`ctxEquiv_not_preserves_projection`). Neither is a reading through a context outside the
  class (`ctxEquivOn_not_preserves_outside`). HTTP equivalence does not reflect to contextual
  equivalence (`reading_not_reflects`).
* **Reflection under full abstraction.** Suppose every context of a class observes a
  function of the HTTP behaviour. Then HTTP equivalence gives contextual equivalence on that
  class (`Reading.ctxEquivOn_of_equivAt`). This is a hypothesis, not a fact about any
  language here.

### `wasi:http` components

In `WasiContext`, components are strategies over the proxy slice of `WasiHttp` and contexts
are hosts `η : Host Y proxyImports`. Pure hosts (`concrete impl`), nondeterministic hosts and
stateful hosts are all hosts. A host's observation is `interacts η σ`: the component's plays
that interact with a play of `η`, *import events included*.

* `linkServer η σ = readExch (interacts η σ)` (`linkServer_eq`). So host equivalence over
  `Hs` (`HostEquivOn`) gives equal linked servers, and equal per-request HTTP behaviours,
  under every host of `Hs` (`linkServer_eq_of_hostEquivOn`, `httpReading_equivAt`).
* Inclusion of interactions gives HTTP refinement (`httpReading_refinesAt`). Inclusion of
  strategies gives inclusion of interactions (`interacts_mono`).
* **Not claimed:** that equal composites `Wasi.link η σ` (which hide the import events) give
  equal HTTP readings.
* **Initialization failure is not modeled here.** The Lean component model has no
  instantiation phase, so this reading is `InitSafe` by construction. Initialization failures
  are observed only at runtime, see below.

## Independent endpoints (`Tensor`)

* **Interfaces and models.** `A.tensor B` tags the requests and responses of two endpoints.
  `Model.tensor M N` has the traces whose left part is a trace of `M` and whose right part is
  a trace of `N`. These are all interleavings: the environment orders the two sides, and
  neither side's part depends on the other's.
* **Laws** (`Thms`):
  * monotone in each factor (`Model.tensor_mono`), so refining an endpoint refines the
    composite;
  * commutative (`tensor_swap_iff`), associative (`tensor_assoc_iff`), and with the unit
    `Model.unit` (`tensor_unit_iff`), up to the canonical maps of traces;
  * each factor is observed alone (`tensor_sat_left`, `tensor_inl_iff`).
* **Routing.** A router `ρ : A.Req → Bool` sends each request to exactly one endpoint, so
  routes are disjoint (`RoutedBy.isLeft_iff`). `Model.routed ρ M N` is the HTTP server that
  answers each route with its endpoint. It is monotone in both endpoints.
* **State isolation.** The histories of `Machine.tensor M₁ M₂`, where each side's handler
  touches only its own state, are the interleavings of the two machines' histories
  (`Machine.tensor_hist_iff`).
* **Shared state is not independent.** Two endpoints sharing a counter have, from `0`,
  histories that no two isolated counters have, from any start (`Tensor.shared_not_tensor`).
  Shared-state servers are therefore never claimed to be tensors.

## Example: dice over a random host (`Examples.Dice`)

The dice server answers three kinds of request:

* `/roll`: one draw `x` of `wasi:random` `get-random-u64`, answered `200` with `x % 6 + 1`;
* `/pair`: two draws, answered with two such faces;
* anything else: `404 not found`.

The planted-bug variant uses `x % 7 + 1` on `/roll`. The server is a `Machine` on the state of
a stateful host. It can run as one long-lived instance (`server`), or as a fresh instance per
request with the host restarting each time (`perRequest`, what `wasmtime serve` does).

| result | kind |
| --- | --- |
| `dice_mustAll`: under every stateful host, of every state type, the spec holds | must, proved |
| `dice_maySome_six`: some host makes `/roll` answer `6` | may, proved |
| `zero_not_maySix`: under the zero host, no run answers `6` | may, refuted for that host |
| `buggy_not_mustAll`: the seven-faced variant fails (host drawing `6`) | must, refuted |
| `buggy_mustAll_zero`: but it passes under the zero host | must over `{zero}`, proved |
| `perRequest_roll_const`: per-request instances answer every `/roll` alike | proved |

## Problems and evidence (`Problems`)

**Problem shapes.** `Shape.Satisfies`, `Refines`, `Equivalent`, `InitSafe`, `MustUnder`,
`MayUnder` and `RefinesUnder` are the obligations a problem may ask of an abstract server.
Twelve problems are registered with `@[problem]`:

* ten are solved or refuted by Lean theorems (`@[solves]`, `@[refutes]`);
* `servers/wasi/route-module/runs-body`, one conjunct of `WasiBinaries.Task.binRuns`, is open;
* `servers/wasi/hello/exports-handle` is solved, but only as a name match (see below).

**Evidence kinds.** `Evidence` keeps five kinds of backing apart. `catalogue` maps each problem
and each runtime check to its kind.

| evidence | badge | what it is |
| --- | --- | --- |
| `proof` | proved | a Lean theorem |
| `refutation` | refuted | a Lean theorem of the negation |
| `validatorCheck` | validated | a tool accepted or rejected an artifact |
| `runtimeTest` | tested | finitely many runs under recorded host policies |
| `nameMatch` | names match | an export has the expected name, nothing more |

**"The component is well typed with the right server interface"** is three different claims,
kept apart:

* **A Lean theorem.** The core module's denotation runs its body over typed hosts:
  `WasiCore.RunsTy`, proved for `hello` (`servers/wasi/hello-module/runs-body`) and open for
  `route`.
* **A validator check.** `wasm-tools component targets` checks the component's type against
  the world. `wasm-tools validate` checks only well-formedness: it accepts a component whose
  `handle` has the wrong type.
* **A name match.** `handleF ∈ proxyWorld.exports`.

## Runtime experiments (`tests/servers/policies`, testing evidence)

The runner `tests/servers/wasi-http-policies.sh` composes the `dice` and `dice-buggy`
components with policy components that implement `wasi:random/random`, using `wac plug`, and
serves the result with `wasmtime serve` 49.0.2 on `127.0.0.1`. The policies:

* `zero`: a pure host;
* `seeded N`: one splitmix64 host per seed;
* `chaos N`: a stateful, replayable schedule of extreme values.

Every run writes a `silmaril.servers.runtime-evidence.v1` record with `"evidence":
"runtime-test"`. A record holds the tool versions and hashes, the artifact hashes, the policy
and seed, the bounds, the full trace, the checks and the negative cases.

Observed with these pins:

* **Must.** `dice` meets its must check under all four policies. `dice-buggy` fails under
  `chaos 7` (it answers `7`), as expected, and passes under `zero`. This matches
  `buggy_not_mustAll` and `buggy_mustAll_zero`.
* **Replay.** Every run, repeated, gives an identical trace.
* **Per-request instances.** All `/roll` answers of a run are equal. This matches
  `perRequest_roll_const`, and shows that `wasmtime serve` instantiates per request (an
  observation, not a proof).
* **Negative cases:**
  * a core module is not a component: `wasmtime serve` refuses it;
  * a component with the right export name but the wrong `handle` type passes
    `wasm-tools validate`, is rejected by `component targets`, and is served by wasmtime with
    a `500` for every request (the type check happens at instantiation, per request);
  * a start function that traps gives a `500` for every request, not a failure at startup;
    under per-request instantiation an initialization failure is observed per request;
  * a handler that loops hits the bound (recorded as `timeout`).

## HTTP/1.1 implementations as servers (`Http1Bridge`, Proved)

This section connects the HTTP/1.1 institution of #158 (`Silmaril.Net.Http1.Inst`) to the
server core.

* **The reading.** Over the interface `wireSig` of framed HTTP/1.1 messages (heads and
  bodies, as octets), `implServer I` is the atomic-handler server of an implementation's
  response relation.
* **Response obligations.** `respRel` translates the obligations about responses: `status`,
  `notStatus`, `respField`, `noRespField`, `unknownMethods`, `headNoContent`, `wellFramed`,
  and conjunctions of these. For each of them, the model satisfies the obligation iff its
  server satisfies the atomic trace sentence (`sat_iff_server_sat`).
* **The reference server.** For a compliant profile and a well-framed handler, the reference
  server of `Http1.Pipeline` has this as core sentences: no content after `HEAD`, and only
  well-framed responses (`refServer_headNoContent`, `refServer_wellFramed`).
* **Refinement.** A server of any platform that refines `implServer` inherits these
  sentences (`sat_of_refines`).
* **What the reading forgets.** Framing, connection and capability obligations
  (`framesSafely`, `closesOnClTe`, `implements`) have no exchange relation. The exchange
  reading is a projection that forgets them: the reference implementation and its
  keep-alive-always variant have the same server, but only one satisfies `closesOnClTe`
  (`closesOnClTe_not_observable`).

## Open

* Relating the runtime traces to the Lean model of a component: the dice component's core
  module is not read by the `WasiCore` denotation (it imports `wasi:random`, outside the proxy
  slice).
* `servers/wasi/route-module/runs-body` (`Task.binRuns`).
* A trace-level independence law for servers:
  `Machine.server (M₁.tensor M₂) = (M₁.server).tensor (M₂.server)` up to disjoint request
  identities. Only the history-level law is proved.
* Beyond the response obligations of #158: relating `wireSig` exchanges to the RFC 9110
  messages of `Servers.Http.sig` (through `Servers.Wire1` decoding), and connection-level
  traces for `closesOnClTe`.

## Provenance

Everything here is a Silmaril addition, written for this repository. The runtime pins are
wasmtime 49.0.2, wasm-tools 1.263.0 and wac-cli 0.12.0, official release binaries of the
Bytecode Alliance (Apache-2.0 WITH LLVM-exception). They are downloaded at test time and not
vendored. Their versions and hashes are recorded in each evidence file.
