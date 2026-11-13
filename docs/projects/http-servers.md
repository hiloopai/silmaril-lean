# HTTP servers as specifications

This page covers a framework for verifying HTTP servers, whatever runs them: Wasm components
under a `wasi:http` host, CGI or WAGI scripts, Linux processes over sockets, containers. It also
covers how such servers are compared by refinement. The Lean code is the `Servers` region
(`Silmaril/Servers/…`). It builds on the HTTP semantics of `Silmaril.Net.Http`
([HTTP](http.md)), the WASI theories ([More Wasm](wasm-wasi.md)) and the CLI behaviours
([CLI](cli.md)). Statuses use the words of [HTTP](http.md): **proved**, **checked**,
**defined**, **planned**. No module uses `sorry`, `native_decide` or extra axioms.

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
  smuggling-freedom theorem of [HTTP](http.md) track C is the formal counterpart.
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
of traces of `i`. That set is a model of the core server institution once `T` is the core's
trace type. `Refines P Q i j` is trace inclusion across platforms. `Refines.sat` (proved)
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
   planned row of [HTTP](http.md) track C). With it, a theorem that
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

### References

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

### Building

```
lake build Silmaril.Servers.Reuse.Thms Silmaril.Servers.Cgi.Thms Silmaril.Servers.Platform.Thms
```
