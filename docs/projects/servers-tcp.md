# HTTP over TCP: readings, protocol selection, and implementing an HTTP server

`Silmaril.Servers.Tcp` reads what a server does at its TCP sockets
(`Silmaril.Servers.Transport`) as HTTP request/response traces of the server core. It also
says when a TCP-level server implements an HTTP-level one, and with which assumptions about
protocol versions.

## Level and assumptions

* **Socket API only.** The model is the reliable in-order byte stream of `Net.Tcp.Service`
  (RFC 9293 §2.2). Nothing here refines the segment-level `Net.Tcp.Transfer`.
* **No TLS model.** The `alpn` selection assumes a TLS layer that delivers plaintext in order
  and reports the negotiated ALPN id. That assumption is not discharged.
* **No HTTP/2 reading.** HTTP/2 connections are detected by their preface but not read: the
  HTTP/1.1 reading is undefined on them. No universal compatibility is claimed:
  * `select_http1_ne_h2`: under `http1`, HTTP/2 is never selected;
  * `select_prior_get`: under prior knowledge, an HTTP/1.1 request line is refused.
* **No `h2c`.** The `Upgrade: h2c` path (RFC 7540 §3.2, removed by RFC 9113) is not modelled.

## Reading HTTP/1.1, with what is left over

`h1Read bs` returns the complete requests, the leftover octets and an error flag.

* An incomplete request (more octets may come) and a malformed one both stop the reading.
  Both leave their octets in `rest`, and the two are not told apart.
* `h1Read_encode`: encoded valid requests read back with nothing left over.
* `h1Read_msgs`: the messages agree with `Servers.Wire1`.

`h1Reading sel alpn p` is a partial observation map from transport traces to core traces. It
is defined only when every connection on port `p` is selected as HTTP/1.1. On a connection,
the `k`-th request (identity `⟨c, k⟩`) is paired with the `k`-th response read from the
octets sent, and pending requests appear as receptions only.

## At least, at most, exactly

For a reading `ρ`, a transport model `T` and an HTTP model `M`:

| relation | meaning |
| --- | --- |
| `AtMost ρ T M` | `ρ.image T ⊆ M` |
| `AtLeast ρ T M` | `M ⊆ ρ.image T` |
| `Exactly ρ T M` | both (`exactly_iff`: equality) |

`AtMost.sat` carries every sentence of `M` down to the TCP traces, read through `ρ`.

**Example: `helloTcp p`.** A TCP-level hello server. Its connections carry complete valid
requests (not `HEAD` or `CONNECT`), each answered `200 hello` with `Content-Length`. On port
`p`, with HTTP/1.1 selection and no TLS:

* `hello_atMost`: it implements at most the per-request HTTP server of the `wasi:http` hello
  module, that is, the denotation of the core module built from
  `tests/servers/wasi-http/hello.wat` over typed hosts.
* `hello_atMost_spec`: hence at most the function server of `200 hello`.
* `hello_realizes`: it realizes every single exchange of a served request.

`Exactly` is not claimed. The reading numbers requests per connection and lists connections
one after another, while the HTTP model allows any identities and interleavings.

## Open

* **A `wasi:sockets` component as a transport model.** There is no denotation yet of a
  `wasi:sockets` TCP component into `TTrace`. With one, a component would be shown to refine
  `helloTcp p`, and through `hello_atMost` it would implement at most the `wasi:http`
  component.
* **HTTP/2 reading.** Reading HTTP/2 exchanges off frames, using `Net.Http2`.
* **Distinguishing errors.** Telling incomplete requests from malformed ones in `rest`, and
  connection close and reset handling in the reading (`eof`, `reset` and `err` events are
  recorded but not yet interpreted).
* **Real endpoints.** Using `Net.Ip.Endpoint` as `Addr` (#180) in the examples.
