# Does an HTTP server satisfy an OpenAPI document?

`Silmaril.Servers.OpenApiInst` is an institution that asks this question of a **server** of the
`Servers` core: a set of request/response traces over RFC 9110 messages. It can be a
`wasi:http` component, a process, or the HTTP/1.1 reference server. The documents are the
OpenAPI 3.1 subset of `Silmaril.Net.Http.OpenApi`.

| institution | here |
| --- | --- |
| signatures, morphisms | operation symbols, maps of symbols (`Sig`, `Sig.Hom`) |
| models, reducts | a document, the operation each symbol denotes, and a server; reducts rebind symbols (`Model`, `Model.reduct`) |
| sentences | `respOk o`, `closed o`, `rejects o cs`, conjunction, negation |
| satisfaction | atomic trace sentences of the server (`Sat`) |

## Obligations

The three kinds of obligation are kept apart:

* **Response obligation** (`respOk`): a conforming request routed to the operation gets a
  conforming response. It is assume–guarantee: request conformance is the client's side,
  taken as the hypothesis.
* **Closed-world status** (`closed`): every routed request gets a documented status.
  OpenAPI itself does not require this.
* **Request validation, a server obligation** (`rejects`): a non-conforming routed request is
  answered with one of the given statuses.

All three constrain each request's response on its own. Connection, framing and ordering
obligations belong to the HTTP/1.1 institution and the transport readings
([servers-transport](servers-transport.md)).

## Proved

* **Satisfaction condition** (`sat_map_iff`). Translation is functorial, and `inst` and
  `classic` are the institution.
* **Refinement**: a refining server keeps every positive obligation (`sat_of_refines`).
* **Agreement with the existing service model**: for a service function `S` and a document
  `d`, the `respOk` obligations of all of `d`'s operations hold iff `OpenApi.Conforms d S`
  (`respOk_all_iff_conforms`). The `closed` obligations hold iff `OpenApi.Closed d S`
  (`closed_all_iff`).
* **Down to octets** (`closed_wire_sat`): a closed service behind the HTTP/1.1 reference
  server meets each status obligation of `Http1.Inst.toTheory d`. Each is a trace sentence of
  its wire-level server (`Servers.Http1Bridge`).
* **Petstore**: the example service meets every `respOk` and `closed` obligation.

## Not covered

* The subset limits of `Net.Http.OpenApi`: no body schemas, no percent-decoding, no
  callbacks or security.
* The wire-level link: it covers status obligations only, behind the reference server. There
  is no wire-level link for `respOk` (media types, headers).
