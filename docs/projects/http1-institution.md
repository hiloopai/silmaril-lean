# HTTP/1.1 institution and REST services (OpenAPI 3.1 subset)

This page covers two layers on top of the HTTP/1.1 compliance modules
([http1-compliance.md](http1-compliance.md)): an institution whose models are HTTP/1.1
implementations, and a REST service model for a stated subset of OpenAPI 3.1.0 that is
related to HTTP/1.1 through that institution. Statuses follow [http.md](http.md): Proved,
Checked, Defined, Abstract, Planned.

## The institution (`Silmaril.Net.Http1.Institution`)

| Part | Here | Status |
| --- | --- | --- |
| Signatures | `Sig`: method, field-name and transfer-coding symbols | Defined |
| Signature morphisms | `Sig.Hom`: maps of the three symbol kinds; a category | Defined |
| Sentences | `Sen`: statuses (or forbidden statuses) per method and route; required and forbidden response fields; implemented codings; responses to unrecognised methods; safe request framing; closure after CL+TE; no content for `HEAD`; well-framed responses; `¬`, `∧` | Defined |
| Models | `Model`: an implementation (`Impl`: request framing, keep-alive decision, implemented codings, response relation) plus an interpretation of the symbols as octets | Defined |
| Reducts | `Model.reduct σ`: the same implementation, with symbols interpreted through `σ` | Defined |
| Satisfaction condition | `sat_map_iff` | Proved |
| Functoriality, `Sig ⥤ Room`, Goguen–Burstall form | `Sen.map_id`, `Sen.map_comp`, `inst`, `classic` | Proved |

All sentences are invariant under reducts by construction. An obligation that quantifies
over "all recognised methods" is not invariant, so `unknownMethods` names the recognised
methods explicitly.

**Vanilla, extension-compliant and noncompliant implementations.**

- `Std` is the standard vocabulary: the RFC 9110 §9.3 methods, the framing and connection
  fields, and the registered codings. `Model.Standard` is its standard interpretation.
- `rfcCore` lists the obligations of every compliant server: safe framing, closure after
  CL+TE, no content in `HEAD` responses, well-framed responses, and `chunked` support.
- `Vanilla M` is a standard model of `Std` that satisfies `rfcCore`.
- `ExtensionCompliant T X` is a model of `Std.extend M F C` (extension methods, fields,
  codings) whose reduct is standard. It satisfies the translated `rfcCore` and its extension
  theory `T`.
- `Violates M φ` names the obligation a noncompliant implementation breaks.

| Result | Status |
| --- | --- |
| An extended implementation satisfies a translated vanilla obligation iff its reduct does (`extension_conservative`), so the reduct of an extension-compliant model is vanilla (`ExtensionCompliant.reduct_vanilla`) | Proved |
| The reference server is vanilla for every compliant profile and well-framed handler (`refModel_vanilla`) | Proved |
| The reference server with a `PATCH` handler is extension-compliant for RFC 5789 (`patchModel_extensionCompliant`) | Proved |
| A `Content-Length`-first server violates `framesSafely` and is not vanilla (`clWins_violates`, `clWins_not_vanilla`) | Proved |
| A keep-alive-always server violates `closesOnClTe` (`keepAlways_violates`) | Proved |
| Comorphisms to the CLI institution or to the server institution of the `Servers` region (#148) | Planned |
| Connection-level sentences (pipelines, traces) rather than single exchanges | Planned |

## Transfer codings from the compression library (`Silmaril.Net.Http1.CodingLib`)

The `Decoders` parameter of `Silmaril.Net.Http1.Codings` is instantiated with the codecs of
`Silmaril.Formats.Compression`: `gzip` (an RFC 1952 file of one or more members, decoded with
`Decoder.members` as RFC 9112 §7.2 and RFC 9110 §8.4.1.3 require) and `deflate` (one whole
zlib member, RFC 1950). `libDecoders_inverts` discharges the assumption `Decoders.Inverts`, so
`lib_roundTrip` proves the round trip for any list of these codings, **for the library's
stored-block encoders only** (Proved). Its only dependencies are `Gzip.roundTrip`,
`Zlib.roundTrip` and `RoundTrip.members_single`. This module does not itself prove that gzip or
DEFLATE decoding is correct on arbitrary compressed input; that is the compression track's
`DeflateSpec.deflateTake_iff` (the decoder against an independent RFC 1951 semantics) and the
append laws, which `CodingLib` does not use.
`compress` (LZW) is not implemented, so a server configured with
`libImplements` answers it with `501`.

## REST services: an OpenAPI 3.1.0 subset (`Silmaril.Net.Http.OpenApi`)

Supported version: **3.1.0** only (`Document.version`, checked by `Document.Valid`).

| OpenAPI object | Modelled | Not modelled (yet) |
| --- | --- | --- |
| Paths, path templating | templates, concrete paths before templated ones, document order | path-level `servers`, `$ref` |
| Path Item | its operations | path-level `parameters` |
| Operation | method (`get`, `put`, `post`, `delete`, `options`, `head`, `patch`, `trace`), `operationId`, parameters, request body, responses | callbacks, security, `deprecated` |
| Parameter | `in: path, query, header`, `required`, schema | `in: cookie`, `style`/`explode`, `content`, percent-decoding of values |
| Schema | `string` (length bounds, `enum`), `integer` (bounds), `boolean` | the rest of JSON Schema 2020-12; body schemas (`Silmaril.Formats.Json` is the intended base) |
| Request Body | `required`, media types | media type parameters, encodings |
| Responses | exact codes, ranges `1XX`–`5XX`, `default`, with this precedence | links |
| Response | media types, required headers | header schemas |

**Semantics.**
- `route` routes a request to an operation, with the values of the path's template expressions.
- `RequestConforms` and `ResponseConforms` check messages against an operation.
- A service `Conforms` to a document when every conforming request gets a conforming response.
- A service is `Closed` when every routed request gets a documented status. OpenAPI does not
  require documents to list every status, so this is the contract-testing reading, kept
  separate.

| Result | Status |
| --- | --- |
| Path templates: match/render round trips (`matchTemplate_sound`, `matchTemplate_render`, `matchTemplate_length`) | Proved |
| Routing addresses an operation of the document with the request's method; the path renders from the template (`route_mem`, `route_sound`) | Proved |
| Services from per-operation handlers conform / are closed when their handlers are (`ofHandlers_conforms`, `ofHandlers_closed`) | Proved |
| A pet store document is valid; its service conforms and is closed; `/pets/mine` routes before `/pets/{petId}` (`OpenApiPetstore.Thms`) | Proved |

## Relating services to HTTP/1.1 (`Silmaril.Net.Http1.Service`)

- `serviceHandler S` runs a service behind the reference HTTP/1.1 server. Checked requests
  become RFC 9110 requests. The server owns the framing: `Content-Length` is computed, and the
  service's framing and hop-by-hop fields are dropped. `CONNECT` is answered `501`.
- `serviceModel S` is the result as a model over `ApiSig` (the standard methods, with `PATCH`
  as the extension).
- `toTheory d` reads a document's closed-world status obligations as sentences: for each
  operation without `default`, documented statuses or a request error of the server (`400`,
  `501`, `505`).

| Result | Status |
| --- | --- |
| A service with valid responses gives a well-framed handler (`serviceHandler_wellFramed`), so it is a vanilla HTTP/1.1 implementation (`serviceModel_vanilla`) | Proved |
| A service closed for a valid document satisfies the document's theory (`closed_satisfies_theory`) | Proved |
| Hence it is extension-compliant for that theory (`serviceModel_extensionCompliant`); the pet store is an instance (`petstore_extensionCompliant`) | Proved |
| `Conforms` (media types, required headers) as sentences | Planned: needs per-status sentences |
| Request validation (`RequestConforms`) enforced by the server, with a `400` | Planned |
