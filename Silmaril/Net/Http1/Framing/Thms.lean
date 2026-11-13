module

public import Silmaril.Proofs.Net.Http1.Framing

/-!
# HTTP/1.1 message framing: laws

Proofs in `Silmaril/Proofs/Net/Http1/Framing.lean`, for RFC 9112 §6.3:

* **Round trips** `parseRequestAt_encode`, `parseResponseAt_encode`: on a connection carrying
  `pre ++ encRequest h b ++ rest`, a valid head `h` whose body `b` fits the framing that the
  head announces (`Body.Fits`) is read back at `|pre|`, and the reader stops exactly where
  the next message starts (`parseRequest_encode` for a single message); `parseBody_encode`.
* **Soundness** `parseRequestAt_sound`: a request read from any buffer has a valid head and
  a body fitting its framing (`parseBody_fits`), so `parseRequestAt_reencode`: reading,
  serializing and reading again gives the same request.
* **Rules** `responseBodyLength_HEAD`, `responseBodyLength_noContent` (no body for `HEAD`,
  `1xx`, `204`, `304`), `bodyLengthOfFields_chunked` (`Transfer-Encoding` ending in
  `chunked` overrides `Content-Length`), `requestBodyLength_framed` (requests are never
  close-delimited or tunnels).
-/
