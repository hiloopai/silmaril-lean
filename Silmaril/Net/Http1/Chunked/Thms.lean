module

public import Silmaril.Proofs.Net.Http1.Chunked
public import Silmaril.Proofs.Net.Http1.ChunkExt

/-!
# The chunked transfer coding: laws

Proofs in `Silmaril/Proofs/Net/Http1/Chunked.lean`, for RFC 9112 §7.1:

* **Round trip** `parseChunked_encode`: a valid `Chunked` (nonempty chunk data, extensions
  accepted by `isChunkExt`, valid trailer fields) is decoded back from
  `pre ++ encChunked c ++ rest` at position `|pre|`, ending at `|pre| + |encChunked c|`.
* **Soundness** `parseChunked_sound`: a decoded body is valid and its octets are in the
  grammar.
* **Rechunking** `parseChunked_ofPieces` (any chunking of a byte string encodes a body whose
  content is that string), `parseChunked_rechunk` (two bodies whose chunk streams have the
  same concatenation decode to the same content), `content_ofPieces`.
* **Extensions** `isChunkExt_iff_abnf`: the automaton accepts exactly the §7.1.1 ABNF
  `ChunkExtAbnf` (proof in `Silmaril/Proofs/Net/Http1/ChunkExt.lean`).
* **Hex numerals** `hexValue_hexDigits`, `hexDigits_hex`.
-/
