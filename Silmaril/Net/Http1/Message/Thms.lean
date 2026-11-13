module

public import Silmaril.Proofs.Net.Http1.Message

/-!
# HTTP/1.1 message heads: laws

Proofs in `Silmaril/Proofs/Net/Http1/Message.lean`. For the grammars of
`Silmaril.Net.Http1.Message.Defs` (RFC 9112 §2–§5):

* **Round trips** `parseRequestHead_encode`, `parseResponseHead_encode`: for a valid head
  `h` and any octets `rest` (the body), the parser returns `h` and stops after
  `encRequestHead h` (resp. `encResponseHead h`).
* **Soundness** `parseRequestHead_sound`, `parseResponseHead_sound`: a parsed head is valid
  (token method, `VCHAR` target, digit versions, 3-digit code, token field names, RFC 9110
  §5.5 field values), and the consumed octets are a start line followed by a
  `FieldSection`.
* **Grammar characterisations** `Grammar.fieldLine_G_iff` (RFC 9112 §5 `field-line` with
  `OWS` stripped), `Grammar.fields_G_iff` (the depth bound only bounds the line count),
  introduction `Grammar.*_G` and elimination `Grammar.*_valid` lemmas.
* **Trimming** `trimOWS_SP`, `trimOWS_valid`; **unambiguity** `requestHead_functional`.
-/
