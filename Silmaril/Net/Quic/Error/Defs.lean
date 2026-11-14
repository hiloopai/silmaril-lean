module

@[expose] public section

/-!
# QUIC transport error codes (RFC 9000 §20.1)

"QUIC transport error codes and application error codes are 62-bit unsigned integers"
(RFC 9000 §20). The transport codes of §20.1 are carried in CONNECTION_CLOSE frames of type
`0x1c` (§19.19); they are the errors the rest of `Silmaril.Net.Quic` reports:

| Code | Name |
| --- | --- |
| 0x00 | NO_ERROR |
| 0x01 | INTERNAL_ERROR |
| 0x02 | CONNECTION_REFUSED |
| 0x03 | FLOW_CONTROL_ERROR |
| 0x04 | STREAM_LIMIT_ERROR |
| 0x05 | STREAM_STATE_ERROR |
| 0x06 | FINAL_SIZE_ERROR |
| 0x07 | FRAME_ENCODING_ERROR |
| 0x08 | TRANSPORT_PARAMETER_ERROR |
| 0x09 | CONNECTION_ID_LIMIT_ERROR |
| 0x0a | PROTOCOL_VIOLATION |
| 0x0b | INVALID_TOKEN |
| 0x0c | APPLICATION_ERROR |
| 0x0d | CRYPTO_BUFFER_EXCEEDED |
| 0x0e | KEY_UPDATE_ERROR |
| 0x0f | AEAD_LIMIT_REACHED |
| 0x10 | NO_VIABLE_PATH |
| 0x0100–0x01ff | CRYPTO_ERROR |

"A range of 256 values is reserved for carrying error codes specific to the cryptographic
handshake" (§20.1): `cryptoError a` carries the code `0x0100 + a`.

`TransportError.ofCode` is the registry lookup; it returns `none` for codes outside the
registry (§22.5 leaves room for registrations; this model knows only RFC 9000's codes).
Application protocol error codes (§20.2: RESET_STREAM, STOP_SENDING, CONNECTION_CLOSE of type
`0x1d`) are plain numbers whose meaning "is left to application protocols".
-/

namespace Silmaril.Net.Quic

/-- The transport error codes of RFC 9000 §20.1. -/
inductive TransportError where
  | noError
  | internalError
  | connectionRefused
  | flowControlError
  | streamLimitError
  | streamStateError
  | finalSizeError
  | frameEncodingError
  | transportParameterError
  | connectionIdLimitError
  | protocolViolation
  | invalidToken
  | applicationError
  | cryptoBufferExceeded
  | keyUpdateError
  | aeadLimitReached
  | noViablePath
  /-- CRYPTO_ERROR `0x0100 + alert` (RFC 9001 §4.8 puts the TLS alert here). -/
  | cryptoError (alert : Fin 256)
  deriving DecidableEq, Repr, Inhabited

namespace TransportError

/-- The registered code (§20.1). -/
def code : TransportError → Nat
  | noError => 0x00 | internalError => 0x01 | connectionRefused => 0x02
  | flowControlError => 0x03 | streamLimitError => 0x04 | streamStateError => 0x05
  | finalSizeError => 0x06 | frameEncodingError => 0x07 | transportParameterError => 0x08
  | connectionIdLimitError => 0x09 | protocolViolation => 0x0a | invalidToken => 0x0b
  | applicationError => 0x0c | cryptoBufferExceeded => 0x0d | keyUpdateError => 0x0e
  | aeadLimitReached => 0x0f | noViablePath => 0x10
  | cryptoError a => 0x0100 + a.val

/-- The error with a code; `none` outside the §20.1 registry. -/
def ofCode (n : Nat) : Option TransportError :=
  match n with
  | 0x00 => some noError | 0x01 => some internalError | 0x02 => some connectionRefused
  | 0x03 => some flowControlError | 0x04 => some streamLimitError
  | 0x05 => some streamStateError | 0x06 => some finalSizeError
  | 0x07 => some frameEncodingError | 0x08 => some transportParameterError
  | 0x09 => some connectionIdLimitError | 0x0a => some protocolViolation
  | 0x0b => some invalidToken | 0x0c => some applicationError
  | 0x0d => some cryptoBufferExceeded | 0x0e => some keyUpdateError
  | 0x0f => some aeadLimitReached | 0x10 => some noViablePath
  | n => if h : 0x0100 ≤ n ∧ n < 0x0200 then some (cryptoError ⟨n - 0x0100, by omega⟩) else none

end TransportError

end Silmaril.Net.Quic
