module

public import Silmaril.Net.Http3.Frame.Defs

@[expose] public section

/-!
# WebTransport over HTTP/3: error codes (draft-ietf-webtrans-http3-17 §4.4, §9.5)

**Version.** This library models draft-ietf-webtrans-http3-17 (in IETF Working Group Last Call
as of November 2026; not an RFC). Every codepoint below is the one of draft -17 and may change
before RFC publication; earlier drafts' codepoints are not modelled.

**Protocol error codes (§9.5).** `WT_BUFFERED_STREAM_REJECTED` (`0x3994bd84`),
`WT_SESSION_GONE` (`0x170d7b68`), `WT_FLOW_CONTROL_ERROR` (`0x045d4487`), `WT_ALPN_ERROR`
(`0x0817b3dd`), `WT_REQUIREMENTS_NOT_MET` (`0x212c0d48`): HTTP/3 error codes (RFC 9114 §8).

**Application error codes (§4.4).** "WebTransport application errors for streams are limited
to an unsigned 32-bit integer, assuming values between 0x00000000 and 0xffffffff. WebTransport
implementations MUST remap those error codes into the error range reserved for
WT_APPLICATION_ERROR, where 0x00000000 corresponds to 0x52e4a40fa8db, and 0xffffffff
corresponds to 0x52e5ac983162. Note that there are codepoints inside that range of form
'0x1f * N + 0x21' that are reserved by Section 8.1 of [HTTP3]; those have to be skipped when
mapping the error codes". Figure 4 of the draft gives the conversion:

```
first = 0x52e4a40fa8db
last = 0x52e5ac983162
def webtransport_code_to_http_code(n):
    return first + n + floor(n / 0x1e)
def http_code_to_webtransport_code(h):
    assert(first <= h <= last)
    assert((h - 0x21) % 0x1f != 0)
    shifted = h - first
    return shifted - floor(shifted / 0x1f)
```

`toHttp` and `ofHttp` are those two functions, with the assertions turned into `none`: "If a
RESET_STREAM, RESET_STREAM_AT, or STOP_SENDING frame is received with an error code outside the
range reserved for WT_APPLICATION_ERROR, the stream is still considered reset, but the error
code is not mapped to a WebTransport application error code." The grease test is
`Silmaril.Net.Http3.isGrease`.
-/

namespace Silmaril.Net.WebTransport

open Silmaril.Net.Http3

/-- WebTransport's HTTP/3 error codes (draft -17 §9.5). -/
inductive ErrorCode where
  /-- Data stream rejected for lack of an associated session (§4.6). -/
  | bufferedStreamRejected
  /-- Data stream aborted because its session is gone (§6). -/
  | sessionGone
  /-- A session-level flow control limit was violated (§5). -/
  | flowControlError
  /-- Application protocol negotiation failed (§3.3). -/
  | alpnError
  /-- The peer lacks the SETTINGS or transport parameters WebTransport needs (§3.1). -/
  | requirementsNotMet
  deriving DecidableEq, Repr, Inhabited

namespace ErrorCode

def code : ErrorCode → Nat
  | bufferedStreamRejected => 0x3994bd84
  | sessionGone => 0x170d7b68
  | flowControlError => 0x045d4487
  | alpnError => 0x0817b3dd
  | requirementsNotMet => 0x212c0d48

def all : List ErrorCode :=
  [bufferedStreamRejected, sessionGone, flowControlError, alpnError, requirementsNotMet]

/-- The error of a code, `none` for codes that are not WebTransport protocol errors. -/
def ofCode (n : Nat) : Option ErrorCode := all.find? (·.code == n)

end ErrorCode

/-! ## Application error codes (§4.4) -/

/-- The first HTTP/3 code of the `WT_APPLICATION_ERROR` range. -/
def appFirst : Nat := 0x52e4a40fa8db

/-- The last HTTP/3 code of the `WT_APPLICATION_ERROR` range. -/
def appLast : Nat := 0x52e5ac983162

/-- A WebTransport application error code: an unsigned 32-bit integer. -/
def AppCode (n : Nat) : Prop := n < 2 ^ 32

instance (n : Nat) : Decidable (AppCode n) := inferInstanceAs (Decidable (n < 2 ^ 32))

/-- `webtransport_code_to_http_code` (Figure 4): one code is skipped after every 30, so the
grease code points of the range are never produced. -/
def toHttp (n : Nat) : Nat := appFirst + n + n / 0x1e

/-- `http_code_to_webtransport_code` (Figure 4), `none` outside the range or on a grease code
point. -/
def ofHttp (h : Nat) : Option Nat :=
  if appFirst ≤ h && h ≤ appLast && !isGrease h then
    let shifted := h - appFirst
    some (shifted - shifted / 0x1f)
  else none

/-- An HTTP/3 code in the `WT_APPLICATION_ERROR` range (§9.5: "0x52e4a40fa8db to
0x52e5ac983162 inclusive, with the exception of the codepoints of form 0x1f * N + 0x21"). -/
def isAppRange (h : Nat) : Bool := appFirst ≤ h && h ≤ appLast && !isGrease h

/-- What an application learns from a stream reset's HTTP/3 error code (§4.4): its application
error code, or `none` ("a stream reset with no application error code"). -/
def resetAppCode (h : Nat) : Option Nat := ofHttp h

end Silmaril.Net.WebTransport
