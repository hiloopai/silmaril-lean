module

public import Silmaril.Net.Http.Field.Defs

@[expose] public section

/-!
# HTTP status codes (RFC 9110 §15)

"The status code of a response is a three-digit integer code" (§15); "Values outside the
range 100..599 are invalid" (§15). The first digit is the class (§15):

* 1xx informational (§15.2), 2xx successful (§15.3), 3xx redirection (§15.4),
  4xx client error (§15.5), 5xx server error (§15.6).

A status code is a `Nat` (WASI's `status-code` is a `u16`, so it may be outside the range;
`Status.isValid` checks it). `Status.reason?` is the registered reason phrase of the codes of
§15.2–§15.6, `isFinal` (§15: a 1xx response is interim, all others final),
`isHeuristicallyCacheable` (§15.1: "200, 203, 204, 206, 300, 301, 308, 404, 405, 410, 414, and
501") and `allowsContent` (§6.4.1: responses to HEAD, 1xx, 204 and 304 have no content).
-/

namespace Silmaril.Net.Http

/-- A status code (§15). -/
abbrev Status := Nat

/-- The class of a status code (§15). -/
inductive StatusClass where
  | informational | successful | redirection | clientError | serverError
  deriving DecidableEq, Repr

namespace Status

/-- In `100..599` (§15). -/
def isValid (s : Nat) : Bool := 100 ≤ s && s ≤ 599

/-- The class of a valid status code: its first digit (§15). -/
def class? (s : Nat) : Option StatusClass :=
  match s / 100 with
  | 1 => some .informational
  | 2 => some .successful
  | 3 => some .redirection
  | 4 => some .clientError
  | 5 => some .serverError
  | _ => none

/-- Final (not interim) (§15, §15.2). -/
def isFinal (s : Nat) : Bool := class? s != some .informational

/-- The status codes defined by RFC 9110, with their reason phrases (§15.2–§15.6). -/
def registered : List (Status × String) :=
  [(100, "Continue"), (101, "Switching Protocols"),
   (200, "OK"), (201, "Created"), (202, "Accepted"), (203, "Non-Authoritative Information"),
   (204, "No Content"), (205, "Reset Content"), (206, "Partial Content"),
   (300, "Multiple Choices"), (301, "Moved Permanently"), (302, "Found"), (303, "See Other"),
   (304, "Not Modified"), (305, "Use Proxy"), (306, "(Unused)"), (307, "Temporary Redirect"),
   (308, "Permanent Redirect"),
   (400, "Bad Request"), (401, "Unauthorized"), (402, "Payment Required"), (403, "Forbidden"),
   (404, "Not Found"), (405, "Method Not Allowed"), (406, "Not Acceptable"),
   (407, "Proxy Authentication Required"), (408, "Request Timeout"), (409, "Conflict"),
   (410, "Gone"), (411, "Length Required"), (412, "Precondition Failed"),
   (413, "Content Too Large"), (414, "URI Too Long"), (415, "Unsupported Media Type"),
   (416, "Range Not Satisfiable"), (417, "Expectation Failed"), (418, "(Unused)"),
   (421, "Misdirected Request"), (422, "Unprocessable Content"), (426, "Upgrade Required"),
   (500, "Internal Server Error"), (501, "Not Implemented"), (502, "Bad Gateway"),
   (503, "Service Unavailable"), (504, "Gateway Timeout"),
   (505, "HTTP Version Not Supported")]

/-- The reason phrase of a code defined by RFC 9110. -/
def reason? (s : Nat) : Option String := (registered.find? (·.1 == s)).map (·.2)

/-- Heuristically cacheable (§15.1). -/
def isHeuristicallyCacheable (s : Nat) : Bool :=
  [200, 203, 204, 206, 300, 301, 308, 404, 405, 410, 414, 501].contains s

/-- A response with this status may have content (§6.4.1: "All 1xx (Informational), 204 (No
Content), and 304 (Not Modified) responses do not include content"). -/
def allowsContent (s : Nat) : Bool := class? s != some .informational && s != 204 && s != 304

/-- Some common codes. -/
def ok : Status := 200
/-- 404 Not Found (§15.5.5). -/
def notFound : Status := 404
/-- 201 Created (§15.3.2). -/
def created : Status := 201
/-- 204 No Content (§15.3.5). -/
def noContent : Status := 204
/-- 405 Method Not Allowed (§15.5.6). -/
def methodNotAllowed : Status := 405
/-- 501 Not Implemented (§15.6.2). -/
def notImplemented : Status := 501

end Status

end Silmaril.Net.Http
