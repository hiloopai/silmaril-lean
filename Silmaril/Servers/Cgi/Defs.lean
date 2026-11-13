module

public import Silmaril.Net.Http.Exchange.Defs
public import Silmaril.Cli.Behaviour.Defs

@[expose] public section

/-!
# CGI: an HTTP server as a command-line program per request (RFC 3875)

The Common Gateway Interface (CGI/1.1, RFC 3875) runs a script once per request: the request
is passed as **meta-variables** in the environment (§4.1) and the request content on standard
input (§4.2), and the script writes a **CGI response** on standard output: header fields, a
blank line, then the content (§6). WAGI (the WebAssembly Gateway Interface) runs WASI command
modules the same way. So a CGI server is a `Silmaril.Cli.Spec` (a behaviour of command-line
programs, at the full level of `Silmaril.Cli.Institution`) read through a gateway:

* `Gateway`: the program name and the declared roots (WASI preopens) the script is given;
* `metaVars r`: the meta-variables of a request: `GATEWAY_INTERFACE`, `REQUEST_METHOD`,
  `PATH_INFO`, `QUERY_STRING`, `SERVER_PROTOCOL`, `CONTENT_LENGTH` and one `HTTP_*` variable per
  header field (§4.1.18: "converted to upper case, has all occurrences of "-" replaced with "_"
  and has "HTTP_" prepended");
* `input g fs r`: the invocation for a request with the files `fs`;
* `parse out`: the CGI response read from standard output, `respond out` the response the
  gateway sends (500 when `out` is not a CGI response), `answer r resp` with the content of a
  response to `HEAD` dropped (RFC 9110 §9.3.2);
* **`origin g S`**: the origin (`Silmaril.Net.Http.Origin`) of the program `S`, whose state is
  the files: one request is one run of `S` on the files left by the run before. This is the
  state model of a server over a file system it alone edits; the files of other writers are
  not modelled here.

Choices where RFC 3875 leaves latitude: response lines end with LF, a CR before it is dropped
(§6 leaves `NL` system-defined); a `Status` field gives the status (§6.3.3), otherwise a
`Location` field gives 302 (a client redirect, §6.2.3) and a `Content-Type` field 200 (§6.2.1:
"status 200 'OK' is assumed if it is omitted"); a response with none of the three is not a CGI
response. The exit code is not observed. `SCRIPT_NAME` is not set: the script is mounted at the
root, so `PATH_INFO` is the whole path. Non-parsed-header scripts (§5) are not modelled.

A Silmaril addition.
-/

namespace Silmaril.Servers.Cgi

open Silmaril.Net.Http Silmaril.Net.Http.Field Silmaril.Net.Http.Abnf Silmaril.Cli

/-- Octets as a string, one character per octet. -/
def latin1 (bs : List UInt8) : String := String.ofList (bs.map fun b => Char.ofNat b.toNat)

/-- The path and the query of a `path-with-query` (split at the first `?`). -/
def splitQuery (pq : List UInt8) : List UInt8 × List UInt8 :=
  (pq.takeWhile (· != 0x3F), (pq.dropWhile (· != 0x3F)).drop 1)

/-- The meta-variable name of a header field (§4.1.18). -/
def headerVar (name : List UInt8) : String :=
  "HTTP_" ++ latin1 (name.map fun b =>
    if 0x61 ≤ b && b ≤ 0x7A then b - 0x20 else if b == 0x2D then 0x5F else b)

/-- **The meta-variables of a request** (§4.1). -/
def metaVars (r : Request) : List (String × String) :=
  let (path, query) := splitQuery (r.target.pathWithQuery.getD [])
  [("GATEWAY_INTERFACE", "CGI/1.1"),
   ("REQUEST_METHOD", latin1 r.method.toToken),
   ("PATH_INFO", latin1 path),
   ("QUERY_STRING", latin1 query),
   ("SERVER_PROTOCOL", "HTTP/1.1")] ++
  (if r.content.isEmpty then [] else [("CONTENT_LENGTH", toString r.content.length)]) ++
  r.headers.map fun l => (headerVar l.name, latin1 l.value)

/-- A gateway: how scripts are invoked. -/
structure Gateway where
  /-- The program name (`argv[0]`). -/
  prog : String := "script"
  /-- The roots the script is given. -/
  roots : List Root := []

/-- **The invocation for a request**: meta-variables in the environment, the content on
standard input (§4.2), the files `fs`. -/
def input (g : Gateway) (fs : Fs) (r : Request) : Input :=
  { prog := g.prog, env := metaVars r, stdin := r.content, roots := g.roots, fs := fs }

/-! ## CGI responses (§6) -/

/-- The first line (before an LF) and the rest, or `none` without an LF. -/
def splitLine : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | 0x0A :: rest => some ([], rest)
  | b :: rest => (splitLine rest).map fun (l, r) => (b :: l, r)

/-- A line without a final CR. -/
def dropCR (l : List UInt8) : List UInt8 := if l.getLast? = some 0x0D then l.dropLast else l

/-- The header lines up to the blank line, and the content after it (`fuel` bounds the number
of lines). -/
def headerLines : Nat → List UInt8 → Option (List (List UInt8) × List UInt8)
  | 0, _ => none
  | fuel + 1, bs =>
    match splitLine bs with
    | none => none
    | some (l, rest) =>
      if dropCR l = [] then some ([], rest)
      else (headerLines fuel rest).map fun (ls, body) => (dropCR l :: ls, body)

/-- A header line `name: value` (leading blanks of the value dropped). -/
def parseField (l : List UInt8) : Option Line :=
  let name := l.takeWhile (· != 0x3A)
  let rest := l.dropWhile (· != 0x3A)
  if name.isEmpty || rest.isEmpty then none
  else some ⟨name, (rest.drop 1).dropWhile (fun b => b == 0x20 || b == 0x09)⟩

/-- The status code at the start of a `Status` value (`status-code SP reason-phrase`). -/
def parseStatus (v : List UInt8) : Option Status :=
  match v with
  | a :: b :: c :: _ =>
    if [a, b, c].all (fun d => 0x30 ≤ d && d ≤ 0x39) then
      some ((a.toNat - 0x30) * 100 + (b.toNat - 0x30) * 10 + (c.toNat - 0x30))
    else none
  | _ => none

/-- The response of header fields and content (§6.2, §6.3.3). -/
def toResponse (fields : List Line) (body : List UInt8) : Option Response :=
  let rest := Section.remove fields (Method.ascii "Status")
  match fields.find? (fun l => eqIgnoreCase l.name (Method.ascii "Status")) with
  | some l => (parseStatus l.value).map fun c => ⟨c, rest, body, []⟩
  | none =>
    if Section.has rest (Method.ascii "Location") then some ⟨302, rest, body, []⟩
    else if Section.has rest (Method.ascii "Content-Type") then some ⟨Status.ok, rest, body, []⟩
    else none

/-- **The CGI response on standard output**, if it is one. -/
def parse (out : List UInt8) : Option Response := do
  let (ls, body) ← headerLines (out.length + 1) out
  let fields ← ls.mapM parseField
  toResponse fields body

/-- 500 (Internal Server Error, RFC 9110 §15.6.1). -/
def internalError : Response := Response.simple 500 []

/-- The response the gateway sends for standard output `out`. -/
def respond (out : List UInt8) : Response := (parse out).getD internalError

/-- The response sent for `r`: without content for `HEAD` (RFC 9110 §9.3.2). -/
def answer (r : Request) (resp : Response) : Response :=
  if r.method = .head then resp.stripContent else resp

/-- **The origin of a CGI program**: its state is the files; one request is one run. -/
def origin (g : Gateway) (S : Spec) : Origin Fs := fun fs r resp fs' =>
  ∃ o, S (input g fs r) o ∧ resp = answer r (respond o.stdout) ∧ fs' = o.fs

/-! ## Hello -/

/-- The output of the hello script. -/
def helloOut : List UInt8 := Method.ascii "Content-Type: text/plain\n\nhello\n"

/-- **The hello script**: prints `helloOut`, exits 0, leaves the files. -/
def hello : Spec := Spec.prints fun _ => helloOut

/-- The response of the hello script. -/
def helloResponse : Response :=
  ⟨Status.ok, [⟨Method.ascii "Content-Type", Method.ascii "text/plain"⟩],
    Method.ascii "hello\n", []⟩

end Silmaril.Servers.Cgi
