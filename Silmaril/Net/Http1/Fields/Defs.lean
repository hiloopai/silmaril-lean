module

public import Silmaril.Net.Http1.Framing.Defs

/-!
# Field lookup and list syntax: the shared API

The HTTP/1.1 track already defines case-insensitive field lookup and the `#rule` list syntax
in `Silmaril.Net.Http1.Framing`. This module names them as the API that other tracks use
(WebSockets, CONNECT, upgrades):

| Need | Definition | Rule |
| --- | --- | --- |
| values of a field, case-insensitive name, in order | `fieldValues fs name` | RFC 9110 §5.1, §5.3 |
| elements of a `#rule` list value: split at `,`, trimmed of `OWS`, empty elements dropped | `listElements v` | RFC 9110 §5.6.1 |
| all list elements of a field (the field lines combined, §5.3) | `fieldElements fs name` | RFC 9110 §5.3, §5.6.1 |
| some element is a token, case-insensitively | `fieldHasToken fs name tok` | e.g. `Connection: Upgrade`, `Upgrade: websocket` |

All of them are structural recursions over `List UInt8` (`splitOn` is this track's own, not
`List.splitOn`), so `decide` evaluates them in the kernel. Names are octets. For a string
literal, use `ascii "Sec-WebSocket-Protocol"`.

Not covered: quoted-string elements that contain commas (RFC 9110 §5.6.4). A list element is
split at every comma, so it is correct for lists of tokens and of tokens with token
parameters, which is every list the HTTP/1.1, WebSocket and CONNECT rules read.
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse (Bytes)

/-- Some list element of the fields named `name` equals `tok`, ASCII case-insensitively. -/
def fieldHasToken (fs : List FieldLine) (name tok : Bytes) : Bool :=
  (fieldElements fs name).any fun e => lower e == lower tok

end Silmaril.Net.Http1
