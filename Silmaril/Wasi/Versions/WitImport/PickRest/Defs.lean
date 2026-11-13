module

public import Silmaril.Wasi.Versions.WitImport.Pick.Defs
public import Silmaril.Wasi.Versions.WitImport.Derived.Defs

@[expose] public section

/-!
# The keys and codes of the remaining socket and HTTP slices, below the hand-written modules

`Silmaril.Wasi.Versions.WitImport.Pick` gives the keys of the `cli`, `clocks`, `filesystem`, 0.2
TCP and HTTP request slices. This module adds the keys of the slices written after it, so
that their function sets are read from the imported tables with `pick`:

* `udpKeys` (0.2 UDP, `Net.udpImports`), `udp3Keys` (0.3 UDP, `Net.udp3Fns`);
* `dns2Keys`, `dns3Keys` (name lookup, `Net.dns2Fns`, `Net.dns3Fns`);
* `body2Keys` (0.2 response bodies, `Net.bodyFns2`, over `http2T` and `io2T`),
  `body3Keys` (0.3 response bodies, `Net.bodyFns3`);
* `req2Keys` (0.2 outgoing bodies, `Net.req2Fns`), `req3Keys` (0.3 `request.new`,
  `Net.req3Fns`).

The canonical built-ins of the 0.3 slices (`stream.read`, `future.read`, …) are not WIT
functions; the hand-written modules append them to the picked lists.

It also reads the 0.3 `ip-name-lookup` `error-code` from the resolved 0.3 sockets package
(`dnsCodes3W`), its case `other` by name (`dnsOther3W`), the translations by case name
between it and the 0.2 socket codes (`dnsE2to3W`, `dnsE3to2W`), and the code value with the
`option` payload of `other` (`dnsEcV3W`), as `Derived` does for the socket codes.

Like `Pick` and `Derived`, this module imports no hand-written WASI module.

A Silmaril addition (track `wf-p3-switch-rest` of the WASI full workflow).
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasm.Wit

/-! ## Keys -/

/-- The keys of the 0.2 UDP slice. -/
def udpKeys : List (String × String) :=
  [("wasi:sockets/instance-network", "instance-network"),
   ("wasi:sockets/udp-create-socket", "create-udp-socket"),
   ("wasi:sockets/udp", "[method]udp-socket.start-bind"),
   ("wasi:sockets/udp", "[method]udp-socket.finish-bind"),
   ("wasi:sockets/udp", "[method]udp-socket.stream"),
   ("wasi:sockets/udp", "[method]incoming-datagram-stream.receive")]

/-- The keys of the 0.3 UDP slice. -/
def udp3Keys : List (String × String) :=
  [("wasi:sockets/types", "[static]udp-socket.create"),
   ("wasi:sockets/types", "[method]udp-socket.bind"),
   ("wasi:sockets/types", "[method]udp-socket.receive"),
   ("wasi:sockets/types", "[method]udp-socket.send")]

/-- The keys of the 0.2 name lookup slice. -/
def dns2Keys : List (String × String) :=
  [("wasi:sockets/instance-network", "instance-network"),
   ("wasi:sockets/ip-name-lookup", "resolve-addresses"),
   ("wasi:sockets/ip-name-lookup", "[method]resolve-address-stream.resolve-next-address")]

/-- The keys of the 0.3 name lookup slice. -/
def dns3Keys : List (String × String) :=
  [("wasi:sockets/ip-name-lookup", "resolve-addresses")]

/-- The keys of the 0.2 response-body slice (`wasi:http/types` and two `wasi:io/streams` reads). -/
def body2Keys : List (String × String) :=
  [("wasi:http/types", "[method]incoming-response.consume"),
   ("wasi:http/types", "[method]incoming-body.stream"),
   ("wasi:http/types", "[static]incoming-body.finish"),
   ("wasi:http/types", "[method]future-trailers.get"),
   ("wasi:http/types", "[method]fields.entries"),
   ("wasi:io/streams", "[method]input-stream.read"),
   ("wasi:io/streams", "[method]input-stream.blocking-read")]

/-- The keys of the WIT functions of the 0.3 response-body slice. -/
def body3Keys : List (String × String) :=
  [("wasi:http/types", "[static]response.consume-body"),
   ("wasi:http/types", "[method]fields.copy-all")]

/-- The keys of the 0.2 outgoing-body functions (`wasi:http/types` and two `wasi:io/streams`
writes). -/
def req2Keys : List (String × String) :=
  [("wasi:http/types", "[method]outgoing-request.body"),
   ("wasi:http/types", "[method]outgoing-body.write"),
   ("wasi:http/types", "[static]outgoing-body.finish"),
   ("wasi:io/streams", "[method]output-stream.write"),
   ("wasi:io/streams", "[method]output-stream.blocking-write-and-flush")]

/-- The keys of the WIT functions of the 0.3 outgoing-body slice. -/
def req3Keys : List (String × String) := [("wasi:http/types", "[static]request.new")]

/-! ## The 0.3 name lookup codes -/

/-- `wasi:sockets/ip-name-lookup@0.3.2`. -/
def dnsI3 : Binary.IfaceName := ⟨⟨"wasi", "sockets", some "0.3.2"⟩, "ip-name-lookup"⟩

/-- The cases of 0.3 `ip-name-lookup.error-code`, from the WIT. -/
def dnsCodes3W : List String := caseNames (findTy sock3P.2 dnsI3 ⟨.local, "error-code"⟩)

/-- 0.3 lookup `error-code.other`, by name. -/
def dnsOther3W : Nat := caseIdx dnsCodes3W "other"

/-- A 0.2 socket code as the 0.3 lookup code of the same name (`other` without one). -/
def dnsE2to3W (k : Nat) : Nat :=
  match codes2W[k]? with
  | some n => if n ∈ dnsCodes3W then caseIdx dnsCodes3W n else dnsOther3W
  | none => dnsOther3W

/-- A 0.3 lookup code as the 0.2 socket code of the same name (`unknown` without one). -/
def dnsE3to2W (k : Nat) : Nat :=
  match dnsCodes3W[k]? with
  | some n => if n ∈ codes2W then caseIdx codes2W n else caseIdx codes2W "unknown"
  | none => caseIdx codes2W "unknown"

/-- The payload types of the 0.3 lookup `error-code` cases. -/
def dnsPayloads3W : List (Option Binary.Ty) :=
  match findTy sock3P.2 dnsI3 ⟨.local, "error-code"⟩ with
  | some (_, .variant cs) => cs.map (·.ty)
  | _ => []

/-- The value of a 0.3 lookup code: an `option` payload is `none`. -/
def dnsEcV3W (k : Nat) : Silmaril.Wasm.Component.Val :=
  match dnsPayloads3W[k]? with
  | some (some (.option _)) => .variant k (some (.variant 0 none))
  | _ => .variant k none

end Silmaril.Wasi.Versions.WitImport
