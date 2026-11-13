module

public import Silmaril.Servers.WasiHttp.Defs
import Silmaril.Proofs.Servers.WasiHttp.Codec

@[expose] public section

/-!
# The `wasi:http` proxy world: encodings and webs

* `pathOf_pathV`: a path-with-query encoded as an `option<string>` is read back.
* `webOf_pathV`: the web of a server answers an outgoing request for an encoded authority and
  path with the status of the server's answer to that `GET`. A client component under the
  outgoing theory `httpTh3 (webOf f)` (`Silmaril.Wasi.Versions.Http3`) is thus specified against
  the server `f`; composing a client with a server component is not yet modelled.
-/

namespace Silmaril.Servers.WasiHttp

open Silmaril.Net.Http (Request Response)

/-- A path read back. -/
theorem pathOf_pathV (p : Option (List UInt8)) : pathOf (some [pathV p]) = p :=
  Proofs.Servers.WasiHttp.pathOf_pathV p

/-- **The web of a server** on encoded requests. -/
theorem webOf_pathV (f : Request → Response) (a p : Option (List UInt8)) :
    webOf f (pathV a) (pathV p) = .status (BitVec.ofNat 16 (f (getAt a p)).status) := by
  simp only [webOf, pathOf_pathV]

end Silmaril.Servers.WasiHttp
