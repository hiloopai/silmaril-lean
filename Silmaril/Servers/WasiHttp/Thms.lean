module

public import Silmaril.Servers.WasiHttp.Defs
public import Silmaril.Servers.Basic.Thms
import Silmaril.Proofs.Servers.WasiHttp.Codec

@[expose] public section

/-!
# The `wasi:http` proxy world: encodings and webs

* `pathOf_pathV`: a path-with-query encoded as an `option<string>` is read back.
* `wasiServerB_refines`: reading request bodies refines the reading without them, so the
  specifications of `wasiServer σ` hold of `wasiServerB σ` (`Refines.sat`).
* `webOf_pathV`: the web of a server answers an outgoing request for an encoded authority and
  path with the status of the server's answer to that `GET`. A client component under the
  outgoing theory `httpTh3 (webOf f)` (`Silmaril.Wasi.Versions.Http3`) is thus specified against
  the server `f`; composing a client with a server component is not yet modelled.
-/

namespace Silmaril.Servers.WasiHttp

open Silmaril.Wasi
open Silmaril.Net.Http (Request Response)

/-- A path read back. -/
theorem pathOf_pathV (p : Option (List UInt8)) : pathOf (some [pathV p]) = p :=
  Proofs.Servers.WasiHttp.pathOf_pathV p

/-- **The web of a server** on encoded requests. -/
theorem webOf_pathV (f : Request → Response) (a p : Option (List UInt8)) :
    webOf f (pathV a) (pathV p) = .status (BitVec.ofNat 16 (f (getAt a p)).status) := by
  simp only [webOf, pathOf_pathV]

/-- **Reading request bodies refines** the reading without them. -/
theorem wasiServerB_refines {X : Set FnName}
    (σ : Silmaril.Games.Strategy (Silmaril.Wasi.nsig proxyImports) (Silmaril.Wasi.nsig X)) :
    Refines (wasiServerB σ) (wasiServer σ) :=
  fun _ ⟨s, hs, hT, hF⟩ => ⟨s, hs, hT, hF.imp fun _ _ h => h.1⟩

end Silmaril.Servers.WasiHttp
