module

public import Silmaril.Servers.WasiFs.Defs
public import Silmaril.Servers.State.Reduct.Defs

@[expose] public section

/-!
# The file-backed `wasi:http` store as the component-state key-value store

See `docs/projects/http-servers.md` (section "State models"). The store component of
`Silmaril.Servers.WasiFs` keeps the representation of target `t` in the file
`keyFile root t`, whose name `keyName` is built from the path-with-query of `t` alone. So
targets that differ only in their scheme or authority share a file, and the store is the
key-value store of state model (a) (`Component.kv`, `Silmaril.Net.Http.storeStep`) **on
targets in origin form**: a request is handled as the request with its target reduced to its
path-with-query (`originForm`, `normReq`; RFC 9112 §3.2.1 calls a target of that shape the
origin form). This module states that specification:

* `viewN root fs`: the store the files hold, read on targets in origin form (other targets
  hold nothing);
* `kvNF`: `kv` on short requests (`smallReq`), with requests read through `normReq` and
  responses through `noFields` (the `wasi:http` reading observes no header fields);
  `Server.comap` of `Silmaril.Servers.State.Reduct`.

A Silmaril addition.
-/

namespace Silmaril.Servers.WasiFs

open Silmaril.Servers.State Silmaril.Servers.State.OwnedFs Silmaril.Servers.State.Component
open Silmaril.Net.Http (Request Response Target Store storeStep)
open Silmaril.Cli (Fs FPath)

/-- **The origin form of a target**: its path-with-query alone. -/
def originForm (t : Target) : Target := ⟨none, none, t.pathWithQuery⟩

/-- A request with its target in origin form. -/
def normReq (r : Request) : Request :=
  ⟨⟨r.method, originForm r.target⟩, r.headers, r.content, r.trailers⟩

/-- **The store the files hold**, on targets in origin form. -/
def viewN (root : String) (fs : Fs) : Store :=
  fun t => if originForm t = t then fs (keyFile root t) else none

/-- **The specification**: the key-value store on short requests, read on targets in origin
form and without header fields. -/
def kvNF : Atomic Store Request Response := (kv.guard smallReq).comap normReq noFields

end Silmaril.Servers.WasiFs
