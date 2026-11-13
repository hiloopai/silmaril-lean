module

public import Silmaril.Servers.State.Component.Defs
public import Silmaril.Cli.Files.Defs

@[expose] public section

/-!
# State model (b): WASI over a file system that the server alone edits

See `docs/projects/http-servers.md` (section "State models"). The server's state is the
contents of the files under its preopened directories (`wasmtime serve --dir`), in the file
model of the CLI work (`Silmaril.Cli.Fs`: rooted paths to contents, the shape a WASI preopen
gives). Nobody else edits these files, so the server is `Server.closed` over `Fs`; unlike
component state the files survive a fresh instance per request, since they are host state.

Two servers:

* **a static file server** (`staticServer loc fs₀`): `GET` answers `200` with the file the
  target names (`loc`), or `404`; `HEAD` the same without content; other methods `405` with
  `Allow: GET, HEAD` (RFC 9110 §15.5.6). It never writes. `docRoot root` is a target-to-file
  mapping: the path of the target (before `?`, as UTF-8; percent-decoding is not modelled), its
  components without empty and `.` components, under the preopen `root`; a path with a `..`
  component names no file.
* **a file-backed key-value store** (`fileStore enc fs₀`): `Silmaril.Net.Http.storeStep`
  implemented over files: the representation of target `t` is the file `enc t`
  (`fileStoreStep`, written against the file system, not the store). `view enc fs` is the
  store the files hold, and `Frame enc fs₀ fs` the file-system-state invariant: every file
  that is not the file of some key is as it was in `fs₀`.

The theorems (`OwnedFs/Thms.lean`) read these as the other state models: the file store, for
an injective layout `enc`, refines the component-state store `Component.kvServer (view enc
fs₀)` (history inclusion) and keeps `Frame`; the static server refines the stateless server
that answers from `fs₀`.

A Silmaril addition.
-/

namespace Silmaril.Servers.State.OwnedFs

open Silmaril.Net.Http Silmaril.Net.Http.Field Silmaril.Cli

/-! ## Static files -/

/-- `Allow: GET, HEAD` (RFC 9110 §10.2.1). -/
def allowGetHead : Line := ⟨Method.ascii "Allow", Method.ascii "GET, HEAD"⟩

/-- The answer to `GET` for the file contents `body` (`none`: no file). -/
def getAnswer : Option (List UInt8) → Response
  | some c => Response.simple Status.ok c
  | none => Response.simple Status.notFound []

/-- **The static file server's answer** to `r` with the files `fs`, files located by `loc`. -/
def staticAnswer (loc : Target → Option FPath) (fs : Fs) (r : Request) : Response :=
  match r.method with
  | .get => getAnswer ((loc r.target).bind fs)
  | .head => (getAnswer ((loc r.target).bind fs)).stripContent
  | _ => ⟨Status.methodNotAllowed, [allowGetHead], [], []⟩

/-- One step of the static file server: answer, files unchanged. -/
def staticStep (loc : Target → Option FPath) (fs : Fs) (r : Request) : Response × Fs :=
  (staticAnswer loc fs r, fs)

/-- **The static file server** over files nobody else edits. -/
def staticServer (loc : Target → Option FPath) (fs₀ : Fs) : Server Request Response :=
  Server.closed (Atomic.ofFun (staticStep loc)) fs₀

/-- The stateless specification: answer as the static server does with the files `fs₀`. -/
def staticSpec (loc : Target → Option FPath) (fs₀ : Fs) : Atomic Unit Request Response :=
  Atomic.ofRel fun r resp => resp = staticAnswer loc fs₀ r

/-- The path part of a path-with-query: the octets before `?`. -/
def pathPart (pq : List UInt8) : List UInt8 := pq.takeWhile (· ≠ 0x3F)

/-- **A document root**: the file under the preopen `root` that a target's path names. -/
def docRoot (root : String) (t : Target) : Option FPath :=
  match t.pathWithQuery with
  | none => none
  | some pq =>
    match String.fromUTF8? ⟨(pathPart pq).toArray⟩ with
    | none => none
    | some s => if ".." ∈ pathComps s then none else some ⟨root, pathComps s⟩

/-! ## A file-backed key-value store -/

/-- The store the files hold, with the file `enc t` holding the representation of `t`. -/
def view (enc : Target → FPath) (fs : Fs) : Store := fun t => fs (enc t)

/-- **One step of the file-backed store**: `storeStep`, reading and writing the file `enc t`. -/
def fileStoreStep (enc : Target → FPath) (fs : Fs) (r : Request) : Response × Fs :=
  match r.method with
  | .get => (getAnswer (fs (enc r.target)), fs)
  | .head => ((getAnswer (fs (enc r.target))).stripContent, fs)
  | .put =>
    (Response.simple (if (fs (enc r.target)).isSome then Status.noContent else Status.created) [],
      fs.set (enc r.target) (some r.content))
  | .delete =>
    match fs (enc r.target) with
    | some _ => (Response.simple Status.noContent [], fs.set (enc r.target) none)
    | none => (Response.simple Status.notFound [], fs)
  | .options => (⟨Status.noContent, [allowLine], [], []⟩, fs)
  | .post | .connect | .trace | .patch => (⟨Status.methodNotAllowed, [allowLine], [], []⟩, fs)
  | .other _ => (Response.simple Status.notImplemented [], fs)

/-- **The file-backed store** over files nobody else edits. -/
def fileStore (enc : Target → FPath) (fs₀ : Fs) : Server Request Response :=
  Server.closed (Atomic.ofFun (fileStoreStep enc)) fs₀

/-- **The file-system-state invariant**: every file that holds no key is as in `fs₀`. -/
def Frame (enc : Target → FPath) (fs₀ fs : Fs) : Prop :=
  ∀ p, (∀ t, enc t ≠ p) → fs p = fs₀ p

end Silmaril.Servers.State.OwnedFs
