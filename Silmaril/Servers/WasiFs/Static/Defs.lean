module

public import Silmaril.Servers.WasiFs.Defs
public import Silmaril.Servers.State.SharedFs.Defs

@[expose] public section

/-!
# The static file server as a `wasi:http` component

See `docs/projects/http-servers.md` (section "State models"). The static file server of state
model (b) (`Silmaril.Servers.State.OwnedFs.staticAnswer (docRoot root)`) written as a component
of the store's world (`Silmaril.Servers.WasiFs`: the proxy slice and `wasi:filesystem` 0.2), run
over the same host `storeHost root q fs`. `tests/servers/wasi-http/static.wat` is the same
program in WAT, served by `wasmtime serve` in the conformance harness.

* `staticName p`: the relative path the path-with-query `p` names: the components of
  `docRoot` joined by `/`, or none (no path, not UTF-8, a `..` component, or no component: the
  preopen itself is not a file);
* `staticBody`: `method()`; for `GET` and `HEAD`, `path-with-query()`, then `get-directories`,
  `open-at` and one `read` of the whole file: `200` with the contents (none for `HEAD`), `404`
  for no name or any error; other methods `405` with `Allow: GET, HEAD`;
* `staticHandler root`, `wasiStatic root fs₀`: the component read as a server whose files
  nobody else edits; `wasiStaticShared root fs₀ E`: over files that others change (state model
  (c));
* `Task.staticRuns root` (**open**): from short files with no file at the preopen itself, the
  run of `handle` answers `staticAnswer (docRoot root) fs q` (with its `Allow` field: the
  `wasi:http` reading observes header fields) and leaves the files. The theorems (`Thms`) are
  conditional on it; it is checked on examples.

A Silmaril addition.
-/

namespace Silmaril.Servers.WasiFs

open Silmaril.Games Silmaril.Wasi Silmaril.Servers.WasiHttp Silmaril.Servers.WasiExamples
open Silmaril.Servers.State Silmaril.Servers.State.OwnedFs
open Silmaril.Wasm.Component (Val)
open Silmaril.Net.Http (Request Response Method Target)
open Silmaril.Cli (Fs FPath)
open Silmaril.Wasi.Versions.FsMore (Comp)

/-- **The relative path a path-with-query names**, components joined by `/`. -/
def staticName (p : Option (List UInt8)) : Option Comp :=
  match docRoot "" ⟨none, none, p⟩ with
  | some ⟨_, rel@(_ :: _)⟩ => some (String.intercalate "/" rel).toList
  | _ => none

/-- `GET` (`head = false`) and `HEAD` of the file named `name`. -/
def staticGet (o : BitVec 32) (name : Option Comp) (head : Bool) : BProg storeImports :=
  match name with
  | none => answerS o (Response.simple 404 [])
  | some n =>
    .call (sop getDirs (a := [])) fun nd =>
    .call (sop openAt (a := openArgs (preOf nd) n false)) fun no =>
    match openFd no with
    | some fd =>
      .call (sop fdRead (a := [.u32 fd, .u64 (BitVec.ofNat 64 maxRead), .u64 0])) fun nr =>
      match readData nr with
      | some c => answerS o (Response.simple 200 (if head then [] else c))
      | none => answerS o (Response.simple 404 [])
    | none => answerS o (Response.simple 404 [])

/-- **The static file server component.** -/
def staticBody : Body storeImports storeWorld.exports := fun q =>
  .call (sop reqMethod (a := [.u32 (reqOf q.2)])) fun nm =>
  match kindAns nm with
  | some .get => .call (sop reqPath (a := [.u32 (reqOf q.2)])) fun np =>
    staticGet (outOf q.2) (staticName (pathOf np)) false
  | some .head => .call (sop reqPath (a := [.u32 (reqOf q.2)])) fun np =>
    staticGet (outOf q.2) (staticName (pathOf np)) true
  | _ => answerS (outOf q.2) ⟨Silmaril.Net.Http.Status.methodNotAllowed, [allowGetHead], [], []⟩

/-- The events of the run of `handle(0, 1)` for `q` with the files `fs`. -/
def runStatic (root : String) (fs : Fs) (q : Request) : List WEv :=
  (Calls.runP (storeHost root q fs) [] (staticBody handleQ)).1

/-- **The static component as an atomic handler.** -/
def staticHandler (root : String) : Atomic Fs Request Response := fun fs q resp fs' =>
  respOf 1 (runStatic root fs q) = some resp ∧ fs' = (replay root fs (runStatic root fs q)).files

/-- **The static component as a server** over files nobody else edits. -/
def wasiStatic (root : String) (fs₀ : Fs) : Server Request Response :=
  Server.closed (staticHandler root) fs₀

/-- **The static component over files that others change.** -/
def wasiStaticShared (root : String) (fs₀ : Fs) (E : Fs → Fs → Prop) :
    Server Request Response :=
  ⟨Fs, staticHandler root, E, fs₀⟩

/-- No file at the preopen itself (a directory). -/
def RootDir (root : String) (fs : Fs) : Prop := fs ⟨root, []⟩ = none

/-- **Open**: the run of the static component answers as the static file server and leaves
the files. -/
def Task.staticRuns (root : String) : Prop :=
  ∀ fs q, Small fs → RootDir root fs →
    respOf 1 (runStatic root fs q) = some (staticAnswer (docRoot root) fs q) ∧
      (replay root fs (runStatic root fs q)).files = fs

/-- A request with a method and a path, no fields, no content. -/
def pathReq (m : Method) (path : String) : Request :=
  ⟨⟨m, ⟨none, none, some (ascii path)⟩⟩, [], [], []⟩

end Silmaril.Servers.WasiFs
