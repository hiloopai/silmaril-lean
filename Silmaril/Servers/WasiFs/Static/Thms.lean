module

public import Silmaril.Servers.WasiFs.Static.Defs
public import Silmaril.Servers.WasiFs.Thms
public import Silmaril.Servers.State.SharedFs.Thms
public meta import Silmaril.Servers.WasiFs.Static.Defs
import Silmaril.Proofs.Servers.WasiFs.Static

@[expose] public section

/-!
# The static file server as a `wasi:http` component: theorems (header)

PROVED (standard axioms) **conditionally on the open `Task.staticRuns root`**, namespace
`Silmaril.Servers.WasiFs`. Proofs in `Silmaril.Proofs.Servers.WasiFs.Static`.

* **`wasiStatic_refines_of`**: the static component over files nobody else edits refines the
  static file server `staticServer (docRoot root) fs₀` of state model (b), so (with
  `static_refines`) the stateless server of its files;
* **`wasiStaticShared_safe_of`**: over files that others change, keeping an invariant `I`
  (which implies short files and no file at the preopen), each response is the static
  server's answer from some files satisfying `I`, and the histories are linearizable with
  respect to that loose specification `staticSafe` of state model (c)
  (`wasiStaticShared_linearizable_of`).

Checked by `#guard` (evaluated, not proved): a `GET` of a nested file through `.` and empty
components with a query, a `..` path, the preopen itself, a directory, a missing file, a
`HEAD`, and a `DELETE` answered `405` with `Allow: GET, HEAD`. (`decide` does not reduce the
UTF-8 decoding of `docRoot`.)
-/

namespace Silmaril.Servers.WasiFs

open Silmaril.Servers.State Silmaril.Servers.State.OwnedFs Silmaril.Servers.State.SharedFs
open Silmaril.Servers.WasiHttp Silmaril.Servers.WasiExamples
open Silmaril.Net.Http (Request Response Target)
open Silmaril.Cli (Fs FPath)

theorem wasiStatic_refines_of {root : String} (ht : Task.staticRuns root) {fs₀ : Fs}
    (h₀ : Small fs₀) (hr : RootDir root fs₀) :
    (wasiStatic root fs₀).Refines (staticServer (docRoot root) fs₀) :=
  (Proofs.Servers.WasiFs.Static.staticAbs ht h₀ hr).refines

theorem wasiStaticShared_linearizable_of {root : String} (ht : Task.staticRuns root)
    {fs₀ : Fs} {E : Fs → Fs → Prop} {I : Fs → Prop} (hI : ∀ fs, I fs → Small fs ∧ RootDir root fs)
    (h₀ : I fs₀) (hE : Keeps E I) :
    (wasiStaticShared root fs₀ E).Sat (Linearizable (staticSafe (docRoot root) I) ()) :=
  (Proofs.Servers.WasiFs.Static.sharedAbs ht hI h₀ hE).sat_linearizable

theorem wasiStaticShared_safe_of {root : String} (ht : Task.staticRuns root) {fs₀ : Fs}
    {E : Fs → Fs → Prop} {I : Fs → Prop} (hI : ∀ fs, I fs → Small fs ∧ RootDir root fs)
    (h₀ : I fs₀) (hE : Keeps E I) {H : Hist Request Response}
    (hH : (wasiStaticShared root fs₀ E).Hists H) {i : Nat} {r : Request} {s : Response}
    (hc : Ev.call i r ∈ H) (hs : Ev.ret i s ∈ H) :
    ∃ fs, I fs ∧ s = staticAnswer (docRoot root) fs r :=
  let ⟨_, _, h⟩ := (Proofs.Servers.WasiFs.Static.sharedAbs ht hI h₀ hE).sat_answer hH hc hs; h

/-! ## Checked runs -/

/-- Files under the preopen `www`: `index.txt` and `a/b.txt`. -/
def fsW : Fs := Fs.ofList [(⟨"www", ["index.txt"]⟩, ascii "top"), (⟨"www", ["a", "b.txt"]⟩, ascii "deep")]

#guard respOf 1 (runStatic "www" fsW (pathReq .get "/a//./b.txt?x=1")) ==
  some (Response.simple 200 (ascii "deep"))
#guard respOf 1 (runStatic "www" fsW (pathReq .get "/a/../index.txt")) ==
  some (Response.simple 404 [])
#guard respOf 1 (runStatic "www" fsW (pathReq .get "/")) == some (Response.simple 404 [])
#guard respOf 1 (runStatic "www" fsW (pathReq .get "/a")) == some (Response.simple 404 [])
#guard respOf 1 (runStatic "www" fsW (pathReq .get "/missing")) == some (Response.simple 404 [])
#guard respOf 1 (runStatic "www" fsW (pathReq .head "/index.txt")) ==
  some (Response.simple 200 [])
#guard respOf 1 (runStatic "www" fsW (pathReq .delete "/index.txt")) ==
  some ⟨405, [allowGetHead], [], []⟩
#guard ∀ q ∈ [pathReq .get "/index.txt", pathReq .get "/a/b.txt", pathReq .get "/x/../a/b.txt",
    pathReq .head "/a/b.txt", pathReq .put "/index.txt", pathReq .get "/a//b.txt?q"],
  respOf 1 (runStatic "www" fsW q) == some (staticAnswer (docRoot "www") fsW q) &&
    (replay "www" fsW (runStatic "www" fsW q)).files ⟨"www", ["index.txt"]⟩ == fsW ⟨"www", ["index.txt"]⟩

end Silmaril.Servers.WasiFs
