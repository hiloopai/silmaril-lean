module

public import Silmaril.Servers.WasiFs.Defs
public import Silmaril.Servers.State.OwnedFs.Thms
import Silmaril.Proofs.Servers.WasiFs.Store

@[expose] public section

/-!
# A file-backed `wasi:http` store: theorems (header)

PROVED (standard axioms), namespace `Silmaril.Servers.WasiFs`. Proofs in
`Silmaril.Proofs.Servers.WasiFs.{Run, Mut, Put, Store}`.

The component and its host (`Defs`): `storeBody`, a component of the `wasi:http` proxy world
that also imports `wasi:filesystem` 0.2, run over `storeHost root q fs` (the reference
`wasi:http` host for the request `q`; the `FsMore` filesystem host of the files `fs` for the
read-only calls; whole-file effects for `open-at` with `create`, `write`, `unlink-file-at`).

* **`run_spec`**: for files shorter than `2^64 - 1` octets, for every request `q`, the complete
  run of `handle` makes the response `(specStep root fs q).1` and leaves the files
  `(specStep root fs q).2`: `fileStoreStep (keyFile root)` without header fields, `413` for a
  `PUT` whose content is too long to read back.
* **`wasiStore_refines`**: the component read as a server (one atomic handler run per request,
  files kept by the host) refines `specStore`, so its histories are linearizable with respect
  to `specStep` (`wasiStore_linearizable`), whatever order the host runs and answers
  overlapping requests in.
* **`wasiStoreSmall_refines`**: on requests shorter than `2^64 - 1` octets, it refines
  `fileStoreNF`, the file-backed store `fileStore (keyFile root)` of state model (b)
  (`Silmaril.Servers.State.OwnedFs`) read without header fields.
* `wasiStore_frame`: the files that are not key files never change; `specStep_small`: a step
  keeps the files shorter than `2^64 - 1` octets.
* **`storeHost_fsOk`**: every read-only filesystem answer of the host passes the check of the
  `wasi:filesystem` 0.2 theory `Silmaril.Wasi.Versions.FsMore.fsThV v2` over `treeOf [root]`
  of the files at that point (the files of `Silmaril.Cli.Fs` as a `wasi:filesystem` tree).
* Checked by `decide` (`get_ref`, `put_ref`, …): a `GET` of a file, a `GET` of a missing file,
  a `PUT` that creates a file (and the file afterwards), a `DELETE`.

Not proved here: that the host's mutating calls satisfy a theory of `wasi:filesystem` (the
`FsMut` theory checks the tree's shape but not contents), and that the component is the
compilation of a Wasm binary (it is written as a program over the imports).
-/

namespace Silmaril.Servers.WasiFs

open Silmaril.Games Silmaril.Wasi Silmaril.Servers.WasiHttp Silmaril.Servers.WasiExamples
open Silmaril.Servers.State Silmaril.Servers.State.OwnedFs
open Silmaril.Wasm.Component (Val)
open Silmaril.Net.Http (Request Response)
open Silmaril.Cli (Fs FPath)

theorem run_spec (root : String) {fs : Fs} (hs : Small fs) (q : Request) :
    respOf 1 (runStore root fs q) = some (specStep root fs q).1 ∧
      (replay root fs (runStore root fs q)).files = (specStep root fs q).2 :=
  Proofs.Servers.WasiFs.run_spec root hs q

theorem specStep_small (root : String) {fs : Fs} (hs : Small fs) (q : Request) :
    Small (specStep root fs q).2 :=
  Proofs.Servers.WasiFs.specStep_small root hs q

theorem wasiStore_refines (root : String) {fs₀ : Fs} (h₀ : Small fs₀) :
    (wasiStore root fs₀).Refines (specStore root fs₀) :=
  (Proofs.Servers.WasiFs.storeAbs root h₀).refines

theorem wasiStore_linearizable (root : String) {fs₀ : Fs} (h₀ : Small fs₀) :
    (wasiStore root fs₀).Sat (Linearizable (Atomic.ofFun (specStep root)) fs₀) :=
  (Proofs.Servers.WasiFs.storeAbs root h₀).sat_linearizable

theorem wasiStoreSmall_refines (root : String) {fs₀ : Fs} (h₀ : Small fs₀) :
    (wasiStoreSmall root fs₀).Refines (fileStoreNF root fs₀) :=
  (Proofs.Servers.WasiFs.storeSmallAbs root h₀).refines

theorem wasiStore_frame (root : String) {fs₀ : Fs} (h₀ : Small fs₀) {c : Conf Fs Request Response}
    (hc : (wasiStore root fs₀).Reach c) : Frame (keyFile root) fs₀ c.st :=
  ((Proofs.Servers.WasiFs.storeAbs root h₀).reach_inv hc).2

theorem storeHost_fsOk (root : String) (q : Request) (fs : Fs) (past : List WEv) (f : FnName)
    (a : List Val) (hf : f ∈ fsList) (hm : mutating f a = false) :
    Versions.FsMore.fsOk Versions.FsMore.v2 (treeOf [root] (replay root fs past).files)
      (Versions.FsMore.fsState Versions.FsMore.v2 (treeOf [root] (replay root fs past).files)
        (fsEvents past))
      (.imp f a (storeHost root q fs past f a)) = true :=
  Proofs.Servers.WasiFs.storeHost_fsOk root q fs past f a hf hm

/-! ## Checked runs -/

/-- A request for a method, a path and a content. -/
def reqAt (m : Silmaril.Net.Http.Method) (path : String) (c : List UInt8) : Request :=
  ⟨⟨m, ⟨none, none, some (ascii path)⟩⟩, [], c, []⟩

/-- Files with `/a` holding `hi` under the preopen `data`. -/
def fsA : Fs := Fs.ofList [(keyFile "data" (reqAt .get "/a" []).target, ascii "hi")]

theorem get_ref : respOf 1 (runStore "data" fsA (reqAt .get "/a" [])) =
    some (Response.simple 200 (ascii "hi")) := by decide

theorem get_missing_ref : respOf 1 (runStore "data" fsA (reqAt .get "/b" [])) =
    some (Response.simple 404 []) := by decide

theorem put_ref : respOf 1 (runStore "data" fsA (reqAt .put "/b" (ascii "yo"))) =
    some (Response.simple 201 []) := by decide

theorem put_files_ref :
    (replay "data" fsA (runStore "data" fsA (reqAt .put "/b" (ascii "yo")))).files
      (keyFile "data" (reqAt .get "/b" []).target) = some (ascii "yo") := by decide

theorem delete_ref : respOf 1 (runStore "data" fsA (reqAt .delete "/a" [])) =
    some (Response.simple 204 []) := by decide

end Silmaril.Servers.WasiFs
