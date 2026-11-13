module

public import Silmaril.Servers.State.OwnedFs.Defs
public import Silmaril.Servers.State.Component.Thms
public meta import Silmaril.Servers.State.OwnedFs.Defs
import Silmaril.Proofs.Servers.State.OwnedFs

@[expose] public section

/-!
# State model (b), a file system the server alone edits: theorems (header)

PROVED (standard axioms), namespace `Silmaril.Servers.State.OwnedFs`. Proofs in
`Silmaril.Proofs.Servers.State.OwnedFs`.

* **`fileStoreStep_view`**: for an injective layout `enc`, a step of the file-backed store,
  seen through `view enc`, is a step of `storeStep`;
* **`fileStore_refines`**: the file-backed store refines the component-state store holding
  `view enc fs₀`: every history of the one is a history of the other, so the choice between
  the two state models is invisible to clients;
* `fileStore_linearizable`: its histories are linearizable with respect to `storeStep`;
* **`fileStore_frame`**: the file-system-state invariant `Frame` holds in every reachable
  state (only files of keys are ever written);
* **`static_refines`**, **`static_answer`**: the static file server refines the stateless
  server of its files, and answers each request `r` with `staticAnswer loc fs₀ r`;
* `docRoot_safe`: `docRoot root` names only files under the preopen `root`, without `..`.
* `fileStoreStep_frame`: a step of the file-backed store writes only the files of keys.
* Checked by `#guard`: `docRoot` on a path with a query, an empty component and `.`; a
  `..` path names nothing.
-/

namespace Silmaril.Servers.State.OwnedFs

open Silmaril.Net.Http Silmaril.Cli Silmaril.Servers.State.Component

theorem fileStoreStep_view {enc : Target → FPath} (hinj : Function.Injective enc) (fs : Fs)
    (r : Request) :
    storeStep (view enc fs) r = ((fileStoreStep enc fs r).1, view enc (fileStoreStep enc fs r).2) :=
  Proofs.Servers.State.OwnedFs.fileStoreStep_view hinj fs r

theorem fileStoreStep_frame (enc : Target → FPath) (fs : Fs) (r : Request) (p : FPath)
    (hp : ∀ t, enc t ≠ p) : (fileStoreStep enc fs r).2 p = fs p :=
  Proofs.Servers.State.OwnedFs.fileStoreStep_frame enc fs r p hp

theorem fileStore_refines {enc : Target → FPath} (hinj : Function.Injective enc) (fs₀ : Fs) :
    (fileStore enc fs₀).Refines (kvServer (view enc fs₀)) :=
  (Proofs.Servers.State.OwnedFs.fileStoreAbs hinj fs₀).refines

theorem fileStore_linearizable {enc : Target → FPath} (hinj : Function.Injective enc)
    (fs₀ : Fs) : (fileStore enc fs₀).Sat (Linearizable kv (view enc fs₀)) :=
  (Proofs.Servers.State.OwnedFs.fileStoreAbs hinj fs₀).sat_linearizable

theorem fileStore_frame {enc : Target → FPath} (hinj : Function.Injective enc) {fs₀ : Fs}
    {c : Conf Fs Request Response} (hc : (fileStore enc fs₀).Reach c) : Frame enc fs₀ c.st :=
  (Proofs.Servers.State.OwnedFs.fileStoreAbs hinj fs₀).reach_inv hc

theorem static_refines (loc : Target → Option FPath) (fs₀ : Fs) :
    (staticServer loc fs₀).Refines (Server.closed (staticSpec loc fs₀) ()) :=
  (Proofs.Servers.State.OwnedFs.staticAbs loc fs₀).refines

theorem static_answer {loc : Target → Option FPath} {fs₀ : Fs} {H : Hist Request Response}
    (hH : (staticServer loc fs₀).Hists H) {i : Nat} {r : Request} {s : Response}
    (hc : Ev.call i r ∈ H) (hr : Ev.ret i s ∈ H) : s = staticAnswer loc fs₀ r :=
  let ⟨_, _, h⟩ := (Proofs.Servers.State.OwnedFs.staticAbs loc fs₀).sat_answer hH hc hr; h

theorem docRoot_safe {root : String} {t : Target} {p : FPath} (h : docRoot root t = some p) :
    p.root = root ∧ ".." ∉ p.rel :=
  Proofs.Servers.State.OwnedFs.docRoot_safe h

/-- A target with only a path-with-query. -/
def pathTarget (s : String) : Target := ⟨none, none, some (Method.ascii s)⟩

#guard docRoot "www" (pathTarget "/a//./b.txt?x=1") == some ⟨"www", ["a", "b.txt"]⟩
#guard docRoot "www" (pathTarget "/a/../secret") == none
#guard docRoot "www" (pathTarget "/") == some ⟨"www", []⟩

end Silmaril.Servers.State.OwnedFs
