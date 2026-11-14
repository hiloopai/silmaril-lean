module

public import Silmaril.Servers.WasiFs.Shared.Defs
public import Silmaril.Servers.WasiFs.Kv.Thms
public import Silmaril.Servers.State.SharedFs.Thms
import Silmaril.Proofs.Servers.WasiFs.Shared

@[expose] public section

/-!
# The file-backed `wasi:http` store over shared files: theorems (header)

PROVED (standard axioms), namespace `Silmaril.Servers.WasiFs`. Proofs in
`Silmaril.Proofs.Servers.WasiFs.Shared`.

For an environment that keeps the files shorter than `2^64 - 1` octets (`Keeps E Small`):

* **`wasiShared_linearizable_safe`**, `wasiShared_safe`: whatever the other writers do, each
  response of the component is `specStep`'s answer to its request from some files;
* **`wasiShared_linearizable_on`**, `wasiShared_refines_on`: when the other writers never
  touch the files of the keys of `K` (they may change any other file, including the files of
  other keys), the component is linearizable with respect to `kvOnNF K`, the key-value store on
  the keys of `K`, from the store those files hold, and refines its closed server;
* `kvOnNF_true`: on all keys, `kvOnNF` is `kvNF`.
-/

namespace Silmaril.Servers.WasiFs

open Silmaril.Servers.State Silmaril.Servers.State.OwnedFs Silmaril.Servers.State.SharedFs
open Silmaril.Servers.State.Component
open Silmaril.Net.Http (Request Response Target Store storeStep)
open Silmaril.Cli (Fs FPath)

theorem wasiShared_linearizable_safe (root : String) {fs₀ : Fs} {E : Fs → Fs → Prop}
    (h₀ : Small fs₀) (hE : Keeps E Small) :
    (wasiShared root fs₀ E).Sat (Linearizable (safeNF root) ()) :=
  (Proofs.Servers.WasiFs.Shared.safeAbs root h₀ hE).sat_linearizable

theorem wasiShared_safe {root : String} {fs₀ : Fs} {E : Fs → Fs → Prop} (h₀ : Small fs₀)
    (hE : Keeps E Small) {H : Hist Request Response} (hH : (wasiShared root fs₀ E).Hists H)
    {i : Nat} {r : Request} {s : Response} (hc : Ev.call i r ∈ H) (hr : Ev.ret i s ∈ H) :
    ∃ fs, Small fs ∧ s = (specStep root fs r).1 :=
  let ⟨_, _, h⟩ := (Proofs.Servers.WasiFs.Shared.safeAbs root h₀ hE).sat_answer hH hc hr; h

theorem wasiShared_refines_on (root : String) {fs₀ : Fs} (K : Target → Prop) [DecidablePred K]
    {E : Fs → Fs → Prop} (h₀ : Small fs₀) (hE : Keeps E Small) (hU : Untouched E (keyOn root K)) :
    (wasiShared root fs₀ E).Refines
      (Server.closed (kvOnNF K) (restrictKeys K (viewN root fs₀))) :=
  (Proofs.Servers.WasiFs.Shared.onAbs root K h₀ hE hU).refines

theorem wasiShared_linearizable_on (root : String) {fs₀ : Fs} (K : Target → Prop)
    [DecidablePred K] {E : Fs → Fs → Prop} (h₀ : Small fs₀) (hE : Keeps E Small)
    (hU : Untouched E (keyOn root K)) :
    (wasiShared root fs₀ E).Sat (Linearizable (kvOnNF K) (restrictKeys K (viewN root fs₀))) :=
  (Proofs.Servers.WasiFs.Shared.onAbs root K h₀ hE hU).sat_linearizable

theorem kvOnNF_true (S : Store) (r : Request) (resp : Response) (S' : Store) :
    kvOnNF (fun _ => True) S r resp S' ↔ kvNF S r resp S' := by
  simp only [kvOnNF, kvNF, Atomic.comap, Atomic.guard, kvOn_true]

end Silmaril.Servers.WasiFs
