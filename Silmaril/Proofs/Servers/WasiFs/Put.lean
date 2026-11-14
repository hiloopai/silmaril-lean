module

public import Silmaril.Proofs.Servers.WasiFs.Run

@[expose] public section

/-!
# Proofs: the `PUT` runs of the file-backed store

* `run_put`: for `PUT`, the complete run of `handle` (reading the request body, then
  `open-at`, `open-at` with `create` and `truncate`, and `write`) makes the response of
  `specStep` and leaves its files.
-/

namespace Silmaril.Proofs.Servers.WasiFs

open Silmaril.Games Silmaril.Wasi Silmaril.Servers.WasiHttp Silmaril.Servers.WasiExamples
open Silmaril.Servers.State Silmaril.Servers.State.OwnedFs Silmaril.Servers.WasiFs
open Silmaril.Servers.Calls
open Silmaril.Wasm.Component (Val)
open Silmaril.Net.Http (Request Response Method Target)
open Silmaril.Cli (Fs FPath)

theorem fs_set_set (fs : Fs) (p : FPath) (a b : Option (List UInt8)) :
    (fs.set p a).set p b = fs.set p b := by
  funext x; simp only [Silmaril.Cli.Fs.set]; split <;> rfl

theorem fs_set_self (fs : Fs) (p : FPath) (a : Option (List UInt8)) : (fs.set p a) p = a := by
  simp [Silmaril.Cli.Fs.set]

theorem run_put (root : String) (fs : Fs) (q : Request) (hm : q.method = .put) :
    respOf 1 (runStore root fs q) = some (specStep root fs q).1 ∧
      (replay root fs (runStore root fs q)).files = (specStep root fs q).2 := by
  by_cases hb : maxRead ≤ q.content.length
  · store_run
    store_run_mut
    refine respOf_answerS _ _ _ _ _ ?_ ?_
    · rfl
    · simp only [simple_status]; decide
  · cases hf : fs (keyFile root q.target) with
    | none =>
      have hf' : fs ⟨root, [String.ofList (keyName q.target.pathWithQuery)]⟩ = none := hf
      store_run
      store_run_mut
      exact ⟨respOf_answerS _ _ _ _ _ rfl (by simp only [simple_status]; decide),
        by simp [fs_set_set, fs_set_self]⟩
    | some c =>
      have hf' : fs ⟨root, [String.ofList (keyName q.target.pathWithQuery)]⟩ = some c := hf
      store_run
      store_run_mut
      exact ⟨respOf_answerS _ _ _ _ _ rfl (by simp only [simple_status]; decide),
        by simp [fs_set_set, fs_set_self]⟩

end Silmaril.Proofs.Servers.WasiFs
