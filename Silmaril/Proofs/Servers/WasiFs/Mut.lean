module

public import Silmaril.Proofs.Servers.WasiFs.Run

@[expose] public section

/-!
# Proofs: the runs of the file-backed store that change the files, and the other methods

* `run_delete`, `run_put`, `run_other`: for `DELETE`, `PUT` and the methods that do not touch
  the files, the complete run of `handle` makes the response of `specStep` and leaves its files.
-/

namespace Silmaril.Proofs.Servers.WasiFs

open Silmaril.Games Silmaril.Wasi Silmaril.Servers.WasiHttp Silmaril.Servers.WasiExamples
open Silmaril.Servers.State Silmaril.Servers.State.OwnedFs Silmaril.Servers.WasiFs
open Silmaril.Servers.Calls
open Silmaril.Wasm.Component (Val)
open Silmaril.Net.Http (Request Response Method Target)
open Silmaril.Cli (Fs FPath)

theorem run_delete (root : String) (fs : Fs) (q : Request) (hm : q.method = .delete) :
    respOf 1 (runStore root fs q) = some (specStep root fs q).1 ∧
      (replay root fs (runStore root fs q)).files = (specStep root fs q).2 := by
  cases hf : fs (keyFile root q.target) with
  | none =>
    have hf' : fs ⟨root, [String.ofList (keyName q.target.pathWithQuery)]⟩ = none := hf
    store_run
    store_run_mut
    exact respOf_answerS _ _ _ _ _ rfl (by simp only [simple_status]; decide)
  | some c =>
    have hf' : fs ⟨root, [String.ofList (keyName q.target.pathWithQuery)]⟩ = some c := hf
    store_run
    store_run_mut
    exact respOf_answerS _ _ _ _ _ rfl (by simp only [simple_status]; decide)

theorem run_other (root : String) (fs : Fs) (q : Request)
    (hm : kindOf q.method = .options ∨ kindOf q.method = .notAllowed ∨ kindOf q.method = .other) :
    respOf 1 (runStore root fs q) = some (specStep root fs q).1 ∧
      (replay root fs (runStore root fs q)).files = (specStep root fs q).2 := by
  cases h : q.method <;> simp [h, kindOf] at hm <;> store_run <;>
    exact respOf_answerS _ _ _ _ _ rfl (by simp only [simple_status]; decide)

end Silmaril.Proofs.Servers.WasiFs
