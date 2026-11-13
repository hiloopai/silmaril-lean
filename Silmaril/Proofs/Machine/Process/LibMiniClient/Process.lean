module

public import Silmaril.Machine.Process.LibMiniClient.Defs
public import Silmaril.Machine.Process.LpsBridge.Thms

/-!
# Proofs: rung 12 as an LPS process (conditional on `Task.startRun`)

`rung12_processSafe`: if the `_start` run reaches `exit(6)` without getting stuck
(`Task.startRun`), then every launch of the rung-12 executable is process-safe under LPS for
`exitAllowed inp.fs`: for every flag oracle and refusal configuration, every finite execution
produces either no event or exactly `exit(6)` with the launch file system, and no execution
reaches an error. The bridge part (`processSafe_of_launch`, `psafe_exit`) is proved and
program-independent; only the open-machine run of `_start`/`cmain` is assumed.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Process.LibMiniClient

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.LibMiniClient
open Silmaril.Proofs.Machine.Process.LpsBridge

/-- The launched model keeps the input's file system. -/
theorem init_fs (oracle : Oracle) (snapshot : X86Launch.Snapshot) (en : ExecEntry) (limit : Int)
    (inp : ProcInput) : (X86Launch.init (machine oracle) snapshot en limit inp).model.fs = inp.fs :=
  rfl

/-- **Rung 12 as a process, from the `_start` run.** -/
theorem rung12_processSafe (hstart : Task.startRun) (snapshot : X86Launch.Snapshot)
    (refusals : SpuriousCfg) (limit : Int) (en : ExecEntry) (inp : ProcInput)
    (himg : snapshot.image = image) (hv : X86Launch.ValidEntry x86ExtNative snapshot en inp) :
    ProcessSafe snapshot refusals limit en inp (exitAllowed inp.fs) := by
  refine processSafe_of_launch (Q := ExitAt) (.inl rfl) (hstart snapshot en inp himg hv) ?_
  intro oracle c m al hm ⟨ht, hrax, hrdi⟩
  refine psafe_exit al ht (.inl hrax) (.inl rfl) ?_
  rw [hrdi, hm, init_fs]
  exact .inr rfl

end Silmaril.Proofs.Machine.Process.LibMiniClient
