module

public import Silmaril.Wasi.Cli.HelloOs.Defs
public import Silmaril.Wasi.Cli.Os.Thms
public import Silmaril.Wasi.Runtime.Thms

/-!
# The x86 runtime of `hello` meets its CLI spec (header)

The behaviour part of `docs/projects/wasm-binaryen-tooling.md`, worked example. PROVED (standard axioms), namespace
`Silmaril.Wasi.Cli`.

* **`helloImg_sat`**: the concrete 42-byte x86 program `helloCode` of `Silmaril.Wasi.Runtime`,
  from its launch state, on every native machine agreeing with `Open.step` and for every flag
  oracle, meets the CLI spec `hiSpec` in LPS (`Silmaril.Cli.Os.Sat`): every finite run only writes
  a prefix of `hi` to stdout, and a finished run is the observation "stdout `hi`, no stderr,
  exit `0`, files unchanged". Hypotheses: descriptor `1` of the LPS model is the live stdout
  channel of the wiring, stderr is wired to another channel, and the invocation's files under
  its roots are those of the LPS file system.
* `hello_run`: the finished run of `hello` as a `Silmaril.Cli.Os.Run` (from which every prefix is
  allowed, `allowed_of_run`).

The proof reuses `Silmaril.Wasi.Runtime.helloImg_psafe` (process safety for "a prefix of `hi`,
then `exit 0`") and weakens its trace predicate (`psafeF_mono`). As there, the runtime is
hand-written, not compiled from the component.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli

open Silmaril.Cli Silmaril.Cli.Os
open Silmaril.Process.LPS
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Wasi.Os (hiOut helloAllowed)
open Silmaril.Wasi.Examples (hiBytes)

/-- The observation of `hello` on the invocation `i`. -/
def hiObs (i : Input) : Obs := { stdout := [0x68, 0x69], fs := i.fs }

theorem hiSpec_hiObs (i : Input) : hiSpec i (hiObs i) :=
  ⟨rfl, rfl, rfl, rfl, rfl, Nat.zero_le _, rfl⟩

theorem lpsBytes_hi : lpsBytes [0x68, 0x69] = hiBytes := by decide

/-- The finished run of `hello`: the write of `hi`, then `exit 0`. -/
theorem hello_run {w : Wiring} {ch : Word} (hout : w.outCh = ch) (herr : w.errCh ≠ ch)
    {i : Input} {lfs : Fs.FileSystem} (hfs : FsAgrees w i i.fs lfs) :
    Run w i (hiObs i) (hiOut ch) 0 lfs where
  expected e he := by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 he
    exact .inl hout.symm
  noExit e he := by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 he
    exact id
  out := by rw [hout, hiOut, written_map_self, ← lpsBytes_hi]; rfl
  err := by rw [hiOut, written_map_ne herr]; rfl
  inp := by rw [hiOut, readFrom_map_write]; rfl
  exit := rfl
  fs := hfs

/-- **The concrete x86 `hello` meets its CLI spec in LPS.** -/
theorem helloImg_sat {oracle : Oracle} {nstep : NStep} {refused : RefusalFilter}
    {segs : List Segment} {ch : Word} (hM : Agrees nstep Silmaril.Machine.X86.Open.step)
    {cfg : Config (flagMachine oracle nstep)} (al : AlignedF cfg Silmaril.Wasi.Runtime.helloStart)
    (hfd : fdLookup cfg.model.fds 1 = some (.channel ch)) (hch : wIs0 ch = false)
    {w : Wiring} (hout : w.outCh = ch) (herr : w.errCh ≠ ch)
    {i : Input} (hfs : FsAgrees w i i.fs cfg.model.fs) :
    Sat segs refused hiSpec w i cfg :=
  psafeF_mono (fun _ htr => allowed_of_run (hiSpec_hiObs i) (hello_run hout herr hfs) htr)
    (Silmaril.Wasi.Runtime.helloImg_psafe hM al hfd hch)

end Silmaril.Wasi.Cli
