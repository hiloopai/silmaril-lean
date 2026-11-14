module

public import Silmaril.Machine.Process.LpsBridge.Defs
public import Silmaril.Machine.Link.Examples.LibMiniClient.Thms

/-!
# Ladder rung 12 as a Linux process: definitions

The linked executable of rung 12 (`examples/elf-ladder/12-libmini-client`, ld.bfd, fixture
`Silmaril.Machine.Link.Fixtures.LibMiniClientBfd`) is `_start → cmain → {memset, memcpy, len1 →
strlen}` followed by `exit(rax)`; it exits with status 6.

* `exitAllowed fs`: the traces the process may produce: nothing yet, or exactly
  `exit(6)` with the launch file system.
* `ExitAt m`: the open state is at the `syscall` of `_start` with `rax = 60` and the low byte
  of `rdi` equal to 6.
* `Task.startRun` (open; **proved**, `startRun_holds` in
  `Silmaril.Machine.Process.LibMiniClient.Thms`; the total form is `startRun_total`): from the
  launch state of every valid launch of the parsed executable, the open machine does not get stuck before it reaches `ExitAt` (partial
  correctness, as R1's `Safe`). Discharging it needs `cmain` (not verified by R1; it carries
  the `unverified` spec), the `_start` prologue, and the launch-memory facts (image loaded,
  stack backed and writable). See an earlier design note.
-/

@[expose] public section

namespace Silmaril.Machine.Process.LibMiniClient

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.Process.LpsBridge

/-- The loader image of the rung-12 executable (R1's `NonVacuity.loadImg`: the kernel-parsed
image of the fixture bytes). -/
abbrev image : Image := Silmaril.Proofs.Machine.Link.LibMiniClient.NonVacuity.loadImg

/-- The allowed traces: empty, or `exit(6)` with file system `fs`. -/
def exitAllowed (fs : Silmaril.Process.LPS.Fs.FileSystem) (tr : List Event) : Prop :=
  tr = [] ∨ tr = [.exitEv 6 fs]

/-- At `_start`'s `syscall`, requesting `exit(6)`. -/
def ExitAt (m : MState) : Prop :=
  AtSyscall m ∧ (m.core.read .rax).toNat = 60 ∧ m.core.read .rdi &&& 255 = 6

/-- **The `_start` run** (proved: `startRun_holds`). For every launch of the rung-12 image
that LPS's x86 launch accepts (`X86Launch.ValidEntry`), the launch state runs to `ExitAt` without getting stuck
(for every step budget). -/
def Task.startRun : Prop :=
  ∀ (snapshot : X86Launch.Snapshot) (en : ExecEntry) (inp : ProcInput),
    snapshot.image = image → X86Launch.ValidEntry x86ExtNative snapshot en inp →
    ∀ n, Silmaril.Machine.Link.FnSpec.SafeN ExitAt n (launchState snapshot en inp)

end Silmaril.Machine.Process.LibMiniClient
