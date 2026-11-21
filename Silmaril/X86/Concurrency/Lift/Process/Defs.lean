module

public import Silmaril.X86.Concurrency.Lift.Defs
public import Silmaril.Process.LpsBridge.Threads.Defs

/-!
# The single-threaded lift for processes: definitions

**Today's LPS has no threads**: one task, no scheduler, and `clone`
with `CLONE_VM` is not modelled (`LpsBridge.Threads`). Every process theorem of the bridge is
therefore a theorem about **one thread** on one flat memory. This module states when such a
process is single-threaded *as a matter of its syscalls*, and what reading its native steps
under a memory model `M` means.

* `sharingNo n`: `n` is the x86-64 number of a syscall through which a process could get a
  second thread of control over its memory, shared memory, or an asynchronous handler: `clone`
  (56), `clone3` (435), `futex` (202), `vfork` (58), `shmget` (29), `shmat` (30),
  `rt_sigaction` (13), `io_uring_setup` (425). `mmap` with `MAP_SHARED` is **not** in the
  list: LPS models only private anonymous mappings (`Sys/Mmap.lean`, `mmapModeledB`), and that
  the shared case is unmodelled is not proved here.
* `PendingSharing c`: an alive configuration whose pending syscall is one of these.
* `SingleThreaded segs refused c`: no configuration reachable from `c` has such a pending
  request.
* `NativeStepUnder M`: every non-syscall step of the native x86 machine LPS runs
  (`x86NativeStep8`) has an event trace, with exactly the access list of the fetched
  instruction (`openActs`), whose only behaviour as one thread under `M` is the step's own
  memory.
* `Task.lpsNativeFlat`: the glue for that machine. It is not a separate open goal: it follows
  from `Lift.Task.openFlatStep` (`lpsNativeFlat_of_openFlatStep`), because a non-syscall native
  step is an `Open.step`.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Lift

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Seq
open Silmaril.X86.MemoryModel.Axiomatic (Exec)
open Silmaril.Process.LpsBridge (Oracle machine spec)

/-- The syscalls that could give a process a second thread of control over its memory, shared
memory, or an asynchronous handler. -/
def sharingNo (n : Nat) : Prop :=
  n = 56 ∨ n = 435 ∨ n = 202 ∨ n = 58 ∨ n = 29 ∨ n = 30 ∨ n = 13 ∨ n = 425

/-- An alive configuration with a pending sharing request. -/
def PendingSharing {oracle : Oracle} (c : Config (machine oracle)) : Prop :=
  c.model.halted = none ∧ ∃ x8, (machine oracle).svcPending c.ms = some x8 ∧ sharingNo x8.toNat

/-- **The single-threaded profile**: no reachable configuration has a pending sharing request. -/
def SingleThreaded {oracle : Oracle} (segs : List Segment) (refused : RefusalFilter)
    (c : Config (machine oracle)) : Prop :=
  ∀ tr c', Silmaril.Process.LPS.Star segs spec refused c tr c' → ¬ PendingSharing c'

/-- **The native steps read the same under `M`**: every non-syscall step of `x86NativeStep8`
has an event trace, whose events are the access list of the fetched instruction
(`openActs`), whose only behaviour, as one thread under `M` from the step's memory, is the
memory after the step. (Without `openActs` the statement would be close to vacuous: any memory
change is the replay of some list of byte stores.) -/
def NativeStepUnder (M : Exec → Prop) : Prop :=
  ∀ (s : X86State) (r : AccessReport X86State), x86NativeStep8 s = .ok r → r.value.pending = none →
    ∃ acts, openActs s.m acts ∧ ∀ m, OneSem M (flat s.m.memory) acts m ↔ m = flat r.value.m.memory

/-- **Glue for LPS's native x86 machine**: every non-syscall step of `x86NativeStep8` has
`ActOk` actions with exactly the access list of the fetched instruction (`openActs`), whose
sequential replay on the flat pre-memory is the flat post-memory. Not a separate open goal:
`x86NativeStep8` runs `Open.step`'s fetch and executor, so it follows from
`Lift.Task.openFlatStep` (`lpsNativeFlat_of_openFlatStep`). PROVED: `Lift.lpsNativeFlat`. -/
def Task.lpsNativeFlat : Prop :=
  ∀ (s : X86State) (r : AccessReport X86State), x86NativeStep8 s = .ok r → r.value.pending = none →
    ∃ acts, openActs s.m acts ∧ (∀ a ∈ acts, ActOk a) ∧
      actsReplay (flat s.m.memory) acts = some (flat r.value.m.memory)

end Silmaril.X86.Concurrency.Lift
