module

public import Silmaril.X86.Concurrency.Lift.Process.Defs
public import Silmaril.X86.Concurrency.Cir.Seq.Thms
public import Silmaril.X86.Concurrency.Lift.Thms
import Silmaril.Proofs.X86.Concurrency.Lift.Process

/-!
# The single-threaded lift for processes: what is proved

**Today's LPS has no threads**, so this is a statement about
single-threaded processes only; it does not model threads, and nothing here is about a
multi-threaded process.

PROVED (standard axioms; proofs in `Silmaril/Proofs/X86/Concurrency/Lift/Process.lean`):

* `sharingNo_unmodeled`: every sharing syscall (`clone`, `clone3`, `futex`, `vfork`, `shmget`,
  `shmat`, `rt_sigaction`, `io_uring_setup`) is a pending, `unmodeled` arm of the native table;
* `singleThreaded_of_psafe`: **a process-safe execution is single-threaded**: no reachable
  configuration has a pending sharing request. This extends `LpsBridge.no_thread_of_psafe`
  (clone/clone3/futex) with shared memory segments, `vfork`, signal handlers and `io_uring`.

* `open_step_of_native`, `lpsNativeFlat_of_openFlatStep`: a non-syscall
  native step is an `Open.step`, so the native glue `Task.lpsNativeFlat` follows from
  `Lift.Task.openFlatStep`; there is one glue goal for `Open`, not two.
* `lpsNativeFlat : Task.lpsNativeFlat`: from `Lift.openFlatStep`, now PROVED.
* `nativeStepUnder_of`, `nativeStepUnder`: every non-syscall native step reads the same under
  every `SC ⊑ M ⊑ XL` (`NativeStepUnder`), with the access list as its events.

What "a process theorem under `M`" means here: LPS runs one thread; its memory effects are the
native steps' accesses and the syscalls' effects, in program order. By the one-thread lift
(`Cir.Seq.oneSem_iff`, `oneSem_append`) such a trace has, under every `SC ⊑ M ⊑ XL`, exactly
its sequential behaviour, so a single-threaded process reads the same under `M`. What is not
formal: a process semantics parametrised by `M` (LPS is not), and the syscall effects as
events (a syscall is a full barrier, as `futexWait` is in CIR).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Lift

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Process.LpsBridge
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.MemoryModel.Axiomatic (Exec)

theorem sharingNo_unmodeled (i : SyscallInput) (m : Model) (h : sharingNo i.sysno.toNat) :
    spec i m .unmodeled :=
  Silmaril.Proofs.X86.Concurrency.Lift.Process.sharingNo_unmodeled i m h

/-- **A process-safe configuration is single-threaded.** -/
theorem singleThreaded_of_psafe {oracle : Oracle} {segs : List Segment} {refused : RefusalFilter}
    {Allowed : List Event → Prop} {c : Config (machine oracle)}
    (h : PSafe segs refused Allowed c) : SingleThreaded segs refused c :=
  Silmaril.Proofs.X86.Concurrency.Lift.Process.singleThreaded_of_psafe h

/-- **A `ProcessSafe` launch is single-threaded**, for every flag oracle. -/
theorem singleThreaded_of_processSafe {snapshot : X86Launch.Snapshot} {refusals : SpuriousCfg}
    {limit : Int} {en : ExecEntry} {inp : ProcInput} {Allowed : List Event → Prop}
    (h : ProcessSafe snapshot refusals limit en inp Allowed) (oracle : Oracle) :
    SingleThreaded snapshot.image.segments (NativeX86.defaultRefusalFilter refusals)
      (X86Launch.init (machine oracle) snapshot en limit inp) :=
  singleThreaded_of_psafe (h oracle)

/-- **A non-syscall native step of LPS is an `Open.step`.** -/
theorem open_step_of_native {s : X86State} {r : AccessReport X86State}
    (hs : x86NativeStep8 s = .ok r) (hp : r.value.pending = none) :
    Silmaril.X86.Open.step s.m = some r.value.m :=
  Silmaril.Proofs.X86.Concurrency.Lift.Process.open_step_of_native hs hp

/-- The native glue follows from the `Open` glue. -/
theorem lpsNativeFlat_of_openFlatStep (hF : Task.openFlatStep) : Task.lpsNativeFlat :=
  Silmaril.Proofs.X86.Concurrency.Lift.Process.lpsNativeFlat_of_openFlatStep hF

/-- **Glue for LPS's native machine** (PROVED). -/
theorem lpsNativeFlat : Task.lpsNativeFlat := lpsNativeFlat_of_openFlatStep openFlatStep

/-- Under the glue, the native steps read the same under every `SC ⊑ M ⊑ XL`. -/
theorem nativeStepUnder_of (hF : Task.lpsNativeFlat) {M : Exec → Prop} (hsc : Exec.Sc ⊑ M)
    (hxl : M ⊑ Exec.Xl) : NativeStepUnder M :=
  Silmaril.Proofs.X86.Concurrency.Lift.Process.nativeStepUnder_of hF hsc hxl

/-- **The native steps read the same under every `SC ⊑ M ⊑ XL`.** -/
theorem nativeStepUnder {M : Exec → Prop} (hsc : Exec.Sc ⊑ M) (hxl : M ⊑ Exec.Xl) :
    NativeStepUnder M :=
  nativeStepUnder_of lpsNativeFlat hsc hxl

end Silmaril.X86.Concurrency.Lift
