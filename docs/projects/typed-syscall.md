# A typed user/kernel boundary

[`Silmaril.Process.TypedSyscall`](../../Silmaril/Process/TypedSyscall/Defs.lean)
is a small POSIX-style process model, not a POSIX or Linux conformance claim.
It describes one selected user step or completed kernel call, without
committing to syscall numbers, an ISA, or a memory representation.

| Plug | Supplied by the caller | Checked filling |
| --- | --- | --- |
| CPU / ABI boundary | `Cpu` consumes an image, core and store; it retires, stops, or yields a typed call with a reply continuation. Registers, trap semantics and syscall-number conversion are outside the interface. | A two-stage client that writes a buffer and then exits; not an x86 runner. |
| Image | Immutable input to the CPU; mapping and ownership constraints are stated by the image/client. | Buffer address and count. No ELF loading. |
| Memory and kernel environment | `Store` is carried explicitly through CPU and kernel transitions. A filling can pair memory with descriptor or other service state; a store frame is a property of that filling. | Existing `Syscall.State`: permissioned byte memory, descriptors and exit state. |
| Parallelism/scheduling | `Scheduler` selects a core and how to replace its slot in the pool. A `none` selection is idle, not a verdict on completion or deadlock. | A singleton pool and an idle-policy check. No thread creation, blocked-call scheduling, fairness or weak-memory semantics is implemented. |

A `Signature` assigns a type `Response req` to each request. `Signature.Hom`
maps requests forward and projects responses **back at that request's index**.
`Action.push` and `Kernel.pull` compose (`Action.push_then`, `Kernel.pull_then`).
[`step_push_iff`](../../Silmaril/Process/TypedSyscall/Thms.lean) proves that
pushing the CPU or pulling the kernel gives the same observations and outcomes,
including store changes and exit without resumption. Its kernel is the
*constructed* pullback, not an arbitrary kernel with a similar signature. To
reuse a theorem on an independent kernel, prove the appropriate reply/exit,
state and observation correspondence and separately establish progress. The
transport neither supplies a return for every call nor turns an absence of
completion into a fault. Precise fault state or resumable traps would require
a richer CPU stop outcome; they are not hidden in the syscall reply type.

The [checked filling](../../Silmaril/Process/TypedSyscall/Checks.lean) maps a
client send request to `write` on descriptor 1 in the existing
[`Syscall.Step`](../../Silmaril/Process/Syscall.lean) relation. The client sees
`Option Nat` rather than a raw result: the continuation loses errno, but the
kernel event is retained. `exit` has response `Empty` and uses a separate
completion constructor. The checks cover a one-byte write and subsequent exit,
plus a bad-descriptor return observed as failure by the client.

```sh
lake build --wfail Silmaril.Process.TypedSyscall.Checks
```

## Container execution and event streams

[`Containers.TypedSyscall.completedMachine`](../../Silmaril/Containers/TypedSyscall/Defs.lean)
packages a completed typed step as the existing
[`Mach.MachineSem`](../../Silmaril/Containers/Machine/Defs.lean). The loader
supplies the image, initial scheduled pool and store; the machine carries
them and the runtime runs it with its chosen policy. A kernel event becomes
`Act.ev`, a silent step becomes `Act.tau`, and a non-returning exit is final
with the low eight bits of its status. A CPU stop that the filling has
already classified as a container `Stop` keeps that classification.
[`completedMachine_push`](../../Silmaril/Containers/TypedSyscall/Thms.lean)
lifts `step_push_iff` to equality of these machines. With the same loader,
clone policy, and observation relation, `MachineSem.Run` and the runtime
therefore give the same behaviours. This is still a constructed pullback,
not an agreement proof for independently defined CPU/kernel fillings.

The [container checks](../../Silmaril/Containers/TypedSyscall/Checks.lean)
run a typed one-byte read followed by exit in `MachRuntime.toRuntime`. The
shared [`Linux.signature` and `Linux.kernel`](../../Silmaril/Process/TypedSyscall/Linux/Defs.lean)
use `Syscall.Step` without changing its store or event. The read writes the
byte into process memory, advances the descriptor cursor, resumes the
client with the count, and emits `Syscall.Event.read 0 [0x41]`. The stream
contains this event, the syscall exit event, then `Check.Obs.stop (.exited 0)`.
It does not serialize the continuation, store, ownership labels, or ghost
threads. Nor does it use the separate `Containers.Env.Ev` capability alphabet;
a projection to that alphabet would need its own assumptions and proof.

The checks reuse [`Check.ObsPrefix`, `vlang` and `vmonitor`](../../Silmaril/Containers/Check/Defs.lean)
and the [stream word and chunk APIs](stream-languages.md): the limit of two
chunks is the same finite `Streams.Word` as the observations in order. The
existing [`vlang_iff`](../../Silmaril/Containers/Check/Thms.lean) relates
acceptance of **all** observation prefixes to no UB and the event policy.
The fixture supplies a run and its observed word, not a universal progress
or no-UB theorem for an independent process.

- **Relabeling.** `Containers.Beh.map` maps each event, keeping the stop or
  divergence kind. `stoppedWord_map` checks its finite observation projection
  using `Streams.Word.map`; `relabel_vlang` transports the verdict only for
  the policy pulled back along the label map. Order, multiplicity, and the
  terminal marker are preserved, even when distinct payloads become equal.
- **Filtering.** Finite event filtering distributes over append (`List.filterMap_append`), but can
  erase a request, error, or the only witness that an obligation was met.
  Never filter terminal UB. On infinite runs a filter can even turn infinitely
  many events into a finite stream; a progress or silent-divergence argument
  is needed. A filtered prefix theorem alone does not give a process contract.
  [`Containers.Http.sockTrace` and `platform`](../../Silmaril/Containers/Http/Defs.lean)
  already use this narrower reading for socket-event prefixes, not as a
  stop-sensitive process semantics.
  For independent models use [`Model.Refines.sat`](../../Silmaril/Containers/Behaviour/Thms.lean)
  or [`Mach.wlp_transfer`](../../Silmaril/Containers/Machine/Thms.lean) with
  behaviour inclusion in the concrete-to-spec direction on the observations
  in scope; `Model.TraceRefines` alone transports prefix safety only.
- **Stops and visibility.** A returning errno is a syscall event/result, not
  a process signal or UB. A classified `.undefined` remains a final UB marker
  and the monitor rejects it; `.signaled` remains a concrete process stop, but
  a no-UB monitor alone does not promise no crash. Image-level unavailable
  is neither outcome and is not accepted as a `Stop` by this bridge. A future
  image filling must handle it explicitly before classifying a stop, not
  relabel it as a memory fault. Idle or an absent completion gets no edge in
  this completed-step pilot: if nothing else can step, `MachineSem.Run`
  reports model `undefined stuck`. Do not use this as an implementation of
  input waiting, scheduling, or clone. Ghost annotations may constrain a
  proof relation; they cannot expose new machine bytes, events, or progress.
  If a filling consults those annotations to choose observable behaviour,
  non-observability requires a separate erasure or simulation proof.

```sh
lake build --wfail Silmaril.Containers.TypedSyscall.Checks Silmaril.Process.TypedSyscall.Checks
```

## Next adapters, not part of the pilot

The next useful filling is one existing CLI-loaded client. Keep the loader's
image predicate and concrete ABI unchanged, and prove that the new boundary
agrees on its emitted requests, replies, store effects and stops before moving a
caller. [`Containers.Lps.lps`](../../Silmaril/Containers/Lps/Defs.lean) is
already a separate LPS-to-container adapter: `mapEv`/`mapEvs` only translate
supported stdio and stop events, with a pending-event queue; exit and signal
come through `Final`. It conservatively classifies unsupported events and
unmodeled steps as UB, and LPS errors classified as faults as `.undefined .memory`.
Do not infer an equality with a profile that preserves concrete faults. A
future common projection needs explicit stop, span, retry, and trace agreement.
For a shared service that needs separately visible calls and replies, consider
[`Servers.State.toTrace`](../../Silmaril/Servers/State/Traces/Defs.lean) and
its request identities. That requires matching call/return pairs and a
typed-answer encoding; the completed-call stream here has no pending-call IDs.

For a decoded x86 image read, [`MemEvent.Event`](../../Silmaril/X86/MemEvent/Defs.lean)
already names kind, span and lock status, and
[`ext_local` / `sse9_local`](../../Silmaril/X86/MemEvent/Thms.lean) give
locality results for their instruction lanes. A later bridge should compare
one successful decoded data read with `MemEvent.extAccesses` and its
`readSet`; keep the footprint at the machine layer, not as container I/O.
`MemEvent.Event` is not a reply/stop log and has no fetch kind; it cannot
attest to returned bytes, ownership or skipped failures. No image-to-MemEvent,
LPS trace, decoder or scheduler replacement is claimed here.
