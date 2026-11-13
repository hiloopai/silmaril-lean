module

public import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs

public import Silmaril.Raw.Wasm.Component.Engine.Mock.Script
public import Silmaril.Wasm.Component.Engine.Laws
public import Silmaril.Raw.Wasm.Component.Wasm.Execution.Memory.Lemmas

/-!
# The Mock core engine

A `CoreEngine` whose modules are Script programs (`Engine/Mock/Script.lean`). It is used to
transcribe the core functions of the reference test suite
(`design/mvp/canonical-abi/run_tests.py` of component-model a25fc0b, next to the pinned
`definitions.py`), which are Python lambdas over memories of either address type, and to
exercise the canonical ABI's memory64 paths, which Lime1 cannot execute (Lime1 and V1 only have
`i32` memories).

* `FuncType := V1.FuncType`, `ExternType := CoreExternType` (memories carry their address
  type, so an `i64` memory is `.memory .i64 n (some n)`; Mock memory limits are in bytes).
* The store holds function instances (Script functions closed over their module instance, or
  host functions `V1.FuncType × H`), memories (`AddrType × ByteArray`), funcref tables (with
  their address type) and globals. Addresses are list positions; nothing is ever removed, and
  only memory contents and global values change.
* `prepare?` checks `Module.validate`, resolves imports positionally (each provided extern
  value must have a type that is a subtype of the declared import type), allocates, and
  returns the start function without running it.
* A thread is `entry f args` (fresh invocation), `exec frames pending` (a stack of Script
  frames, head = current, with an optional pending host callout), or `done r`. Calls to other
  Script functions push a frame; calls to host functions first take an internal step that
  records the callout in `pending` (so a thread is a callout exactly when it is parked), and
  `resume` writes the host results and advances the caller. Invoking a host function directly
  is a callout immediately (required by `Lawful.allocHost_callout`).
* `Internal` is the deterministic one-instruction step `stepMock?`; argument, result and
  register type mismatches, out-of-bounds accesses and falling off the end of the code are
  traps (`done .trap`), never stuck states. The only stuck threads are invocations of
  unallocated addresses and the empty frame stack (unreachable).

Proved: `Lawful mock`, `ResumeLawful mock`, `mockExec : mock.Exec` with `step?_sound` by `rfl`,
`ExecDeterministic mockExec` (hence `ExecComplete`), and `stepMock?_isSome_iff` (the stepper is
total exactly on running threads). Tests (kernel-checked by `decide`): an `i64` memory,
an i64 address above 2^32 is bounds checked without truncation, an `i32` pointer register on
an `i64` memory traps at the access, an `i64` table (`tableAddrType? = some .i64`) indexed by
`callIndirect` with signature check and without index truncation, rejection of duplicate
export names, and a host callout round trip (`callout` then `resume`, then `returned`).

Not modelled: WebAssembly validation or typing of Script code, memory or table growth,
exceptions, and any cost model. The Mock engine is a test vehicle, not a WebAssembly semantics.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Mock

open Silmaril.Wasm.Execution.Memory (readBytes writeBytes decodeLE encodeLE)
open Silmaril.Wasm.Execution.Runtime (Value)

/-! ## Store -/

variable {H : Type}

/-! ## Instantiation -/

/-! ## Threads -/

/-! ## Registers and values -/

/-! ## The step -/

/-! ## The engine -/

/-! ## Laws -/

/-- The Mock stepper computes every internal step (and hence is complete). -/
theorem mockExec_deterministic : CoreEngine.ExecDeterministic mockExec :=
  .of_deterministic fun h => h

theorem mockExec_complete : CoreEngine.ExecComplete mockExec :=
  mockExec_deterministic.toExecComplete

/-! ## Tests -/

namespace Test

theorem mem64Module_valid : mem64Module.Valid := by decide

/-- The memory has address type i64 and 64 bytes. -/
theorem mem64_addrType : mock.memAddrType? mem64Store 0 = some .i64 := by decide
theorem mem64_size : mock.memSize? mem64Store 0 = some 64 := by decide

/-- Little-endian load at an in-bounds i64 address. -/
theorem mem64_read_ok : runRead (i64 8) = .returned (.values [i32 0x04030201]) := by decide

/-- The address 2^33 + 8 is out of bounds: it is not truncated to 32 bits. -/
theorem mem64_read_high : runRead (i64 (2 ^ 33 + 8)) = .returned .trap := by decide

/-- Parameter type check: an i32 argument does not match the `[i64]` parameter type, so the
invocation traps before any memory access. -/
theorem mem64_read_i32 : runRead (i32 8) = .returned .trap := by decide

/-- An `i32` pointer register on an i64 memory traps at the access (`effAddr?`). -/
theorem mem64_ptr_i32_traps : runPtr false = .returned .trap := by decide

/-- After `i64.extend_i32_u` the same access succeeds (zero-filled memory). -/
theorem mem64_ptr_extended : runPtr true = .returned (.values [i32 0]) := by decide

/-- Duplicate export names are rejected by validation. -/
theorem dup_export_invalid :
    ¬ ({ funcs := [⟨⟨[], []⟩, [.ret []]⟩],
         exports := [("f", .func 0), ("f", .func 0)] } : Module).Valid := by decide

theorem table64_addrType : mock.tableAddrType? table64Store 0 = some .i64 := by decide

/-- `call_indirect` through an i64 table with an i64 index. -/
theorem table64_call_ok : runTable (i64 1) = .returned (.values [i32 7]) := by decide

/-- A null entry traps. -/
theorem table64_call_null : runTable (i64 0) = .returned .trap := by decide

/-- A callee whose result type differs from the declared type traps (signature check). -/
theorem table64_call_sig : runTable (i64 2) = .returned .trap := by decide

/-- An index above 2^32 is not truncated: out of bounds, trap. -/
theorem table64_call_high : runTable (i64 (2 ^ 32 + 1)) = .returned .trap := by decide

/-- The run parks on a callout of host code 42 with arguments `7, 5`. -/
theorem callout_parks :
    mock.status calloutRun.1 calloutRun.2 = .callout 42 [i32 7, i32 5] := by decide

/-- Resuming with 100 finishes with 200. -/
theorem callout_resume : resumeRun (.values [i32 100]) = .returned (.values [i32 200]) := by
  decide

/-- Resuming with a result of the wrong type traps. -/
theorem callout_resume_bad : resumeRun (.values [i64 100]) = .returned .trap := by decide

/-- A host trap is propagated. -/
theorem callout_resume_trap : resumeRun .trap = .returned .trap := by decide

/-- Invoking the host function directly is immediately a callout. -/
theorem host_invoke : mock.status calloutStore (mock.invoke (0 : Nat) [i32 1, i32 2]) =
    .callout 42 [i32 1, i32 2] := by decide

end Test

end Silmaril.Wasm.Component.Engine.Mock
