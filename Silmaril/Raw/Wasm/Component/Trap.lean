module

public import Silmaril.Wasm.Component.Reference.Trap.Defs

/-!
# Component Model trap reasons

`TrapReason` has one constructor per distinct trap site of the Canonical ABI reference
`definitions.py` at component-model `a25fc0b` (every `trap_if`, plus core traps,
uncaught exceptions and host traps), and `TrapReason.wasmtimeMessage` gives the wasmtime
`a7b4f29` trap message (`crates/environ/src/trap_encoding.rs`, and `bail!` strings in
`crates/wasmtime/src/runtime/component`) that the `.wast` tests match as a substring.

**The specification compares traps only as "some trap".** The reason is informative:
it documents which check fired and lets differential tests compare messages. Where
wasmtime has no dedicated message, `wasmtimeMessage` returns a descriptive string that
is not claimed to match wasmtime. The constructors whose strings are such descriptive
fallbacks (no wasmtime `a7b4f29` or `.wast` counterpart) are exactly: `setNotEmpty`,
`backpressureUnderflow`, `contextIndex`, `reentrantHostCall` and `internal`
(`hostTrap msg` returns the host's own message). All other strings occur in wasmtime
sources or in `.wast` `assert_trap` expectations.

Special constructors:
* `cannotLeave` is REF `trap_if(not task.inst.may_leave)` at every builtin entry,
  including `thread.index` and `thread.resume-later`;
* `reentrantHostCall` is reserved for embeddings and is not produced by the
  specification;
* `internal msg` marks a state unreachable in validated runs (a Python assert that the model must
  still handle); its unreachability is not proved here;
* `exhausted` is fuel exhaustion of the executable machine, not a REF trap.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

namespace TrapReason

theorem wasmtimeMessage_dropBusy_writable_stream :
    (dropBusy false false).wasmtimeMessage = "cannot drop busy stream" :=
  rfl

theorem wasmtimeMessage_dropBusy_readable_stream :
    (dropBusy false true).wasmtimeMessage = "cannot remove busy stream" :=
  rfl

theorem wasmtimeMessage_cannotBlockSync :
    cannotBlockSync.wasmtimeMessage = "cannot block a synchronous task before returning" :=
  rfl

end TrapReason

end Silmaril.Wasm.Component
