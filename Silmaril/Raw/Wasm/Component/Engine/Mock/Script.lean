module

public import Silmaril.Wasm.Component.Reference.Engine.Mock.Script.Defs

public import Silmaril.Wasm.Component.Engine.Interface

/-!
# Script programs of the Mock core engine

The reference test suite `run_tests.py` (`design/mvp/canonical-abi/run_tests.py` of component-model
a25fc0b, next to the pinned `definitions.py`)
implements core functions as Python lambdas that call canon built-ins and read or write
memories of arbitrary size and address type (`'i32'` or `'i64'`). The Mock engine
(`Engine/Mock.lean`) transcribes such functions as *Script* programs: a small first-order
register language whose modules are plain data with decidable equality. It is not WebAssembly:
it has no operand stack, no structured control and no validation beyond scoping of indices
(`Module.validate`). It exists so that component-level tests can be ported, and so that the
canonical ABI's memory64 paths can be executed (Lime1 and V1 only have i32 memories).

* Registers are `List FlatValue`, indexed by `Nat`. Reading a register at or beyond the
  current register-file length (one past the highest register written so far) traps; writing
  past the end pads the gap with `i32` zeros, so those intermediate registers read as `i32` 0.
* `call f args results` calls the function with module-local index `f` (imports first, as in
  WebAssembly); `callIndirect` goes through a funcref table (trapping, like `call_indirect`,
  unless the callee's type equals the declared type) and `callAddr` through a function address
  held in a register (checking only the argument types). Host functions become callouts of the
  engine.
* Memory accesses name a module-local memory, a pointer register (which must hold an integer of
  the memory's address type) and a static offset; bounds are checked on the natural-number
  effective address, so an i64 address is never truncated.
* Control flow is by explicit program counter (`branchIfZero`, `jump`), so loops are allowed;
  falling off the end of the code traps.

Sizes of Mock memories are in BYTES (not pages), including in the `CoreExternType.memory`
limits that the engine reports for them. Mock tables carry an address type (`i32` or `i64`), so
the memory64/table64 paths (`thread.new-indirect` with an `i64` table index) can be exercised.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Mock

namespace Module

variable (m : Module)

end Module

end Silmaril.Wasm.Component.Engine.Mock
