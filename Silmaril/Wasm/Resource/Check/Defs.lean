module

public import Silmaril.Wasm.Resource.Handle.Defs
public import Silmaril.Wasm.Verify.Check.Defs

@[expose] public section

/-!
# Checking handle protocols on modules

Computable checks for the client handle sentence (`clientSpec`) on Core 3.0 modules, run by kernel
evaluation.

* **Refutation** (`firstCall?`): some export call (candidate arguments `0`/`1`), run by
  silmaril-lean's verified interpreter, reaches a call of import `k` (`use` or `free`) with one
  argument **before any other import call**. The play is then `[call j args, icall k [h]]`: a use
  or free with no handle live, rejected by the client sentence whatever the environment does
  (`client_refuted`). This catches use-before-alloc and free of a never-allocated handle.
* **Proof** for clients that never use or free (`clientSpec_of_neverCall`): the call-graph
  verifier `Silmaril.Wasm.Verify.check` proves that `use` and `free` are never called.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
open Silmaril.Wasm.Verify

/-- One argument. -/
def oneArg (args : List Val) : Bool := args.length == 1

/-- The type of import `k` of a module. -/
def importType? (m : Module) (k : Nat) : Option FnType :=
  (validate? m).bind fun mt => ((CExternType.funcs mt.imports)[k]?).bind FnType.ofDefType?

/-- **The first-call refuter**: an export call whose first import call is a call of `k` with one
argument. -/
def firstCall? (m : Module) (k : Nat) : Option Cex :=
  (importType? m k).bind fun imp => refuteStore (instOf m).store (instOf m).addrs imp k oneArg

end Silmaril.Wasm.Resource
