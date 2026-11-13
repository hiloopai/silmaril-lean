module

public import Silmaril.Wasm.Replace.Congruence.Defs

/-!
# A non-identity instance of the replacement congruence: definitions

silmaril-lean's `V1.Execution.eq_of_forall_callSim` shows that `CallSim` at every store forces
`a = b`. This example shows the `Reach`-restricted hypothesis of `Silmaril.Wasm.Replace` does not
collapse the same way: a store, a step-closed `Reach`, two distinct addresses holding distinct
instances, and `CallSimOn` for them.

* `idleFn ls`: a function of type `[] -> []` with locals `ls` and the empty body.
* `store`: over the closed host (`H := Empty`), address `0` holds `idleFn []` and address `1`
  holds `idleFn [.i32]`. The two instances differ (in their locals) but cannot be told apart by
  a caller: invoking either on any value stack returns that stack unchanged.
* `Reach := (· = store)`. The store has no globals and no memories, so with the closed host no
  step writes it (`stepClosed_eq_of_fixed`).

The source, an earlier development `Silmaril/Wasm/Equiv/ReplaceExample.lean`, uses the two
bodies `i32.const x; i32.const y; i32.add` and `i32.const y; i32.const x; i32.add`, and proves
that their runs are forced with a determinism theorem of its `Compile` layer, which silmaril-lean
does not have. Here the runs are forced by direct one-step inversions
(`Silmaril.Proofs.Wasm.Replace.Example.Inversion`); an empty body keeps them to the invocation,
label and frame rules, at the price of a less arithmetic example.
-/

@[expose] public section

namespace Silmaril.Wasm.Replace.Example

open Silmaril.Wasm.V1.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1 (Func FuncType ValType)

/-- The type `[] -> []`. -/
def unitType : Silmaril.Wasm.V1.FuncType := ⟨[], []⟩

/-- A function of type `0` with locals `ls` and the empty body. -/
def idleFn (ls : List Silmaril.Wasm.V1.ValType) : Silmaril.Wasm.V1.Func := ⟨⟨0⟩, ls, []⟩

/-- The module instance owning both functions. -/
def inst : ModuleInst := { types := [unitType], funcs := [⟨0⟩, ⟨1⟩] }

/-- The store of the example: `idleFn []` at address `0`, `idleFn [.i32]` at address `1`. -/
def store : Store Empty :=
  { funcs := [.wasm unitType inst (idleFn []), .wasm unitType inst (idleFn [.i32])] }

/-- The reachability predicate of the example: the one store the module has. -/
def Reach : Store Empty → Prop := (· = store)

end Silmaril.Wasm.Replace.Example
