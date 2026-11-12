module

public import tests.wasm.auto.FrontBenchX.Defs
public import Silmaril.Wasm.Auto.Front.Thms

/-!
# The front-end benchmark, extended set: refuted cases

Each counterexample (the one `wasm-check` reports) replayed on silmaril-lean's verified
interpreter by kernel evaluation (`wasm_diff_refute`). Not here: `adlersum8-mutant` (a module
with a memory: its kernel instantiation does not finish, see `Proved`); the tool's refutation is
by the compiled interpreter.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.FrontBenchX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Auto.Front
open Silmaril.Wasm.SingleThreaded (profile)
open Silmaril.Wasm.Verify (refOracle)
open Silmaril.Wasm.Auto.FrontBench (requantV0)

/-- Binaryen's `-O2` `requant` does not refine `requant` v0 (the zero point added in 32 bits):
on `(0, 0, 2^31 - 1, 2^31 - 1)` it returns `127`, v0 `-128`. -/
theorem requantO2_not_refines_v0 :
    ¬ ModRefines Rel.eq.toProp (profile refOracle) Silmaril.Wasm.Auto.EquivXBench.requantO2
      requantV0 0 := by
  wasm_diff_refute [Val.i32 0, Val.i32 0, Val.i32 0x7fffffff, Val.i32 0x7fffffff]

/-- Signed division traps on `(-2^31) / (-1)`, where the unsigned one returns. -/
theorem divRemSigned_not_refines :
    ¬ ModRefines Rel.eq.toProp (profile refOracle) divRemSigned divRem 0 := by
  wasm_diff_refute [Val.i32 0x80000000, Val.i32 0xffffffff]

end Silmaril.Wasm.Auto.FrontBenchX
