module

public import tests.wasm.auto.FrontBenchX.Defs
public import Silmaril.Wasm.Auto.Front.Thms

/-!
# The front-end benchmark, extended set: proved cases

The cases the extended summaries settle, as theorems at **every** profile and for both
front-end relations, by the tactic `wasm_prove` (kernel evaluation of the proving stages).

Not here: `adlersum8-O2`. Its modules have a memory, and instantiating a one-page memory (and
its data segment) in the kernel did not finish (stopped at 44 GB after 6 min), so the case is
proved by the compiled checker only (`wasm-check`, sound by
`Silmaril.Wasm.Auto.Front.checkRefines_proved`, trusting the compiler).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.FrontBenchX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Auto.Front
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Auto.FrontBench (requantFixed)

/-- The `requant` kernel is equivalent to its Binaryen `-O2` output (and `-O3`, the
same text), at every profile. -/
theorem requantO2_equiv (R : Rel) (P : Profile) :
    ModEquiv R.toProp P Silmaril.Wasm.Auto.EquivXBench.requantO2 requantFixed 0 := by
  wasm_prove

/-- `(x / y) * y + x % y` is equivalent to its Binaryen `-O2` output, traps included. -/
theorem divRemO2_equiv (R : Rel) (P : Profile) : ModEquiv R.toProp P divRemO2 divRem 0 := by
  wasm_prove

/-- `x % y + y * (x / y)` is equivalent to `(x / y) * y + x % y`, traps included. -/
theorem divRemRef_equiv (R : Rel) (P : Profile) : ModEquiv R.toProp P divRemRef divRem 0 := by
  wasm_prove

/-- The 64-bit counter is equivalent to its Binaryen `-O2` output. -/
theorem counterO2_equiv (R : Rel) (P : Profile) : ModEquiv R.toProp P counterO2 counter 0 := by
  wasm_prove

end Silmaril.Wasm.Auto.FrontBenchX
