module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VElse.Defs

/-!
# Round 7, memory SIMD: the `otherwise` rules of `Step_read` and `Step`, by the kernel

Kernel computations (`decide +kernel`, kernel reduction, no native code) on the relations as the fixed
wasm-3.0 script's environment finds them.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VElse

set_option maxRecDepth 100000

/-- The `otherwise` rules of `Step_read` (0-based indices). -/
theorem read_else : onRel "Step_read" elseIdx = some [3, 5, 21, 29, 30, 32, 33, 34, 36, 37, 54,
    55, 57, 58, 59, 61, 62, 66, 68, 84, 85, 90, 91, 92, 96, 97, 101, 102] := by
  decide +kernel

/-- `Step` has no `otherwise` rule. -/
theorem step_else : onRel "Step" elseIdx = some [] := by decide +kernel

/-- Rule 43 of `Step_read` ends its left-hand side with `VLOAD`. -/
theorem read_43_atom : onRel "Step_read" (fun rules => rules[43]?.bind ruleAtom) =
    some (some "VLOAD") := by
  decide +kernel

/-- Every `otherwise` rule of `Step_read` after 43 ends its left-hand side with an instruction
other than rule 43's. -/
theorem read_elseOk : onRel "Step_read" elseOk = some true := by decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.VElse
