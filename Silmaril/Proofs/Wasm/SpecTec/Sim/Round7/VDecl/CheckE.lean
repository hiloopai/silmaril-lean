module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VDecl.Defs

/-!
# Round 7, memory SIMD: `otherwise` at any depth, and the atoms of the conclusion alternatives

Kernel computations (`decide +kernel`, kernel reduction, no native code) on the relations as the fixed
wasm-3.0 script's environment finds them:

* `read_elseDeep`, `step_elseDeep`: the rules with an `otherwise` premise at any depth are those
  of `VElse.read_else` for `Step_read`, and there are none for `Step`;
* `step_ctxOk`: the premises of `Step` rules 1–5 are `RG`, or calls of `Step`/`Step_read` with
  `RG` arguments, and rule 23 ends in `VSTORE`;
* `read_elseAltsOk`: rule 43's conclusion alternatives all end in `VLOAD`, and every later
  `otherwise` rule has an atom other than `VLOAD` on all its alternatives.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VDecl

set_option maxRecDepth 100000

/-- The rules of `Step_read` with an `otherwise` premise at any depth. -/
theorem read_elseDeep : VElse.onRel "Step_read" elseFreeIdx = some [3, 5, 21, 29, 30, 32, 33, 34,
    36, 37, 54, 55, 57, 58, 59, 61, 62, 66, 68, 84, 85, 90, 91, 92, 96, 97, 101, 102] := by
  decide +kernel

/-- No rule of `Step` has an `otherwise` premise at any depth. -/
theorem step_elseDeep : VElse.onRel "Step" elseFreeIdx = some [] := by decide +kernel

/-- Rule 43 ends in `VLOAD` on every conclusion alternative; every later `otherwise` rule ends in
another atom on every alternative. -/
theorem read_elseAltsOk : VElse.onRel "Step_read" elseAltsOk = some true := by decide +kernel

/-- The premises of `Step` rules 1–5 are `RG` or `RG` calls of `Step`/`Step_read`, and rule 23
ends in `VSTORE` on every conclusion alternative. -/
theorem step_ctxOk : VElse.onRel "Step" stepCtxOk = some true := by decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.VDecl
