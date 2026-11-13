module

public import Silmaril.Wasm.OCaml.SpecTecEval.Defs

/-! Kernel runs of the pinned `il/eval.ml` on comparisons (header:
`Silmaril.Wasm.OCaml.SpecTecEval.Thms`). -/

@[expose] public section
namespace Silmaril.Wasm.OCaml.SpecTecEval

set_option maxRecDepth 100000

/-- At the pin, `reduce_exp` on `CmpE (op, ot, NumE a, NumE b)` agrees with `Sem.evalExp` for
the six comparisons (including `=` and `≠`, which go through `Il.Eq.eq_exp`) and every operand
pair of `opCases`. -/
theorem cmp_pin_agrees :
    opCases.all (fun (a, b) => (List.range 6).all fun op =>
      agreesOp 6 (semCmp op a b) (opOut (runCmp pinProgram op a b))) = true := by
  decide +kernel

end Silmaril.Wasm.OCaml.SpecTecEval
