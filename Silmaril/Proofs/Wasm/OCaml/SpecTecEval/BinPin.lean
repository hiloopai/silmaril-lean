module

public import Silmaril.Wasm.OCaml.SpecTecEval.Defs

/-! Kernel runs of the pinned `il/eval.ml` on arithmetic (header:
`Silmaril.Wasm.OCaml.SpecTecEval.Thms`). -/

@[expose] public section
namespace Silmaril.Wasm.OCaml.SpecTecEval

set_option maxRecDepth 100000

/-- At the pin, `reduce_exp` on `BinE (op, ot, NumE a, NumE b)` agrees with `Sem.evalExp` for
the six numeric operators and every operand pair of `opCases`. -/
theorem bin_pin_agrees :
    opCases.all (fun (a, b) => (List.range 6).all fun op =>
      agreesOp 5 (semBin op a b) (opOut (runBin pinProgram op a b))) = true := by
  decide +kernel

end Silmaril.Wasm.OCaml.SpecTecEval
