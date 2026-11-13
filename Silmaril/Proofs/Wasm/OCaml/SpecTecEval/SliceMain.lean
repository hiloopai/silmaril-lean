module

public import Silmaril.Wasm.OCaml.SpecTecEval.Defs

/-! Kernel runs of `il/eval.ml` on main on slices (header: `Silmaril.Wasm.OCaml.SpecTecEval.Thms`). -/

@[expose] public section
namespace Silmaril.Wasm.OCaml.SpecTecEval

set_option maxRecDepth 100000

/-- On main, `reduce_exp` on `es[i : n]` agrees with Silmaril's corrected `Sem.Value.slice?` on
every case of `sliceCases`. -/
theorem slice_main_agrees :
    sliceCases.all (fun c =>
      agreesSlice (Silmaril.SpecTec.Sem.Value.slice? (.list (c.1.map natV)) c.2.1 c.2.2)
        (sliceOut (runSlice mainProgram c.1 c.2.1 c.2.2))) = true := by
  decide +kernel

end Silmaril.Wasm.OCaml.SpecTecEval
