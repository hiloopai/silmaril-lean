module

public import Silmaril.Wasm.OCaml.SpecTecEval.Defs
public import Silmaril.Wasm.SpecTec.Broken.Thms

/-! Kernel runs of the pinned `il/eval.ml` on slices (header: `Silmaril.Wasm.OCaml.SpecTecEval.Thms`). -/

@[expose] public section
namespace Silmaril.Wasm.OCaml.SpecTecEval

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000

/-- The strict slice, by its two public facts: undefined at the boundary
(`sliceEvalMl?_boundary`) and `Value.slice?` elsewhere (`sliceEvalMl?_eq_slice?`). -/
theorem sliceEvalMl?_list (vs : List Value) (i n : Nat) :
    Silmaril.Wasm.SpecTec.Broken.sliceEvalMl? (.list vs) i n =
      if i + n = vs.length then none else Value.slice? (.list vs) i n := by
  by_cases h : i + n = vs.length
  · simp only [h, ↓reduceIte]
    exact (Silmaril.Wasm.SpecTec.Broken.sliceEvalMl?_boundary h).2.1
  · simp only [h, ↓reduceIte]
    exact Silmaril.Wasm.SpecTec.Broken.sliceEvalMl?_eq_slice? fun bs hbs => by
      cases hbs
      exact h

theorem slice_pin_agrees_aux :
    sliceCases.all (fun c =>
      agreesSlice (if c.2.1 + c.2.2 = (c.1.map natV).length then none
          else Value.slice? (.list (c.1.map natV)) c.2.1 c.2.2)
        (sliceOut (runSlice pinProgram c.1 c.2.1 c.2.2))) = true := by
  decide +kernel

/-- At the pin, `reduce_exp` on `es[i : n]` agrees with `Broken.sliceEvalMl?`, the strict
transcription of `eval.ml:284`, on every case of `sliceCases`. -/
theorem slice_pin_agrees :
    sliceCases.all (fun c =>
      agreesSlice (Silmaril.Wasm.SpecTec.Broken.sliceEvalMl? (.list (c.1.map natV)) c.2.1 c.2.2)
        (sliceOut (runSlice pinProgram c.1 c.2.1 c.2.2))) = true := by
  simpa only [sliceEvalMl?_list] using slice_pin_agrees_aux

end Silmaril.Wasm.OCaml.SpecTecEval
