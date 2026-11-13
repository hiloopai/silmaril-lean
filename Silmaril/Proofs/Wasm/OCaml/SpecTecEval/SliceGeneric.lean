module

public import Silmaril.Wasm.OCaml.SpecTecEval.Defs
public import Silmaril.Wasm.Verify.Kernel.Defs

/-! Kernel runs of `il/eval.ml` on slices of a list of three **arbitrary** numerals (header:
`Silmaril.Wasm.OCaml.SpecTecEval.Thms`).

`reduce_exp` inspects only the constructor of each element (`NumE _ -> Ok e`), never its
number, so its run on `[a, b, c]` reduces in the kernel with `a`, `b`, `c` free:
`kernel_rfl` (`Silmaril.Wasm.Verify.Kernel`) checks the equations by the kernel's definitional
check alone. The shape (the length and `i`, `n`) stays concrete: the guard
`Z.(i + n) < Z.of_int (List.length es)` branches on it. -/

@[expose] public section
namespace Silmaril.Wasm.OCaml.SpecTecEval

set_option maxRecDepth 100000

/-- At the pin, for all `a b c`: `[a, b, c][1 : 2]` (the boundary) is not reduced,
`[a, b, c][0 : 2]` is `[a, b]` and `[a, b, c][1 : 1]` is `[b]`. -/
theorem slice3_pin (a b c : Nat) :
    (answerTags (runSlice pinProgram [a, b, c] 1 2), answerElems (runSlice pinProgram [a, b, c] 0 2),
      answerElems (runSlice pinProgram [a, b, c] 1 1)) =
    (some (1, 22), some [numE a, numE b], some [numE b]) := by
  kernel_rfl

/-- On main, for all `a b c`: `[a, b, c][1 : 2]` is `[b, c]`, `[a, b, c][0 : 3]` is the whole
list, and `[a, b, c][2 : 2]` (past the end) is not reduced. -/
theorem slice3_main (a b c : Nat) :
    (answerElems (runSlice mainProgram [a, b, c] 1 2), answerElems (runSlice mainProgram [a, b, c] 0 3),
      answerTags (runSlice mainProgram [a, b, c] 2 2)) =
    (some [numE b, numE c], some [numE a, numE b, numE c], some (1, 22)) := by
  kernel_rfl

end Silmaril.Wasm.OCaml.SpecTecEval
