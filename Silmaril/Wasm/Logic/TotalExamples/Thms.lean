module

public import Silmaril.Proofs.Wasm.Logic.TotalExamples.Count

/-!
# A worked example for total correctness

`countLoop_twp` (`Silmaril.Proofs.Wasm.Logic.TotalExamples.Count`): the count-down
loop `countLoop bt` terminates from every frame whose only local is a nonzero
`i32`, leaving local `0` equal to `0`, for every profile and host relation,
proved with the loop rule with a variant (`Hoare.TWP.loop`). It is stated for
any module instance in which `bt` is the empty block type.
-/
