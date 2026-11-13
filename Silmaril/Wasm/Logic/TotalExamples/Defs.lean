module

public import Silmaril.Wasm.Logic.Total.Defs
public import Silmaril.Wasm.Logic.HoareExamples.Defs

/-!
# A worked example for total correctness: programs

`countLoop bt`: a `loop` (of block type `bt`, with no parameters or results)
that decrements local `0` and branches back while it is nonzero:
`loop bt (local.get 0; i32.const 1; i32.sub; local.tee 0; br_if 0)`.
It is checked in `Silmaril.Wasm.Logic.TotalExamples.Thms` with the loop rule with a
variant (`Hoare.TWP.loop`), the variant being the value of local `0`.

`count f` is that value (as a natural number) when local `0` of frame `f` is
the only local and holds an `i32`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.TotalExamples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.HoareExamples (l0 x0)

/-- The count-down loop. -/
def countLoop (bt : BlockType) : List Instr :=
  [.loop bt [.localGet x0, .intConst .i32 1, .intBinOp .i32 .sub, .localTee x0, .brIf l0]]

/-- The value of the only local, if it is an `i32`. -/
def count (f : Frame) : Nat :=
  match f.locals with
  | [some (.num ⟨.int .i32, n⟩)] => n.toNat
  | _ => 0

end Silmaril.Wasm.Logic.TotalExamples
