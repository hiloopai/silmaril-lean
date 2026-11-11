module

public import Silmaril.Wasm.Auto.ESeg.Thms
public import Silmaril.Wasm.Auto.Rules.Thms

/-! # Tests of the segment checker

Small certificates checked by `decide +kernel`: a `local.set`/`local.get` pair is a
`local.tee`; a dropped division keeps its trap; a recomputed division stored in a scratch
local is the same body; and the computed rewrites of the second family.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.ESeg.Tests

open Silmaril.Wasm Silmaril.Wasm.Auto.EGraph Silmaril.Wasm.Auto.Rules Silmaril.Wasm.Auto.ESeg

/-- `local.set 1; local.get 1` is `local.tee 1`. -/
theorem tee_form :
    SegEquiv [.i32, .i32]
      [.localGet (lidx 0), .intConst .i32 1, .intBinOp .i32 .add, .localSet (lidx 1),
        .localGet (lidx 1)]
      [.localGet (lidx 0), .intConst .i32 1, .intBinOp .i32 .add, .localTee (lidx 1)] :=
  segEquiv_of_checkSeg
    { stack := [[]], locs := [[], []], covA := [.total, .total, .total, .total],
      covB := [.total, .total, .total, .total] } library_sound (by decide +kernel)

/-- A quotient stored in a scratch local and recomputed is one division (the locals differ). -/
theorem scratch_div :
    BodyEquiv [.i32, .i32, .i32]
      [.localGet (lidx 0), .localGet (lidx 1), .intBinOp .i32 (.div .unsigned),
        .localSet (lidx 2), .localGet (lidx 0), .localGet (lidx 1),
        .intBinOp .i32 (.div .unsigned)]
      [.localGet (lidx 0), .localGet (lidx 1), .intBinOp .i32 (.div .unsigned)] :=
  bodyEquiv_of_checkBody
    { stack := [[]], covA := [.total, .total, .total, .sub 3 [] [], .sub 3 [] []],
      covB := [.total, .total, .total, .sub 3 [] []] } library_sound (by decide +kernel)

/-- Dropping a division is not `nop`: the certificate cannot cover the guard (no theorem);
the check fails. -/
example :
    checkBody [.i32, .i32] library
      [.localGet (lidx 0), .localGet (lidx 1), .intBinOp .i32 (.div .unsigned), .drop] []
      { stack := [], covA := [.total, .total, .total], covB := [.total, .total] } =
        false := by decide +kernel

/-- Signed division by 4 in the bias form (a computed rewrite of the second family). -/
theorem sdiv4 :
    BodyEquiv [.i32]
      [.localGet (lidx 0), .intConst .i32 4, .intBinOp .i32 (.div .signed)]
      [.localGet (lidx 0), .localGet (lidx 0), .intConst .i32 31, .intBinOp .i32 (.shr .signed),
        .intConst .i32 30, .intBinOp .i32 (.shr .unsigned), .intBinOp .i32 .add,
        .intConst .i32 2, .intBinOp .i32 (.shr .signed)] :=
  bodyEquiv_of_checkBody
    { stack := [[.comp2 []]], covA := [.total, .sub 1 [] [.comp2 []]],
      covB := [.total, .total] } library_sound (by decide +kernel)

end Silmaril.Wasm.Auto.ESeg.Tests
