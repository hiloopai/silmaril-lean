module

public import Silmaril.Wasm.Binaryen.Syntax
public import Silmaril.Wasm.Binaryen.Exe.Valid

@[expose] public section

/-! # Dropped local reads (a Vacuum subrule): run functions

Binaryen's `Vacuum` removes a dropped expression without side effects. Here:

  `local.get x; drop` ⟶ `nop`

in folded (`drop (local.get x)`) and flat form. The `nop` is then removed by
silmaril's anchored `vacuum`. `local.get x; drop` arises from silmaril's `rse-line`
run function and the verified `rse-line` stage.

Run functions only; soundness (at every numerical profile) is in
`Silmaril.Wasm.Binaryen.DropGet.Thms`.
-/

namespace Silmaril.Wasm.Binaryen.DropGet

open Silmaril.Wasm Silmaril.Wasm.Binaryen

mutual
def elimE : BExpr → BExpr
  | .op .drop [.op (.localGet _) []] => .op .nop []
  | .op i args => .op i (elimL args)
  | .block bt b => .block bt (elimL b)
  | .loop bt b => .loop bt (elimL b)
  | .if_ bt c t e => .if_ bt (elimL c) (elimL t) (elimL e)
  | .tryTable bt cs b => .tryTable bt cs (elimL b)
termination_by x => sizeOf x

def elimL : List BExpr → List BExpr
  | .op (.localGet _) [] :: .op .drop [] :: es => .op .nop [] :: elimL es
  | [] => []
  | e :: es => elimE e :: elimL es
termination_by es => sizeOf es
end

def dropGet (m : BModule) : BModule :=
  { m with funcs := m.funcs.map fun f => { f with body := elimL f.body } }

/-- **The dropped-read stage**: the rewrite, kept when the validator accepts it. -/
def dropGetChecked (m : BModule) : BModule :=
  let m' := dropGet m
  if Exe.validOk m' then m' else m

/-- The source base pairs of the rewrite (the original on the left), for its soundness proof and
for the body relation of `dropGet` (`Silmaril.Wasm.Binaryen.DropGet.dropGet_bodiesRel`). -/
inductive dgBI : List Instr → List Instr → Prop where
  | mk (x : LocalIdx) : dgBI [.localGet x, .drop] [.nop]

end Silmaril.Wasm.Binaryen.DropGet
