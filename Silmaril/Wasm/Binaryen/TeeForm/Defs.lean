module

public import Silmaril.Wasm.Binaryen.Syntax
public import Silmaril.Wasm.Binaryen.Exe.Valid

@[expose] public section

/-! # Tee formation (a SimplifyLocals subrule): run functions

Binaryen's `SimplifyLocals` turns a store immediately followed by a read of the same
local into a tee:

  `local.set x; local.get x` ⟶ `local.tee x`

Unoptimised code (clang `-O0`, rustc `-O0`) does this constantly. The read is found
as the *leftmost leaf* of the next sibling tree (`headGet?`), which covers both the
flat form and the folded form `local.set x (e); op (local.get x) …`, where it becomes
`op (local.tee x (e)) …`. The rest of the next tree is left unchanged in that round.

Run functions only; soundness (at every numerical profile) is in
`Silmaril.Wasm.Binaryen.TeeForm.Thms`.
-/

namespace Silmaril.Wasm.Binaryen.TeeForm

open Silmaril.Wasm Silmaril.Wasm.Binaryen

/-- Replace the leftmost leaf of a tree, when it is `local.get x`, by `r`. -/
def headGet? (x : LocalIdx) (r : BExpr) : BExpr → Option BExpr
  | .op (.localGet y) [] => if y == x then some r else none
  | .op i (a :: args) => (headGet? x r a).map fun a' => .op i (a' :: args)
  | .if_ bt (c :: cs) t e => (headGet? x r c).map fun c' => .if_ bt (c' :: cs) t e
  | _ => none
termination_by e => sizeOf e

mutual
def elimE : BExpr → BExpr
  | .op i args => .op i (elimL args)
  | .block bt b => .block bt (elimL b)
  | .loop bt b => .loop bt (elimL b)
  | .if_ bt c t e => .if_ bt (elimL c) (elimL t) (elimL e)
  | .tryTable bt cs b => .tryTable bt cs (elimL b)
termination_by x => sizeOf x

def elimL : List BExpr → List BExpr
  | .op (.localSet x) args :: e :: es =>
    match headGet? x (.op (.localTee x) (elimL args)) e with
    | some e' => e' :: elimL es
    | none => .op (.localSet x) (elimL args) :: elimL (e :: es)
  | [] => []
  | e :: es => elimE e :: elimL es
termination_by es => sizeOf es
end

def teeForm (m : BModule) : BModule :=
  { m with funcs := m.funcs.map fun f => { f with body := elimL f.body } }

/-- **The tee-formation stage**: the rewrite, kept when the validator accepts it. -/
def teeFormChecked (m : BModule) : BModule :=
  let m' := teeForm m
  if Exe.validOk m' then m' else m

/-- The source base pairs of the rewrite (the result on the left, the original on the right), for
its soundness proof and for the body relation of `teeForm`
(`Silmaril.Wasm.Binaryen.TeeForm.teeForm_bodiesRel`). -/
inductive tfBI : List Instr → List Instr → Prop where
  | mk (x : LocalIdx) : tfBI [.localTee x] [.localSet x, .localGet x]

end Silmaril.Wasm.Binaryen.TeeForm
