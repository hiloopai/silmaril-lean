module

public import Silmaril.Wasm.Binaryen.Syntax

@[expose] public section

/-! # Vacuum, anchored nop and constant-drop removal

The part of Binaryen's `Vacuum` (`src/passes/Vacuum.cpp`) that the code simulation of
`Execution/Core/Sim` proves in both directions without typing: a `nop`, or a `drop` of
a constant leaf, is removed when the code that follows it in the same sequence starts
with constants and then a flat non-constant instruction other than `throw_ref` (the
**anchor**). Bottom-up; a run of removable trees before one anchor is removed at once.

The anchor is what makes the reverse simulation work: the side that kept the removed
code runs it away just before the anchor steps, and the anchor's step is matched
by the same step (`Binaryen/VacuumLiteSim.lean`). A `nop` with no anchor after it (at
the end of a body, or before a structured instruction, whose body may change) stays.
-/

namespace Silmaril.Wasm.Binaryen.VacuumLite

/-- A constant instruction (a value on the stack). -/
def constInstr : Instr → Bool
  | .intConst .. | .floatConst .. | .vecConst .. => true
  | _ => false

/-- An anchor: a flat non-constant instruction other than `throw_ref`. -/
def anchorInstr (i : Instr) : Bool := !constInstr i && !(i matches .throwRef)

/-- A removable tree: `nop`, or the `drop` of an integer constant leaf. -/
def removable : BExpr → Bool
  | .op .nop [] => true
  | .op .drop [.op (.intConst ..) []] => true
  | _ => false

mutual
/-- The first non-constant instruction of a tree's lowering: `none` when the tree
lowers to constants only, `some true` when it is an anchor. -/
def headE : BExpr → Option Bool
  | .op i args => match headL args with
    | some b => some b
    | none => if constInstr i then none else some (anchorInstr i)
  | .if_ _ c _ _ => match headL c with
    | some b => some b
    | none => some false
  | _ => some false
/-- `headE` of a sequence. -/
def headL : List BExpr → Option Bool
  | [] => none
  | e :: es => match headE e with
    | some b => some b
    | none => headL es
end

mutual
/-- Vacuum the children of a tree. -/
def vacE : BExpr → BExpr
  | .op i args => .op i (vacL args)
  | .block bt b => .block bt (vacL b)
  | .loop bt b => .loop bt (vacL b)
  | .if_ bt c t e => .if_ bt (vacL c) (vacL t) (vacL e)
  | .tryTable bt cs b => .tryTable bt cs (vacL b)
/-- Vacuum a sequence: drop a removable tree whose (vacuumed) tail is anchored. -/
def vacL : List BExpr → List BExpr
  | [] => []
  | e :: es =>
    let es' := vacL es
    let e' := vacE e
    if removable e' && headL es' == some true then es' else e' :: es'
end

/-- The pass on a module. -/
def vacuumLite (m : BModule) : BModule :=
  { m with funcs := m.funcs.map fun f => { f with body := vacL f.body } }

end Silmaril.Wasm.Binaryen.VacuumLite
