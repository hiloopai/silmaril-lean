module

public import Silmaril.Wasm.SSA.Fragment.Defs
public import Silmaril.Wasm.Binaryen.Syntax
public import Silmaril.Wasm.Binaryen.Interp

/-!
# The fragment inside Binaryen's folded IR

`ofBExpr?` recognises the fragment in silmaril's layer-D trees
(`Silmaril.Wasm.Binaryen.BExpr`): every operator must be applied to the trees
of all its operands (no stack-style siblings), block types must be empty or
a single integer, `if` conditions are single trees, and only the integer
instructions of `Fragment` occur. `toBExpr?` lowers back (failing only on
indices of `2³²` or more). `ofBFunc?`/`toBFunc?` do the same for functions,
given the function type.

`WVal.toVal`/`WVal.ofVal?` convert values and `flowOut` reads the call outcome
of a final flow of silmaril's native Binaryen interpreter; the adequacy of that
interpreter is proved in `Silmaril.Wasm.SSA.Native.Thms`.

`Thms` proves `toBExpr? e = some b → ofBExpr? b = some e`. The other
direction holds up to `select` annotations (`select (some [t])` is read as
`select none`).
-/

@[expose] public section

namespace Silmaril.Wasm.SSA

open Silmaril.Wasm
open Silmaril.Wasm.Binaryen

/-- Integer value types. -/
def ofValType? : ValType → Option IntType
  | .num (.int t) => some t
  | _ => none

/-- Block types of the fragment. -/
def ofBlockType? : BlockType → Option (Option IntType)
  | .empty => some none
  | .value t => (ofValType? t).map some
  | .typeIdx _ => none

def toBlockType : Option IntType → BlockType
  | none => .empty
  | some t => .value (.num (.int t))

/-- An integer constant's bits at its own type. -/
def WVal.bits : (v : WVal) → BitVec v.type.width
  | .i32 x => x
  | .i64 x => x

/-- Recognise one flat instruction applied to recognised operands. -/
def ofInstr? : Instr → List Expr → Option Expr
  | .intConst t b, [] => some (.op (.const (.ofInt t b)) [])
  | .localGet x, [] => some (.localGet x.toNat)
  | .localSet x, [e] => some (.localSet x.toNat e)
  | .localTee x, [e] => some (.localTee x.toNat e)
  | .intUnOp t op, [a] => if op.valid t then some (.op (.un (.int t op)) [a]) else none
  | .intTestOp t .eqz, [a] => some (.op (.un (.test t)) [a])
  | .convert .wrap, [a] => some (.op (.un .wrap) [a])
  | .convert (.extend s), [a] => some (.op (.un (.extend s)) [a])
  | .intBinOp t op, [a, b] => some (.op (.bin (.int t op)) [a, b])
  | .intRelOp t op, [a, b] => some (.op (.bin (.rel t op)) [a, b])
  | .select none, [a, b, c] => some (.op .select [a, b, c])
  | .select (some [.num (.int _)]), [a, b, c] => some (.op .select [a, b, c])
  | .drop, [e] => some (.drop e)
  | .nop, [] => some .nop
  | .unreachable, [] => some .unreachable
  | .br l, args => if args.length ≤ 1 then some (.br l.toNat args) else none
  | .brIf l, args =>
      if 1 ≤ args.length ∧ args.length ≤ 2 then some (.brIf l.toNat args) else none
  | .return_, args => if args.length ≤ 1 then some (.return_ args) else none
  | _, _ => none

mutual

/-- Recognise a tree of the fragment. -/
def ofBExpr? : BExpr → Option Expr
  | .op i args => do ofInstr? i (← ofBExprs? args)
  | .block bt body => do pure (.block (← ofBlockType? bt) (← ofBExprs? body))
  | .loop bt body => do pure (.loop (← ofBlockType? bt) (← ofBExprs? body))
  | .if_ bt [c] t e => do
      pure (.if_ (← ofBlockType? bt) (← ofBExpr? c) (← ofBExprs? t) (← ofBExprs? e))
  | .if_ _ _ _ _ => none
  | .tryTable .. => none

/-- Recognise a list of trees. -/
def ofBExprs? : List BExpr → Option (List Expr)
  | [] => some []
  | e :: es => do pure ((← ofBExpr? e) :: (← ofBExprs? es))

end

/-- The instruction of an operator. -/
def Op.toInstr? : Op → Option Instr
  | .const v => some (.intConst v.type v.bits)
  | .un (.int t op) => if op.valid t then some (.intUnOp t op) else none
  | .un (.test t) => some (.intTestOp t .eqz)
  | .un .wrap => some (.convert .wrap)
  | .un (.extend s) => some (.convert (.extend s))
  | .bin (.int t op) => some (.intBinOp t op)
  | .bin (.rel t op) => some (.intRelOp t op)
  | .select => some (.select none)

mutual

/-- Lower a fragment expression to a folded tree. -/
def toBExpr? : Expr → Option BExpr
  | .op o args => do
      guard (args.length = o.arity)
      pure (.op (← o.toInstr?) (← toBExprs? args))
  | .localGet i => do pure (.op (.localGet (← Idx.ofNat? i)) [])
  | .localSet i e => do pure (.op (.localSet (← Idx.ofNat? i)) [← toBExpr? e])
  | .localTee i e => do pure (.op (.localTee (← Idx.ofNat? i)) [← toBExpr? e])
  | .drop e => do pure (.op .drop [← toBExpr? e])
  | .nop => some (.op .nop [])
  | .unreachable => some (.op .unreachable [])
  | .block ty body => do pure (.block (toBlockType ty) (← toBExprs? body))
  | .loop ty body => do pure (.loop (toBlockType ty) (← toBExprs? body))
  | .if_ ty c t e => do
      pure (.if_ (toBlockType ty) [← toBExpr? c] (← toBExprs? t) (← toBExprs? e))
  | .br l args => do
      guard (args.length ≤ 1)
      pure (.op (.br (← Idx.ofNat? l)) (← toBExprs? args))
  | .brIf l args => do
      guard (1 ≤ args.length ∧ args.length ≤ 2)
      pure (.op (.brIf (← Idx.ofNat? l)) (← toBExprs? args))
  | .return_ args => do
      guard (args.length ≤ 1)
      pure (.op .return_ (← toBExprs? args))

/-- Lower a list of expressions. -/
def toBExprs? : List Expr → Option (List BExpr)
  | [] => some []
  | e :: es => do pure ((← toBExpr? e) :: (← toBExprs? es))

end

/-- The Wasm result types of a fragment result type. -/
def resultTypes : Option IntType → List ValType
  | none => []
  | some t => [.num (.int t)]

/-- Recognise a function of the fragment, given its type. -/
def ofBFunc? (ft : FuncType) (f : BFunc) : Option FragFunc := do
  let params ← ft.params.mapM ofValType?
  let result ← match ft.results with
    | [] => some none
    | [t] => (ofValType? t).map some
    | _ => none
  let locals ← f.locals.mapM ofValType?
  let body ← ofBExprs? f.body
  pure { params, locals, result, body }

/-- Lower a fragment function, keeping the type index. -/
def toBFunc? (type : TypeIdx) (f : FragFunc) : Option BFunc := do
  pure { type, locals := f.locals.map fun t => .num (.int t), body := ← toBExprs? f.body }

/-! ## Values and flows of silmaril's native interpreter -/

open Silmaril.Wasm.Execution.Core (Val)

/-- A fragment value as a Core value. -/
def WVal.toVal (v : WVal) : Val := Silmaril.Wasm.Binaryen.ofInt v.type v.bits

/-- A Core value as a fragment value, if it is an integer. -/
def WVal.ofVal? : Val → Option WVal
  | .num ⟨.int .i32, x⟩ => some (.i32 x)
  | .num ⟨.int .i64, x⟩ => some (.i64 x)
  | _ => none

/-- The call outcome of a final interpreter flow of a function body (top-first
stack; the body is label `0`). Exceptions and outer branches have none. -/
def flowOut (res : Option IntType) : Silmaril.Wasm.Binaryen.Flow → Option FOut
  | .normal vs | .brk 0 vs | .ret vs =>
      match res with
      | none => some (.ret none)
      | some _ => (vs.head?.bind WVal.ofVal?).map fun v => .ret (some v)
  | .trap => some .trap
  | _ => none

end Silmaril.Wasm.SSA
