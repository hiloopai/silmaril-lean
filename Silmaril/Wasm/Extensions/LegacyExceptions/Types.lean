module

public import Silmaril.Wasm.Extensions.BinaryenMemory.Types

/-! # Retained legacy exception-handling syntax

Legacy try/catch/catch_all/delegate bodies remain part of the AST. The Core
exception proposal's try_table/throw_ref syntax and all existing memory profiles
remain available through the shared structured syntax and base leaves.
-/

@[expose] public section

namespace Silmaril.Wasm.Extensions.LegacyExceptions

inductive Leaf where
  | base (i : BinaryenMemory.Leaf)
  | rethrow (label : LabelIdx)
  | try_ (type : BlockType) (body : List (Structured.Instr Leaf))
      (catches : List (TagIdx × List (Structured.Instr Leaf)))
      (catchAll : Option (List (Structured.Instr Leaf)))
  | delegate (type : BlockType) (body : List (Structured.Instr Leaf)) (label : LabelIdx)
  deriving Repr

abbrev Instr := Structured.Instr Leaf
abbrev Expr := Structured.Expr Leaf
abbrev Func := Declaration.Func ValType Expr
abbrev Module := Structured.FunctionModule Expr

mutual
  def leafDepth : Leaf → Nat
    | .base _ | .rethrow _ => 1
    | .try_ _ body catches all =>
        max (exprDepth body) (max (handlerDepth catches) (match all with | none => 0 | some is => exprDepth is)) + 1
    | .delegate _ body _ => exprDepth body + 1
  def instructionDepth : Instr → Nat
    | .leaf i => leafDepth i
    | .block _ body | .loop _ body | .tryTable _ _ body => exprDepth body + 1
    | .if_ _ a b => max (exprDepth a) (exprDepth b) + 1
  def exprDepth : Expr → Nat
    | [] => 0
    | i :: is => max (instructionDepth i) (exprDepth is)
  def handlerDepth : List (TagIdx × Expr) → Nat
    | [] => 0
    | (_, is) :: rest => max (exprDepth is) (handlerDepth rest)
end

/-- Context/data-index syntax utility only. A legacy try is represented as a
block whose body lists all retained alternatives in wire order; no execution
simulation is asserted by this shape. -/
def leafContextShapeFuel : Nat → Leaf → Wasm.Instr
  | 0, _ => .nop
  | _ + 1, .base i => i.contextShape
  | _ + 1, .rethrow _ => .nop
  | fuel + 1, .try_ t body catches all =>
      let shape := Structured.Expr.contextShape (leafContextShapeFuel fuel)
      .block t (shape body ++ catches.flatMap (fun c => shape c.2) ++ all.toList.flatMap shape)
  | fuel + 1, .delegate t body _ =>
      .block t (Structured.Expr.contextShape (leafContextShapeFuel fuel) body)

def Leaf.contextShape (i : Leaf) : Wasm.Instr := leafContextShapeFuel (leafDepth i) i

def contextShape (m : Module) : SharedMemory.Module :=
  m.contextShape (Structured.Expr.contextShape Leaf.contextShape)

end Silmaril.Wasm.Extensions.LegacyExceptions
