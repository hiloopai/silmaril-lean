module

public import Silmaril.Wasm.Binaryen.Lower
public import Silmaril.Wasm.Validation.Intrinsic.Defs

/-! Intrinsic folded layer-D trees. Operands are evaluated left to right, each from
an empty stack relative to its caller. The fragment makes no changes to local
initialization, and control nodes take no stack parameters. -/

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Intrinsic

open Validation
open Validation.Intrinsic (Body Step LocalRef FunctionRef LabelRef)

/-- The subset of Core result vectors representable here: void or one value. -/
def resultTy : Option CValType → Ty (.list .val)
  | none => .nil
  | some type => .cons type .nil

@[simp] theorem resultTy_toList (result : Option CValType) :
    (resultTy result).toList = result.toList := by cases result <;> rfl

mutual

/-- A folded expression, indexed by the Core context and its zero or one result. -/
inductive Expr : Context → Option CValType → Type where
  | nop {context} : Expr context none
  | intConst {context} (type : IntType) (bits : BitVec type.width) :
      Expr context (some (.num (.int type)))
  | localGet {context type} (ref : LocalRef context ⟨.set, type⟩) : Expr context (some type)
  | drop {context type} (valid : TyOk context.toTypeCtx type) (value : Expr context (some type)) :
      Expr context none
  | call {context params result} (ref : FunctionRef context params (resultTy result))
      (args : Operands context params.toList) : Expr context result
  | block {context result} (type : BlockType) (valid : BlockTypeOk context type [] result.toList)
      (body : Expr (context.withLabel result.toList) result) : Expr context result
  | loop {context result} (type : BlockType) (valid : BlockTypeOk context type [] result.toList)
      (body : Expr (context.withLabel []) result) : Expr context result
  | if_ {context result} (type : BlockType) (valid : BlockTypeOk context type [] result.toList)
      (cond : Expr context (some .i32))
      (thenExpr elseExpr : Expr (context.withLabel result.toList) result) : Expr context result
  | brIf {context} (label : LabelRef context []) (cond : Expr context (some .i32)) : Expr context none

/-- Exactly one single-valued tree per call parameter, in stack order. -/
inductive Operands : Context → List CValType → Type where
  | nil {context} : Operands context []
  | cons {context type tail} (valid : TyOk context.toTypeCtx type) (head : Expr context (some type))
      (rest : Operands context tail) : Operands context (type :: tail)

end

mutual

def Expr.erase {context result} : Expr context result → BExpr
  | .nop => .op .nop []
  | .intConst type bits => .op (.intConst type bits) []
  | .localGet ref => .op (.localGet ref.index) []
  | .drop _ value => .op .drop [value.erase]
  | .call ref args => .op (.call ref.ref.index) args.erase
  | .block type _ body => .block type [body.erase]
  | .loop type _ body => .loop type [body.erase]
  | .if_ type _ cond thenExpr elseExpr => .if_ type [cond.erase] [thenExpr.erase] [elseExpr.erase]
  | .brIf label cond => .op (.brIf label.index) [cond.erase]

def Operands.erase {context types} : Operands context types → List BExpr
  | .nil => []
  | .cons _ head rest => head.erase :: rest.erase

end

/-- Compose at a shared stack boundary with no updates to local initialization. -/
def thenPlain {context input middle output} (first : Body context (.plain input middle))
    (rest : Body context (.plain middle output)) : Body context (.plain input output) :=
  .seq first (by simp) rest

/-- Evaluate an operand with the previously pushed value underneath it. -/
def keepValue {context type output} (valid : TyOk context.toTypeCtx type)
    (body : Body context (.plain [] output)) : Body context (.plain [type] (type :: output)) :=
  .frame (stackPrefix := [type]) body (by simpa [ResultOk] using valid)

/-- Direct Core calls use the same zero-or-one result vector, represented as a Core list type. -/
def callStep {context params result} (ref : FunctionRef context params (resultTy result)) :
    Step context (.plain params.toList result.toList) := by
  rw [← resultTy_toList result]
  exact .call ref

theorem callStep_erase {context params result} (ref : FunctionRef context params (resultTy result)) :
    (callStep ref).erase = .call ref.ref.index := by cases result <;> rfl

mutual

/-- Translate operands into stack producers before emitting their consumer. -/
def Expr.toCore {context result} : Expr context result → Body context (.plain [] result.toList)
  | .nop => .single (.atom .nop rfl (.parametric .nop))
  | .intConst type bits => .single (.atom (.intConst type bits) rfl (.numeric (.intConst type bits)))
  | .localGet ref => .single (.localGet ref)
  | .drop valid value => thenPlain value.toCore (.single (.atom .drop rfl (.parametric (.drop valid))))
  | .call ref args => thenPlain args.toCore (.single (callStep ref))
  | .block type valid body => .single (.block type valid body.toCore)
  | .loop type valid body => .single (.loop type valid body.toCore)
  | .if_ type valid cond thenExpr elseExpr =>
      thenPlain cond.toCore (.single (.if_ type valid thenExpr.toCore elseExpr.toCore))
  | .brIf label cond => thenPlain cond.toCore (.single (.brIf label))

def Operands.toCore {context types} : Operands context types → Body context (.plain [] types)
  | .nil => .nil
  | .cons valid head rest => thenPlain head.toCore (keepValue valid rest.toCore)

end

/-- A function position in a layer-D module. This is syntactic plugging: the
caller is responsible for matching the expression context to the function. -/
structure FunctionSlot where
  base : Module
  before : List BFunc
  after : List BFunc
  type : TypeIdx
  locals : List ValType

def FunctionSlot.folded (slot : FunctionSlot) (body : BExpr) : BModule :=
  ⟨slot.base, slot.before ++ ⟨slot.type, slot.locals, [body]⟩ :: slot.after⟩

def FunctionSlot.core (slot : FunctionSlot) (body : List Instr) : Module :=
  { slot.base with funcs := slot.before.map (Declaration.Func.mapBody BExpr.lowerList) ++
      ⟨slot.type, slot.locals, body⟩ :: slot.after.map (Declaration.Func.mapBody BExpr.lowerList) }

end Silmaril.Wasm.Binaryen.Intrinsic
