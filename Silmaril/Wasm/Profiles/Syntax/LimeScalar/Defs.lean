module

public import Silmaril.Wasm.Profiles.Syntax.Defs
public import Silmaril.Wasm.V1.Intrinsic.Scalar.Defs
public import Silmaril.Wasm.Component.Reference.Wasm.Lime1.Validation.FromV1.Defs

/-! Native Lime scalar functions and a one-definition module shape. Unlike
the corresponding Wasm1 fragment, Lime permits multi-result signatures. -/

@[expose] public section

namespace Silmaril.Wasm.Profiles.Syntax.LimeScalar

open Lime1.Validation (Context functionContext)

inductive Instr (context : Context) : Lime1.ResultType → Lime1.ResultType → Type where
  | intConst (width : IntType) (bits : BitVec width.width) : Instr context [] [.int width]
  | intBinOp (width : IntType) (op : IntBinOp) : Instr context [.int width, .int width] [.int width]
  | intRelOp (width : IntType) (op : IntRelOp) : Instr context [.int width, .int width] [.i32]
  | floatConst (width : FloatType) (bits : BitVec width.width) : Instr context [] [.float width]
  | floatUnOp (width : FloatType) (op : FloatUnOp) : Instr context [.float width] [.float width]
  | floatBinOp (width : FloatType) (op : FloatBinOp) : Instr context [.float width, .float width] [.float width]
  | floatRelOp (width : FloatType) (op : FloatRelOp) : Instr context [.float width, .float width] [.i32]
  | convert (op : Lime1.ConvertOp) : Instr context [op.source] [op.target]
  | select (type : Lime1.ValType) : Instr context [type, type, .i32] [type]
  | localGet (index : LocalIdx) {type : Lime1.ValType} (found : context.locals[index.toNat]? = some type) :
      Instr context [] [type]
  | localSet (index : LocalIdx) {type : Lime1.ValType} (found : context.locals[index.toNat]? = some type) :
      Instr context [type] []
  | call (index : FuncIdx) {sig : Lime1.FuncType} (found : context.funcs[index.toNat]? = some sig) :
      Instr context sig.params sig.results

def Instr.erase {context inputs outputs} : Instr context inputs outputs → Lime1.Instr
  | .intConst width bits => .intConst width bits
  | .intBinOp width op => .intBinOp width op
  | .intRelOp width op => .intRelOp width op
  | .floatConst width bits => .floatConst width bits
  | .floatUnOp width op => .floatUnOp width op
  | .floatBinOp width op => .floatBinOp width op
  | .floatRelOp width op => .floatRelOp width op
  | .convert op => .convert op
  | .select _ => .select
  | .localGet index _ => .localGet index
  | .localSet index _ => .localSet index
  | .call index _ => .call index

inductive Body (context : Context) : Lime1.ResultType → Lime1.ResultType → Type where
  | nil (stack : Lime1.ResultType) : Body context stack stack
  | step (pre : Lime1.ResultType) {inputs outputs results : Lime1.ResultType} :
      Instr context inputs outputs → Body context (pre ++ outputs) results →
      Body context (pre ++ inputs) results

def Body.erase {context inputs outputs} : Body context inputs outputs → Lime1.Expr
  | .nil _ => []
  | .step _ head tail => head.erase :: tail.erase

structure Func (context : Context) (type : TypeIdx) (sig : Lime1.FuncType) where
  resolved : context.types[type.toNat]? = some sig
  locals : List Lime1.ValType
  body : Body (functionContext context sig locals) [] sig.results

def Func.erase {context type sig} (term : Func context type sig) : Lime1.Func :=
  ⟨type, term.locals, term.body.erase⟩

def closedContext (sig : Lime1.FuncType) : Context := { types := [sig], funcs := [sig] }

structure ClosedModule (sig : Lime1.FuncType) where
  exportName : String
  fn : Func (closedContext sig) ⟨0⟩ sig

def ClosedModule.erase {sig} (term : ClosedModule sig) : Lime1.Module :=
  Wasm.Scalar.Module.ofFunction sig term.fn.locals term.fn.body.erase (some term.exportName)

def Instr.ofWasm1 {context inputs outputs} : V1.Intrinsic.Scalar.Instr context inputs outputs →
    Instr context.toLime inputs outputs
  | .intConst width bits => .intConst width bits
  | .intBinOp width op => .intBinOp width op
  | .intRelOp width op => .intRelOp width op
  | .select type => .select type
  | .localGet index found => .localGet index found
  | .localSet index found => .localSet index found
  | .call index found => .call index found

def Body.ofWasm1 {context inputs outputs} : V1.Intrinsic.Scalar.Body context inputs outputs →
    Body context.toLime inputs outputs
  | .nil stack => .nil stack
  | .step pre head tail => .step pre (Instr.ofWasm1 head) (Body.ofWasm1 tail)

def Func.ofWasm1 {context type sig} (term : V1.Intrinsic.Scalar.Function context type sig) :
    Func context.toLime type sig := ⟨term.resolved, term.locals, Body.ofWasm1 term.body⟩

def ClosedModule.ofWasm1 {sig} (term : V1.Intrinsic.Scalar.ClosedModule sig) : ClosedModule sig :=
  ⟨term.exportName, Func.ofWasm1 term.fn⟩

end Silmaril.Wasm.Profiles.Syntax.LimeScalar
