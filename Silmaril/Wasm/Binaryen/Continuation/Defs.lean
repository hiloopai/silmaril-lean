module

public import Silmaril.Wasm.Binaryen.Lower
public import Silmaril.Wasm.Validation.Intrinsic.Defs

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Continuation

open Validation Validation.Intrinsic

/-- The non-structural operations of the fragment. Calls may reach an import. -/
inductive Op where
  | nop | drop
  | intConst (type : IntType) (bits : BitVec type.width)
  | intBinOp (type : IntType) (op : IntBinOp)
  | localGet (index : LocalIdx)
  | call (callee : FuncIdx)
  | brIf (target : LabelIdx)

def Op.lower : Op → Instr
  | .nop => .nop
  | .drop => .drop
  | .intConst type bits => .intConst type bits
  | .intBinOp type op => .intBinOp type op
  | .localGet index => .localGet index
  | .call callee => .call callee
  | .brIf target => .brIf target

def Op.read : Instr → Option Op
  | .nop => some .nop
  | .drop => some .drop
  | .intConst type bits => some (.intConst type bits)
  | .intBinOp type op => some (.intBinOp type op)
  | .localGet index => some (.localGet index)
  | .call callee => some (.call callee)
  | .brIf target => some (.brIf target)
  | _ => none

/-- A continuation form rather than an operand tree: each operation is followed
by its continuation, and control operators own delimited subprograms. -/
inductive Raw where
  | done
  | let_ (op : Op) (next : Raw)
  | block (type : BlockType) (body next : Raw)
  | if_ (type : BlockType) (thenBody elseBody next : Raw)

def Raw.lower : Raw → List Instr
  | .done => []
  | .let_ op next => op.lower :: next.lower
  | .block type body next => .block type body.lower :: next.lower
  | .if_ type thenBody elseBody next => .if_ type thenBody.lower elseBody.lower :: next.lower

/-- Recognize the syntax fragment, independently of stack or name validation. -/
def Raw.read : List Instr → Option Raw
  | [] => some .done
  | .block type body :: next =>
      match read body, read next with
      | some body', some next' => some (.block type body' next')
      | _, _ => none
  | .if_ type thenBody elseBody :: next =>
      match read thenBody, read elseBody, read next with
      | some thenBody', some elseBody', some next' => some (.if_ type thenBody' elseBody' next')
      | _, _, _ => none
  | instr :: next =>
      match Op.read instr, read next with
      | some op, some next' => some (.let_ op next')
      | _, _ => none

/-- Embed using the existing structured Core lift. Operands still on the stack
are not invented as tree children; in particular the `if` condition occupies
its existing position in the surrounding forest. -/
def Raw.toBinaryen (code : Raw) : List BExpr := liftInstrs code.lower

def Raw.ofBinaryen (forest : List BExpr) : Option Raw := read (BExpr.lowerList forest)

/-- The exact-cut fragment of raw Core typing. No intermediate subsumption or
unreachable-stack adjustment is allowed. This predicate does not mention the
continuation AST and can be applied directly to an intrinsic Core erasure. -/
inductive Cuts : Context → List CValType → List CValType → List Instr → Prop where
  | done {ctx stack} (valid : ResultOk ctx.toTypeCtx stack) : Cuts ctx stack stack []
  | atom {ctx stackPrefix inputs outputs result instr next}
      (supported : (Op.read instr).isSome = true)
      (prefixOk : ResultOk ctx.toTypeCtx stackPrefix)
      (valid : InstrOk ctx instr (.plain inputs outputs))
      (rest : Cuts ctx (stackPrefix ++ outputs) result next) :
      Cuts ctx (stackPrefix ++ inputs) result (instr :: next)
  | block {ctx stackPrefix params results result type body next}
      (prefixOk : ResultOk ctx.toTypeCtx stackPrefix) (valid : BlockTypeOk ctx type params results)
      (inner : Cuts (ctx.withLabel results) params results body)
      (rest : Cuts ctx (stackPrefix ++ results) result next) :
      Cuts ctx (stackPrefix ++ params) result (.block type body :: next)
  | if_ {ctx stackPrefix params results result type thenBody elseBody next}
      (prefixOk : ResultOk ctx.toTypeCtx stackPrefix) (valid : BlockTypeOk ctx type params results)
      (onTrue : Cuts (ctx.withLabel results) params results thenBody)
      (onFalse : Cuts (ctx.withLabel results) params results elseBody)
      (rest : Cuts ctx (stackPrefix ++ results) result next) :
      Cuts ctx (stackPrefix ++ (params ++ [.i32])) result (.if_ type thenBody elseBody :: next)

/-- Fallthrough cuts are explicit: an operation takes an input suffix and
produces an output suffix, leaving the prefix alone. The continuation consumes
the resulting whole stack. Inside an `if` or `block` only its declared
parameters are visible on entry; a taken branch goes to the Core label, not to
the lexical continuation of the branch instruction. -/
inductive Code : Context → List CValType → List CValType → Raw → Type where
  | done {ctx stack} (valid : ResultOk ctx.toTypeCtx stack) : Code ctx stack stack .done
  | let_ {ctx stackPrefix inputs outputs result op next}
      (prefixOk : ResultOk ctx.toTypeCtx stackPrefix)
      (valid : InstrOk ctx op.lower (.plain inputs outputs))
      (rest : Code ctx (stackPrefix ++ outputs) result next) :
      Code ctx (stackPrefix ++ inputs) result (.let_ op next)
  | block {ctx stackPrefix params results result type body next}
      (prefixOk : ResultOk ctx.toTypeCtx stackPrefix) (valid : BlockTypeOk ctx type params results)
      (inner : Code (ctx.withLabel results) params results body)
      (rest : Code ctx (stackPrefix ++ results) result next) :
      Code ctx (stackPrefix ++ params) result (.block type body next)
  | if_ {ctx stackPrefix params results result type thenBody elseBody next}
      (prefixOk : ResultOk ctx.toTypeCtx stackPrefix) (valid : BlockTypeOk ctx type params results)
      (onTrue : Code (ctx.withLabel results) params results thenBody)
      (onFalse : Code (ctx.withLabel results) params results elseBody)
      (rest : Code ctx (stackPrefix ++ results) result next) :
      Code ctx (stackPrefix ++ (params ++ [.i32])) result (.if_ type thenBody elseBody next)

def Code.erase {ctx inputs outputs raw} (_ : Code ctx inputs outputs raw) : Raw := raw

theorem Op.isAtomic (op : Op) : isAtomic op.lower = true := by cases op <;> rfl

def prepend {ctx stackPrefix inputs outputs result}
    (prefixOk : ResultOk ctx.toTypeCtx stackPrefix) (step : Step ctx (.plain inputs outputs))
    (rest : Body ctx (.plain (stackPrefix ++ outputs) result)) :
    Body ctx (.plain (stackPrefix ++ inputs) result) :=
  .seq (.frame (.single step) prefixOk) (by simp) rest

def castBody {ctx inputs outputs inputs' outputs'} (ins : inputs = inputs') (outs : outputs = outputs')
    (body : Body ctx (.plain inputs outputs)) : Body ctx (.plain inputs' outputs') :=
  ins ▸ outs ▸ body

theorem castBody_erase {ctx inputs outputs inputs' outputs'} (ins : inputs = inputs')
    (outs : outputs = outputs') (body : Body ctx (.plain inputs outputs)) :
    (castBody ins outs body).erase = body.erase := by
  cases ins; cases outs; rfl

def finish {ctx stack} (valid : ResultOk ctx.toTypeCtx stack) : Body ctx (.plain stack stack) :=
  castBody (List.append_nil stack) (List.append_nil stack) (.frame .nil valid)

/-- Compile to the actual Core intrinsic syntax, without introducing locals,
reducing structured boundaries, or moving instructions across a cut. -/
def Code.toCore {ctx inputs outputs raw} : Code ctx inputs outputs raw → Body ctx (.plain inputs outputs)
  | .done valid => finish valid
  | .let_ prefixOk valid rest => prepend prefixOk (.atom _ (Op.isAtomic _) valid) rest.toCore
  | .block prefixOk valid inner rest => prepend prefixOk (.block _ valid inner.toCore) rest.toCore
  | .if_ prefixOk valid onTrue onFalse rest =>
      prepend prefixOk (.if_ _ valid onTrue.toCore onFalse.toCore) rest.toCore

theorem prepend_erase {ctx stackPrefix inputs outputs result}
    (prefixOk : ResultOk ctx.toTypeCtx stackPrefix) (step : Step ctx (.plain inputs outputs))
    (rest : Body ctx (.plain (stackPrefix ++ outputs) result)) :
    (prepend prefixOk step rest).erase = step.erase :: rest.erase := rfl

theorem finish_erase {ctx : Context} {stack} (valid : ResultOk ctx.toTypeCtx stack) :
    (Code.done valid).toCore.erase = [] := by
  rw [Code.toCore, finish, castBody_erase]
  rfl

end Silmaril.Wasm.Binaryen.Continuation
