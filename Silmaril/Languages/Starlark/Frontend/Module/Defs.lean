module

public import Silmaril.Languages.Starlark.Frontend.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Defs

/-! # Source text to normalized Starlark modules

The adapter preserves command order and locations and uses the existing checked
module entry point for resolution, execution, and publication.
-/

public section

namespace Silmaril.Languages.Starlark.Frontend.Module

open Modules (Published)

/-- The complete application span, its callee, and its grouped operands. -/
structure ApplicationSpans where
  span : Span
  callee : Span
  operands : CallSpans

structure LocatedCommand where
  span : Span
  command : Modules.Resolve.Command
  /-- Applications in source statement order and preorder within each expression. -/
  applications : List ApplicationSpans := []

/-- The outer application of a top-level call assignment or call statement. -/
def LocatedCommand.application (command : LocatedCommand) : Option ApplicationSpans :=
  match command.command with
  | .assign _ (.list _) | .eval (.list _) | .assign _ (.tuple _) | .eval (.tuple _) => none
  | .assign .. | .eval .. => command.applications.head?
  | _ => none

def LocatedCommand.callSpans (command : LocatedCommand) : Option CallSpans :=
  command.application.map ApplicationSpans.operands

def LocatedCommand.nestedCalls (command : LocatedCommand) : List ApplicationSpans :=
  if command.application.isSome then command.applications.drop 1 else command.applications

structure ParsedModule where
  commands : List LocatedCommand

@[expose] def ParsedModule.toCommands (parsed : ParsedModule) : List Modules.Resolve.Command :=
  parsed.commands.map LocatedCommand.command

private def lowerExpr (span : Span) : SourceExpr →
    Except Diagnostic Functions.Lowering.Resolve.SourceExpr
  | .unary .. | .binary .. => .error ⟨.unsupported .operator, span⟩
  | .conditional test yes no =>
    return .conditional (← lowerExpr span test) (← lowerExpr span yes) (← lowerExpr span no)
  | .logical op left right => return .logical op (← lowerExpr span left) (← lowerExpr span right)
  | .int value => pure (.scalar (.int value))
  | .read name => pure (.scalar (.read name))

private def lowerStmt (span : Span) : SourceStmt → Except Diagnostic Modules.Resolve.Statement
  | .pass => pure .pass
  | .assign name rhs => return .assign name (← lowerExpr span rhs)
  | .eval value => return .eval (← lowerExpr span value)
  | .ret value => return .ret (← value.mapM (lowerExpr span))
  | .seq first rest => return .seq (← lowerStmt span first) (← lowerStmt span rest)
  | .branch test yes no =>
    return .branch (← lowerExpr span test) (← lowerStmt span yes) (← lowerStmt span no)

private def lowerParameter (parameter : LocatedParameter) :
    Except Diagnostic Modules.Resolve.SourceParameter := do
  let defaultExpr ← parameter.defaultValue.mapM fun value =>
    Modules.Resolve.CompExpr.plain <$> lowerExpr value.span value.expr
  return ⟨parameter.name, defaultExpr⟩

private def lowerArgument (argument : LocatedArgument) :
    Except Diagnostic Functions.Lowering.Resolve.SourceExpr := lowerExpr argument.span argument.expr

/-- Lower a scalar named group in order and retain every name. -/
def lowerNamedArguments (arguments : List LocatedNamedArgument) :
    Except Diagnostic (List (String × Functions.Lowering.Resolve.SourceExpr)) :=
  arguments.mapM fun argument => do
    return (argument.name, ← lowerArgument argument.value)

private def lowerDisplay : CollectionDisplay → Except Diagnostic Functions.Lowering.Resolve.SourceExpr
  | .sequence isTuple operands => do
    let elements ← operands.mapM lowerArgument
    return if isTuple then .tuple elements else .list elements
  | .mapping operands => do
    let entries ← lowerNamedArguments operands
    return .dict (entries.map fun (name, value) => (.string name, value))

structure LoweredOperand where
  expression : Functions.Lowering.Resolve.SourceExpr
  applications : List ApplicationSpans := []

private def lowerGroupedCall (callee : Functions.Lowering.Resolve.SourceExpr) (arguments : LocatedCallArguments)
    (lower : (operand : CallOperand) → sizeOf operand < sizeOf arguments → Except Diagnostic LoweredOperand) :
    Except Diagnostic LoweredOperand := do
  let positional ← arguments.positional.attach.mapM fun ⟨operand, member⟩ =>
    lower operand (by
      have := List.sizeOf_lt_of_mem member
      cases arguments; simp_all <;> omega)
  let named ← arguments.named.attach.mapM fun ⟨argument, member⟩ => do
    have smaller : sizeOf argument.value < sizeOf arguments := by
      have := List.sizeOf_lt_of_mem member
      cases arguments; cases argument; simp_all <;> omega
    return (argument.name, ← lower argument.value smaller)
  let star ← arguments.star.attach.mapM fun ⟨spread, member⟩ =>
    lower spread.operand (by cases arguments; cases spread; simp_all <;> omega)
  let starStar ← arguments.starStar.attach.mapM fun ⟨spread, member⟩ =>
    lower spread.operand (by cases arguments; cases spread; simp_all <;> omega)
  return ⟨.call callee (positional.map LoweredOperand.expression)
      (named.map fun (name, value) => (name, value.expression))
      (star.map LoweredOperand.expression) (starStar.map LoweredOperand.expression),
    positional.flatMap LoweredOperand.applications ++ named.flatMap (LoweredOperand.applications ∘ Prod.snd) ++
      star.toList.flatMap LoweredOperand.applications ++ starStar.toList.flatMap LoweredOperand.applications⟩

def lowerOperand : CallOperand → Except Diagnostic LoweredOperand
  | .scalar value => return { expression := ← lowerArgument value }
  | .display _ display => return { expression := ← lowerDisplay display }
  | .call span callee arguments => do
    let root : ApplicationSpans := ⟨span, callee.span, LocatedCallArguments.spans arguments⟩
    let callable ← lowerOperand callee
    let lowered ← lowerGroupedCall callable.expression arguments fun operand _ => lowerOperand operand
    return { lowered with applications := root :: (callable.applications ++ lowered.applications) }
  | .logical _ op left right => do
    let left ← lowerOperand left
    let right ← lowerOperand right
    return ⟨.logical op left.expression right.expression, left.applications ++ right.applications⟩
  | .group _ body => lowerOperand body
  | .conditional _ test yes no => do
    let yes ← lowerOperand yes
    let test ← lowerOperand test
    let no ← lowerOperand no
    return ⟨.conditional test.expression yes.expression no.expression,
      yes.applications ++ test.applications ++ no.applications⟩
  | .list _ elements => do
    let lowered ← elements.attach.mapM fun ⟨element, member⟩ => do
      have := List.sizeOf_lt_of_mem member
      lowerOperand element
    return ⟨.list (lowered.map LoweredOperand.expression), lowered.flatMap LoweredOperand.applications⟩
  | .tuple _ elements => do
    let lowered ← elements.attach.mapM fun ⟨element, member⟩ => do
      have := List.sizeOf_lt_of_mem member
      lowerOperand element
    return ⟨.tuple (lowered.map LoweredOperand.expression), lowered.flatMap LoweredOperand.applications⟩
termination_by operand => sizeOf operand
decreasing_by all_goals (simp_all <;> omega)

structure LoweredCall where
  expression : Functions.Lowering.Resolve.SourceExpr
  spans : CallSpans
  nestedCalls : List ApplicationSpans

/-- Project the span groups onto the normalized binder's argument shape. -/
def callShape (spans : CallSpans) : Functions.ArgumentShape :=
  Functions.Lowering.argumentShape spans.positional spans.named spans.star spans.starStar

/-- Lower the groups in source order for an already lowered callee. -/
def lowerCallWithCallee (callee : Functions.Lowering.Resolve.SourceExpr) (arguments : LocatedCallArguments) :
    Except Diagnostic LoweredCall := do
  let lowered ← lowerGroupedCall callee arguments (fun operand _ => lowerOperand operand)
  return ⟨lowered.expression, arguments.spans, lowered.applications⟩

def lowerCall (callee : String) (arguments : LocatedCallArguments) : Except Diagnostic LoweredCall :=
  lowerCallWithCallee (.scalar (.read callee)) arguments

/-- Lower the callee before the argument groups and retain their application locations. -/
theorem lowerOperand_call (span : Span) (callee : CallOperand) (arguments : LocatedCallArguments) :
    lowerOperand (.call span callee arguments) = (do
      let callable ← lowerOperand callee
      let call ← lowerCallWithCallee callable.expression arguments
      return ⟨call.expression, ⟨span, callee.span, call.spans⟩ :: (callable.applications ++ call.nestedCalls)⟩) := by
  simp only [lowerOperand.eq_3, lowerCallWithCallee, bind_assoc, pure_bind]

/-- Retain the short-circuit node and collect the operand application spans in source order. -/
theorem lowerOperand_logical (span : Span) (op : LogicalOp) (left right : CallOperand) :
    lowerOperand (.logical span op left right) = (do
      let lhs ← lowerOperand left
      let rhs ← lowerOperand right
      return ⟨.logical op lhs.expression rhs.expression, lhs.applications ++ rhs.applications⟩) :=
  lowerOperand.eq_4 span op left right

/-- Retain the normalized conditional and order its application spans by source position. -/
theorem lowerOperand_conditional (span : Span) (test yes no : CallOperand) :
    lowerOperand (.conditional span test yes no) = (do
      let consequent ← lowerOperand yes
      let condition ← lowerOperand test
      let alternative ← lowerOperand no
      return ⟨.conditional condition.expression consequent.expression alternative.expression,
        consequent.applications ++ condition.applications ++ alternative.applications⟩) :=
  lowerOperand.eq_6 span test yes no

/-- Lower the elements into the existing list node and keep their application locations in order. -/
theorem lowerOperand_list (span : Span) (elements : List CallOperand) :
    lowerOperand (.list span elements) = (do
      let lowered ← elements.mapM lowerOperand
      return ⟨.list (lowered.map LoweredOperand.expression), lowered.flatMap LoweredOperand.applications⟩) := by
  rw [lowerOperand.eq_7]
  rw [List.mapM_subtype (g := lowerOperand) (fun _ _ => rfl), List.unattach_attach]

/-- Lower tuple elements in order and retain their application locations. -/
theorem lowerOperand_tuple (span : Span) (elements : List CallOperand) :
    lowerOperand (.tuple span elements) = (do
      let lowered ← elements.mapM lowerOperand
      return ⟨.tuple (lowered.map LoweredOperand.expression), lowered.flatMap LoweredOperand.applications⟩) := by
  rw [lowerOperand.eq_8]
  rw [List.mapM_subtype (g := lowerOperand) (fun _ _ => rfl), List.unattach_attach]

private structure LoweredBody where
  statement : Modules.Resolve.Statement
  applications : List ApplicationSpans := []

private def LoweredBody.sequence (body : List LoweredBody) : Modules.Resolve.Statement :=
  match body.reverse with
  | [] => .pass
  | last :: preceding => preceding.foldl (fun rest first => .seq first.statement rest) last.statement

private def lowerBodyStmt (span : Span) (source : FunctionStmt) : Except Diagnostic LoweredBody := do
  match source with
  | .scalar stmt => return { statement := ← lowerStmt span stmt }
  | .returnCall value =>
    let call ← lowerOperand value
    return ⟨.ret (some call.expression), call.applications⟩
  | .assignCall target value =>
    let call ← lowerOperand value
    return ⟨.assign target call.expression, call.applications⟩
  | .evalCall value =>
    let call ← lowerOperand value
    return ⟨.eval call.expression, call.applications⟩
  | .branch test yes no =>
    let test ← lowerOperand test
    let yes ← yes.attach.mapM fun ⟨stmt, member⟩ => do
      have := List.sizeOf_lt_of_mem member
      have : sizeOf stmt.stmt ≤ sizeOf stmt := by cases stmt; simp
      lowerBodyStmt stmt.span stmt.stmt
    let no ← no.attach.mapM fun ⟨stmt, member⟩ => do
      have := List.sizeOf_lt_of_mem member
      have : sizeOf stmt.stmt ≤ sizeOf stmt := by cases stmt; simp
      lowerBodyStmt stmt.span stmt.stmt
    return ⟨.branch test.expression (LoweredBody.sequence yes) (LoweredBody.sequence no),
      test.applications ++ yes.flatMap LoweredBody.applications ++ no.flatMap LoweredBody.applications⟩
termination_by sizeOf source
decreasing_by all_goals (simp_all <;> omega)

private def lowerFunction (fn : LocatedFunction FunctionStmt) :
    Except Diagnostic (Modules.Resolve.Command × List ApplicationSpans) := do
  let positional ← fn.parameters.mapM lowerParameter
  let keywordOnly ← (fn.keywordOnly.map LocatedKeywordOnly.parameters |>.getD []).mapM lowerParameter
  let body ← fn.body.mapM fun stmt => lowerBodyStmt stmt.span stmt.stmt
  return (.define fn.name { positional, keywordOnly } (LoweredBody.sequence body),
    body.flatMap LoweredBody.applications)

private def lowerCommand (source : LocatedFileCommand) :
    Except Diagnostic (Option LocatedCommand) := do
  let located (command : Modules.Resolve.Command) : Option LocatedCommand :=
    some { span := source.span, command }
  match source.command with
  | .simple .pass => return none
  | .simple (.assign name rhs) => return located (.assign name (← lowerExpr source.span rhs))
  | .simple (.eval value) => return located (.eval (← lowerExpr source.span value))
  | .simple _ => .error ⟨.unsupported .compoundStatement, source.span⟩
  | .define fn =>
    let (command, applications) ← lowerFunction fn
    return some ⟨source.span, command, applications⟩
  | .assignDisplay target display => return located (.assign target (← lowerDisplay display))
  | .assignCall target value =>
    let call ← lowerOperand value
    return some ⟨source.span, .assign target call.expression, call.applications⟩
  | .evalCall value =>
    let call ← lowerOperand value
    return some ⟨source.span, .eval call.expression, call.applications⟩
  | .load label imports =>
    return located (.load label.text (imports.map fun item => ⟨item.exported.text, item.localName.text⟩))

private def lowerCommands (source : List LocatedFileCommand) : Except Diagnostic ParsedModule := do
  return ⟨(← source.mapM lowerCommand).filterMap id⟩

/-- Parse a file and produce the normalized module commands with their source spans. -/
def parse (source : String) : Except Diagnostic ParsedModule := do
  lowerCommands (← parseFile source)

/-- Parse and normalize original UTF-8 file bytes. -/
def parseUtf8 (source : ByteArray) : Except Diagnostic ParsedModule := do
  lowerCommands (← parseFileUtf8 source)

/-- Initialize a module with an empty import catalog. Use the finite loader for load graphs. -/
@[expose] def ParsedModule.run (parsed : ParsedModule) : Modules.Resolve.Result :=
  Modules.Resolve.runModule parsed.toCommands (fun _ => none) {}

inductive IntakeError where
  | frontend (diagnostic : Diagnostic)
  | validation (error : Modules.Resolve.Error)
  deriving DecidableEq, Repr

/-- Frontend and validation failures precede the runtime result. Runtime failure
carries the existing residual state and no publication. -/
def runUtf8 (source : ByteArray) : Except IntakeError (Modules.Result Published) := do
  let parsed ← (parseUtf8 source).mapError .frontend
  parsed.run.mapError .validation

end Silmaril.Languages.Starlark.Frontend.Module
