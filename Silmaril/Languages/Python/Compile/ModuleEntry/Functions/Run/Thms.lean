module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs
public import Silmaril.Languages.Python.Core.Module.Functions.Thms
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Prefix

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run

theorem seed_lookup (globals : Core.Module.Globals) (heap : Core.Closure.Heap) (name : String) :
    (seed globals heap).globals name = (globals.lookup name).map embed := rfl

theorem evaluate_conditionalResult {scope : Source.Scope} (session : Core.Module.Functions.Session)
    (operand : Operand scope) : evaluate session operand.conditionalResult = evaluate session operand := by
  cases operand with
  | boolean value => cases value <;> simp [Operand.conditionalResult, Operand.booleanResult, evaluate] <;> rfl
  | _ => rfl

theorem evaluate_scalarResult {scope : Source.Scope} (session : Core.Module.Functions.Session)
    (value : Core.Module.Value) : evaluate session (Operand.scalarResult (scope := scope) value) = .ok (embed value) := by
  cases value with
  | int value => simp [Operand.scalarResult, evaluate, embed]
  | bool value => simpa [Operand.scalarResult, Operand.conditionalResult, evaluate, embed] using
      (evaluate_conditionalResult (scope := scope) session (.boolean value))
  | none => simp [Operand.scalarResult, evaluate, embed]

theorem advance_scalarResultAssign {scope : Source.Scope} (table : Core.Closure.Executor.CodeTable)
    (session : Core.Module.Functions.Session) (name : Source.Name) (reference : GlobalReference scope name)
    (value : Core.Module.Value) (rest : List (Instruction scope)) :
    advance table (.ready session (.scalar (.assign name reference (.scalarResult value)) :: rest)) =
      ([], .ready (session.bindGlobal name (embed value)) rest) := by
  simp only [advance, evaluate_scalarResult]

theorem assertOperand_scalarResult {scope : Source.Scope} (session : Core.Module.Functions.Session)
    (value : Core.Module.Value) (expected : Bool) (rest : List (Instruction scope)) :
    assertOperand session (.scalarResult value) expected rest =
      (if value.truth = expected then .ready session rest else .finished session .assertionError) := by
  simp only [assertOperand, evaluate_scalarResult]
  cases value <;> rfl

theorem advance_conditionalAssign {scope : Source.Scope} (table : Core.Closure.Executor.CodeTable)
    (session : Core.Module.Functions.Session) (name : Source.Name)
    (reference : GlobalReference scope name) (selected : Operand scope) (rest : List (Instruction scope)) :
    advance table (.ready session (.scalar (.assign name reference selected.conditionalResult) :: rest)) =
      advance table (.ready session (.scalar (.assign name reference selected) :: rest)) := by
  simp only [advance, evaluate_conditionalResult]

theorem advance_conditionalAssert {scope : Source.Scope} (table : Core.Closure.Executor.CodeTable)
    (session : Core.Module.Functions.Session) (selected : Operand scope) (rest : List (Instruction scope)) :
    advance table (.ready session (.scalar (.assertion selected.conditionalResult) :: rest)) =
      advance table (.ready session (.scalar (.assertion selected) :: rest)) := by
  simp only [advance, assertOperand, evaluate_conditionalResult]

/-- Scalar actions emit a prefix of scalar instructions and consume no code
keys. Both runners receive the same instructions and linked rows. -/
theorem lowerInstructions_scalarPrefix {scope : Source.Scope} (tree : Source.ScopeTree) (key : Nat)
    (actions : List (ModuleEntry.Action scope)) (rest : List (Functions.Action scope)) :
    lowerInstructions tree key (actions.map .scalar ++ rest) =
      (lowerInstructions tree key rest).map fun (instructions, rows) =>
        (actions.map .scalar ++ instructions, rows) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.lowerInstructions_scalarPrefix tree key actions rest

theorem invoke_current_globals {scope : Source.Scope} (session : Core.Module.Functions.Session)
    (table : Core.Closure.Executor.CodeTable) (target : Core.Module.Functions.Destination)
    (name : String) (arguments : List Core.Module.Functions.Operand) (remaining : List (Instruction scope)) :
    advance table (.ready session (.call target name arguments :: remaining)) =
      ([], .calling (session.prepareCall target (.readGlobal name) arguments) remaining) := rfl

theorem prepareSpread_missing {session : Core.Module.Functions.Session}
    {name : String} {parts : List SpreadPart} (missing : session.globals name = none) :
    prepareSpread session name parts = (.error (.operand (.defined (.nameError name))), session.heap) := by
  simp [prepareSpread, Core.Closure.Call.preparePositionalCall, readSpreadInput, missing]

theorem advance_spread_prepared {scope : Source.Scope} (table : Core.Closure.Executor.CodeTable)
    {session : Core.Module.Functions.Session} {target : Core.Module.Functions.Destination}
    {name : String} {parts : List SpreadPart} {callee : Core.Closure.Value}
    {values : List Core.Closure.Value} {heap : Core.Closure.Heap} {rest : List (Instruction scope)}
    (prepared : prepareSpread session name parts = (.ok (callee, values), heap)) :
    advance table (.ready session (.spreadCall target name parts :: rest)) =
      ([], .calling (spreadInvocation { session with heap } target callee values) rest) := by
  simp [advance, prepared]

theorem advance_literalArmBoolean {scope : Source.Scope} (table : Core.Closure.Executor.CodeTable)
    (session : Core.Module.Functions.Session) (value : Bool) (rest : List (Instruction scope)) :
    advance table (.ready session (.scalar (ModuleEntry.Action.assertion (.boolean value)).inLiteralArm :: rest)) =
      ([], if value then .ready session rest else .finished session .assertionError) := by
  cases value <;> simp [Action.inLiteralArm, advance, assertOperand, evaluate, Core.Module.Functions.truth] <;> rfl

theorem advance_adjacentKeywordDiscard {scope : Source.Scope} (table : Core.Closure.Executor.CodeTable)
    (session : Core.Module.Functions.Session) (name : String) (value : Int)
    (remaining : List (Instruction scope)) :
    advance table (.ready session (.adjacentKeywordDiscard name value :: remaining)) =
      ([], .calling (session.prepareCall .discard (.readGlobal name) [.literal (.int value)]) remaining) := rfl

theorem lowerInstructions_assertSequenceLength {scope : Source.Scope} (tree : Source.ScopeTree) (key : Nat)
    (test : SequenceLengthTest scope) (rest : List (Functions.Action scope)) :
    lowerInstructions tree key (.assertSequenceLength test :: rest) =
      (lowerInstructions tree key rest).map fun (instructions, rows) =>
        (.assertSequenceLength test :: instructions, rows) := by
  rw [lowerInstructions]
  cases lowerInstructions tree key rest with | error _ => rfl | ok result => cases result; rfl

theorem advance_assertSequenceLength {scope : Source.Scope} (table : Core.Closure.Executor.CodeTable)
    (session : Core.Module.Functions.Session) (test : SequenceLengthTest scope) (rest : List (Instruction scope)) :
    advance table (.ready session (.assertSequenceLength test :: rest)) =
      ([], .finished session (match session.globals "len" with
        | none => .raised (.nameError "len")
        | some (.function _) => .scalarProfile
        | some _ => .raised .notCallable)) := rfl

theorem lowerInstructions_assertBoolIdentity {scope : Source.Scope} (tree : Source.ScopeTree) (key : Nat)
    (test : BoolIdentityTest scope) (rest : List (Functions.Action scope)) :
    lowerInstructions tree key (.assertBoolIdentity test :: rest) =
      (lowerInstructions tree key rest).map fun (instructions, rows) =>
        (.assertBoolIdentity test :: instructions, rows) := by
  rw [lowerInstructions]
  cases lowerInstructions tree key rest with | error _ => rfl | ok result => cases result; rfl

theorem advance_assertBoolIdentity {scope : Source.Scope} (table : Core.Closure.Executor.CodeTable)
    (session : Core.Module.Functions.Session) (test : BoolIdentityTest scope) (rest : List (Instruction scope)) :
    advance table (.ready session (.assertBoolIdentity test :: rest)) =
      ([], .finished session (boolIdentityCompletion session test)) := rfl

theorem lowerInstructions_assertListConstruction {scope : Source.Scope} (tree : Source.ScopeTree) (key : Nat)
    (test : ListConstructionTest scope) (rest : List (Functions.Action scope)) :
    lowerInstructions tree key (.assertListConstruction test :: rest) =
      (lowerInstructions tree key rest).map fun (instructions, rows) =>
        (.assertListConstruction test :: instructions, rows) := by
  rw [lowerInstructions]
  cases lowerInstructions tree key rest with | error _ => rfl | ok result => cases result; rfl

theorem advance_assertListConstruction {scope : Source.Scope} (table : Core.Closure.Executor.CodeTable)
    (session : Core.Module.Functions.Session) (test : ListConstructionTest scope) (rest : List (Instruction scope)) :
    advance table (.ready session (.assertListConstruction test :: rest)) =
      ([], .finished session (match session.globals "list" with
        | none => .raised (.nameError "list")
        | some (.function _) => .scalarProfile
        | some _ => .raised .notCallable)) := rfl

theorem lowerInstructions_assertTupleChain {scope : Source.Scope} (tree : Source.ScopeTree) (key : Nat)
    (test : TupleChainTest scope) (rest : List (Functions.Action scope)) :
    lowerInstructions tree key (.assertTupleChain test :: rest) =
      (lowerInstructions tree key rest).map fun (instructions, rows) =>
        (.assertTupleChain test :: instructions, rows) := by
  rw [lowerInstructions]
  cases lowerInstructions tree key rest with | error _ => rfl | ok result => cases result; rfl

theorem advance_assertTupleChain {scope : Source.Scope} (table : Core.Closure.Executor.CodeTable)
    (session : Core.Module.Functions.Session) (test : TupleChainTest scope) (rest : List (Instruction scope)) :
    advance table (.ready session (.assertTupleChain test :: rest)) =
      ([], match checkTupleChain session test with
        | .ok () => .ready session rest
        | .error error => .finished session error) := rfl

theorem advance_assertVarNames {scope : Source.Scope} (table : Core.Closure.Executor.CodeTable)
    (session : Core.Module.Functions.Session) (receiver : String) (needle : List UInt32)
    (remaining : List (Instruction scope)) :
    advance table (.ready session (.assertVarNames receiver needle :: remaining)) =
      ([], match checkVarNames table session receiver needle with
        | .ok () => .ready session remaining
        | .error completion => .finished session completion) := rfl

theorem runPrefix_append {scope : Source.Scope} (table : Core.Closure.Executor.CodeTable)
    (first second : Nat) (initial : State scope) :
    let (log, paused) := runPrefix table first initial
    let (tail, residual) := runPrefix table second paused
    runPrefix table (first + second) initial = (log ++ tail, residual) :=
  Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.runPrefix_append table first second initial

/-- The saved literal is part of the linked function and consumes no code key. -/
theorem link_keywordDefault {layout : Core.Closure.Layout} (key : Nat) (tree : Source.ScopeTree)
    (code : Compile.Closure.Body.Code layout) (slot : Fin layout.locals) (value : Int) :
    Compile.Closure.Link.linkBody key tree (initializeKeywordDefault code (some (slot, value))) =
      let linked := Compile.Closure.Link.linkBody key tree code
      ⟨.assign (.local slot) (.integer value) linked.code, linked.children⟩ := rfl

/-- Omission passes the zero-positional binder. An explicit positional value
fails arity checking before the default store. -/
theorem keywordDefault_bind {layout : Core.Closure.Layout}
    (before : Core.Closure.Heap × Core.Closure.Frame layout)
    (value : Core.Closure.Value) (rest : List Core.Closure.Value) :
    Core.Closure.Call.bindPositional ⟨[], .nil⟩ [] before = .ok before ∧
      Core.Closure.Call.bindPositional ⟨[], .nil⟩ (value :: rest) before =
        .error (.defined (.positionalArity 0 (rest.length + 1))) := ⟨rfl, rfl⟩

/-- Installing the saved literal changes only its frame local. -/
theorem advance_keywordDefault {layout : Core.Closure.Layout} (table : Core.Closure.Executor.CodeTable)
    (globals : Core.Closure.Executor.GlobalLookup) (heap : Core.Closure.Heap)
    (frame : Core.Closure.Frame layout) (slot : Fin layout.locals) (value : Int)
    (body : Core.Closure.Executor.Body layout) (stack : Core.Closure.Executor.Stack) :
    Core.Closure.Executor.advanceIn table globals
        (.running heap frame (.store (.local slot) (.literal (.int value)) body) stack) =
      some (none, .running heap
        { frame with locals := fun query => if query = slot then some (.int value) else frame.locals query }
        body stack) := rfl

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run
