module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Defs
public import Silmaril.Languages.Python.Compile.ModuleEntry.Thms

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions

theorem Positional.length {scope : Source.Scope} {sources targets}
    (translated : Positional scope sources targets) : targets.length = sources.length :=
  match translated with
  | .nil => rfl
  | .cons _ tail => congrArg Nat.succ (Positional.length tail)

theorem CallArguments.length {scope : Source.Scope} {sources targets}
    (translated : CallArguments scope sources targets) : targets.length = sources.length :=
  match translated with
  | .nil => rfl
  | .cons _ tail => congrArg Nat.succ (CallArguments.length tail)

theorem global_read_resolved {scope : Source.Scope} {name : Source.Name}
    (global : Compile.Closure.Body.GlobalRead scope name) :
    scope.access name = some .implicitGlobal ∨ scope.access name = some .declaredGlobal :=
  match global with
  | .implicit access => Or.inl access
  | .declared access => Or.inr access

theorem sequenceLengthTest_tagged {scope : Source.Scope} {source right : Source.Expr}
    {operator : Source.Comparison} {sequence : ClosedSequence} {operand : Operand scope} {equal : Bool}
    (reference : GlobalReference scope "len") (argument : ClosedSequence.ValueOf source sequence)
    (comparison : lengthEquality? operator = some equal)
    (expected : OperandTranslation scope right operand) (scalar : operand.comparable = true) :
    (sequenceLengthTest? scope
      (.assert_ (.comparison (.callWith (.name "len") [(.positional, source)]) [(operator, right)]) none)).map
        Subtype.val = some ⟨reference, sequence.values.length, operand, equal⟩ := by
  simp only [sequenceLengthTest?, callExpression?, checkClosedSequence_complete argument,
    global_reference reference, operand_complete expected, Except.toOption, bind, Option.bind, scalar, dite_true]
  split <;> simp_all

theorem listConstructorArguments_complete {arguments : List (Source.ArgumentKind × Source.Expr)}
    {argument : ListConstructorArgument} (checked : ListConstructorArguments arguments argument) :
    (listConstructorArguments? arguments).map Subtype.val = some argument := by
  cases checked <;> simp [listConstructorArguments?]
  all_goals split <;> simp_all

theorem boolCallArgument_positional {scope : Source.Scope} {source : Source.Expr} {operand : Operand scope}
    (checked : OperandTranslation scope source operand) (scalar : operand.comparable = true) :
    (boolCallArgument? scope [(.positional, source)]).map Subtype.val = some (some operand) := by
  simp [boolCallArgument?, operand_complete checked, Except.toOption, scalar]

/-- A checked literal branch contributes the selected actions in order at
the current lexical child index, ahead of the rest of the module. -/
theorem lowerPlan_literalIf {tree : Source.ScopeTree} {index : Nat}
    {guard : Source.Expr} {yes no rest : List Source.Stmt}
    {selected : List (ModuleEntry.Action tree.scope)} {tail : List (Action tree.scope)}
    {tailTranslation : Translation tree index rest tail}
    (checked : ModuleEntry.Translation tree.scope [.if_ guard yes no] selected)
    (remaining : lowerPlan tree index rest = .ok ⟨tail, tailTranslation⟩) :
    (lowerPlan tree index (.if_ guard yes no :: rest)).toOption.map Subtype.val =
      some (selected.map .scalar ++ tail) := by
  simp [lowerPlan, callSite?, binding?, ModuleEntry.statements_complete checked, remaining,
    Except.mapError, Except.toOption]
  rfl

/-- The linked variadic destinations follow declaration order, including the final rest slot. -/
theorem DefinitionTranslation.variadicOrder {tree : Source.ScopeTree} {index declaration body child
    signature code} (definition : DefinitionTranslation tree index declaration body child signature code)
    {rest : Variadic signature.parameters} (_selected : signature.variadic = some rest) :
    rest.val.fixed.slots.map (Compile.Closure.parameterName child.scope) ++
      [Compile.Closure.parameterName child.scope rest.val.rest] = declaration.map Source.Parameter.name := by
  have order := congrArg (fun slots : Core.Closure.Parameters (Compile.Closure.frameLayout child.scope) =>
    slots.slots.map (Compile.Closure.parameterName child.scope)) rest.property
  simpa [Core.Closure.Call.VariadicParameters.destinations] using order.trans definition.parameterOrder

/-- The adjacent keyword proof supplies exactly the one slot of the checked definition. -/
theorem AdjacentKeywordDiscard.parameterCount {tree : Source.ScopeTree} {index name declaration body child
    signature code statement value}
    (shape : AdjacentKeywordDiscard name declaration statement value)
    (definition : DefinitionTranslation tree index declaration body child signature code) :
    signature.parameters.slots.length = 1 := by
  cases shape
  simpa using congrArg List.length definition.parameterOrder

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions
