module

public import Silmaril.Languages.Python.Compile.Closure.Body.Defs
public import Silmaril.Languages.Python.Compile.ModuleEntry.Defs

/-! # Lower module function bindings and positional call sites

The module plan preserves ordering between definitions, assignments and
calls. Reads from a function's module scope retain the resolved name for
runtime lookup in the module's current namespace.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions

open Source (BlockPath Name Scope ScopeTree)
open Compile.Closure (frameLayout)
open Compile.Closure.Body (Code)

inductive CallExpression : Source.Expr → Name → List (Source.ArgumentKind × Source.Expr) → Prop where
  | plain (name : Name) (arguments : List Source.Expr) :
      CallExpression (.call (.name name) arguments) name (arguments.map (.positional, ·))
  | tagged (name : Name) (arguments : List (Source.ArgumentKind × Source.Expr)) :
      CallExpression (.callWith (.name name) arguments) name arguments

def callExpression? : (source : Source.Expr) →
    Option {result : Name × List (Source.ArgumentKind × Source.Expr) // CallExpression source result.1 result.2}
  | .call (.name name) arguments => some ⟨(name, arguments.map (.positional, ·)), .plain name arguments⟩
  | .callWith (.name name) arguments => some ⟨(name, arguments), .tagged name arguments⟩
  | _ => none

inductive Placement where
  | discard
  | store (name : Name)
  | assertion

inductive CallSite : Source.Stmt → Placement → Name → List (Source.ArgumentKind × Source.Expr) → Prop where
  | discard {value callee arguments} (call : CallExpression value callee arguments) :
      CallSite (.expression value) .discard callee arguments
  | assign {source name value callee arguments} (binding : Binding source name value)
      (call : CallExpression value callee arguments) : CallSite source (.store name) callee arguments
  | assertion {condition callee arguments} (call : CallExpression condition callee arguments) :
      CallSite (.assert_ condition none) .assertion callee arguments

def callSite? : (source : Source.Stmt) →
    Option {result : Placement × Name × List (Source.ArgumentKind × Source.Expr) //
      CallSite source result.1 result.2.1 result.2.2}
  | .expression value =>
    (callExpression? value).map fun ⟨(name, arguments), call⟩ => ⟨(.discard, name, arguments), .discard call⟩
  | .assert_ condition none =>
    (callExpression? condition).map fun ⟨(name, arguments), call⟩ => ⟨(.assertion, name, arguments), .assertion call⟩
  | source => do
    let ⟨(target, value), binding⟩ ← binding? source
    let ⟨(name, arguments), call⟩ ← callExpression? value
    return ⟨(.store target, name, arguments), .assign binding call⟩

inductive Destination (scope : Scope) where
  | discard
  | store (name : Name) (reference : GlobalReference scope name)
  | assertion

def Destination.placement {scope : Scope} : Destination scope → Placement
  | .discard => .discard
  | .store name _ => .store name
  | .assertion => .assertion

inductive Error where
  | scope (diagnostic : Source.Diagnostic)
  | moduleScope
  | scalar (error : ModuleEntry.Error)
  | functionBody (error : Compile.Closure.Body.Error)
  | functionScope (path : BlockPath)
  | argumentProfile
  | unresolvedGlobal (name : Name)
  deriving Repr

def lowerDestination (scope : Scope) : (source : Placement) →
    Except Error {target : Destination scope // target.placement = source}
  | .discard => .ok ⟨.discard, rfl⟩
  | .assertion => .ok ⟨.assertion, rfl⟩
  | .store name => do
    let some reference := globalReference? scope name | throw (.unresolvedGlobal name)
    return ⟨.store name reference, rfl⟩

inductive Positional (scope : Scope) :
    List (Source.ArgumentKind × Source.Expr) → List (Operand scope) → Prop where
  | nil : Positional scope [] []
  | cons {source operand rest targets} (first : OperandTranslation scope source operand)
      (tail : Positional scope rest targets) :
      Positional scope ((.positional, source) :: rest) (operand :: targets)

def lowerArguments (scope : Scope) : (source : List (Source.ArgumentKind × Source.Expr)) →
    Except Error {target // Positional scope source target}
  | [] => .ok ⟨[], .nil⟩
  | (.positional, expression) :: rest => do
    let operand ← (lowerOperand scope expression).mapError .scalar
    let tail ← lowerArguments scope rest
    return ⟨operand.val :: tail.val, .cons operand.property tail.property⟩
  | _ => .error .argumentProfile

/-- A module argument can contain one direct call with scalar arguments. -/
inductive CallArgument (scope : Scope) where
  | scalar (operand : Operand scope)
  | call (name : Name) (reference : GlobalReference scope name) (arguments : List (Operand scope))

inductive ArgumentTranslation (scope : Scope) : Source.Expr → CallArgument scope → Prop where
  | scalar {source operand} (translated : OperandTranslation scope source operand) :
      ArgumentTranslation scope source (.scalar operand)
  | call {source name arguments reference operands}
      (shape : CallExpression source name arguments) (translated : Positional scope arguments operands) :
      ArgumentTranslation scope source (.call name reference operands)

inductive CallArguments (scope : Scope) :
    List (Source.ArgumentKind × Source.Expr) → List (CallArgument scope) → Prop where
  | nil : CallArguments scope [] []
  | cons {source argument rest targets} (first : ArgumentTranslation scope source argument)
      (tail : CallArguments scope rest targets) :
      CallArguments scope ((.positional, source) :: rest) (argument :: targets)

def lowerCallArgument (scope : Scope) (source : Source.Expr) :
    Except Error {argument // ArgumentTranslation scope source argument} := do
  if let some ⟨(name, arguments), shape⟩ := callExpression? source then
    let some reference := globalReference? scope name | throw (.unresolvedGlobal name)
    let operands ← lowerArguments scope arguments
    return ⟨.call name reference operands.val, .call shape operands.property⟩
  else
    let operand ← (lowerOperand scope source).mapError .scalar
    return ⟨.scalar operand.val, .scalar operand.property⟩

def lowerCallArguments (scope : Scope) : (source : List (Source.ArgumentKind × Source.Expr)) →
    Except Error {target // CallArguments scope source target}
  | [] => .ok ⟨[], .nil⟩
  | (.positional, source) :: rest => do
    let argument ← lowerCallArgument scope source
    let tail ← lowerCallArguments scope rest
    return ⟨argument.val :: tail.val, .cons argument.property tail.property⟩
  | _ => .error .argumentProfile

/-- The call immediately after a definition supplies exactly its one required
positional-or-keyword parameter. A text literal in a mapping keeps its code points. -/
inductive AdjacentKeywordDiscard (name : Name) :
    List Source.Parameter → Source.Stmt → Int → Prop where
  | literal (parameter : Name) (value : Int) :
      AdjacentKeywordDiscard name [⟨parameter, none, .positionalOrKeyword, none⟩]
        (.expression (.callWith (.name name)
          [(.unpackMapping, .dictionary [(some (.text (parameter.toList.map Char.val)), .integer value)])]))
        value

def adjacentKeywordDiscard? (name : Name) :
    (declaration : List Source.Parameter) → (statement : Source.Stmt) →
    Option {value : Int // AdjacentKeywordDiscard name declaration statement value}
  | [⟨parameter, none, .positionalOrKeyword, none⟩],
      .expression (.callWith (.name receiver)
        [(.unpackMapping, .dictionary [(some (.text key), .integer value)])]) =>
    if sameReceiver : receiver = name then
      if sameKey : key = parameter.toList.map Char.val then
        some ⟨value, by
          subst receiver
          subst key
          exact .literal parameter value⟩
      else none
    else none
  | _, _ => none

/-- The initial default profile has one literal keyword-only default and
one message-free equality assertion using that parameter. -/
inductive LiteralKeywordDefault (parameter : Name) (value : Int) :
    List Source.Parameter → List Source.Stmt → Prop where
  | assertion (expected : Int) :
      LiteralKeywordDefault parameter value [⟨parameter, some (.integer value), .keywordOnly, none⟩]
        [.assert_ (.comparison (.name parameter) [(.eq, .integer expected)]) none]

def literalKeywordDefault? : (declaration : List Source.Parameter) → (body : List Source.Stmt) →
    Option {binding : Name × Int // LiteralKeywordDefault binding.1 binding.2 declaration body}
  | [⟨parameter, some (.integer value), .keywordOnly, none⟩],
      [.assert_ (.comparison (.name name) [(.eq, .integer expected)]) none] =>
    if same : name = parameter then
      some ⟨(parameter, value), by
        subst name
        exact .assertion expected⟩
    else none
  | _, _ => none

/-- Default evaluation is limited to exact scalars and live module reads. -/
inductive DefaultOperand (scope : Scope) where
  | literal (value : Core.Module.Value)
  | read (name : Name) (reference : GlobalReference scope name)

inductive DefaultTranslation (scope : Scope) : Source.Expr → DefaultOperand scope → Prop where
  | literal {source value} (encoded : scalarLiteral? source = some value) :
      DefaultTranslation scope source (.literal value)
  | none_ : DefaultTranslation scope .none_ (.literal .none)
  | read {name} (reference : GlobalReference scope name) :
      DefaultTranslation scope (.name name) (.read name reference)

def lowerDefault (scope : Scope) : (source : Source.Expr) →
    Except Error {operand // DefaultTranslation scope source operand}
  | .none_ => .ok ⟨.literal .none, .none_⟩
  | .name name => do
    let some reference := globalReference? scope name | throw (.unresolvedGlobal name)
    return ⟨.read name reference, .read reference⟩
  | source =>
    match encoded : scalarLiteral? source with
    | some value => .ok ⟨.literal value, .literal encoded⟩
    | none => .error (.functionBody .parameterProfile)

def eraseDefault (parameter : Source.Parameter) : Source.Parameter :=
  { parameter with defaultValue := none }

/-- Required parameters precede the saved suffix. Both relations preserve
declaration order, and each saved operand comes from the parent scope. -/
inductive DefaultSuffix (scope : Scope) : Bool → List Source.Parameter → List (DefaultOperand scope) → Prop where
  | nil (saving : Bool) : DefaultSuffix scope saving [] []
  | required {parameter rest operands} (absent : parameter.defaultValue = none)
      (tail : DefaultSuffix scope false rest operands) : DefaultSuffix scope false (parameter :: rest) operands
  | optional {saving parameter source rest operand operands}
      (present : parameter.defaultValue = some source) (checked : DefaultTranslation scope source operand)
      (tail : DefaultSuffix scope true rest operands) :
      DefaultSuffix scope saving (parameter :: rest) (operand :: operands)

def lowerDefaultSuffix (scope : Scope) (saving : Bool) : (declaration : List Source.Parameter) →
    Except Error {operands // DefaultSuffix scope saving declaration operands}
  | [] => .ok ⟨[], .nil saving⟩
  | parameter :: rest =>
    match present : parameter.defaultValue with
    | some source => do
      let operand ← lowerDefault scope source
      let tail ← lowerDefaultSuffix scope true rest
      return ⟨operand.val :: tail.val, .optional present operand.property tail.property⟩
    | none =>
      match saving with
      | true => .error (.functionBody .parameterProfile)
      | false => do
        let tail ← lowerDefaultSuffix scope false rest
        return ⟨tail.val, .required present tail.property⟩

/-- The ordinary definition checks used with or without an adjacent call. -/
structure DefinitionTranslation (tree : ScopeTree) (index : Nat) (declaration : List Source.Parameter)
    (body : List Source.Stmt) (child : ScopeTree) (parameters : Core.Closure.Parameters (frameLayout child.scope))
    (code : Code (frameLayout child.scope)) (defaults : List (DefaultOperand tree.scope) := []) : Prop where
  located : tree.children[index]? = some child
  path : child.scope.context.path = tree.scope.context.path ++ [index]
  kind : child.scope.context.kind = .function
  fixed : (declaration.map eraseDefault).all Compile.Closure.Body.fixed = true
  saved : DefaultSuffix tree.scope false declaration defaults
  parameterOrder : parameters.slots.map (Compile.Closure.parameterName child.scope) =
    declaration.map Source.Parameter.name
  functionBody : Compile.Closure.Body.Translation child 0 body code

def lengthEquality? : Source.Comparison → Option Bool
  | .eq => some true
  | .ne => some false
  | _ => none

structure SequenceLengthTest (scope : Scope) where
  reference : GlobalReference scope "len"
  length : Nat
  right : Operand scope
  expectedEqual : Bool

/-- Only the sequence argument is closed. The callee and right operand
still use their live namespace at this assertion. -/
inductive SequenceLengthTranslation (scope : Scope) : Source.Stmt → SequenceLengthTest scope → Prop where
  | assertion {left source right operator sequence reference operand equal}
      (call : CallExpression left "len" [(.positional, source)])
      (argument : ClosedSequence.ValueOf source sequence)
      (comparison : lengthEquality? operator = some equal)
      (expected : OperandTranslation scope right operand) (scalar : operand.comparable = true) :
      SequenceLengthTranslation scope (.assert_ (.comparison left [(operator, right)]) none)
        ⟨reference, sequence.values.length, operand, equal⟩

def sequenceLengthTest? (scope : Scope) : (statement : Source.Stmt) →
    Option {test // SequenceLengthTranslation scope statement test}
  | .assert_ (.comparison left [(operator, right)]) none => do
    let ⟨("len", [(.positional, source)]), call⟩ ← callExpression? left | none
    let ⟨sequence, checked⟩ ← checkClosedSequence source
    let reference ← globalReference? scope "len"
    let operand ← (lowerOperand scope right).toOption
    if scalar : operand.val.comparable = true then
      match comparison : lengthEquality? operator with
      | some equal => some ⟨⟨reference, sequence.values.length, operand.val, equal⟩,
          .assertion call checked comparison operand.property scalar⟩
      | none => none
    else none
  | _ => none

inductive ListConstructorArgument where
  | omitted
  | literal (sequence : ClosedSequence)

inductive ListConstructorArguments : List (Source.ArgumentKind × Source.Expr) → ListConstructorArgument → Prop where
  | omitted : ListConstructorArguments [] .omitted
  | tuple {elements values} (checked : elements.mapM scalarLiteral? = some values) :
      ListConstructorArguments [(.positional, .tuple elements)] (.literal ⟨.tuple, values⟩)
  | list {elements values} (checked : elements.mapM scalarLiteral? = some values) :
      ListConstructorArguments [(.positional, .list_ elements)] (.literal ⟨.list, values⟩)

def listConstructorArguments? : (arguments : List (Source.ArgumentKind × Source.Expr)) →
    Option {argument // ListConstructorArguments arguments argument}
  | [] => some ⟨.omitted, .omitted⟩
  | [(.positional, .tuple elements)] =>
    match checked : elements.mapM scalarLiteral? with
    | some values => some ⟨.literal ⟨.tuple, values⟩, .tuple checked⟩
    | none => none
  | [(.positional, .list_ elements)] =>
    match checked : elements.mapM scalarLiteral? with
    | some values => some ⟨.literal ⟨.list, values⟩, .list checked⟩
    | none => none
  | _ => none

inductive ListTestOrder where
  | constructorFirst
  | literalFirst

structure ListConstructionTest (scope : Scope) where
  reference : GlobalReference scope "list"
  argument : ListConstructorArgument
  literal : List Core.Module.Value
  order : ListTestOrder

/-- Both operands are fully checked. Only the stock constructor is dynamic. -/
inductive ListConstructionTranslation (scope : Scope) : Source.Stmt → ListConstructionTest scope → Prop where
  | constructorFirst {call arguments argument elements literal reference}
      (site : CallExpression call "list" arguments)
      (checked : ListConstructorArguments arguments argument)
      (values : elements.mapM scalarLiteral? = some literal) :
      ListConstructionTranslation scope (.assert_ (.comparison call [(.eq, .list_ elements)]) none)
        ⟨reference, argument, literal, .constructorFirst⟩
  | literalFirst {call arguments argument elements literal reference}
      (site : CallExpression call "list" arguments)
      (checked : ListConstructorArguments arguments argument)
      (values : elements.mapM scalarLiteral? = some literal) :
      ListConstructionTranslation scope (.assert_ (.comparison (.list_ elements) [(.eq, call)]) none)
        ⟨reference, argument, literal, .literalFirst⟩

def listConstructionTest? (scope : Scope) : (statement : Source.Stmt) →
    Option {test // ListConstructionTranslation scope statement test}
  | .assert_ (.comparison left [(.eq, .list_ elements)]) none => do
    let ⟨("list", arguments), site⟩ ← callExpression? left | none
    let argument ← listConstructorArguments? arguments
    let reference ← globalReference? scope "list"
    match values : elements.mapM scalarLiteral? with
    | some literal => some ⟨⟨reference, argument.val, literal, .constructorFirst⟩,
        .constructorFirst site argument.property values⟩
    | none => none
  | .assert_ (.comparison (.list_ elements) [(.eq, right)]) none => do
    let ⟨("list", arguments), site⟩ ← callExpression? right | none
    let argument ← listConstructorArguments? arguments
    let reference ← globalReference? scope "list"
    match values : elements.mapM scalarLiteral? with
    | some literal => some ⟨⟨reference, argument.val, literal, .literalFirst⟩,
        .literalFirst site argument.property values⟩
    | none => none
  | _ => none

inductive Action (scope : Scope) where
  | scalar (action : ModuleEntry.Action scope)
  | assertNot (condition : Operand scope)
  | assertSequenceLength (test : SequenceLengthTest scope)
  | assertListConstruction (test : ListConstructionTest scope)
  /-- Read the current module binding once at this assertion. -/
  | assertVarNames (receiver : Name) (reference : GlobalReference scope receiver) (needle : List UInt32)
  | define (name : Name) (reference : GlobalReference scope name) (child : ScopeTree)
      (parameters : Core.Closure.Parameters (frameLayout child.scope)) (code : Code (frameLayout child.scope))
      (keywordDefault : Option (Fin (frameLayout child.scope).locals × Int) := none)
      (defaults : List (DefaultOperand scope) := [])
  | call (destination : Destination scope) (name : Name) (reference : GlobalReference scope name)
      (arguments : List (Operand scope))
  | adjacentKeywordDiscard (name : Name) (reference : GlobalReference scope name) (value : Int)
  | nestedCall (destination : Destination scope) (name : Name) (reference : GlobalReference scope name)
      (arguments : List (CallArgument scope))

inductive Translation (tree : ScopeTree) : Nat → List Source.Stmt → List (Action tree.scope) → Prop where
  | done {index} (covered : index = tree.children.length) : Translation tree index [] []
  | scalar {index statement rest actions tail}
      (first : ModuleEntry.Translation tree.scope [statement] actions) (remaining : Translation tree index rest tail) :
      Translation tree index (statement :: rest) (actions.map .scalar ++ tail)
  | assertNot {index condition operand rest tail}
      (translated : TestTranslation tree.scope condition operand)
      (remaining : Translation tree index rest tail) :
      Translation tree index (.assert_ (.unary .not_ condition) none :: rest) (.assertNot operand :: tail)
  | assertSequenceLength {index statement test rest tail}
      (checked : SequenceLengthTranslation tree.scope statement test)
      (remaining : Translation tree index rest tail) :
      Translation tree index (statement :: rest) (.assertSequenceLength test :: tail)
  | assertListConstruction {index statement test rest tail}
      (checked : ListConstructionTranslation tree.scope statement test)
      (remaining : Translation tree index rest tail) :
      Translation tree index (statement :: rest) (.assertListConstruction test :: tail)
  | assertVarNames {index receiver needle rest tail} (reference : GlobalReference tree.scope receiver)
      (remaining : Translation tree index rest tail) :
      Translation tree index
        (.assert_ (.comparison (.text needle)
          [(.in_, .attribute (.attribute (.name receiver) "__code__") "co_varnames")]) none :: rest)
        (.assertVarNames receiver reference needle :: tail)
  | call {index statement rest target name arguments destination reference values tail}
      (site : CallSite statement target name arguments) (result : destination.placement = target)
      (operandOrder : Positional tree.scope arguments values) (remaining : Translation tree index rest tail) :
      Translation tree index (statement :: rest) (.call destination name reference values :: tail)
  | nestedCall {index statement rest target name arguments destination reference values tail}
      (site : CallSite statement target name arguments) (result : destination.placement = target)
      (operandOrder : CallArguments tree.scope arguments values) (remaining : Translation tree index rest tail) :
      Translation tree index (statement :: rest) (.nestedCall destination name reference values :: tail)
  | define {index name declaration body rest child reference parameters code tail defaults}
      (definition : DefinitionTranslation tree index declaration body child parameters code defaults)
      (remaining : Translation tree (index + 1) rest tail) :
      Translation tree index (.functionDef name declaration body [] none :: rest)
        (.define name reference child parameters code none defaults :: tail)
  | defineLambda {index statement name declaration body rest child reference parameters code tail defaults}
      (binding : Compile.Closure.Body.Assignment statement name (.lambda declaration body))
      (definition : DefinitionTranslation tree index declaration [.return_ (some body)] child parameters code defaults)
      (remaining : Translation tree (index + 1) rest tail) :
      Translation tree index (statement :: rest) (.define name reference child parameters code none defaults :: tail)
  | defineLiteralKeywordDefault {index name declaration body rest child reference parameter slot value code tail}
      (located : tree.children[index]? = some child)
      (path : child.scope.context.path = tree.scope.context.path ++ [index])
      (kind : child.scope.context.kind = .function)
      (shape : LiteralKeywordDefault parameter value declaration body)
      (binding : Compile.Closure.SlotTranslation child.scope parameter (.local slot))
      (functionBody : Compile.Closure.Body.Translation child 0 body code)
      (remaining : Translation tree (index + 1) rest tail) :
      Translation tree index (.functionDef name declaration body [] none :: rest)
        (.define name reference child ⟨[], .nil⟩ code (some (slot, value)) :: tail)
  | defineThenKeywordDiscard {index name declaration body statement rest child reference parameters code value tail}
      (definition : DefinitionTranslation tree index declaration body child parameters code)
      (call : AdjacentKeywordDiscard name declaration statement value)
      (remaining : Translation tree (index + 1) rest tail) :
      Translation tree index (.functionDef name declaration body [] none :: statement :: rest)
        (.define name reference child parameters code :: .adjacentKeywordDiscard name reference value :: tail)

def lowerPlan (tree : ScopeTree) (index : Nat) : (source : List Source.Stmt) →
    Except Error {actions // Translation tree index source actions}
  | [] =>
    if covered : index = tree.children.length then .ok ⟨[], .done covered⟩
    else .error (.functionScope tree.scope.context.path)
  | .functionDef name declaration body [] none :: rest => do
    let path := tree.scope.context.path ++ [index]
    match located : tree.children[index]? with
    | none => throw (.functionScope path)
    | some child =>
      if scopeMatches : child.scope.context.path = path ∧ child.scope.context.kind = .function then
        let some reference := globalReference? tree.scope name | throw (.unresolvedGlobal name)
        if let some checked := literalKeywordDefault? declaration body then
          let destination ← (Compile.Closure.Body.lowerSlot child.scope checked.val.1).mapError .functionBody
          match bound : destination.val with
          | .local slot =>
            let code ← (Compile.Closure.Body.lowerBodyWith child true 0 body).mapError .functionBody
            let tail ← lowerPlan tree (index + 1) rest
            return ⟨.define name reference child ⟨[], .nil⟩ code.val (some (slot, checked.val.2)) :: tail.val,
              .defineLiteralKeywordDefault located scopeMatches.1 scopeMatches.2 checked.property
                (bound ▸ destination.property) code.property tail.property⟩
          | _ => throw (.functionBody .parameterProfile)
        let parameters ← (Compile.Closure.Body.checkParameters child.scope (declaration.map eraseDefault)).mapError .functionBody
        let code ← (Compile.Closure.Body.lowerBodyWith child true 0 body).mapError .functionBody
        let defaults ← lowerDefaultSuffix tree.scope false declaration
        let definition : DefinitionTranslation tree index declaration body child parameters.val code.val defaults.val :=
          ⟨located, scopeMatches.1, scopeMatches.2, parameters.property.1, defaults.property,
            by simpa [List.map_map, Function.comp_def, eraseDefault] using parameters.property.2, code.property⟩
        let action := Action.define name reference child parameters.val code.val none defaults.val
        match adjacent : rest with
        | statement :: remaining =>
          if empty : defaults.val = [] then
            if let some call := adjacentKeywordDiscard? name declaration statement then
              let tail ← lowerPlan tree (index + 1) remaining
              let ordinary : DefinitionTranslation tree index declaration body child parameters.val code.val :=
                empty ▸ definition
              return ⟨.define name reference child parameters.val code.val ::
                .adjacentKeywordDiscard name reference call.val :: tail.val,
                adjacent.symm ▸ .defineThenKeywordDiscard ordinary call.property tail.property⟩
          let tail ← lowerPlan tree (index + 1) (statement :: remaining)
          return ⟨action :: tail.val, adjacent.symm ▸ .define definition tail.property⟩
        | [] =>
          let tail ← lowerPlan tree (index + 1) []
          return ⟨action :: tail.val, adjacent.symm ▸ .define definition tail.property⟩
      else throw (.functionScope path)
  | .assert_ (.comparison (.text needle)
      [(.in_, .attribute (.attribute (.name receiver) "__code__") "co_varnames")]) none :: rest => do
    let some reference := globalReference? tree.scope receiver | throw (.unresolvedGlobal receiver)
    let tail ← lowerPlan tree index rest
    return ⟨.assertVarNames receiver reference needle :: tail.val, .assertVarNames reference tail.property⟩
  | .assert_ (.unary .not_ condition) none :: rest => do
    let operand ← (lowerTest tree.scope condition).mapError .scalar
    let tail ← lowerPlan tree index rest
    return ⟨.assertNot operand.val :: tail.val, .assertNot operand.property tail.property⟩
  | statement :: rest => do
    if let some test := sequenceLengthTest? tree.scope statement then
      let tail ← lowerPlan tree index rest
      return ⟨.assertSequenceLength test.val :: tail.val, .assertSequenceLength test.property tail.property⟩
    else if let some test := listConstructionTest? tree.scope statement then
      let tail ← lowerPlan tree index rest
      return ⟨.assertListConstruction test.val :: tail.val, .assertListConstruction test.property tail.property⟩
    else if let some ⟨(name, .lambda declaration body), binding⟩ := Compile.Closure.Body.assignment? statement then
      unless (declaration.map eraseDefault).all Compile.Closure.Body.fixed do throw (.functionBody .parameterProfile)
      let path := tree.scope.context.path ++ [index]
      match located : tree.children[index]? with
      | none => throw (.functionScope path)
      | some child =>
        if scopeMatches : child.scope.context.path = path ∧ child.scope.context.kind = .function then
          let some reference := globalReference? tree.scope name | throw (.unresolvedGlobal name)
          let parameters ← (Compile.Closure.Body.checkParameters child.scope (declaration.map eraseDefault)).mapError .functionBody
          let code ← (Compile.Closure.Body.lowerBodyWith child true 0 [.return_ (some body)]).mapError .functionBody
          let defaults ← lowerDefaultSuffix tree.scope false declaration
          let tail ← lowerPlan tree (index + 1) rest
          let definition : DefinitionTranslation tree index declaration [.return_ (some body)] child
              parameters.val code.val defaults.val :=
            ⟨located, scopeMatches.1, scopeMatches.2, parameters.property.1, defaults.property,
              by simpa [List.map_map, Function.comp_def, eraseDefault] using parameters.property.2, code.property⟩
          return ⟨.define name reference child parameters.val code.val none defaults.val :: tail.val,
            .defineLambda binding definition tail.property⟩
        else throw (.functionScope path)
    else if let some ⟨(target, name, arguments), site⟩ := callSite? statement then
      let destination ← lowerDestination tree.scope target
      let some reference := globalReference? tree.scope name | throw (.unresolvedGlobal name)
      match lowerArguments tree.scope arguments with
      | .ok operands =>
        let tail ← lowerPlan tree index rest
        return ⟨.call destination.val name reference operands.val :: tail.val,
          .call site destination.property operands.property tail.property⟩
      | .error flatError =>
        let operands ← (lowerCallArguments tree.scope arguments).mapError fun _ => flatError
        let tail ← lowerPlan tree index rest
        return ⟨.nestedCall destination.val name reference operands.val :: tail.val,
          .nestedCall site destination.property operands.property tail.property⟩
    else
      let first ← (lowerStatements tree.scope [statement]).mapError .scalar
      let tail ← lowerPlan tree index rest
      return ⟨first.val.map .scalar ++ tail.val, .scalar first.property tail.property⟩

structure Checked (source : Source.Module) where
  tree : ScopeTree
  analyzed : Source.analyze source = .ok tree
  moduleScope : tree.scope.context.kind = .module_
  actions : List (Action tree.scope)
  lowered : Translation tree 0 source.body actions

def check (source : Source.Module) : Except Error (Checked source) :=
  match analyzed : Source.analyze source with
  | .error diagnostic => .error (.scope diagnostic)
  | .ok tree =>
    if kind : tree.scope.context.kind = .module_ then
      (lowerPlan tree 0 source.body).map fun lower =>
        ⟨tree, analyzed, kind, lower.val, lower.property⟩
    else .error .moduleScope

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions
