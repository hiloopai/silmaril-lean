module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Defs
public import Silmaril.Languages.Python.Core.Closure.Defs

/-! # Reached completion and cleanup for checked module suites -/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ExceptionalTry

inductive Arm (action : Type) where
  | named (name : String) (body : List action) (target : Option String := none)
  | bare (body : List action)

structure Plan (action : Type) where
  body : List action
  handlers : List (Arm action)
  otherwise : List action
  cleanup : List action

structure SelectedArm (action : Type) where
  body : List action
  target : Option String

structure HandlerOperations (state failure : Type) where
  testClass : state → failure → String → Except failure Bool
  bindCaught : state → String → failure → Except failure state
  unbind : state → String → state

structure Outcome (state failure : Type) where
  reached : state
  completion : Except failure Unit

/-- Settle each successful scalar action before evaluating the next.
The failed action contributes no write and leaves the earlier state available. -/
def runSuite {state failure action : Type} (step : state → action → Except failure state) :
    state → List action → Outcome state failure
  | state, [] => ⟨state, .ok ()⟩
  | state, action :: rest =>
    match step state action with
    | .ok reached => runSuite step reached rest
    | .error error => ⟨state, .error error⟩

def Outcome.canEnterCleanup {state failure : Type} (outcome : Outcome state failure)
    (isPythonError : failure → Bool) : Bool :=
  match outcome.completion with
  | .ok () => true
  | .error failure => isPythonError failure

/-- Normal cleanup preserves the pending completion. A cleanup error takes
precedence with the state reached by that cleanup. -/
def Outcome.afterCleanup {state failure : Type} (pending cleaned : Outcome state failure) :
    Outcome state failure :=
  match cleaned.completion with
  | .ok () => ⟨cleaned.reached, pending.completion⟩
  | .error _ => cleaned

/-- A class test is reached only after every previous named test
has returned false. A match or error ends selection. -/
def selectHandler {state failure action : Type}
    (testClass : state → failure → String → Except failure Bool) (reached : state) (pending : failure) :
    List (Arm action) → Except failure (Option (SelectedArm action))
  | [] => .ok none
  | .bare actions :: _ => .ok (some ⟨actions, none⟩)
  | .named name actions target :: rest =>
    match testClass reached pending name with
    | .error error => .error error
    | .ok true => .ok (some ⟨actions, target⟩)
    | .ok false => selectHandler testClass reached pending rest

/-- Clear the target from the reached namespace on either completion of
the arm. Cleanup outside the arm sees this namespace. -/
def runHandler {state failure action : Type} (suite : state → List action → Outcome state failure)
    (operations : HandlerOperations state failure) (reached : state) (pending : failure)
    (selected : SelectedArm action) : Outcome state failure :=
  match selected.target with
  | none => suite reached selected.body
  | some name =>
    match operations.bindCaught reached name pending with
    | .error error => ⟨reached, .error error⟩
    | .ok bound =>
      let handled := suite bound selected.body
      { handled with reached := operations.unbind handled.reached name }

def afterBody {state failure action : Type} (suite : state → List action → Outcome state failure)
    (isPythonError : failure → Bool) (operations : HandlerOperations state failure)
    (body : Outcome state failure) (handlers : List (Arm action))
    (otherwise : List action) : Outcome state failure :=
  match body.completion with
  | .ok () => suite body.reached otherwise
  | .error failure =>
    if isPythonError failure then
      match selectHandler operations.testClass body.reached failure handlers with
      | .ok (some arm) => runHandler suite operations body.reached failure arm
      | .ok none => body
      | .error error => ⟨body.reached, .error error⟩
    else body

def runCleanup {state failure action : Type} (suite : state → List action → Outcome state failure)
    (isPythonError : failure → Bool) (pending : Outcome state failure)
    (cleanup : List action) : Outcome state failure :=
  if pending.canEnterCleanup isPythonError then
    pending.afterCleanup (suite pending.reached cleanup)
  else pending

def run {state failure action : Type} (suite : state → List action → Outcome state failure)
    (isPythonError : failure → Bool) (operations : HandlerOperations state failure)
    (initial : state) (plan : Plan action) : Outcome state failure :=
  let body := suite initial plan.body
  let pending := afterBody suite isPythonError operations body plan.handlers plan.otherwise
  runCleanup suite isPythonError pending plan.cleanup

open Source (ExceptHandler Expr Name Scope Stmt)
open Core.Closure (ExceptionClass ExceptionInstance RuntimeError)

inductive HandlerClass where
  | stock (kind : ExceptionClass)
  | invalid
  | outsideProfile

/-- Read the handler name exactly when its arm is considered. A present
invalid binding replaces the pending error instead of falling through. -/
def matchClass {Value : Type} (lookup : Name → Option Value) (classOf : Value → HandlerClass)
    (actual : ExceptionClass) (name : Name) : Except (Option RuntimeError) Bool :=
  match lookup name with
  | none => .error (some (.nameError name))
  | some value =>
    match classOf value with
    | .stock expected => .ok (decide (expected.catches actual))
    | .invalid => .error (some .invalidHandlerClass)
    | .outsideProfile => .error none

def scalarAtom : Expr → Bool
  | .name _ => true
  | source => (exactScalarLiteral? source).isSome

def scalarCondition : Expr → Bool
  | .comparison left [(.eq, right)] | .comparison left [(.ne, right)] =>
    scalarAtom left && scalarAtom right
  | source => scalarAtom source

def scalarStatement : Stmt → Bool
  | .pass => true
  | .assert_ condition none => scalarCondition condition
  | statement =>
    match binding? statement with
    | some checked => scalarAtom checked.val.2
    | none => false

inductive RaiseArgument (scope : Scope) where
  | text (value : Core.Text)
  | read (name : Name) (reference : GlobalReference scope name)

inductive RaiseArgument.Translation (scope : Scope) : Expr → RaiseArgument scope → Prop where
  | text {points value} (checked : Core.Text.ofPoints? points = some value) :
      Translation scope (.text points) (.text value)
  | read (name : Name) (reference : GlobalReference scope name) :
      Translation scope (.name name) (.read name reference)

def raiseArgument? (scope : Scope) :
    (source : Expr) → Option {value // RaiseArgument.Translation scope source value}
  | .text points =>
    match checked : Core.Text.ofPoints? points with
    | some value => some ⟨.text value, .text checked⟩
    | none => none
  | .name name =>
    (globalReference? scope name).map fun reference => ⟨.read name reference, .read name reference⟩
  | _ => none

structure RaiseName (scope : Scope) where
  name : Name
  reference : GlobalReference scope name

inductive RaiseName.Translation (scope : Scope) : Stmt → RaiseName scope → Prop where
  | named (name : Name) (reference : GlobalReference scope name) :
      Translation scope (.raise_ (some (.name name)) none) ⟨name, reference⟩

def raiseName? (scope : Scope) : (source : Stmt) → Option {operand // RaiseName.Translation scope source operand}
  | .raise_ (some (.name name)) none =>
    (globalReference? scope name).map fun reference => ⟨⟨name, reference⟩, .named name reference⟩
  | _ => none

structure RaiseCall (scope : Scope) where
  name : Name
  reference : GlobalReference scope name
  argument : Option (RaiseArgument scope)

inductive RaiseCall.Translation (scope : Scope) : Stmt → RaiseCall scope → Prop where
  | positional {name reference source argument} (checked : RaiseArgument.Translation scope source argument) :
      Translation scope (.raise_ (some (.callWith (.name name) [(.positional, source)])) none)
        ⟨name, reference, some argument⟩
  | plain {name reference source argument} (checked : RaiseArgument.Translation scope source argument) :
      Translation scope (.raise_ (some (.call (.name name) [source])) none) ⟨name, reference, some argument⟩
  | positionalEmpty (name : Name) (reference : GlobalReference scope name) :
      Translation scope (.raise_ (some (.callWith (.name name) [])) none) ⟨name, reference, none⟩
  | plainEmpty (name : Name) (reference : GlobalReference scope name) :
      Translation scope (.raise_ (some (.call (.name name) [])) none) ⟨name, reference, none⟩

def raiseCall? (scope : Scope) : (source : Stmt) → Option {call // RaiseCall.Translation scope source call}
  | .raise_ (some (.callWith (.name name) [(.positional, source)])) none => do
    let reference ← globalReference? scope name
    let checked ← raiseArgument? scope source
    return ⟨⟨name, reference, some checked.val⟩, .positional checked.property⟩
  | .raise_ (some (.call (.name name) [source])) none => do
    let reference ← globalReference? scope name
    let checked ← raiseArgument? scope source
    return ⟨⟨name, reference, some checked.val⟩, .plain checked.property⟩
  | .raise_ (some (.callWith (.name name) [])) none =>
    (globalReference? scope name).map fun reference => ⟨⟨name, reference, none⟩, .positionalEmpty name reference⟩
  | .raise_ (some (.call (.name name) [])) none =>
    (globalReference? scope name).map fun reference => ⟨⟨name, reference, none⟩, .plainEmpty name reference⟩
  | _ => none

inductive RaiseValue where
  | stockClass (kind : ExceptionClass)
  | exceptionInstance (value : ExceptionInstance)
  | nonCallable
  | otherCallable

/-- A class normalizes to an empty-argument exception payload. An
instance supplies its already constructed payload. -/
def RaiseValue.normalize : RaiseValue → RuntimeError
  | .stockClass kind => .raisedInstance (.empty kind)
  | .exceptionInstance value => .raisedInstance value
  | .nonCallable | .otherCallable => .invalidRaiseOperand

def RaiseName.error {scope : Scope} {Value : Type} (operand : RaiseName scope)
    (lookup : Name → Option Value) (classify : Value → RaiseValue) : RuntimeError :=
  (lookup operand.name).elim (.nameError operand.name) (fun value => (classify value).normalize)

inductive RaiseArguments where
  | empty
  | one (text : Option Core.Text)

def RaiseArgument.eval {scope : Scope} {Value : Type} (lookup : Name → Option Value)
    (text? : Value → Option Core.Text) : RaiseArgument scope → Except RuntimeError (Option Core.Text)
  | .text value => .ok (some value)
  | .read name _ => (lookup name).elim (.error (.nameError name)) (.ok ∘ text?)

def RaiseCall.evalArguments {scope : Scope} {Value : Type} (call : RaiseCall scope)
    (lookup : Name → Option Value) (text? : Value → Option Core.Text) : Except RuntimeError RaiseArguments :=
  match call.argument with
  | none => .ok .empty
  | some argument => (argument.eval lookup text?).map .one

def RaiseValue.construct : RaiseValue → RaiseArguments → Option RuntimeError
  | .stockClass kind, .empty => some (.raisedInstance (.empty kind))
  | .stockClass .exception, .one (some message) => some (.explicitException message)
  | .stockClass _, .one _ | .otherCallable, _ => none
  | .exceptionInstance _, _ | .nonCallable, _ => some .notCallable

/-- Save the live callee before reading the argument. Dispatch occurs only
after argument evaluation. The constructed exception is immediately raised. -/
def RaiseCall.error {scope : Scope} {Value : Type} (call : RaiseCall scope)
    (lookup : Name → Option Value) (classify : Value → RaiseValue) (text? : Value → Option Core.Text) :
    Option RuntimeError :=
  match lookup call.name with
  | none => some (.nameError call.name)
  | some callee =>
    match call.evalArguments lookup text? with
    | .error error => some error
    | .ok arguments => (classify callee).construct arguments

inductive Step (scope : Scope) where
  | scalar (action : Action scope)
  | raiseName (operand : RaiseName scope)
  | raiseCall (call : RaiseCall scope)
  | raiseInactive

/-- Only the protected suite of a module-level try starts without an
active exception in this standalone module profile. -/
inductive Suite (scope : Scope) (allowInactiveRaise : Bool) : List Stmt → List (Step scope) → Prop where
  | nil : Suite scope allowInactiveRaise [] []
  | scalar {source rest actions tail} (allowed : scalarStatement source = true)
      (code : ModuleEntry.Translation scope [source] actions)
      (remaining : Suite scope allowInactiveRaise rest tail) :
      Suite scope allowInactiveRaise (source :: rest) ((actions.map (Step.scalar ∘ Action.inLiteralArm)) ++ tail)
  | raiseName {source rest operand tail} (checked : RaiseName.Translation scope source operand)
      (remaining : Suite scope allowInactiveRaise rest tail) :
      Suite scope allowInactiveRaise (source :: rest) (.raiseName operand :: tail)
  | raiseCall {source rest call tail} (checked : RaiseCall.Translation scope source call)
      (remaining : Suite scope allowInactiveRaise rest tail) :
      Suite scope allowInactiveRaise (source :: rest) (.raiseCall call :: tail)

  | raiseInactive {source rest tail} (form : source = .raise_ none none)
      (inactive : allowInactiveRaise = true) (remaining : Suite scope allowInactiveRaise rest tail) :
      Suite scope allowInactiveRaise (source :: rest) (.raiseInactive :: tail)

def suite? (scope : Scope) (allowInactiveRaise : Bool) :
    (source : List Stmt) → Option {actions // Suite scope allowInactiveRaise source actions}
  | [] => some ⟨[], .nil⟩
  | statement :: rest => do
    let tail ← suite? scope allowInactiveRaise rest
    if allowed : scalarStatement statement = true then
      let lowered ← (lowerStatements scope [statement]).toOption
      return ⟨lowered.val.map (Step.scalar ∘ Action.inLiteralArm) ++ tail.val,
        .scalar allowed lowered.property tail.property⟩
    else
      match form : statement with
      | .raise_ none none =>
        if inactive : allowInactiveRaise = true then
          some ⟨.raiseInactive :: tail.val, .raiseInactive form inactive tail.property⟩
        else none
      | _ =>
        if let some checked := raiseName? scope statement then
          some ⟨.raiseName checked.val :: tail.val, .raiseName checked.property tail.property⟩
        else
          let checked ← raiseCall? scope statement
          return ⟨.raiseCall checked.val :: tail.val, .raiseCall checked.property tail.property⟩

inductive HandlerTarget (scope : Scope) : Option Name → Prop where
  | absent : HandlerTarget scope none
  | present {name : Name} (reference : GlobalReference scope name) : HandlerTarget scope (some name)

def handlerTarget? (scope : Scope) : (target : Option Name) → Option (PLift (HandlerTarget scope target))
  | none => some ⟨.absent⟩
  | some name => (globalReference? scope name).map fun reference => ⟨.present reference⟩

inductive Handlers (scope : Scope) : List ExceptHandler → List (Arm (Step scope)) → Prop where
  | nil : Handlers scope [] []
  | bare {source actions} (present : source.isEmpty = false)
      (translated : Suite scope false source actions) :
      Handlers scope [⟨none, none, source⟩] [.bare actions]
  | named {name target source actions rest arms} (reference : GlobalReference scope name)
      (targetCode : HandlerTarget scope target)
      (present : source.isEmpty = false) (translated : Suite scope false source actions)
      (remaining : Handlers scope rest arms) :
      Handlers scope (⟨some (.name name), target, source⟩ :: rest) (.named name actions target :: arms)

def handlers? (scope : Scope) :
    (source : List ExceptHandler) → Option {arms // Handlers scope source arms}
  | [] => some ⟨[], .nil⟩
  | [⟨none, none, source⟩] =>
    if present : source.isEmpty = false then
      (suite? scope false source).map fun checked => ⟨[.bare checked.val], .bare present checked.property⟩
    else none
  | ⟨some (.name name), target, source⟩ :: rest => do
    if present : source.isEmpty = false then
      let reference ← globalReference? scope name
      let targetCode ← handlerTarget? scope target
      let checked ← suite? scope false source
      let tail ← handlers? scope rest
      return ⟨.named name checked.val target :: tail.val,
        .named reference targetCode.down present checked.property tail.property⟩
    else none
  | _ => none

/-- An unconditional named raise uses the same reached-state transfer with no
handler, else suite, or cleanup. -/
def RaiseName.plan {scope : Scope} (operand : RaiseName scope) : Plan (Step scope) :=
  ⟨[.raiseName operand], [], [], []⟩

inductive Translation (scope : Scope) : Stmt → Plan (Step scope) → Prop where
  | namedRaise {statement operand} (checked : RaiseName.Translation scope statement operand) :
      Translation scope statement operand.plan
  | checked {body handlers otherwise cleanup first handler normal final}
      (present : body.isEmpty = false)
      (shape : (!handlers.isEmpty || (otherwise.isEmpty && !cleanup.isEmpty)) = true)
      (bodyCode : Suite scope true body first) (handlerCode : Handlers scope handlers handler)
      (elseCode : Suite scope false otherwise normal) (cleanupCode : Suite scope false cleanup final) :
      Translation scope (.try_ body handlers otherwise cleanup) ⟨first, handler, normal, final⟩

def check (scope : Scope) : (source : Stmt) → Option {plan // Translation scope source plan}
  | .try_ body handlers otherwise cleanup =>
    if present : body.isEmpty = false then do
      if shape : (!handlers.isEmpty || (otherwise.isEmpty && !cleanup.isEmpty)) = true then
        let first ← suite? scope true body
        let handler ← handlers? scope handlers
        let normal ← suite? scope false otherwise
        let final ← suite? scope false cleanup
        return ⟨⟨first.val, handler.val, normal.val, final.val⟩,
          .checked present shape first.property handler.property normal.property final.property⟩
      else none
    else none
  | statement =>
    (raiseName? scope statement).map fun checked => ⟨checked.val.plan, .namedRaise checked.property⟩

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ExceptionalTry
