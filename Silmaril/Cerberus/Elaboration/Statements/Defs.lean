module

public import Silmaril.Cerberus.Elaboration.Expressions.Defs
public import Silmaril.Cerberus.Elaboration.Conversion.Defs
public import Silmaril.Cerberus.Elaboration.LocalObjects.Defs
public import Silmaril.Cerberus.Elaboration.Scheduling.Defs
public import Silmaril.Cerberus.Elaboration.ControlFlow.Defs

/-! Focused actual `translation.lem` statement cases: skip, automatic-object
blocks, arithmetic local initialization, integer conditionals and integer returns
with local lifetime kills. The expression stage is separate. Other statement and
lifetime obligations reject explicitly. No C0
interpreter or observed result is used to construct these Core expressions. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Statements
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Construction

structure Environment where
  returnType : Ctype
  returnLabel : Sym
  noreturn : Bool

/-- Source `mk_unit_sseq`, including the final skip even after a return. -/
def unitSequence (expressions : List Effect) (continuation : Effect) : Effect :=
  expressions.foldr (fun expression rest => strongSequence (wildcard .unit) expression rest) continuation

/-- This focused subset has no object kills or creations across a transfer. -/
def emptyLifetimeRun (label : Sym) (arguments : List Pure) : State.ElabM Effect := do
  let visible ← State.getVisibleObjects
  unless visible.isEmpty do
    throw (.message "statement translation with live object lifetimes is not ported")
  return Construction.run label arguments

def liftError {α : Type} : Except String α → State.ElabM α
  | .ok value => pure value
  | .error why => throw (.message why)

def integerType : Ctype → Bool
  | .mk _ (.basic (.integer _)) => true
  | .mk _ (.atomic type) => integerType type
  | _ => false

/-- The upstream integer return branch retains the source return Ctype,
including its locations, as the argument to `conv_loaded_int`. -/
def returnExpression (config : Target.Config) (types : Target.Environment)
    (runtime : List Runtime.Binding) (environment : Environment)
    (expression : Ail.TypedExpression) (statementLocation : Loc := .unknown)
    (aliases : Designators.Aliases := []) : State.ElabM Effect := do
  if environment.noreturn then
    throw (.message "noreturn statement elaboration is not ported")
  let visible ← Lifetimes.captureVisible
  let sourceType ← liftError <| (GeneralizedTypes.expressionType config types expression).mapError reprStr
  unless integerType sourceType && integerType environment.returnType do
    throw (.message "noninteger return elaboration is not ported")
  let core ← Expressions.wrappedExpression config types runtime expression aliases
  let temporary ← State.wrappedFreshSymbol (.loaded .integer)
  let value ← liftError <| Conversion.loadedArithmetic runtime sourceType environment.returnType temporary.expression
  let transfer ← if visible.isEmpty then emptyLifetimeRun environment.returnLabel [value]
    else pure (Lifetimes.returnRun statementLocation environment.returnLabel visible [value])
  return strongSequence temporary.pattern core transfer

/-- Source annotation wrapper is independent of construction-time freshness. -/
def annotate (statement : Ail.TypedStatement) (core : Effect) : Effect :=
  let .mk location _ attributes _ := statement
  addLocation location (addStatement (addAttributes attributes core))

/-- Construct the raw node action before executing it. Sibling block actions
are constructed in the pinned source map order; bind continuations, including
nested if branches, are constructed when reached during execution. -/
def construct (config : Target.Config) (types : Target.Environment)
    (runtime : List Runtime.Binding) (environment : Environment)
    (statement : Ail.TypedStatement) (sourceFunction : Option Sym := none)
    (aliases : Designators.Aliases := []) : Scheduling.Computation Effect :=
  let .mk location _ _ node := statement
  match _hnode : node with
  | .skip => Scheduling.defer (pure skip)
  | .return_ expression => Scheduling.defer
      (returnExpression config types runtime environment expression location aliases)
  | .block bindings statements =>
      (do
        let children ← Scheduling.mapM (fun (child : { item : Ail.TypedStatement // item ∈ statements }) =>
          Scheduling.map (annotate child.val)
            (construct config types runtime environment child.val sourceFunction aliases)) statements.attach
        return (if bindings.isEmpty then do
          let (_, compoundLiterals, translated) ← State.withBlockObjects [] children
          unless compoundLiterals.isEmpty do
            throw (.message "block compound-literal lifetimes are not ported")
          return unitSequence translated skip
        else do
          let some functionSymbol := sourceFunction
            | throw (.message "local-object block requires its actual source function symbol")
          LocalObjects.block config functionSymbol location bindings children : State.ElabM Effect)
        : Scheduling.Build (State.ElabM Effect))
  | .declaration inputs => Scheduling.defer
      (LocalObjects.initializers config types runtime location
        (fun input => Expressions.wrappedExpression config types runtime input aliases) inputs)
  | .if_ condition yes no =>
      Scheduling.bind (Scheduling.wrappedFreshSymbol .boolean) fun prepared =>
        Scheduling.defer (ControlFlow.integerIf config types prepared location condition
          (fun _ input => Expressions.wrappedExpression config types runtime input aliases)
          (annotate yes <$> Scheduling.execute
            (construct config types runtime environment yes sourceFunction aliases))
          (annotate no <$> Scheduling.execute
            (construct config types runtime environment no sourceFunction aliases)))
  | _ => Scheduling.defer (throw (.message "statement form is not ported by the actual elaborator"))
termination_by sizeOf statement
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have memberBound := List.sizeOf_lt_of_mem child.property
      omega

/-- Actual public statement translation keeps every source wrapper outside
execution of the staged raw node action. -/
def translate (config : Target.Config) (types : Target.Environment)
    (runtime : List Runtime.Binding) (environment : Environment)
    (statement : Ail.TypedStatement) (sourceFunction : Option Sym := none)
    (aliases : Designators.Aliases := []) : State.ElabM Effect :=
  annotate statement <$> Scheduling.execute
    (construct config types runtime environment statement sourceFunction aliases)

def translateList (config : Target.Config) (types : Target.Environment)
    (runtime : List Runtime.Binding) (environment : Environment)
    (statements : List Ail.TypedStatement) (sourceFunction : Option Sym := none)
    (aliases : Designators.Aliases := []) : State.ElabM (List Effect) :=
  Scheduling.execute (Scheduling.mapM (fun statement =>
    Scheduling.map (annotate statement)
      (construct config types runtime environment statement sourceFunction aliases)) statements)

end Silmaril.Cerberus.Elaboration.Statements
