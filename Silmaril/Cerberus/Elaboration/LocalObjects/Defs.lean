module

public import Silmaril.Cerberus.Elaboration.Arithmetic.Defs
public import Silmaril.Cerberus.Elaboration.Conversion.Defs
public import Silmaril.Cerberus.Elaboration.Lifetimes.Defs

/-! Focused local-object block and initializer equations from pinned
`translation.lem:3713-3771,4083-4175`. Recursive expression/statement dispatch
is passed in. Non-CHERI automatic scalar initializers and blocks without
compound literals are supported. No computation-construction scheduling claim
is made for arbitrary callbacks with eager source-side fresh prefixes. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.LocalObjects
open Silmaril.Cerberus
open Construction

/-- Wire projection of `Loc.with_cursor_from` where its first input has a known
region/point/other representation. Unknown can depend on a cursor omitted by
the imported wire location model and therefore rejects explicitly. -/
def blockActionLocation : Loc → Except String Loc
  | .unknown => .error "unsupported: unknown block location needs omitted upstream cursor information"
  | .point file line column => .ok (.region file line column file line column)
  | location => .ok location

def alignment (type : Ctype) : Option Alignment → Pure
  | none => alignof (ailCtype type)
  | some (.integer value) => integer value
  | some (.ctype alignedType) => alignof (ailCtype alignedType)

def objectBindings (bindings : Ail.Bindings) : List State.ObjectBinding :=
  bindings.map fun (symbol, (_, _, qualifiers, type)) => (symbol, qualifiers, type)

def automatic (bindings : Ail.Bindings) : Bool :=
  bindings.all fun (_, ((_, duration, _), _, _, _)) => decide (duration = .automatic)

def blockCreates (functionSymbol : Sym) (actionLocation : Loc) (bindings : Ail.Bindings) :
    List (Pat × Effect) :=
  bindings.map fun (symbol, ((identifierLocation, _, _), alignmentOption, _, type)) =>
    (symbolPattern symbol (.object .pointer),
      MemoryActions.create actionLocation (alignment type alignmentOption) (ailCtype type)
        (.source identifierLocation [functionSymbol, symbol]))

def blockKills (actionLocation : Loc) (bindings : Ail.Bindings) : List Effect :=
  bindings.map fun (symbol, (_, _, _, type)) =>
    MemoryActions.staticKill actionLocation type (symbolPure symbol)

/-- Creates/kills use original object symbols and consume no fresh IDs. Const
aliases are still allocated by `withBlockObjects`, even outside CHERI. -/
def block (config : Target.Config) (functionSymbol : Sym) (location : Loc)
    (bindings : Ail.Bindings) (body : State.ElabM (List Effect)) : State.ElabM Effect := do
  if config.cheri then throw (.message "unsupported: CHERI local-object blocks")
  unless automatic bindings do
    throw (.message "unsupported: nonautomatic local binding")
  let actionLocation ← Constants.liftResult (blockActionLocation location)
  let (_, compoundLiterals, expressions) ← State.withBlockObjects (objectBindings bindings) body
  unless compoundLiterals.isEmpty do
    throw (.message "unsupported: local block compound-literal lifetimes")
  return Lifetimes.sequenceBindings (blockCreates functionSymbol actionLocation bindings)
    (Lifetimes.sequenceUnits (expressions ++ blockKills actionLocation bindings) skip)

def arithmeticType : Ctype → Bool
  | .mk _ (.basic (.integer _)) | .mk _ (.basic (.floating _)) => true
  | _ => false

/-- Initializer fresh temporary precedes recursive wrapped expression
translation. Its destination CType and locking qualifier remain exact. -/
def initializer (config : Target.Config) (env : Target.Environment)
    (bindings : List Runtime.Binding) (location : Loc)
    (translate : Ail.TypedExpression → State.ElabM Effect) (symbol : Sym)
    (input : Option Ail.TypedExpression) : State.ElabM Effect := do
  if config.cheri then throw (.message "unsupported: CHERI local-object initializer")
  let (qualifiers, type) ← State.resolveObjectType symbol
  let store := MemoryActions.store location qualifiers.const (ailCtype type) (symbolPure symbol)
  match input with
  | none =>
      if (← get).backend == "Cn" then return skip
      else return addStandard "§6.2.4#6" (store (unspecified type) .na)
  | some input =>
      unless arithmeticType type do
        throw (.message "unsupported: initialized local is not a direct arithmetic object")
      let sourceType ← Constants.liftResult (Constants.targetResult (GeneralizedTypes.expressionType config env input))
      let objectType ← Constants.liftResult (Arithmetic.scalarObjectType sourceType)
      let temporary ← State.wrappedFreshSymbol (.loaded objectType)
      let core ← translate input
      let value ← Constants.liftResult (Conversion.loadedArithmetic bindings sourceType type temporary.expression)
      return strongSequence temporary.pattern core (store value .na)

/-- Exact `Core_aux.concat_sseq`, including removal of a final pure Unit. -/
def concatStrong : Effect → Effect → Effect
  | .mk annotations (.sseq pattern first rest), continuation =>
      .mk annotations (.sseq pattern first (concatStrong rest continuation))
  | .mk _ (.pure (.mk _ _ (.val .unit))), continuation => continuation
  | first, continuation => strongSequence (wildcard .unit) first continuation

def initializers (config : Target.Config) (env : Target.Environment)
    (bindings : List Runtime.Binding) (location : Loc)
    (translate : Ail.TypedExpression → State.ElabM Effect)
    (inputs : List (Sym × Option Ail.TypedExpression)) : State.ElabM Effect := do
  let translated ← inputs.mapM fun (symbol, input) => initializer config env bindings location translate symbol input
  match translated with
  | [] => return skip
  | first :: rest => return rest.foldl concatStrong first

end Silmaril.Cerberus.Elaboration.LocalObjects
