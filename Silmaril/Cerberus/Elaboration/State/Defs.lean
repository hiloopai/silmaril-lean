module

public import Silmaril.Cerberus.Elaboration.Construction.Defs
public import Silmaril.Cerberus.Elaboration.Freshness.Defs

/-! Explicit translation state from `translation_effect.lem` at Cerberus
`b3e11ea334e95359907d4abf9194f0e7fedc6c6a`. Freshness and backend selection are
explicit inputs. `ExceptT` retains diagnostic state on rejection; upstream fatal
exceptions do not return a local state, although their global fresh counter has
already advanced. Correspondence of successful state equations does not assert
correspondence of failure states. Debug printing and location/symbol printers
are not ported; errors needing them retain structured inputs instead.
-/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.State
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Construction

structure WrappedSymbol where
  symbol : Sym
  pattern : Pat
  expression : Pure
  deriving Repr

abbrev CompoundLiteral := Loc × Prefix × Sym × Bool × Ctype
abbrev StringLiteral := Loc × Sym × Ctype × Pure
abbrev ObjectBinding := Sym × (Qualifiers × Ctype)
abbrev ConstAlias := Sym × (Qualifiers × Ctype × Sym)

/-- Exactly the fields of upstream `elab_state`; freshness is separate. -/
structure Effects where
  visibleObjectTypes : Map Sym (Qualifiers × Ctype)
  visibleObjects : List (List Sym)
  stringLiterals : List StringLiteral
  compoundLiterals : List CompoundLiteral
  temporaryObjects : List (WrappedSymbol × Ctype)
  visibleObjectTypeMarkers : Map Nat (List (Sym × Ctype))
  cheriConstAliases : Map Sym Sym
  errors : List String
  callingConvention : CallingConvention

def initialEffects (convention : CallingConvention) : Effects where
  visibleObjectTypes := ∅
  visibleObjects := [[]]
  stringLiterals := []
  compoundLiterals := []
  temporaryObjects := []
  visibleObjectTypeMarkers := ∅
  cheriConstAliases := ∅
  errors := []
  callingConvention := convention

structure Context where
  freshness : Freshness.Context
  effects : Effects
  /-- Upstream `Global.backend_name ()`; only the exact name `Cn` records markers. -/
  backend : String

inductive Error where
  | freshness : Freshness.Error → Error
  | message : String → Error
  /-- The missing symbol is retained; upstream's `Show` output is not invented. -/
  | missingObjectType : Sym → Error
  deriving DecidableEq, Repr

abbrev ElabM := ExceptT Error (StateM Context)

def initial (freshness : Freshness.Context) (convention : CallingConvention)
    (backend : String) : Context := ⟨freshness, initialEffects convention, backend⟩

def run {α : Type} (computation : ElabM α) (context : Context) : Except Error α × Context :=
  computation.run context

def getEffects : ElabM Effects := return (← get).effects
def modifyEffects (update : Effects → Effects) : ElabM Unit :=
  modify fun context => {context with effects := update context.effects}

def freshInteger : ElabM Nat := do
  let context ← get
  match Freshness.integer context.freshness with
  | .error error => throw (.freshness error)
  | .ok (index, after) =>
      set {context with freshness := after}
      return index

def freshDescription (description : SymbolDescription) : ElabM Sym := do
  let context ← get
  match Freshness.description description context.freshness with
  | .error error => throw (.freshness error)
  | .ok (symbol, after) =>
      set {context with freshness := after}
      return symbol

def wrappedFreshSymbolWith (description : SymbolDescription) (type : BaseType) :
    ElabM (Sym × Pat × Pure) := do
  let symbol ← freshDescription description
  return (symbol, symbolPattern symbol type, symbolPure symbol)

def wrappedFreshSymbol (type : BaseType) : ElabM WrappedSymbol := do
  let (symbol, pattern, expression) ← wrappedFreshSymbolWith .none type
  return ⟨symbol, pattern, expression⟩

def getCallingConvention : ElabM CallingConvention := return (← getEffects).callingConvention
def getConstAliases : ElabM (Map Sym Sym) := return (← getEffects).cheriConstAliases

/-- Left-to-right allocations; aliases are accumulated in reverse const-binding
order. This is unconditional for const bindings in the upstream source. -/
def allocateConstAliases : List ObjectBinding → List ConstAlias → ElabM (List ConstAlias)
  | [], aliases => return aliases
  | (symbol, qualifiers, type) :: rest, aliases => do
      if qualifiers.const then
        let aliasSymbol ← freshDescription .none
        modifyEffects fun effects =>
          {effects with cheriConstAliases := Map.insert symbol aliasSymbol effects.cheriConstAliases}
        allocateConstAliases rest ((symbol, qualifiers, type, aliasSymbol) :: aliases)
      else allocateConstAliases rest aliases

/-- Scope exit pops the body's current head and restores only the prior compound
literal list. Object type and const-alias maps, and all other body effects, persist. -/
def withBlockObjects {α : Type} (bindings : List ObjectBinding) (body : ElabM α) :
    ElabM (List ConstAlias × List CompoundLiteral × α) := do
  let before ← getEffects
  let aliases ← allocateConstAliases bindings []
  modifyEffects fun effects => {effects with
    visibleObjectTypes := bindings.foldl
      (fun types binding => Map.insert binding.1 binding.2 types) effects.visibleObjectTypes
    visibleObjects := bindings.map Prod.fst :: effects.visibleObjects
    compoundLiterals := []}
  let result ← body
  let after ← getEffects
  match after.visibleObjects with
  | [] => throw (.message "[Translation.E.with_block_objects] found an ill-formed scope stack.")
  | _ :: scopes =>
      modifyEffects fun effects => {effects with
        visibleObjects := scopes
        compoundLiterals := before.compoundLiterals}
      return (aliases, after.compoundLiterals, result)

def trackTemporaryObjects {α : Type} (body : ElabM α) :
    ElabM (List (WrappedSymbol × Ctype) × α) := do
  let before ← getEffects
  match before.temporaryObjects with
  | _ :: _ => throw (.message "[Translation.E.track_temporary_objects]")
  | [] =>
      let result ← body
      let objects := (← getEffects).temporaryObjects
      modifyEffects fun effects => {effects with temporaryObjects := []}
      return (objects, result)

def registerTemporaryObject (pointer : WrappedSymbol) (type : Ctype) : ElabM Unit :=
  modifyEffects fun effects => {effects with temporaryObjects := (pointer, type) :: effects.temporaryObjects}

/-- Inner scopes precede outer scopes, retaining each scope's binding order. -/
def getVisibleObjects : ElabM (List Sym) := return (← getEffects).visibleObjects.flatten

def registerStringLiteral (location : Loc) (symbol : Sym) (type : Ctype)
    (expression : Pure) : ElabM Unit :=
  modifyEffects fun effects =>
    {effects with stringLiterals := (location, symbol, type, expression) :: effects.stringLiterals}
def getStringLiterals : ElabM (List StringLiteral) := return (← getEffects).stringLiterals

def registerCompoundLiteral (location : Loc) (allocationPrefix : Prefix) (symbol : Sym)
    (isConst : Bool) (type : Ctype) : ElabM Unit :=
  modifyEffects fun effects =>
    {effects with compoundLiterals := (location, allocationPrefix, symbol, isConst, type) :: effects.compoundLiterals}

def resolveObjectType (symbol : Sym) : ElabM (Qualifiers × Ctype) := do
  match Map.lookup symbol (← getEffects).visibleObjectTypes with
  | some binding => return binding
  | none => throw (.missingObjectType symbol)

/-- Every backend consumes an ID from the same counter as symbols. Only `Cn`
also resolves and records visible types. -/
def recordObjectTypesMarker : ElabM Nat := do
  let marker ← freshInteger
  if (← get).backend == "Cn" then
    let visible ← getVisibleObjects
    let typed ← visible.mapM fun symbol => do
      let (_, type) ← resolveObjectType symbol
      return (symbol, type)
    modifyEffects fun effects =>
      {effects with visibleObjectTypeMarkers := Map.insert marker typed effects.visibleObjectTypeMarkers}
  return marker

/-- Debug printing is outside this pure interface. -/
def recordError (message : String) : ElabM Unit :=
  modifyEffects fun effects => {effects with errors := message :: effects.errors}

/-- After a successful computation, reject its oldest accumulated error. -/
def runErrors {α : Type} (computation : ElabM α) : ElabM α := do
  let result ← computation
  match (← getEffects).errors.reverse with
  | [] => return result
  | oldest :: _ => throw (.message oldest)

end Silmaril.Cerberus.Elaboration.State
