module

public import Silmaril.Cerberus.Elaboration.Statements.Defs
public import Silmaril.Cerberus.Elaboration.GlobalOrder.Defs
public import Silmaril.Cerberus.Codec.WellFormed.Defs

/-! Initial actual function/file assembly from `translation.lem:4201–4544`.
Defined functions are limited to integer returns, normal pointer parameters and
matching declared/defined formal counts; the separate
statement and expression stages reject other forms. Independent direct integer
and selected null-pointer globals are supported by the separate Globals and
GlobalOrder stages. Runtime maps and aliases are explicit pinned inputs. This does not replace the imported reject-all
entrypoint, establish whole-C coverage, or certify the external runtime parser. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Functions
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Construction

structure RuntimeInputs where
  stdlib : List Runtime.Binding
  impl : List (ImplementationConstant × ImplDecl Codec.wireModel Unit)
  aliases : List (String × Sym)

abbrev FunctionInfo := Loc × Attributes × Ctype × List (Option Sym × Ctype) × Bool × Bool

structure Declarations where
  globals : List (Sym × Global Codec.wireModel Unit Unit) := []
  functions : List Runtime.Binding := []
  info : List (Sym × FunctionInfo) := []

/-- Runtime/source map insertion uses semantic symbol identity. -/
def insertSymbol {α : Type} (symbol : Sym) (value : α) (bindings : List (Sym × α)) : List (Sym × α) :=
  (symbol, value) :: bindings.filter (fun entry => decide (entry.1.key ≠ symbol.key))

/-- Source `core_object_type_of_ctype`; impossible source cases reject explicitly. -/
def objectType : Ctype → Except String ObjectType
  | .mk _ (.basic (.integer _)) | .mk _ .byte => .ok .integer
  | .mk _ (.basic (.floating _)) => .ok .floating
  | .mk _ (.pointer _ _) => .ok .pointer
  | .mk _ (.array type _) => return .array (← objectType type)
  | .mk _ (.struct tag) => .ok (.struct tag)
  | .mk _ (.union tag) => .ok (.union tag)
  | .mk _ (.atomic type) => objectType type
  | _ => .error "function or void Ctype has no Core object type"

def resultType : Ctype → Except String BaseType
  | .mk _ .void => .ok .unit
  | type => return .loaded (← objectType type)

def liftError {α : Type} : Except String α → State.ElabM α
  | .ok value => pure value
  | .error why => throw (.message why)

def integerType : Ctype → Bool
  | .mk _ (.basic (.integer _)) => true
  | _ => false

/-- Allocation uses the supplied global history, never a guessed maximum Ail ID. -/
def freshReturnLabel : State.ElabM Sym := do
  let before ← get
  let index ← State.freshInteger
  return ⟨before.freshness.digest, index, .id s!"ret_{index}"⟩

def metadataSymbol (runtime : RuntimeInputs) (symbol : Sym) : Sym :=
  Designators.resolveAlias runtime.aliases symbol

/-- Actual return `save`: main defaults to specified zero; a nonvoid ordinary
function falling through raises the pinned upstream undefined behavior. -/
def returnSave (startup : Option Sym) (symbol label temporary : Sym)
    (location : Loc) (type : Ctype) (baseType : BaseType) : Effect :=
  let isMain := match startup with
    | some main => decide (main.key = symbol.key)
    | none => false
  let defaultValue := if isMain then specified (integer 0)
    else standardPure "§6.9.1#12" (undefined location .UB088_reached_end_of_function)
  saveWith [.label .return_, .loc location] (label, baseType)
    [(temporary, ((baseType, some (type, .value)), defaultValue))]
    (pureEffect (symbolPure temporary))

/-- The pinned normal convention still allocates the unused argument-value
wrappers before the return label. Its procedure binds the original object-pointer
symbols; it neither creates their objects nor registers a callee-local scope.
See `translation.lem:4333–4344,4373–4379,4447–4457`. -/
def reserveParameterSymbols (symbols : List Sym) (types : List BaseType) : State.ElabM Unit := do
  let _ ← (symbols.zip types).mapM fun (_, type) => State.wrappedFreshSymbolWith .none type
  pure ()

def declaration (config : Target.Config) (types : Target.Environment)
    (runtime : RuntimeInputs) (program : Ail.TypedProgram) (accumulator : Declarations)
    (entry : Sym × (Loc × Attributes × Ail.Declaration)) : State.ElabM Declarations := do
  let (symbol, location, attributes, decl) := entry
  match decl with
  | .object _ alignment qualifiers type => do
      let global ← Globals.declaration config types runtime.stdlib program.2.objectDefinitions
        symbol location attributes alignment qualifiers type
      return { accumulator with globals := (symbol, global) :: accumulator.globals }
  | .function prototype (_, returnType) parameters variadic _ noreturn => do
    let baseType ← liftError (resultType returnType)
    let parameterTypes := parameters.map fun _ => BaseType.object .pointer
    match program.2.functionDefinitions.find? (fun item => decide (item.1.key = symbol.key)) with
    | none =>
        let info : FunctionInfo := (location, attributes, returnType,
          parameters.map (fun parameter => (none, parameter.2.1)), variadic, prototype)
        return { accumulator with
          functions := insertSymbol symbol (.procedureDecl location baseType parameterTypes) accumulator.functions
          info := insertSymbol (metadataSymbol runtime symbol) info accumulator.info }
    | some (_, definition) =>
        unless !variadic && !noreturn && integerType returnType do
          throw (.message "defined-function variadics, noreturn or noninteger returns are not ported")
        -- Explicitly restricted successful-equation domain: upstream relies on
        -- frontend typing and zips these lists without a local mismatch check.
        unless parameters.length == definition.params.length do
          throw (.message "defined-function declared/defined parameter counts differ")
        reserveParameterSymbols definition.params parameterTypes
        let info : FunctionInfo := (definition.loc, attributes, returnType,
          (definition.params.zip parameters).map (fun (symbol, parameter) => (some symbol, parameter.2.1)),
          variadic, prototype)
        let label ← freshReturnLabel
        let body ← Statements.translate config types runtime.stdlib ⟨returnType, label, noreturn⟩ definition.body (some symbol) runtime.aliases
        let temporary ← State.freshDescription .none
        let ending := returnSave program.1 symbol label temporary definition.loc returnType baseType
        return { accumulator with
          functions := insertSymbol symbol
            (.procedure definition.loc (some definition.marker) baseType (definition.params.zip parameterTypes)
              (strongSequence (wildcard .unit) body ending)) accumulator.functions
          info := insertSymbol symbol info accumulator.info }

def externalKind (symbol : Sym) : Ail.IdKind → LinkingKind
  | .declaration => .none
  | .tentative => .tentative symbol
  | .definition => .normal symbol

/-- Reverse declaration traversal retains all source effects. The selected constant
and integer-null-cast globals have their actual free symbols checked before the pinned
empty-dependency ordering specialization is applied. -/
def translate (config : Target.Config) (types : Target.Environment)
    (runtime : RuntimeInputs) (program : Ail.TypedProgram) : State.ElabM Codec.FileBindings := do
  let selected ← State.getCallingConvention
  unless decide (selected = .normal) do
    throw (.message "inner-argument calling convention elaboration is not ported")
  let declarations ← program.2.declarations.reverse.foldlM
    (declaration config types runtime program) {}
  let effects ← State.getEffects
  unless effects.stringLiterals.isEmpty do
    throw (.message "string-global elaboration is not ported")
  let globals ← liftError (GlobalOrder.mergeIndependent declarations.globals)
  return {
    main := program.1, callingConvention := selected
    tagDefs := (program.2.tagDefinitions.map fun (symbol, location, _, type) =>
      (symbol, location, type)).mergeSort (fun a b => Codec.WellFormed.compareSym a.1 b.1 != .gt)
    stdlib := runtime.stdlib, impl := runtime.impl, globs := globals
    funs := declarations.functions.mergeSort (fun a b => Codec.WellFormed.compareSym a.1 b.1 != .gt)
    extern := program.2.externIdmap.map fun (identifier, symbol, kind) =>
      (identifier, [symbol], externalKind symbol kind)
    funInfo := declarations.info.mergeSort (fun a b => Codec.WellFormed.compareSym a.1 b.1 != .gt)
    loopAttributes := program.2.loopAttributes
    visibleObjects := [] }

def elaborate (config : Target.Config) (types : Target.Environment)
    (runtime : RuntimeInputs) (program : Ail.TypedProgram)
    (freshness : Freshness.Context) : Except State.Error Codec.FileBindings × State.Context :=
  State.run (State.runErrors (translate config types runtime program))
    (State.initial freshness .normal "Driver")

end Silmaril.Cerberus.Elaboration.Functions
