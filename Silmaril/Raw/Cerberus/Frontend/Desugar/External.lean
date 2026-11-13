module

public import Silmaril.Cerberus.Frontend.Desugar.Statements.Defs

/-! # External declarations

`desugar_and_register_external_declaration` (`cabs_to_ail.lem:4731-4890`) at `b3e11ea3`: a
file-scope declaration registers its identifiers, then records each as a function
declaration, or as an object declaration with its tentative definition.

A function definition (`desugar_and_register_function_definition`, 4646-4727) desugars its
declarator in the scope of the body, so that the parameters are the body's objects.

Not ported yet: static assertions and the CN declarations (which only magic comments
produce).
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Desugar

open Silmaril.Cerberus Silmaril.Cerberus.Ail

/-- `Located external_declaration`'s `locOf` (`cabs.lem:419-447`): the location of the first
declared identifier. -/
def locOfExternalDeclaration : Cabs.ExternalDeclaration → Loc
  | .func f => locOfDeclarator f.declarator
  | .decl (.base _ _ []) => .unknown
  | .decl (.base _ _ (.mk _ decl _ :: _)) => locOfDeclarator decl
  | .decl (.staticAssert (.mk (.mk loc _) _)) => loc
  | .magic (loc, _) => loc
  | .funcCn f => f.name.loc
  | .lemmaCn l => l.name.loc
  | .funSpecCn s => s.name.loc
  | .predCn p => p.name.loc
  | .datatypeCn d => d.name.loc
  | .typeSynCn t => t.name.loc

/-- `add_toplevel_magic` (`cabs_to_ail_effect.lem:1177`). -/
def addToplevelMagic (str : Loc × String) : DesugM Unit :=
  modify fun st => { st with toplevelMagicStatements := str :: st.toplevelMagicStatements }

/-- The registration of one init-declarator of a file-scope declaration
(`cabs_to_ail.lem:4794-4876`): a function declaration (unqualified, without alignment
specifier, STD §6.7.3#9 and §6.7.5#2), or an object declaration with its tentative
definition (STD §6.9.2). -/
def registerExternalInitDeclarator (r : Rec) (attrs : Attributes) (specifs : Cabs.Specifiers) :
    Option InitDeclaratorResult → DesugM Unit
  | none => return ()
  | some (identLoc, identAttrs, link, sym, isTentative, (qs, ty), mkDesugInit) => do
    let .mk scs _ _ fspecs aspecs := specifs
    let doFunction (returnQsTy : Qualifiers × Ctype) (paramsOpt : Option (List (Qualifiers × Ctype × Bool)))
        (isVariadic : Bool) : DesugM Unit :=
      if qs != noQualifiers then undef identLoc .UB066_qualified_function_specification
      else if !aspecs.isEmpty then constraintViolation identLoc (.illegalAlignas .function)
      else registerFunctionDeclaration identLoc attrs sym true
        (returnQsTy, paramsOpt, isVariadic, fspecs.contains .inline, fspecs.contains .noreturn)
    match ty with
    | .mk _ (.function returnQsTy params isVariadic) => doFunction returnQsTy (some params) isVariadic
    | .mk _ (.functionNoParams returnQsTy) => doFunction returnQsTy none false
    | ty =>
      if scs.contains .register && !aspecs.isEmpty then
        constraintViolation identLoc (.illegalAlignas .register)
      else
        let alignOpt ← desugarAlignmentSpecifiers r identLoc ty aspecs
        let dur := determinateStorageDuration link scs
        registerExternalObjectDeclaration sym
          (isTentative, identLoc, combineAttributes attrs identAttrs, dur, scs.contains .register,
            alignOpt, qs, ty)
        match ← mkDesugInit () with
        | some (ty', dE) =>
          if !ctypeEqual ty ty' then updateExternalObjectType sym ty'
          -- the type after the initialisation must be complete
          if link == .none_ && (← isIncompleteM ty') then
            undef identLoc .UB059_incomplete_no_linkage_identifier
          else registerGlobalObjectDefinition2 identLoc sym link (.externalDefinition dE)
        | none =>
          let isIncomplete ← isIncompleteM ty
          if link == .internal && isIncomplete then
            undef identLoc .UB089_tentative_definition_internal_linkage
          else if link == .none_ && isIncomplete then
            undef identLoc .UB059_incomplete_no_linkage_identifier
          else if dur == .static || dur == .thread then
            if scs.contains scExtern then return ()
            else registerGlobalObjectDefinition2 identLoc sym link (.tentative identLoc ty)
          else return ()

/-- `desugar_and_register_function_definition` (`cabs_to_ail.lem:4646-4727`): only `extern`
and `static` (STD §6.9.1#4) and no alignment specifier; the declarator alone must give a
function type (STD §6.9.1#2). The parameters are registered in the scope of the body, the
labels before the body (STD §6.2.1#3); a function is defined once (STD §6.9#3). -/
def desugarAndRegisterFunctionDefinition (r : Rec) (fdef : Cabs.FunctionDefinition) : DesugM Unit := do
  let ⟨fundefLoc, fundefAttrs, specifs, decltor, stmt⟩ := fdef
  let .mk scs tspecs tquals fspecs aspecs := specifs
  let .mk _ ddecltor := decltor
  if scs.any (fun sc => sc != scExtern && sc != .static) then
    constraintViolation fundefLoc .illegalStorageClassFunctionDefinition
  else if !aspecs.isEmpty then
    constraintViolation fundefLoc (.illegalAlignas .function)
  else
    -- STD §6.9.1#5 is checked by desugar_direct_declarator
    let funblockScope ← freshBlockScope
    let (identsMap, ((_, funIdent), mkQsCtype)) ← withScope2 funblockScope (r.declarator .isFunDef decltor)
    -- STD §6.9.1#2: the type specified by the declarator alone
    match mkQsCtype noQualifiers (.mk [] .void) with
    | (_, .mk _ (.function ..)) | (_, .mk _ (.functionNoParams _)) => pure ()
    | _ => constraintViolation (locOfDirectDeclarator declaratorDepth ddecltor) .wrongTypeFunctionIdentifier
    let (_, funSym) ← registerOrdinaryIdentifier funIdent .function scs
    underScope .function do
      registerLabels stmt
      let (loc, markerId, funSym, dStmt) ← underScope funblockScope do
        hackInjectIdentsMap identsMap
        let (specsQs, specsTy) ← r.typeSpecifiers tspecs
        let (isAtomic, tqualsQs) := translateTypeQualifiers tquals
        let baseTy ← if isAtomic then mkCtypeAtomicM specsTy else pure specsTy
        let baseQs := combineQualifiers specsQs tqualsQs
        let (_, ty) := mkQsCtype baseQs baseTy
        -- STD §6.9.1#3 is checked by the Ail typing
        let process (returnQsTy : Qualifiers × Ctype) (paramsOpt : Option (List (Qualifiers × Ctype × Bool)))
            (isVariadic : Bool) : DesugM (Loc × Nat × Sym × Statement Unit) := do
          if ← functionIsDefined funSym then
            constraintViolation funIdent.loc (.externalRedefinition funSym)
          registerFunctionDeclaration funIdent.loc fundefAttrs funSym false
            (returnQsTy, paramsOpt, isVariadic, fspecs.contains .inline, fspecs.contains .noreturn)
          insideFunction returnQsTy.2 do
            let markerId ← recordMarker
            let dStmt ← desugarStatement r stmt
            return (funIdent.loc, markerId, funSym, dStmt)
        match ty with
        | .mk _ (.function returnQsTy params isVariadic) => process returnQsTy (some params) isVariadic
        | .mk _ (.functionNoParams returnQsTy) => process returnQsTy none false
        | _ => internalError "Cabs_to_ail.desugar_and_register_function_definition"
      let bindings ← bindingsOfIdentsMap identsMap
      -- the Cabs parser does not locate the function identifier
      registerFunctionDefinition funSym (withCursorFrom fundefLoc loc, markerId, fundefAttrs, bindings, dStmt)

/-- `desugar_and_register_external_declaration` (`cabs_to_ail.lem:4731-4890`): no `auto` or
`register` at file scope (STD §6.9#2); `struct T;` and `union T;` declare a tag (STD
§6.7.2.3#7); `enum T;` is not allowed. -/
def desugarAndRegisterExternalDeclaration (r : Rec) (edecl : Cabs.ExternalDeclaration) :
    DesugM Unit := do
  let edeclLoc := locOfExternalDeclaration edecl
  let storageClasses := match specifiersOfExternalDeclaration edecl with
    | some (.mk scs ..) => scs
    | none => []
  -- STD §6.9#2
  if storageClasses.any (fun z => z == .auto || z == .register) then
    constraintViolation edeclLoc .illegalStorageClassFileScoped
  else match edecl with
    | .func fdef => desugarAndRegisterFunctionDefinition r fdef
    -- STD §6.7.2.3#7
    | .decl (.base _ (.mk [] [.mk _ (.struct _ (some ident) none)] [] [] []) []) => do
      let _ ← registerTag edeclLoc .struct (some ident)
    | .decl (.base _ (.mk [] [.mk _ (.union _ (some ident) none)] [] [] []) []) => do
      let _ ← registerTag edeclLoc .union (some ident)
    | .decl (.base _ (.mk [] [.mk _ (.enum (some ident) none)] [] [] []) []) =>
      fail ident.loc (.miscViolation .enumSimpleDeclarationConstruction)
    | .decl (.base attrs specifs idecltors) => do
      let .mk scs tspecs tquals _ aspecs := specifs
      let (specsQs, baseTy) ← r.typeSpecifiers tspecs
      let (isAtomic, tqualsQs) := translateTypeQualifiers tquals
      let baseQs := combineQualifiers specsQs tqualsQs
      -- every init-declarator registers its identifier before any is recorded
      let xs ← idecltors.mapM (desugarInitDeclarator r attrs isAtomic (!aspecs.isEmpty) baseQs baseTy scs)
      xs.forM (registerExternalInitDeclarator r attrs specifs)
    | .decl (.staticAssert _) => notPorted edeclLoc "static assertions"
    | .magic str => addToplevelMagic str
    | _ => notPorted edeclLoc "CN declarations"

end Silmaril.Cerberus.Frontend.Desugar
