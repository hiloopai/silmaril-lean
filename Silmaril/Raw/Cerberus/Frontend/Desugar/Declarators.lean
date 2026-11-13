module

public import Silmaril.Cerberus.Frontend.Desugar.Specifiers.Defs
public import Silmaril.Cerberus.Frontend.Desugar.ConstEval.Defs

/-! # Declarators, parameters and type names

The declarator part of `cabs_to_ail.lem` at `b3e11ea3`: array, pointer, abstract and direct
declarators (1833-2084), parameter type lists and declarations (2086-2209), declarators
(2211), storage-class checks (2541), init-declarators (2629) and type names (2894). A
declarator desugars to its identifier and a `QsCtypeBuilder`, which turns the qualified
base type into the declared one.

Not ported yet: alignment specifiers (`_Alignas`); array sizes are evaluated as far as
`Desugar.ConstEval` goes.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Desugar

open Silmaril.Cerberus Silmaril.Cerberus.Ail

/-- How deep the location and shape functions below follow nested declarators: as deep as
the parser builds them (`Grammar.depth`). -/
def declaratorDepth : Nat := 1000000

/-- `Cabs.loc_of_direct_declarator` (`cabs.lem:396-406`): the location of the declared
identifier. -/
def locOfDirectDeclarator : Nat → Cabs.DirectDeclarator → Loc
  | 0, _ => .unknown
  | _ + 1, .identifier _ ident => ident.loc
  | n + 1, .declarator (.mk _ dd) | n + 1, .array dd _ | n + 1, .function dd _ =>
    locOfDirectDeclarator n dd

/-- `Located declarator`'s `locOf` (`cabs.lem:412-416`): the location of the identifier. -/
def locOfDeclarator : Cabs.Declarator → Loc
  | .mk _ dd => locOfDirectDeclarator declaratorDepth dd

/-- `reduces_to_ddecl_identifier` (`cabs_to_ail.lem:1483-1495`): an identifier, possibly in
parentheses. -/
def reducesToDdeclIdentifier : Nat → Cabs.DirectDeclarator → Bool
  | 0, _ => false
  | _ + 1, .identifier .. => true
  | n + 1, .declarator (.mk none dd) => reducesToDdeclIdentifier n dd
  | _ + 1, _ => false

/-- `mk_ctype_atomic` inside a builder, where Lem's failure is unreachable. -/
def mkCtypeAtomic' (ty : Ctype) : Ctype := (mkCtypeAtomic ty).getD ty

/-- `desugar_array_declarator` (`cabs_to_ail.lem:1833-1909`): qualifiers and `static` only in
the outermost array of a parameter (STD §6.7.6.2#1), where they qualify the adjusted
pointer; `[*]` only in a prototype (STD §6.7.6.2#4). -/
def desugarArrayDeclarator (r : Rec) (underArray : UnderArray) : Cabs.ArrayDeclarator →
    DesugM QsCtypeBuilder
  | .mk loc tquals isStatic aDecltorSizeOpt => do
    let (isAtomic, tqualsQs) := translateTypeQualifiers tquals
    let performAdjust ← match ← getScope with
      | .prototype _ =>
        if underArray == .isUnderArray && (!tquals.isEmpty || isStatic) then
          -- STD §6.7.6.2#1, sentence 5, not outermost
          constraintViolation loc .arrayDeclarationQsAndStaticOnlyOutmost
        else
          pure fun qs ty => (combineQualifiers qs tqualsQs, if isAtomic then mkCtypeAtomic' ty else ty)
      | _ =>
        if !tquals.isEmpty || isStatic then
          -- STD §6.7.6.2#1, sentence 5, not function parameter
          constraintViolation loc .arrayDeclarationQsAndStaticOutsideFunctionProto
        else pure idBuilder
    if isStatic then fail loc (.notYetSupported "array parameter with the static keyword")
    else match aDecltorSizeOpt with
      -- STD §6.7.6.2#4, sentence 3
      | some (.expression e) => do
        let dE ← r.expression e
        if !(← isIntegerConstantExpression dE) then
          fail loc (.notYetSupported "variable length array type 2")
        else
          -- STD §6.7.6.2#1, sentence 2 (the typing is the evaluator's)
          let n ← evaluateIntegerConstantExpression loc none dE
          if n ≤ 0 then constraintViolation loc .arrayDeclarationNegativeSize
          else return fun qs ty => performAdjust qs (.mk [.loc loc] (.array ty (some n)))
      | some .asterisk =>
        match ← getScope with
        -- STD §6.7.6.2#4, sentence 2
        | .prototype _ => fail loc (.notYetSupported "variable length array type")
        | _ => fail loc (.miscViolation .arrayDeclarationStarIllegalScope)
      | none => return fun qs ty => performAdjust qs (.mk [.loc loc] (.array ty none))

/-- `desugar_pointer_declarator` (`cabs_to_ail.lem:1912-1939`), STD §6.7.6.1#1: the
qualifiers of the innermost `*` qualify the pointer being built; those of an outer `*`
qualify the type the next one points to. -/
def desugarPointerDeclarator (r : Rec) : Cabs.PointerDeclarator → DesugM QsCtypeBuilder
  | .mk ptrLoc tquals ptrDecltorOpt => do
    let (isAtomic, tqualsQs) := translateTypeQualifiers tquals
    let mkPointerCtype (refQs : Qualifiers) (refTy : Ctype) : Ctype :=
      let .mk annots _ := refTy
      let loc := bboxLocation [getLoc_ annots, ptrLoc]
      let ty : Ctype := .mk [.loc loc] (.pointer refQs refTy)
      if isAtomic then mkCtypeAtomic' ty else ty
    match ptrDecltorOpt with
    | some ptrDecltor =>
      let mkOuterPointerCtype ← r.pointerDeclarator ptrDecltor
      return fun baseQs baseTy => mkOuterPointerCtype tqualsQs (mkPointerCtype baseQs baseTy)
    | none => return fun baseQs baseTy => (tqualsQs, mkPointerCtype baseQs baseTy)

/-- `maybe (E.return (fun qs ty -> (qs, ty))) f opt`. -/
def builderOfOption {α : Type} (f : α → DesugM QsCtypeBuilder) : Option α → DesugM QsCtypeBuilder
  | some a => f a
  | none => return idBuilder

/-- The composition of two builders: `inner` first, then `outer`. -/
def composeBuilders (outer inner : QsCtypeBuilder) : QsCtypeBuilder :=
  fun baseQs baseTy => let (qs, ty) := inner baseQs baseTy; outer qs ty

/-- `desugar_abstract_declarator` (`cabs_to_ail.lem:1942-1954`). -/
def desugarAbstractDeclarator (r : Rec) (underArray : UnderArray) : Cabs.AbstractDeclarator →
    DesugM QsCtypeBuilder
  | .pointer ptrDecltor => r.pointerDeclarator ptrDecltor
  | .direct ptrDecltorOpt dabsDecltor => do
    let mkPointerQsCtype ← builderOfOption r.pointerDeclarator ptrDecltorOpt
    let mkQsCtype ← r.directAbstractDeclarator underArray dabsDecltor
    return composeBuilders mkQsCtype mkPointerQsCtype

/-- The type of a function declarator: `FunctionNoParams` without a parameter type list. -/
def mkFunCtype (paramsOpt : Option (List (Qualifiers × Ctype × Bool))) (isVariadic : Bool)
    (retQsTy : Qualifiers × Ctype) : CtypeNode :=
  match paramsOpt with
  | none => .functionNoParams retQsTy
  | some params => .function retQsTy params isVariadic

/-- The parameters of a parameter type list, without their identifiers. -/
def dropParamIdents (paramsOpt : Option (List (Option Identifier × (Qualifiers × Ctype × Bool)))) :
    Option (List (Qualifiers × Ctype × Bool)) :=
  paramsOpt.map (·.map (·.2))

/-- `desugar_parameter_declaration` (`cabs_to_ail.lem:2112-2208`): a parameter's type,
adjusted (STD §6.7.6.3#7-8), and complete unless unnamed in a declaration; only `register`
(STD §6.7.6.3#2) and no alignment specifier. A named parameter is registered as an object
without linkage. -/
def desugarParameterDeclaration (r : Rec) (isFirst : Bool) (fundef : Fundef) :
    Cabs.ParameterDeclaration → DesugM (Option Identifier × (Qualifiers × Ctype × Bool))
  | .declarator (.mk scs tspecs tquals _ aspecs) decltor => do
    let decltorLoc := locOfDeclarator decltor
    if scs.any (· != .register) then
      constraintViolation decltorLoc .illegalStorageClassFunctionDeclarator
    else if !aspecs.isEmpty then
      constraintViolation decltorLoc (.illegalAlignas .parameter)
    else
      let (specsQs, baseTy) ← r.typeSpecifiers tspecs
      let ((_, ident), mkQsCtype) ← r.declarator .notFunDef decltor
      let (isAtomic, tqualsQs) := translateTypeQualifiers tquals
      -- STD §6.9.1#7, sentence 4
      let (qs₀, ty₀) := mkQsCtype (combineQualifiers specsQs tqualsQs) baseTy
      if isVoid ty₀ then
        match fundef with
        | .isFunDef => constraintViolation decltorLoc .illegalIdentifierTypeVoidInFunctionDefinition
        -- STD §6.7#7 (a parameter has no linkage)
        | .notFunDef => undef decltorLoc .UB059_incomplete_no_linkage_identifier
      else
        let (qs, ty) := adjust qs₀ ty₀
        if ← isIncompleteM ty then
          match fundef with
          -- STD §6.9.1#7, sentence 4
          | .isFunDef => undef decltorLoc .UB086_incomplete_adjusted_parameter
          -- STD §6.7#7
          | .notFunDef => undef decltorLoc .UB059_incomplete_no_linkage_identifier
        else
          let isRegister := scs.contains .register
          let (link, sym) ← registerOrdinaryIdentifier ident (.object true) scs
          let dur := determinateStorageDuration link scs
          registerInternalObjectDeclaration sym (ident.loc, dur, isRegister, none, qs, ty)
          return (some ident, (qs, if isAtomic then mkCtypeAtomic' ty else ty, isRegister))
  | .abstract (.mk scs tspecs tquals _ aspecs) absDecltorOpt => do
    let loc := bboxLocation (tspecs.map fun (.mk l _) => l)
    if scs.any (· != .register) then
      constraintViolation loc .illegalStorageClassFunctionDeclarator
    else if !aspecs.isEmpty then
      constraintViolation loc (.illegalAlignas .parameter)
    else
      let (specsQs, baseTy) ← r.typeSpecifiers tspecs
      let mkQsCtype ← builderOfOption (r.abstractDeclarator .notUnderArray) absDecltorOpt
      let (isAtomic, tqualsQs) := translateTypeQualifiers tquals
      -- STD §6.9.1#7, sentence 4
      let (qs₀, ty₀) := mkQsCtype (combineQualifiers specsQs tqualsQs) baseTy
      let (qs, ty) := adjust qs₀ ty₀
      let ret := (none, (qs, if isAtomic then mkCtypeAtomic' ty else ty, scs.contains .register))
      match fundef with
      | .isFunDef =>
        if !(isFirst && isVoid ty) then
          constraintViolation (ctypeLocOf ty) .uniqueVoidParameterInFunctionDefinition
        else return ret
      | .notFunDef =>
        if !isFirst && isVoid ty then
          fail (ctypeLocOf ty) (.miscViolation .uniqueVoidParameterInFunctionDeclaration)
        -- STD §6.7.6.3#12 allows incomplete types
        else return ret

/-- `desugar_parameter_type_list` (`cabs_to_ail.lem:2086-2109`): `none` for `()`; a lone
unqualified `void` is the empty list (STD §6.7.6.3#10). -/
def desugarParameterTypeList (r : Rec) (fundef : Fundef) : Cabs.ParameterTypeList →
    DesugM (Option (List (Option Identifier × (Qualifiers × Ctype × Bool))) × Bool)
  | .mk paramDecls isVariadic => do
    let paramsOpt ← match paramDecls with
      | [] => pure none
      | x :: xs => do
        let p ← desugarParameterDeclaration r true fundef x
        let ps ← xs.mapM (desugarParameterDeclaration r false fundef)
        pure (some (p :: ps))
    match paramsOpt with
    | some [(none, (qs, .mk annots .void, isRegister))] =>
      if !isUnqualified qs || isRegister then
        undef (getLoc_ annots) .UB078_modified_void_parameter
      else return (some [], isVariadic)
    | _ => return (paramsOpt, isVariadic)

/-- `desugar_direct_abstract_declarator` (`cabs_to_ail.lem:1957-2016`): a function abstract
declarator desugars its parameters in a fresh prototype scope. -/
def desugarDirectAbstractDeclarator (r : Rec) (underArray : UnderArray) :
    Cabs.DirectAbstractDeclarator → DesugM QsCtypeBuilder
  | .abstract absDecltor => r.abstractDeclarator underArray absDecltor
  | .array dabsDecltorOpt aDecltor => do
    let mkOuterQsCtype ← builderOfOption (r.directAbstractDeclarator .isUnderArray) dabsDecltorOpt
    let mkArrayQsCtype ← desugarArrayDeclarator r underArray aDecltor
    return composeBuilders mkOuterQsCtype mkArrayQsCtype
  | .function dabsDecltorOpt paramTys => do
    let mkQsCtype ← builderOfOption (r.directAbstractDeclarator underArray) dabsDecltorOpt
    let protoScope ← freshPrototypeScope
    let (paramsOpt, isVariadic) ← underScope protoScope (desugarParameterTypeList r .notFunDef paramTys)
    let paramsOpt ← match paramsOpt with
      | some [(none, (qs, .mk annots .void, _))] =>
        if !isUnqualified qs then undef (getLoc_ annots) .UB078_modified_void_parameter
        -- STD §6.7.6.3#10
        else pure (some [])
      | paramsOpt => pure (dropParamIdents paramsOpt)
    return fun baseQs baseTy =>
      mkQsCtype noQualifiers (.mk [] (mkFunCtype paramsOpt isVariadic (baseQs, baseTy)))

/-- `desugar_direct_declarator` (`cabs_to_ail.lem:2019-2083`): the parameters of a function
declarator are in a fresh prototype scope, except in a function definition, whose caller
opens the scope of the body. -/
def desugarDirectDeclarator (r : Rec) (fundef : Fundef) (underArray : UnderArray) :
    Cabs.DirectDeclarator → DesugM ((Attributes × Identifier) × QsCtypeBuilder)
  | .identifier attrs ident => return ((attrs, ident), idBuilder)
  | .declarator decltor => r.declarator fundef decltor
  | .array ddecltor aDecltor => do
    let (attrsIdent, mkOuterQsCtype) ← r.directDeclarator fundef .isUnderArray ddecltor
    let mkArrayQsCtype ← desugarArrayDeclarator r underArray aDecltor
    return (attrsIdent, composeBuilders mkOuterQsCtype mkArrayQsCtype)
  | .function ddecltor paramTys => do
    let fundef' : Fundef :=
      if fundef == .isFunDef && reducesToDdeclIdentifier declaratorDepth ddecltor then .isFunDef
      else .notFunDef
    let (attrsIdent, mkQsCtype) ← r.directDeclarator fundef underArray ddecltor
    let (paramsOpt, isVariadic) ← match fundef' with
      | .isFunDef => desugarParameterTypeList r fundef' paramTys
      | .notFunDef => do
        let protoScope ← freshPrototypeScope
        underScope protoScope (desugarParameterTypeList r fundef' paramTys)
    let params := dropParamIdents paramsOpt
    let loc := locOfDirectDeclarator declaratorDepth ddecltor
    return (attrsIdent, fun baseQs baseTy =>
      mkQsCtype noQualifiers (.mk [.loc loc] (mkFunCtype params isVariadic (baseQs, baseTy))))

/-- `desugar_declarator` (`cabs_to_ail.lem:2211-2219`). -/
def desugarDeclarator (r : Rec) (fundef : Fundef) : Cabs.Declarator →
    DesugM ((Attributes × Identifier) × QsCtypeBuilder)
  | .mk ptrDecltorOpt ddecltor => do
    let mkPointerQsCtype ← builderOfOption r.pointerDeclarator ptrDecltorOpt
    let (attrsIdent, mkQsCtype) ← r.directDeclarator fundef .notUnderArray ddecltor
    return (attrsIdent, composeBuilders mkQsCtype mkPointerQsCtype)

/-- `desugar_type_name` (`cabs_to_ail.lem:2894-2905`); the alignment specifiers are ignored,
as in Lem. -/
def desugarTypeName (r : Rec) : Cabs.TypeName → DesugM (Qualifiers × Ctype)
  | .mk specs tquals _ absDecltorOpt => do
    let (specsQs, baseTy) ← r.typeSpecifiers specs
    let mkQsCtype ← builderOfOption (r.abstractDeclarator .notUnderArray) absDecltorOpt
    let (isAtomic, tqualsQs) := translateTypeQualifiers tquals
    let (qs, ty) := mkQsCtype (combineQualifiers specsQs tqualsQs) baseTy
    return (qs, if isAtomic then wrapAtomic ty else ty)

/-- `check_storage_class_specifiers` (`cabs_to_ail.lem:2541-2569`), STD §6.7.1#2-7. -/
def checkStorageClassSpecifiers (loc : Loc) (declCtxt : DeclarationContext)
    (scs : List Cabs.StorageClassSpecifier) : DesugM Unit := do
  let scope ← getScope
  if scs.length > 1 &&
      !(scs.all (fun z => z == .threadLocal || z == .static) ||
        scs.all (fun z => z == .threadLocal || z == scExtern)) then
    -- STD §6.7.1#2
    constraintViolation loc .illegalMultipleStorageClasses
  else if !(!(declCtxt == .objectDeclContext && isBlockScope scope && scs.contains .threadLocal) ||
      (scs.contains .static || scs.contains scExtern)) then
    -- STD §6.7.1#3, sentence 1
    constraintViolation loc .illegalMultipleStorageClassesThreadLocal
  else if declCtxt == .functionDeclContext && scs.contains .threadLocal then
    -- STD §6.7.1#4
    constraintViolation loc .threadLocalFunctionDeclaration
  else if !(!(declCtxt == .functionDeclContext && isBlockScope scope) || scs.isEmpty || scs == [scExtern]) then
    -- STD §6.7.1#7
    undef loc .UB060_block_scope_function_with_storage_class
  else return ()

/-- A desugared init-declarator: the identifier's location and attributes, the linkage, the
symbol, whether the declaration is a tentative definition, the qualified type, and the
desugaring of the initializer, postponed until the identifier is registered. -/
abbrev InitDeclaratorResult :=
  Loc × Attributes × Linkage × Sym × Bool × (Qualifiers × Ctype) ×
    (Unit → DesugM (Option (Ctype × Expression Unit)))

/-- `desugar_init_declarator` (`cabs_to_ail.lem:2629-2694`): register a typedef name (`none`)
or an ordinary identifier, with its linkage. A tentative definition is a file-scope object
declaration without initializer, `static` or without storage class (STD §6.9.2#2). An
initialised type must be complete or an array of unknown size (STD §6.7.9#3), and an
identifier with linkage cannot be initialised at block scope (STD §6.7.9#5). -/
def desugarInitDeclarator (r : Rec) (attrs : Attributes) (isAtomic hasAlignment : Bool)
    (baseQs : Qualifiers) (baseTy : Ctype) (scs : List Cabs.StorageClassSpecifier) :
    Cabs.InitDeclarator → DesugM (Option InitDeclaratorResult)
  | .mk loc decltor none => do
    let scope ← getScope
    let ((identAttrs, ident), mkQsCtype) ← r.declarator .notFunDef decltor
    let (qs, ty₀) := mkQsCtype baseQs baseTy
    let ty := if isAtomic then wrapAtomic ty₀ else ty₀
    let mkDesugInit : Unit → DesugM (Option (Ctype × Expression Unit)) := fun _ => return none
    -- STD §6.9.2#2, sentence 1
    let isTentative := match scope with
      | .file => isObject ty && (scs.contains .static || scs.isEmpty)
      | _ => false
    if scs == [.typedef] then
      if hasAlignment then constraintViolation loc (.illegalAlignas .typedef)
      else
        registerTypedef ident attrs qs ty
        return none
    else
      let (ctx, ok) : DeclarationContext × OrdinaryKind :=
        if isFunction ty then (.functionDeclContext, .function) else (.objectDeclContext, .object false)
      checkStorageClassSpecifiers loc ctx scs
      let (link, sym) ← registerOrdinaryIdentifier ident ok scs
      return some (ident.loc, identAttrs, link, sym, isTentative, (qs, ty), mkDesugInit)
  | .mk loc decltor (some init) => do
    let scope ← getScope
    if scs == [.typedef] then fail loc (.miscViolation .typedefInitializer)
    else
      let ((identAttrs, ident), mkQsCtype) ← r.declarator .notFunDef decltor
      let (qs, ty₀) := mkQsCtype baseQs baseTy
      let ty := if isAtomic then wrapAtomic ty₀ else ty₀
      let kind : OrdinaryKind := if isFunction ty then .function else .object false
      let link ← determinateLinkage ident .ordinary kind scs
      -- STD §6.7.9#3
      checkInitialisedTypeConstraint loc ty
      -- STD §6.7.9#5
      if isBlockScope scope && (link == .external || link == .internal) then
        constraintViolation (locOfDeclarator decltor) .illegalLinkageAndInitialization
      else
        -- the initializer is desugared once the identifier is registered, to be in its scope
        let mkDesugInit : Unit → DesugM (Option (Ctype × Expression Unit)) := fun _ => do
          return some (← r.wipInitializer loc (determinateStorageDuration link scs) ty init)
        let (ctx, ok) : DeclarationContext × OrdinaryKind :=
          if isFunction ty then (.functionDeclContext, .function) else (.objectDeclContext, .object false)
        checkStorageClassSpecifiers loc ctx scs
        let (link, sym) ← registerOrdinaryIdentifier ident ok scs
        return some (ident.loc, identAttrs, link, sym, false, (qs, ty), mkDesugInit)

end Silmaril.Cerberus.Frontend.Desugar
