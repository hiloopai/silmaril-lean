module

public import Silmaril.Cerberus.Frontend.Desugar.Builtins.Defs
public import Silmaril.Cerberus.Frontend.Desugar.Alignment.Defs
public import Silmaril.Cerberus.Frontend.Desugar.ConstEval.Defs
public import Silmaril.Cerberus.Mem.Layout.Defs

/-! # Type specifiers and qualifiers

The type-specifier part of `cabs_to_ail.lem` at `b3e11ea3`: the projection of the basic type
specifiers (1249-1291), their combinations (STD §6.7.2#2, 1337-1422), type qualifiers
(1425) and `desugar_type_specifiers` (1531-1758).

Struct and union definitions (1544-1631, with `desugar_struct_declaration` 2697 and
`desugar_struct_declarator` 2728), enum definitions (`register_enumerators` 1762), and
their constraint diagnostics are here too. `typeof(expression)` needs the typing of
expressions and rejects explicitly. Alignment specifiers are in `Alignment.lean`.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Desugar

open Silmaril.Cerberus Silmaril.Cerberus.Ail

/-- The basic type specifiers. Lem: `Cabs.cabs_base_type_specifier`. -/
inductive BaseTypeSpecifier where
  | void | char | short | int | long | float | double | signed | unsigned | bool | complex
  deriving DecidableEq, Repr, Ord

/-- `project_base_type_specifier` (`cabs_to_ail.lem:1250-1276`). -/
def projectBaseTypeSpecifier : Cabs.TypeSpecifier → Option (BaseTypeSpecifier × Loc)
  | .mk loc tspec =>
    match tspec with
    | .void => some (.void, loc)
    | .char => some (.char, loc)
    | .short => some (.short, loc)
    | .int => some (.int, loc)
    | .long => some (.long, loc)
    | .float => some (.float, loc)
    | .double => some (.double, loc)
    | .signed => some (.signed, loc)
    | .unsigned => some (.unsigned, loc)
    | .bool => some (.bool, loc)
    | .complex => some (.complex, loc)
    | _ => none

/-- `project_base_type_specifiers_aux` (`cabs_to_ail.lem:1280-1289`): the specifiers in
order, with their locations in reverse order, if all are basic. -/
def projectBaseTypeSpecifiersAux (accBts : List BaseTypeSpecifier) (accLocs : List Loc) :
    List Cabs.TypeSpecifier → Option (List BaseTypeSpecifier × List Loc)
  | [] => some (accBts.reverse, accLocs)
  | spec :: specs' =>
    match projectBaseTypeSpecifier spec with
    | some (z, loc) => projectBaseTypeSpecifiersAux (z :: accBts) (loc :: accLocs) specs'
    | none => none

/-- `project_base_type_specifiers` (`cabs_to_ail.lem:1291`). -/
def projectBaseTypeSpecifiers (specs : List Cabs.TypeSpecifier) :
    Option (List BaseTypeSpecifier × List Loc) :=
  projectBaseTypeSpecifiersAux [] [] specs

/-- Equality of `Multiset.from_list`s. -/
def multisetEq (xs ys : List BaseTypeSpecifier) : Bool :=
  let sort (l : List BaseTypeSpecifier) := l.mergeSort fun a b => compare a b != .gt
  sort xs == sort ys

/-- `desugar_basic_type_specifiers` (`cabs_to_ail.lem:1338-1422`), STD §6.7.2#2: the basic
type a multiset of basic specifiers denotes, at the box of their locations. -/
def desugarBasicTypeSpecifiers (locs : List Loc) (specs : List BaseTypeSpecifier) :
    DesugM (Option (Loc × BasicType)) := do
  let loc := bboxLocation locs
  let is (l : List BaseTypeSpecifier) := multisetEq specs l
  let isAny (ls : List (List BaseTypeSpecifier)) := ls.any is
  -- STD §6.7.2#2, items 17-19
  if is [.float, .complex] || is [.double, .complex] || is [.long, .double, .complex] then
    fail loc (.neverSupported "_Complex types")
  else
    let int (ity : IntegerType) := some (loc, BasicType.integer ity)
    let real (fty : RealFloatingType) := some (loc, BasicType.floating (.realFloating fty))
    return (
      if is [.char] then int .char
      else if is [.signed, .char] then int (.signed .ichar)
      else if is [.unsigned, .char] then int (.unsigned .ichar)
      else if isAny [[.short], [.signed, .short], [.short, .int], [.signed, .short, .int]] then
        int (.signed .short)
      else if isAny [[.unsigned, .short], [.unsigned, .short, .int]] then int (.unsigned .short)
      else if isAny [[.int], [.signed], [.signed, .int]] then int (.signed .int)
      else if isAny [[.unsigned], [.unsigned, .int]] then int (.unsigned .int)
      else if isAny [[.long], [.signed, .long], [.long, .int], [.signed, .long, .int]] then
        int (.signed .long)
      else if isAny [[.unsigned, .long], [.unsigned, .long, .int]] then int (.unsigned .long)
      else if isAny [[.long, .long], [.signed, .long, .long], [.long, .long, .int],
          [.signed, .long, .long, .int]] then
        int (.signed .longLong)
      else if isAny [[.unsigned, .long, .long], [.unsigned, .long, .long, .int]] then
        int (.unsigned .longLong)
      else if is [.float] then real .float
      else if is [.double] then real .double
      else if is [.long, .double] then real .longDouble
      else if is [.bool] then int .bool
      else none)

/-- `translate_type_qualifiers` (`cabs_to_ail.lem:1426`), STD §6.7.3#5: whether `_Atomic` is
among them, and the other qualifiers. -/
def translateTypeQualifiers (qs : List Cabs.TypeQualifier) : Bool × Qualifiers :=
  (qs.contains .atomic, makeQualifiers (qs.contains .const) (qs.contains .restrict) (qs.contains .volatile))

/-- The kind of a new tag type. Lem: `struct_or_union` (`cabs_to_ail.lem:1519`). -/
inductive StructOrUnion where
  | struct | union
  deriving DecidableEq, Repr

/-- `desugar_struct_declarator` (`cabs_to_ail.lem:2728-2744`): the oracle does not ignore
bit-fields, which are not supported. -/
def desugarStructDeclarator (r : Rec) (hasAlignment : Bool) : Cabs.StructDeclarator →
    DesugM ((Attributes × Identifier) × QsCtypeBuilder)
  | .simple decltor => r.declarator .notFunDef decltor
  | .bitfield _ (.mk loc _) =>
    if hasAlignment then constraintViolation loc (.illegalAlignas .bitfield)
    else fail loc (.notYetSupported "bit-fields")

/-- `desugar_struct_declaration` (`cabs_to_ail.lem:2697-2725`): the members a member
declaration declares; without declarators, the members of an anonymous struct or union
(STD §6.7.2.1#13), or a violation (STD §6.7.2.1#2). -/
def desugarStructDeclaration (r : Rec) : Cabs.StructDeclaration → DesugM (List Member)
  | .member outerAttrs specs tquals alignSpecs sdecltors => do
    let (specsQs, baseTy) ← r.typeSpecifiers specs
    let (isAtomic, tqualsQs) := translateTypeQualifiers tquals
    if sdecltors.isEmpty then
      match ← getAnonymousStructOrUnion baseTy with
      | some membrs => return membrs
      | none => constraintViolation (ctypeLocOf baseTy) .structDeclarationLacksDeclaratorList
    else
      sdecltors.mapM fun sdecltor => do
        let ((attrs, ident), mkQsCtype) ← desugarStructDeclarator r (!alignSpecs.isEmpty) sdecltor
        let (qs, ty) := mkQsCtype (combineQualifiers tqualsQs specsQs) baseTy
        let alignOpt ← desugarAlignmentSpecifiers r ident.loc ty alignSpecs
        return (ident, (combineAttributes outerAttrs attrs, alignOpt, qs, if isAtomic then wrapAtomic ty else ty))
  | .staticAssert (.mk (.mk loc _) _) => notPorted loc "static assertions"

/-- `check_members` (`cabs_to_ail.lem:1506-1517`), STD §6.7.2.1#3 except for the flexible
array member: no function and no incomplete member. -/
def checkMembers (membrDefs : List Member) : DesugM Unit :=
  membrDefs.forM fun (ident, (_, _, qs, ty)) => do
    if isFunction ty then constraintViolation ident.loc (.structMemberFunctionType ident)
    else if ← isIncompleteM ty then
      constraintViolation ident.loc (.structMemberIncompleteType qs ty)

/-- `Utils.last` (`utils.lem:276-286`): the last element and the others. -/
def utilsLast {α : Type} : List α → Option (α × List α)
  | [] => none
  | xs => xs.getLast?.map fun x => (x, xs.dropLast)

/-- `desugar_new_struct_or_union` (`cabs_to_ail.lem:1544-1631`): a struct or union definition
declares a new type (STD §6.7.2.1#8): its tag, its members (distinct, STD §6.7.2.1#3), at
least one named member, and in a struct of two or more members a last member of unknown
array size that becomes the flexible array member. -/
def desugarNewStructOrUnion (r : Rec) (loc : Loc) (attrs : Attributes) (structOrUnion : StructOrUnion)
    (tagIdentOpt : Option Identifier) (sdecls : List Cabs.StructDeclaration) :
    DesugM (Qualifiers × Ctype) := do
  let (kindCtor, typeCtor) : TagKind × (Sym → Ctype) := match structOrUnion with
    | .struct => (.struct, fun sym => .mk [.loc loc] (.struct sym))
    | .union => (.union, fun sym => .mk [.loc loc] (.union sym))
  -- STD §6.7.2.1#8, sentence 1
  let tagSym ← registerTag loc kindCtor tagIdentOpt
  let allMembDefs := (← sdecls.mapM (desugarStructDeclaration r)).flatten
  let _ ← allMembDefs.foldlM (init := ([] : List Identifier)) fun acc (ident, _) =>
    if acc.any (·.name == ident.name) then fail ident.loc (.todo ("duplicate member: " ++ ident.name))
    else return ident :: acc
  let flexibleOpt ←
    if allMembDefs.length == 0 && structOrUnion == .union then
      -- STD §6.7.2.1#8, sentence 3
      undef loc .UB061_no_named_members
    else if allMembDefs.length == 1 || structOrUnion == .union then do
      checkMembers allMembDefs
      pure none
    else match utilsLast allMembDefs with
      -- STD §6.7.2.1#8, sentence 3
      | none => undef loc .UB061_no_named_members
      | some ((lastIdent, (lastMembAttrs, _, lastMembQs, lastMembTy)), membDefs) => do
        -- STD §6.7.2.1#3
        checkMembers membDefs
        if isFunction lastMembTy then
          constraintViolation lastIdent.loc (.structMemberFunctionType lastIdent)
        else if ← isIncompleteM lastMembTy then
          match structOrUnion, lastMembTy with
          | .struct, .mk _ (.array elemTy none) =>
            if allMembDefs.length == 1 then
              constraintViolation lastIdent.loc (.illegalFlexibleArrayMember lastIdent)
            else pure (some (membDefs, FlexibleArrayMember.mk lastMembAttrs lastIdent lastMembQs elemTy))
          | _, _ => constraintViolation lastIdent.loc (.structMemberIncompleteType lastMembQs lastMembTy)
        else pure none
  let (loc', cursorLoc) := match tagIdentOpt with
    | none => (loc, withCursor loc)
    | some tagIdent => (withCursorFrom loc tagIdent.loc, tagIdent.loc)
  let isAnonymous := tagIdentOpt.isNone
  registerTagDefinition loc' cursorLoc tagSym <| match structOrUnion, flexibleOpt with
    | .union, _ => .union loc' attrs isAnonymous allMembDefs
    | .struct, none => .struct loc' attrs isAnonymous allMembDefs none
    | .struct, some (membDefs', flexible) => .struct loc' attrs isAnonymous membDefs' (some flexible)
  return (noQualifiers, typeCtor tagSym)

/-- `desugar_enumerator` (`cabs_to_ail.lem:2747-2764`): the value of an explicit enumerator,
an integer constant expression (STD §6.7.2.2#2) representable as an `int`. -/
def desugarEnumerator (r : Rec) : Identifier × Option Cabs.Expression → DesugM (Identifier × Option (Loc × Int))
  | (ident, none) => return (ident, none)
  | (ident, some e) => do
    let loc := locOfExpression e
    let dE ← r.expression e
    -- STD §6.7.2.2#2
    if !(← isIntegerConstantExpression dE) then constraintViolation loc .wrongTypeEnumConstant
    else
      let n ← evaluateIntegerConstantExpression loc (some (mkCtypeInteger (.signed .int))) dE
      return (ident, some (loc, n))

/-- `register_enumerators` (`cabs_to_ail.lem:1762-1800`): each enumeration constant is an
`int`, the previous one plus one by default (STD §6.7.2.2#3), in scope from its enumerator on
(STD §6.2.1#7, sentence 2); the values in reverse order. -/
def registerEnumerators (r : Rec) (_tagSym : Sym) (enums : List (Identifier × Option Cabs.Expression)) :
    DesugM (List Int) := do
  let (_, nsRev) ← enums.foldlM (init := ((0 : Int), ([] : List Int))) fun (currentN, acc) enum => do
    let (ident, locNOpt) ← desugarEnumerator r enum
    let (loc, n) := locNOpt.getD (.other "TODO: register_enumerators", currentN)
    let dE : ExpressionNode Unit :=
      .annot (mkCtypeInteger (.signed .int))
        (.mk () [.std "§6.7.2.2#3"] loc (.const (.integer (.iconstant n .decimal none))))
    registerEnumConstant ident dE
    return (n + 1, n :: acc)
  return nsRev

/-- `desugar_type_specifiers` (`cabs_to_ail.lem:1531-1758`): the qualifiers and type a list of
type specifiers denotes. -/
def desugarTypeSpecifiers (r : Rec) (specs : List Cabs.TypeSpecifier) : DesugM (Qualifiers × Ctype) := do
  let basic ← match projectBaseTypeSpecifiers specs with
    | some (z, locs) => desugarBasicTypeSpecifiers locs z
    | none => pure none
  match basic with
  | some (loc, bty) => return (noQualifiers, .mk [.loc loc] (.basic bty))
  | none =>
    match specs with
    -- STD §6.7.2#2, sentence 1 (the parser never gives an empty list)
    | [] => constraintViolation .unknown .noTypeSpecifierInDeclaration
    -- STD §6.7.2#2, sentence 2 (`void' case)
    | [.mk loc .void] => return (noQualifiers, .mk [.loc loc] .void)
    | [.mk _ (.enum none none)] => internalError "TSpec_enum Nothing, Nothing"
    | [.mk _ (.struct _ none none)] => internalError "TSpec_struct Nothing, Nothing"
    | [.mk _ (.union _ none none)] => internalError "TSpec_union Nothing, Nothing"
    | [.mk loc (.enum (some tagIdent) none)] =>
      match ← resolveExtraordinaryIdentifier tagIdent .tag with
      -- STD §6.7.2.3#9
      | some (_, (tagSym, _)) => return (noQualifiers, .mk [.loc loc] (.basic (.integer (.enum tagSym))))
      | none => constraintViolation loc .enumTagIncomplete
    | [.mk loc (.struct attrs (some tagIdent) none)] =>
      if attrs != noAttributes then
        fail loc (.todo "Attribute constraint violation ==> N2335 6.7.2.1#6 and 6.7.2.3#4")
      else
        match ← resolveExtraordinaryIdentifier tagIdent .tag with
        -- STD §6.7.2.3#9
        | some (_, (tagSym, .tag .struct)) => return (noQualifiers, .mk [] (.struct tagSym))
        | some (_, (tagSym, _)) => constraintViolation loc (.tagRedeclaration tagSym)
        | none =>
          -- STD §6.7.2.3#8
          let tagSym ← registerTag loc .struct (some tagIdent)
          return (noQualifiers, .mk [.loc loc] (.struct tagSym))
    | [.mk loc (.union _ (some tagIdent) none)] =>
      match ← resolveExtraordinaryIdentifier tagIdent .tag with
      -- STD §6.7.2.3#9
      | some (_, (tagSym, .tag .union)) => return (noQualifiers, .mk [] (.union tagSym))
      | some (_, (tagSym, _)) => constraintViolation loc (.tagRedeclaration tagSym)
      | none =>
        -- STD §6.7.2.3#8
        let tagSym ← registerTag loc .union (some tagIdent)
        return (noQualifiers, .mk [.loc loc] (.union tagSym))
    | [.mk loc (.struct attrs tagIdentOpt (some sdecls))] =>
      desugarNewStructOrUnion r loc attrs .struct tagIdentOpt sdecls
    | [.mk loc (.union attrs tagIdentOpt (some sdecls))] =>
      desugarNewStructOrUnion r loc attrs .union tagIdentOpt sdecls
    | [.mk loc (.atomic tyname)] =>
      let (qs, ty) ← r.typeName tyname
      -- STD §6.7.2.4#3
      if isArray ty || isFunction ty || isAtomic ty || !isUnqualified qs then
        constraintViolation loc .atomicTypeConstraint
      else if ← isIncompleteM ty then constraintViolation loc .atomicTypeConstraint
      else return (qs, .mk [.loc loc] (.atomic ty))
    | [.mk loc (.enum tagIdentOpt (some enums))] => do
      let tagSym ← registerTag loc .enum tagIdentOpt
      let nsRev ← registerEnumerators r tagSym enums
      registerTagDefinition loc (withCursor loc) tagSym (.enum nsRev)
      return (noQualifiers, .mk [.loc loc] (.basic (.integer (.enum tagSym))))
    | [.mk _ (.name ident)] =>
      match translateBuiltinTypenames ident.name with
      | some ty => return (noQualifiers, ty)
      | none =>
        let cidLoc := ident.loc
        match ← resolveOrdinaryIdentifier cidLoc ident with
        | some (_, .typedef sym) =>
          let (_, qs, .mk _ ty) ← resolveTypedef sym
          return (qs, .mk [.loc cidLoc, .typedef sym] ty)
        | some _ => fail cidLoc (.notYetSupported "TODO: Tspec_name, not King_typedef")
        | none => fail cidLoc (.notYetSupported "TODO: Tspec_name, not resolved")
    | [.mk loc (.typeofExpr _)] => notPorted loc "typeof(expression) (needs GenTyping.annotate_expression)"
    | [.mk _ (.typeofType tyname)] => r.typeName tyname
    | _ =>
      let loc := bboxLocation (specs.map fun (.mk l _) => l)
      constraintViolation loc .illegalTypeSpecifierInDeclaration

end Silmaril.Cerberus.Frontend.Desugar
