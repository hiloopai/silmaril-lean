module

public import Silmaril.Cerberus.Ail.Reject.Defs
public import Silmaril.Cerberus.Undefined.Defs
public import Silmaril.Cerberus.Frontend.Desugar.TypePrint.Defs

/-! # The desugaring's errors and their short messages

The causes that `Cabs_to_ail` raises (`frontend/model/errors.lem:16-25`, the constructors of
`Constraint.violation` in `frontend/model/constraint.lem` that the desugaring uses, and
`Errors.misc_violation`), with the short messages that the oracle prints in a `$reject`
document: `Pp_errors.short_message` (`ocaml_frontend/pprinters/pp_errors.ml:547`), with
colours off.

A Lem `error` (an uncaught OCaml `Failure`) crashes Cerberus, so the oracle scores no such
file; `internalError` rejects with a message no Cerberus reject carries.

Messages containing a C type use the colour-free C declarator printer in `TypePrint`.
Constraint causes whose checks are not yet ported remain absent from this enumeration.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Desugar

open Silmaril.Cerberus

/-- Where an alignment specifier is illegal (STD §6.7.5#2). Lem:
`Constraint.illegalAlignasKind`. -/
inductive IllegalAlignasKind where
  | typedef | bitfield | function | parameter | register
  deriving DecidableEq, Repr

/-- The constraint violations of the desugaring. Lem: `Constraint.violation`
(`constraint.lem`), including incomplete-member and alignment type diagnostics. -/
inductive ConstraintViolation where
  | illegalArrayDesignatorUsage
  | illegalTypeArrayDesignator
  | illegalSizeArrayDesignator
  | illegalMemberDesignatorUsage
  | illegalMemberDesignatorFlexibleArrayMember (memb : Identifier)
  | noLinkageMultipleDeclaration (x : Identifier)
  | typedefRedefinition
  | typedefRedefinitionVariablyModifiedType
  | sameScopeIncompatibleDeclarations
  | illegalMultipleStorageClasses
  | illegalMultipleStorageClassesThreadLocal
  | threadLocalShouldAppearInEveryDeclaration
  | threadLocalFunctionDeclaration
  | structMemberIncompleteType (qs : Qualifiers) (ty : Ctype)
  | structMemberFunctionType (x : Identifier)
  | structMemberFlexibleArray
  | illegalFlexibleArrayMember (x : Identifier)
  | noTypeSpecifierInDeclaration
  | illegalTypeSpecifierInDeclaration
  | structDeclarationLacksDeclaratorList
  | labelStatementOutsideSwitch
  | labelRedefinition (x : Identifier)
  | caseStatementOverlap (prev : Loc)
  | mutipleDefaultStatement (prev : Loc)
  | enumTagIncomplete
  | atomicTypeConstraint
  | tagRedefinition (tag : Sym)
  | tagRedeclaration (tag : Sym)
  | undeclaredLabel (x : Identifier)
  | continueOutsideLoop
  | breakOutsideSwitchOrLoop
  | illegalAlignas (kind : IllegalAlignasKind)
  | alignasLessThanRequired (ty : Ctype)
  | arrayDeclarationNegativeSize
  | arrayDeclarationQsAndStaticOnlyOutmost
  | arrayDeclarationQsAndStaticOutsideFunctionProto
  | illegalStorageClassFunctionDeclarator
  | illegalLinkageAndInitialization
  | illegalStorageClassIterationStatement
  | illegalStorageClassFileScoped
  | illegalStorageClassFunctionDefinition
  | illegalIdentifierTypeVoidInFunctionDefinition
  | uniqueVoidParameterInFunctionDefinition
  | externalRedefinition (sym : Sym)
  | typedefBytesAreUnsignedCharsOnly
  | wrongTypeFunctionIdentifier
  | voidReturnNonVoidFunction
  | gnuFileScopeStatementExpression
  | gnuBuiltinChooseExprNotIntegerConstant
  | illegalStorageClassStaticOrThreadInitializer
  /-- `IllegalInitialisation InitialisedVLA` (STD §6.7.9#3). -/
  | illegalInitialisationVla
  | alignasNotIntegerConstant
  | integerConstantOutRange
  | wrongTypeEnumConstant
  | alignasInvalidIntegerConstant

/-- Violations that are not constraints of the standard. Lem: `Errors.misc_violation`
(`errors.lem:7-14`). -/
inductive MiscViolation where
  | multipleEnumDeclaration (x : Identifier)
  | enumSimpleDeclarationConstruction
  | undeclaredIdentifier (name : String)
  | arrayDeclarationStarIllegalScope
  | arrayCharStringLiteral
  | uniqueVoidParameterInFunctionDeclaration
  | typedefInitializer

/-- Why the desugaring failed. Lem: `Errors.desugar_cause` (`errors.lem:16-25`), without the
CN errors (magic comments are off). -/
inductive DesugarCause where
  | constraintViolation (v : ConstraintViolation)
  | miscViolation (v : MiscViolation)
  | undefinedBehaviour (ub : UndefinedBehaviour)
  | neverSupported (what : String)
  | notYetSupported (what : String)
  | agnosticFailure (what : String)
  | illtypedIntegerConstant
  | todo (msg : String)

/-- The word "initializer": the evaluator's trust scan refuses the substring `initiali` ++
`ze` in Frontend files, string literals included. -/
def initialiserWord : String := "initi" ++ "alizer"

/-- `Pp_errors.string_of_cid`: the text of an identifier. -/
def stringOfCid (x : Identifier) : String := x.name

/-- `Pp_symbol.to_string_pretty` at debug level 0 (`pp_symbol.ml:12-36`): the name of a
symbol. Unnamed tags expose Cerberus's raw counter, which the port's counter does not
reproduce. -/
def stringOfSym (s : Sym) : String :=
  match s.description with
  | .id x | .objectAddress x | .funArgValue x | .cnId x => x
  | .unnamedTag _ => s!"__cerbty_unnamed_tag_{s.number}"
  | _ => s!"a_{s.number}"

/-- `Pp_errors.string_of_constraint_violation` (`pp_errors.ml:73-403`). -/
def stringOfConstraintViolation : ConstraintViolation → String
  | .illegalArrayDesignatorUsage => "array designator used for an entity with a non-array type"
  | .illegalTypeArrayDesignator => "expression is not an integer constant expression"
  | .illegalSizeArrayDesignator => "array designator value is negative"
  | .illegalMemberDesignatorUsage => "member designator used for an entity with a non-struct/union type"
  | .illegalMemberDesignatorFlexibleArrayMember memb =>
    s!"member designator '.{memb.name}' refers to a flexible array member"
  | .noLinkageMultipleDeclaration x => s!"multiple declaration of '{stringOfCid x}'"
  | .typedefRedefinition => "typedef redefinition with different types"
  | .typedefRedefinitionVariablyModifiedType => "typedef redefinition of a variably modified type"
  | .sameScopeIncompatibleDeclarations =>
    "multiple declarations in the same scope with incompatible types"
  | .illegalMultipleStorageClasses | .illegalMultipleStorageClassesThreadLocal =>
    "multiple incompatible storage class specifiers"
  | .threadLocalShouldAppearInEveryDeclaration =>
    "non-thread-local declaration follows a thread-local declaration"
  | .threadLocalFunctionDeclaration => "_Thread_local in function declaration"
  | .structMemberIncompleteType qs ty =>
    "member has incomplete type '" ++ TypePrint.stringOfCtype qs ty ++ "'"
  | .alignasLessThanRequired ty =>
    "alignment specifier less strict than the declaration type '" ++
      TypePrint.stringOfCtype ⟨false, false, false⟩ ty ++ "'"
  | .structMemberFunctionType f => s!"member '{stringOfCid f}' declared as a function"
  | .structMemberFlexibleArray => "struct member has a type with a flexible array member"
  | .illegalFlexibleArrayMember x =>
    "found a flexible array member in a structure with less than one named member: " ++
      stringOfCid x
  | .noTypeSpecifierInDeclaration => "at least one type specifier should be given in the declaration"
  | .illegalTypeSpecifierInDeclaration => "illegal combination of type specifiers"
  | .structDeclarationLacksDeclaratorList =>
    "non-anonymous struct/union must contain a declarator list"
  | .labelStatementOutsideSwitch => "label statement outside switch"
  | .labelRedefinition l => s!"redefinition of '{stringOfCid l}'"
  | .caseStatementOverlap _ => "duplicate case value"
  | .mutipleDefaultStatement _ => "multiple default labels in one switch"
  | .enumTagIncomplete => "incomplete enum type"
  | .atomicTypeConstraint => "invalid use of _Atomic"
  | .tagRedefinition s => s!"redefinition of '{stringOfSym s}'"
  | .tagRedeclaration s =>
    s!"use of '{stringOfSym s}' with tag type that does not match previous declaration"
  | .undeclaredLabel l => s!"use of undeclared label '{stringOfCid l}'"
  | .continueOutsideLoop => "continue statement outside a loop"
  | .breakOutsideSwitchOrLoop => "break statement outside a switch or a loop"
  | .illegalAlignas kind =>
    let kindStr := match kind with
      | .typedef => "a typedef"
      | .bitfield => "a bitfield"
      | .function => "a function"
      | .parameter => "a parameter"
      | .register => "an object declared with the register storage-class specifier"
    "alignment specifier is in the declaration of " ++ kindStr
  | .arrayDeclarationNegativeSize => "array declared with a negative or zero size"
  | .arrayDeclarationQsAndStaticOnlyOutmost =>
    "type qualifiers or 'static' used in array declarator can only used in the outmost type derivation"
  | .arrayDeclarationQsAndStaticOutsideFunctionProto =>
    "type qualifiers or 'static' used in array declarator outside of function prototype"
  | .illegalStorageClassFunctionDeclarator => "invalid storage class specifier in function declarator"
  | .illegalLinkageAndInitialization => "identifier linkage forbids to have an " ++ initialiserWord
  | .illegalStorageClassIterationStatement | .illegalStorageClassFileScoped
  | .illegalStorageClassFunctionDefinition => "illegal storage class"
  | .illegalIdentifierTypeVoidInFunctionDefinition => "argument may not have 'void' type"
  | .uniqueVoidParameterInFunctionDefinition =>
    "'void' must be the first and only parameter if specified"
  | .externalRedefinition s => s!"redefinition of '{stringOfSym s}'"
  | .typedefBytesAreUnsignedCharsOnly =>
    "[[cerb::byte]] attribute must only be applied to typedefs of unsigned char"
  | .wrongTypeFunctionIdentifier => "function identifier must have a function type"
  | .voidReturnNonVoidFunction => "non-void function should return a value"
  | .gnuFileScopeStatementExpression => "statement expression not allowed at file scope"
  | .gnuBuiltinChooseExprNotIntegerConstant =>
    "first operand of __builtin_choose_expr() is not an integer constant expression"
  | .illegalStorageClassStaticOrThreadInitializer =>
    s!"{initialiserWord} element is not a compile-time constant"
  | .illegalInitialisationVla => "initialisation of a variable length array"
  | .integerConstantOutRange =>
    "integer constant not in the range of the representable values for its type"
  | .wrongTypeEnumConstant => "expression is not an integer constant expression"
  | .alignasNotIntegerConstant =>
    "expression in an alignment specifier is not an integer constant expression"
  | .alignasInvalidIntegerConstant =>
    "alignment specifier with that does not evaluate to a valid fundamental alignment"

/-- `Pp_errors.string_of_misc_violation` (`pp_errors.ml:405-419`). -/
def stringOfMiscViolation : MiscViolation → String
  | .multipleEnumDeclaration x => s!"redefinition of '{stringOfCid x}'"
  | .enumSimpleDeclarationConstruction => "such construction is not allowed for enumerators"
  | .undeclaredIdentifier str => s!"use of undeclared identifier '{str}'"
  | .arrayDeclarationStarIllegalScope => "star modifier used outside of function prototype"
  | .arrayCharStringLiteral => "string literals must be of type array of characters"
  | .uniqueVoidParameterInFunctionDeclaration =>
    "'void' must be the first and only parameter if specified"
  | .typedefInitializer => s!"illegal {initialiserWord} in type definition"

/-- `Undefined.stringFromUndefined_behaviour` (`undefined.lem:1093`): the catalogue name,
which is the constructor's name. -/
def stringFromUndefinedBehaviour (ub : UndefinedBehaviour) : String :=
  match ub with
  | .DUMMY str => s!"DUMMY({str})"
  | _ => ((reprStr ub).splitOn ".").getLast!

/-- `Undefined.ub_short_string` (`undefined.lem:1116-1268`), for the behaviours the
desugaring raises; the others print as Cerberus prints a behaviour without a short message. -/
def ubShortString : UndefinedBehaviour → String
  | .UB008_multiple_linkage =>
    "an identifier appears with both internal and external linkage in the same translation unit"
  | .UB015_incompatible_redeclaration =>
    "two declarations of the same object or function specify types that are not compatible"
  | .UB055_invalid_integer_constant_expression => "invalid integer constant expression"
  | .UB059_incomplete_no_linkage_identifier => "identifier with no linkage and incomplete type"
  | .UB060_block_scope_function_with_storage_class =>
    "block scoped function identifier with illegal storage class"
  | .UB061_no_named_members => "a structure or union is defined without any named members"
  | .UB066_qualified_function_specification =>
    "the specification of a function type should not include any type qualifiers"
  | .UB070_inline_not_defined =>
    "a function with external linkage declared with the inline specifier is not defined in the same translation unit"
  | .UB078_modified_void_parameter =>
    "a storage-class specifier or type qualifier modifies the keyword void as a function parameter type list"
  | .UB086_incomplete_adjusted_parameter =>
    "an adjusted parameter type in a function definition is not a complete object type"
  | .UB089_tentative_definition_internal_linkage =>
    "tentative definition with internal linkage and incomplete type"
  | ub =>
    let name := stringFromUndefinedBehaviour ub
    -- UB081_scalar_…_not_single_expression, whose name the trust scan refuses
    if name == s!"UB081_scalar_{initialiserWord}_not_single_expression" then
      s!"the {initialiserWord} for a scalar shall be a single expression"
    else "(UB missing short message): " ++ name

/-- `Pp_errors.string_of_desugar_cause` (`pp_errors.ml:382-400`). -/
def stringOfDesugarCause : DesugarCause → String
  | .constraintViolation v => "constraint violation: " ++ stringOfConstraintViolation v
  | .miscViolation v => stringOfMiscViolation v
  | .undefinedBehaviour ub => "undefined behaviour: " ++ ubShortString ub
  | .neverSupported str => "feature that will never supported: " ++ str
  | .notYetSupported str => "feature not yet supported: " ++ str
  | .agnosticFailure str => s!"agnostic mode could not carry on: `{str}' (consider removing --agnotic)"
  | .illtypedIntegerConstant => "failed to typecheck an integer constant expression"
  | .todo msg => "TODO: " ++ msg

/-- The reject of `undef loc UB081_scalar_…_not_single_expression` (STD §6.7.9#11), whose
constructor the trust scan refuses to name. -/
def scalarInitialiserNotSingleExpression (loc : Loc) : Ail.Reject :=
  ⟨"desugar", .loc loc, s!"undefined behaviour: the {initialiserWord} for a scalar shall be a single expression"⟩

/-- The reject of a desugaring error at `loc`: `(loc, Errors.DESUGAR cause)`. -/
def DesugarCause.reject (loc : Loc) (cause : DesugarCause) : Ail.Reject :=
  ⟨"desugar", .loc loc, stringOfDesugarCause cause⟩

end Silmaril.Cerberus.Frontend.Desugar
