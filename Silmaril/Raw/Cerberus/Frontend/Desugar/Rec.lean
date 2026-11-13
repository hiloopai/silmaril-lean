module

public import Silmaril.Cerberus.Frontend.Desugar.Effect.Defs

/-! # The recursive functions of the desugaring

Lem defines `desugar_type_specifiers` … `desugar_statement_aux` (`cabs_to_ail.lem:1531-4089`)
as one mutually recursive group, which recurses through type names inside expressions,
expressions inside declarators and statements inside expressions. As in the parser
(`Frontend.Rec`), each desugaring file takes `r : Rec` and calls the members of the group
through it, never itself; `Desugar.knot n` ties the record lazily, one level per recursive
call, so every function is total and the files can be split. To add a function that another
file calls, add a field here, a line to `Rec.exhausted` and a line to `knot`.

The types of this file are the small enumerations of `cabs_to_ail.lem` that the group's
signatures use.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Desugar

open Silmaril.Cerberus Silmaril.Cerberus.Ail

/-- Whether a declarator is that of a function definition. Lem: `fundef`
(`cabs_to_ail.lem:982`). -/
inductive Fundef where
  | isFunDef | notFunDef
  deriving DecidableEq, Repr

/-- Whether a declarator is nested in an array declarator. Lem: `under_array`
(`cabs_to_ail.lem:1445`). -/
inductive UnderArray where
  | isUnderArray | notUnderArray
  deriving DecidableEq, Repr

/-- Whether a declaration declares an object or a function. Lem: `declaration_context`
(`cabs_to_ail.lem:37`). -/
inductive DeclarationContext where
  | objectDeclContext | functionDeclContext
  deriving DecidableEq, Repr

/-- The type a declarator builds from the base type: the qualifiers and type it is given
become those of the innermost derivation. Lem: `qs_ctype_builder`
(`cabs_to_ail.lem:986`). -/
abbrev QsCtypeBuilder := Qualifiers → Ctype → Qualifiers × Ctype

/-- The identity builder, `fun qs ty -> (qs, ty)`. -/
def idBuilder : QsCtypeBuilder := fun qs ty => (qs, ty)

/-- The statement context: the label `continue` jumps to inside a loop. Lem: `stmt_context`
(`cabs_to_ail.lem:1524`). -/
structure StmtContext where
  contIdentOpt : Option Identifier

/-- The members of the recursive group that other files call. -/
structure Rec where
  /-- `desugar_type_specifiers` (`cabs_to_ail.lem:1531`). -/
  typeSpecifiers : List Cabs.TypeSpecifier → DesugM (Qualifiers × Ctype)
  /-- `desugar_pointer_declarator` (`cabs_to_ail.lem:1912`). -/
  pointerDeclarator : Cabs.PointerDeclarator → DesugM QsCtypeBuilder
  /-- `desugar_abstract_declarator` (`cabs_to_ail.lem:1942`). -/
  abstractDeclarator : UnderArray → Cabs.AbstractDeclarator → DesugM QsCtypeBuilder
  /-- `desugar_direct_abstract_declarator` (`cabs_to_ail.lem:1957`). -/
  directAbstractDeclarator : UnderArray → Cabs.DirectAbstractDeclarator → DesugM QsCtypeBuilder
  /-- `desugar_direct_declarator` (`cabs_to_ail.lem:2019`). -/
  directDeclarator : Fundef → UnderArray → Cabs.DirectDeclarator →
    DesugM ((Attributes × Identifier) × QsCtypeBuilder)
  /-- `desugar_declarator` (`cabs_to_ail.lem:2211`). -/
  declarator : Fundef → Cabs.Declarator → DesugM ((Attributes × Identifier) × QsCtypeBuilder)
  /-- `desugar_type_name` (`cabs_to_ail.lem:2894`). -/
  typeName : Cabs.TypeName → DesugM (Qualifiers × Ctype)
  /-- `desugar_expression` (`cabs_to_ail.lem:2248`). -/
  expression : Cabs.Expression → DesugM (Expression Unit)
  /-- `wip_desugar_initializer_` (`cabs_to_ail.lem:3346`): the type after initialisation and
  the desugared initializer of an entity of the given storage duration and type. -/
  wipInitializer : Loc → StorageDuration → Ctype → Cabs.Initializer → DesugM (Ctype × Expression Unit)
  /-- `desugar_statement_aux` (`cabs_to_ail.lem:3691`). -/
  statementAux : StmtContext → Cabs.Statement → DesugM (Statement Unit)

/-- Every member rejecting: the knot at depth 0. -/
def Rec.exhausted : Rec :=
  let f {α : Type} : DesugM α := internalError "nesting too deep"
  ⟨fun _ => f, fun _ => f, fun _ _ => f, fun _ _ => f, fun _ _ _ => f, fun _ _ => f, fun _ => f,
    fun _ => f, fun _ _ _ _ => f, fun _ _ => f⟩

end Silmaril.Cerberus.Frontend.Desugar
