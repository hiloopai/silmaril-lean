module

public import Silmaril.Logic.Temporal.TLA.Surface.Defs
import Silmaril.Logic.Temporal.TLA.Surface.Parser.Operators

/-! Names and declaration identities for Surface TLA+ binding resolution. -/

public section

namespace Silmaril.Logic.Temporal.TLA.Resolution

open Surface

/-- An identity chosen by the caller, independent of the module header's spelling. -/
abbrev ModuleId := String

inductive Fixity where
  | prefix | infix | postfix
  deriving DecidableEq, Repr

inductive Name where
  | ident (spelling : Ident)
  | symbol (fixity : Fixity) (spelling : String)
  | qualified (prefixes : List Ident) (member : Name)
  deriving DecidableEq, Repr

def Name.ofSymbol : Symbol → Name
  | .prefix op => .symbol .prefix (match op with
    | .negation => "\\lnot"
    | .minus => "-."
    | .enabled => "ENABLED"
    | .unchanged => "UNCHANGED"
    | .always => "[]"
    | .eventually => "<>"
    | .subset => "SUBSET"
    | .union => "UNION"
    | .domain => "DOMAIN"
    | .symbol spelling => spelling)
  | .infix op => .symbol .infix (match op with
    | .compose => "\\cdot"
    | .leadsTo => "~>"
    | .guarantees => "-+->"
    | .symbol spelling => spelling)
  | .postfix op => .symbol .postfix (match op with
    | .prime => "'"
    | .symbol spelling => spelling)

def Name.ofOperator : OperatorName → Name
  | .ident spelling => .ident spelling
  | .symbolic op => ofSymbol op

/-- Operator synonyms compare within the same fixity. Identifier names are case-sensitive. -/
def Name.canonical (name : Name) : Name :=
  match name with
  | .ident _ => name
  | .qualified prefixes member => .qualified prefixes member.canonical
  | .symbol fixity spelling =>
    match Surface.Parser.lookupOperator spelling with
    | some op =>
      match fixity, op.fixity with
      | .prefix, .prefix | .infix, .infix | .infix, .product | .postfix, .postfix =>
        .symbol fixity op.canonical
      | _, _ => name
    | none => name

/-- The signature of an ordinary call slot. An operator slot expects a first-order
operator with the given positive number of expression parameters. -/
inductive Slot where
  | expression
  | operator (arity : Nat)
  deriving DecidableEq, Repr

/-- A component of a path in the original Surface tree. All indices are zero-based. -/
inductive Step where
  | import_ (index : Nat)
  | unit (index : Nat)
  | member (index : Nat)
  | letDecl (index : Nat)
  | parameter (index : Nat)
  | body
  | argument (index : Nat)
  | operand (index : Nat)
  | field (index : Nat)
  | update (index : Nat)
  | updateComponent (index : Nat)
  | arm (index : Nat)
  | other
  | bound (index : Nat)
  | domain
  | binder (index : Nat)
  | substitution (index : Nat)
  | instanceMember (index : Nat)
  | selector (index : Nat)
  deriving DecidableEq, Repr

abbrev Path := List Step

structure Site where
  moduleId : ModuleId
  path : Path
  deriving DecidableEq, Repr

def Site.child (site : Site) (step : Step) : Site :=
  { site with path := site.path ++ [step] }

inductive BindingId where
  | builtin (name : Name)
  | declared (site : Site)
  deriving DecidableEq, Repr

inductive BindingKind where
  | builtin | constant | variable | operator | namedFunction | formal | rigid | flexible
  | instanceNamespace | oldValue
  deriving DecidableEq, Repr

structure Binding where
  id : BindingId
  /-- Canonical name for lookup. The spelling at parsed sites remains in the Surface tree. -/
  name : Name
  kind : BindingKind
  slots : List Slot
  isLocal : Bool := false
  deriving DecidableEq, Repr

inductive ReferenceRole where
  | application | operatorArgument
  deriving DecidableEq, Repr

structure Reference where
  target : BindingId
  role : ReferenceRole
  deriving DecidableEq, Repr

/-- A public declaration directly owned by a signature-only module. Its dependencies
supply inherited declarations. The caller attests to the module's identity and signature. -/
inductive SignatureDecl where
  | constant (declaration : OperatorDecl)
  | variable (name : Ident)
  | operator (name : Name) (slots : List Slot)
  deriving Repr

/-- Each edge maps an EXTENDS spelling in this module to the caller's module identity. -/
abbrev ImportMap := List (Ident × ModuleId)

inductive ModuleInput where
  | parsed (source : Surface.Module) (imports : ImportMap)
  | signature (name : Ident) (imports : ImportMap) (declarations : List SignatureDecl)
  deriving Repr

abbrev Registry := List (ModuleId × ModuleInput)

/-- Resolve an explicit replacement in its host tree. An implicit replacement
references the exact host binding selected at the instance declaration. -/
inductive Replacement where
  | expression (site : Site) (body : Surface.Expr)
  | binding (id : BindingId)
  deriving Repr

structure InstanceMember where
  id : BindingId
  home : BindingId
  /-- Arity of each qualified segment, including the final member. -/
  argumentCounts : List Nat
  deriving Repr

structure InstancePlan where
  site : Site
  target : ModuleId
  parameters : List BindingId
  substitutions : List (BindingId × Replacement)
  members : List InstanceMember
  deriving Repr

inductive Unsupported where
  | instantiation | submodule | recursive | functionDefinition
  | assumption | theoremDecl | proofDirective | proofReference
  | qualifiedReference | labeledExpression | actionOrTemporal
  | operatorSubstitution | instanceParameter | instanceTheorem | letInstance
  | instanceSignature | selectionScope
  deriving DecidableEq, Repr

inductive DiagnosticKind where
  | unknownModule (id : ModuleId)
  | duplicateModuleId (id : ModuleId)
  | duplicateImportMapping (name : Ident)
  | unresolvedImport (name : Ident)
  | importNameMismatch (expected actual : Ident) (target : ModuleId)
  | importCycle (cycle : List ModuleId)
  | conflictingImport (name : Name) (first second : BindingId)
  | conflictingName (name : Name) (previous : BindingId)
  | unknownName (name : Name)
  | oldValueOutOfScope
  | arityMismatch (name : Name) (expected actual : Nat)
  | expectedExpression
  | incompleteInstanceName (name : Name)
  | illegalSubstitutionTarget (name : Name)
  | duplicateSubstitution (id : BindingId)
  | missingSubstitution (name : Name) (id : BindingId)
  | expectedOperatorArgument (arity : Nat)
  | operatorArgumentMismatch (expectedArity : Nat) (actualSlots : List Slot)
  | malformed (form : String)
  | unsupported (form : Unsupported)
  deriving DecidableEq, Repr

structure Diagnostic where
  site : Site
  kind : DiagnosticKind
  deriving DecidableEq, Repr

end Silmaril.Logic.Temporal.TLA.Resolution
