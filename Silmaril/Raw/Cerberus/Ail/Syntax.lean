module

public import Silmaril.Cerberus.Cabs.Syntax.Defs
public import Silmaril.Cerberus.Mem.Defs

/-! # Cerberus Ail and typed Ail

The types of Cerberus's `frontend/model/ail/ailSyntax.lem` and
`frontend/model/ail/genTypes.lem` at commit `b3e11ea334e95359907d4abf9194f0e7fedc6c6a`,
as far as `AilSyntax.ail_program` and `GenTypes.genTypeCategory` reach them
(`export2/schema.json` of the oracle, levels `ail` and `tail`). Ail is what
`Cabs_to_ail.desugar` returns: C with names resolved to symbols, declarations
collected into `Sigma`, `for` loops desugared to `while`, initializers made explicit,
and every type a `Ctype`. **Typed Ail** is the same syntax after
`GenTyping.annotate_program`, with every expression annotated by its
`GenTypeCategory`: `TypedProgram = Program GenTypeCategory`. Untyped Ail is
`Program Unit`.

This is the input language of the C compiler (`Silmaril.Compile.C`): it is still C
(lvalues, integer promotions, decays and implicit conversions are explicit in the
typing annotations), but with no syntactic ambiguity left.

Shared with the Core port: `Loc`, `Sym`, `Identifier`, `Attributes`, `Annot`,
`LabelAnnot`, `LoopAttribute`, the C types of `Silmaril.Cerberus.Ctype` (`Ctype`,
`Qualifiers`, `IntegerType`, `FloatingType`, `Alignment`, `TagDefinition`), and the
operators `ArithmeticOperator`, `UnaryOperator` and `BinaryOperator` of
`Silmaril.Cerberus.Mem` (Lem's `AilSyntax` operators, which Core reuses). String
literal pieces are the Cabs lexemes `Cabs.RawString` (`$str` or `$bytes`). The CN
specification types are those of `Silmaril.Cerberus.Cabs.Syntax`.

## Representation choices

* Lem maps (`extern_idmap`, `typedef_attributes`, `loop_attributes`, `cn_idents`) are
  kept as the **list of bindings in Lem key order**, as `Pmap.bindings_list` returns
  them and the wire prints them (`$map`). The list is what the document says; it is
  strictly increasing in the Lem key order when the document comes from Cerberus.
* Symbol, loop and marker numbers are the oracle's canonical ranks
  (`$fresh` in the schema), as natural numbers.
* Naming follows `Silmaril.Cerberus.Names`: types `UpperCamelCase`, constructors and
  fields `lowerCamelCase`, keywords with a trailing `_`, Lem's `x_` types as `XNode`,
  the `Ail`/`AilE`/`AilS` prefixes dropped. `Silmaril.Cerberus.Ail.Names` maps every
  Lem name, and the Lem names are the wire tags of `Silmaril.Cerberus.Ail.Codec`.

Most types are nested inductives through `List`, `Option` and products, so they
derive nothing; compare them through their wire encoding.
-/

@[expose] public section

namespace Silmaril.Cerberus.Ail

open Silmaril.Cerberus

/-! ## Constants -/

/-- Integer suffixes. Lem: `AilSyntax.integerSuffix`. -/
inductive IntegerSuffix where
  | u | ul | ull | l | ll
  deriving DecidableEq, Repr

/-- The base in which an integer constant was written. Lem: `AilSyntax.basis`. -/
inductive Basis where
  | octal | decimal | hexadecimal | binary
  deriving DecidableEq, Repr

/-- Integer constants: a value with its spelling, or the bound of an integer type
(`INT_MAX`-like constants that the desugarer introduces). Lem:
`AilSyntax.integerConstant`. -/
inductive IntegerConstant where
  | iconstant (value : Int) (basis : Basis) (suffix : Option IntegerSuffix)
  | max (ty : IntegerType)
  | min (ty : IntegerType)
  deriving DecidableEq, Repr

/-- Floating suffixes. Lem: `AilSyntax.floatingSuffix`. -/
inductive FloatingSuffix where
  | f | l
  deriving DecidableEq, Repr

/-- A floating constant: its source text and suffix. Lem:
`AilSyntax.floatingConstant`. -/
abbrev FloatingConstant := String × Option FloatingSuffix

/-- Character prefixes `L`, `u`, `U`. Lem: `AilSyntax.characterPrefix`. -/
inductive CharacterPrefix where
  | wide | utf16 | utf32
  deriving DecidableEq, Repr

/-- A character constant: its prefix and its source text between the quotes, escapes
undecoded. The text is a Lem `string` of source bytes, so it need not be valid UTF-8 (the
desugaring of a string-literal initializer makes one character constant per lexeme, and a
lexeme is one byte); it is a `Cabs.RawString` (`$str` or `$bytes`). Lem:
`AilSyntax.characterConstant`. -/
abbrev CharacterConstant := Option CharacterPrefix × Cabs.RawString

/-- C23 `false` and `true`. Lem: `AilSyntax.predefinedConstant`. -/
inductive PredefinedConstant where
  | false_ | true_
  deriving DecidableEq, Repr

/-- String-literal encoding prefixes `u8`, `u`, `U`, `L`. Lem:
`AilSyntax.encodingPrefix`. -/
inductive EncodingPrefix where
  | utf8 | utf16 | utf32 | wide
  deriving DecidableEq, Repr

/-- A string literal: its prefix and, per concatenated piece, the piece's location and
its raw lexemes (one byte or one escape sequence each, undecoded). Lem:
`AilSyntax.stringLiteral`. -/
abbrev StringLiteral := Option EncodingPrefix × List (Loc × List Cabs.RawString)

/-- Constants. Aggregate constants come from the desugaring of initializers. Lem:
`AilSyntax.constant`. -/
inductive Constant where
  | indeterminate (ty : Ctype)
  | null
  | integer (c : IntegerConstant)
  | floating (c : FloatingConstant)
  | character (c : CharacterConstant)
  | array (elem : Ctype) (elems : List Constant)
  | struct (tag : Sym) (members : List (Identifier × Constant))
  | union (tag : Sym) (member : Identifier) (value : Constant)
  | predefined (c : PredefinedConstant)

/-! ## Builtins, storage and declarations -/

/-- C11 atomic builtins. Lem: `AilSyntax.ail_builtin_atomic`. -/
inductive BuiltinAtomic where
  | threadFence | store | load | exchange | compareExchangeStrong | compareExchangeWeak
  | fetchKey
  deriving DecidableEq, Repr

/-- Linux-kernel memory-model builtins. Lem: `AilSyntax.ail_builtin_linux`. -/
inductive BuiltinLinux where
  | fence | read | write | rmw
  deriving DecidableEq, Repr

/-- Builtin functions. Lem: `AilSyntax.ail_builtin`. -/
inductive Builtin where
  | atomic (b : BuiltinAtomic)
  | linux (b : BuiltinLinux)
  | copyAllocId
  | cheri (name : String)
  deriving DecidableEq, Repr

/-- Storage durations (STD §6.2.4#1). Lem: `AilSyntax.storageDuration`. -/
inductive StorageDuration where
  | static | thread | automatic
  deriving DecidableEq, Repr

/-- Block-scope bindings: per symbol, its location, storage duration, whether it was
declared `register`, its alignment, qualifiers and type. Lem: `AilSyntax.bindings`. -/
abbrev Bindings :=
  List (Sym × ((Loc × StorageDuration × Bool) × Option Alignment × Qualifiers × Ctype))

/-- Which desugaring produced a statement. Lem: `AilSyntax.desug_case`. -/
inductive DesugCase where
  | forloop | continue_
  deriving DecidableEq, Repr

/-- Desugaring provenance of a statement. Lem: `AilSyntax.desug_info`. -/
structure DesugInfo where
  isForloopBody : Bool
  desugCase : Option DesugCase
  deriving DecidableEq, Repr

/-- Why a subtree is `invalid`. Lem: `AilSyntax.ail_invalid_reason`. -/
inductive InvalidReason where
  | desugaringInitFailed (msg : String)
  | other (msg : String)
  deriving DecidableEq, Repr

/-! ## Generic types (typed Ail) -/

/-- Integer types before resolution: a concrete type, the implementation's `size_t`,
`ptrdiff_t` and `ptraddr_t`, the type of an integer constant (`unknown`, decided by
its value), the integer promotion of a type, and the usual arithmetic conversion of two
(STD §6.3.1.8). Lem: `GenTypes.genIntegerType`. -/
inductive GenIntegerType where
  | concrete (ty : IntegerType)
  | sizeT
  | ptrdiffT
  | ptraddrT
  | unknown (c : IntegerConstant)
  | promote (ty : GenIntegerType)
  | usual (a b : GenIntegerType)
  deriving DecidableEq, Repr

/-- Lem: `GenTypes.genBasicType`. -/
inductive GenBasicType where
  | integer (ty : GenIntegerType)
  | floating (ty : FloatingType)
  deriving DecidableEq, Repr

/-- The type of an rvalue, with integer types not yet resolved. Lem:
`GenTypes.genType`. -/
inductive GenType where
  | void
  | basic (ty : GenBasicType)
  | array (elem : Ctype) (size : Option Int)
  | function (ret : Qualifiers × Ctype) (params : List (Qualifiers × Ctype × Bool))
      (variadic : Bool)
  | functionNoParams (ret : Qualifiers × Ctype)
  | pointer (q : Qualifiers) (ty : Ctype)
  | struct (tag : Sym)
  | union (tag : Sym)
  | atomic (ty : GenType)
  | byte

/-- The annotation of a typed-Ail expression: an lvalue of a qualified object type
(the `Bool` says whether it was declared `register`), or an rvalue of a generic type.
Lem: `GenTypes.genTypeCategory`. -/
inductive GenTypeCategory where
  | lvalue (q : Qualifiers) (ty : Ctype) (isRegister : Bool)
  | rvalue (ty : GenType)

/-! ## Expressions and statements -/

mutual

/-- Expression nodes. Lem: `AilSyntax.expression_ 'a`. The typing makes lvalue
conversion (`rvalue`), array-to-pointer decay (`arrayDecay`) and
function-to-pointer decay (`functionDecay`) explicit. -/
inductive ExpressionNode (α : Type) where
  | unary (op : UnaryOperator) (e : Expression α)
  | binary (e₁ : Expression α) (op : BinaryOperator) (e₂ : Expression α)
  | assign (lhs rhs : Expression α)
  | compoundAssign (lhs : Expression α) (op : ArithmeticOperator) (rhs : Expression α)
  /-- `c ? a : b`; `none` is GNU's `c ?: b`. -/
  | cond (c : Expression α) (a : Option (Expression α)) (b : Expression α)
  | cast (q : Qualifiers) (ty : Ctype) (e : Expression α)
  | call (f : Expression α) (args : List (Expression α))
  | assert (e : Expression α)
  | offsetof (ty : Ctype) (member : Identifier)
  /-- `_Generic`; the `Nat` is the index of the selected association, set by typing. -/
  | generic (e : Expression α) (selected : Option Nat) (assocs : List (GenericAssociation α))
  /-- An array initializer; the `Bool` says it comes from a string literal. -/
  | array (fromString : Bool) (ty : Ctype) (elems : List (Option (Expression α)))
  | struct (tag : Sym) (members : List (Identifier × Option (Expression α)))
  | union (tag : Sym) (member : Identifier) (value : Option (Expression α))
  | compound (q : Qualifiers) (ty : Ctype) (e : Expression α)
  | memberof (e : Expression α) (member : Identifier)
  | memberofptr (e : Expression α) (member : Identifier)
  | builtin (b : Builtin)
  | str (s : StringLiteral)
  | const (c : Constant)
  | ident (x : Sym)
  | sizeof (q : Qualifiers) (ty : Ctype)
  | sizeofExpr (e : Expression α)
  | alignof (q : Qualifiers) (ty : Ctype)
  /-- A type annotation, used for desugared enumeration constants. -/
  | annot (ty : Ctype) (e : Expression α)
  | vaStart (ap : Expression α) (last : Sym)
  | vaArg (ap : Expression α) (ty : Ctype)
  | vaCopy (dst src : Expression α)
  | vaEnd (ap : Expression α)
  | printType (e : Expression α)
  | bmcAssume (e : Expression α)
  | regLoad (r : Nat)
  /-- Lvalue conversion (STD §6.3.2.1#2). -/
  | rvalue (e : Expression α)
  /-- Array-to-pointer decay (STD §6.3.2.1#3). -/
  | arrayDecay (e : Expression α)
  /-- Function-to-pointer decay (STD §6.3.2.1#4). -/
  | functionDecay (e : Expression α)
  | atomic (e : Expression α)
  | labelAddressGnu (label : Sym)
  | gccStatement (bindings : Bindings) (body : List (Statement α))
  | invalid (ty : Ctype) (reason : InvalidReason)

/-- `_Generic` associations. Lem: `AilSyntax.generic_association 'a`. -/
inductive GenericAssociation (α : Type) where
  | type_ (q : Qualifiers) (ty : Ctype) (e : Expression α)
  | default (e : Expression α)

/-- An annotated expression: the annotation (`Unit` in Ail, `GenTypeCategory` in
typed Ail), Core annotations (standard citations), the location and the node. Lem:
`AilSyntax.expression 'a`. -/
inductive Expression (α : Type) where
  | mk (annot : α) (annots : List Annot) (loc : Loc) (node : ExpressionNode α)

/-- Statement nodes. `for` loops are desugared to `while` (`DesugInfo` says so). Lem:
`AilSyntax.statement_ 'a`. -/
inductive StatementNode (α : Type) where
  | skip
  | expr (e : Expression α)
  | block (bindings : Bindings) (body : List (Statement α))
  | if_ (c : Expression α) (then_ else_ : Statement α)
  | while_ (c : Expression α) (body : Statement α) (loopId : Nat)
  | do_ (body : Statement α) (c : Expression α) (loopId : Nat)
  | break_
  | continue_
  | returnVoid
  | return_ (e : Expression α)
  | switch (e : Expression α) (body : Statement α)
  | case_ (value : Int) (body : Statement α)
  | caseRangeGnu (lo hi : Int) (body : Statement α)
  | default (body : Statement α)
  | label (l : Sym) (body : Statement α) (annot : Option LabelAnnot)
  | goto (l : Sym)
  /-- The initializations of a block's declarations, in order. -/
  | declaration (decls : List (Sym × Option (Expression α)))
  | par (body : List (Statement α))
  | regStore (r : Nat) (e : Expression α)
  | marker (id : Nat) (body : Statement α)

/-- A statement with its location, desugaring provenance and attributes. Lem:
`AilSyntax.statement 'a`. -/
inductive Statement (α : Type) where
  | mk (loc : Loc) (desugInfo : DesugInfo) (attrs : Attributes) (node : StatementNode α)

end

/-! ## Programs -/

/-- External declarations. Lem: `AilSyntax.declaration`. -/
inductive Declaration where
  /-- An object: storage duration and `register`, alignment, qualifiers, type. -/
  | object (storage : StorageDuration × Bool) (align : Option Alignment) (q : Qualifiers)
      (ty : Ctype)
  /-- A function: has a prototype, return type, parameters (with `register`),
  variadic, `inline`, `_Noreturn`. -/
  | function (hasProto : Bool) (ret : Qualifiers × Ctype)
      (params : List (Qualifiers × Ctype × Bool)) (variadic inline_ noreturn : Bool)

/-- External identifier kinds. Lem: `AilSyntax.id_kind`. -/
inductive IdKind where
  | declaration | tentative | definition
  deriving DecidableEq, Repr

/-- CN namespaces. Lem: `Cn.cn_namespace`. -/
inductive CnNamespace where
  | predicate | function | lemma | funSpec | datatype | constructor | vars | oarg | typeName
  deriving DecidableEq, Repr

/-- A function definition: location, CN marker id, attributes, parameter symbols, body.
Lem: `AilSyntax.sigma_function_definition 'a` (without the name). -/
structure FunctionDefinition (α : Type) where
  loc : Loc
  marker : Nat
  attrs : Attributes
  params : List Sym
  body : Statement α

/-- The program's declarations. Lem: `AilSyntax.sigma 'a`. -/
structure Sigma (α : Type) where
  declarations : List (Sym × (Loc × Attributes × Declaration))
  /-- Initializers of objects with static storage, in source order. -/
  objectDefinitions : List (Sym × Expression α)
  functionDefinitions : List (Sym × FunctionDefinition α)
  staticAssertions : List (Expression α × StringLiteral)
  tagDefinitions : List (Sym × (Loc × Attributes × TagDefinition))
  /-- `map Symbol.identifier sigma_extern_id`, as bindings in key order. -/
  externIdmap : List (Identifier × (Sym × IdKind))
  /-- `map ail_identifier Annot.attributes`, as bindings in key order. -/
  typedefAttributes : List (Sym × Attributes)
  /-- `Annot.loop_attributes`, as bindings in key order. -/
  loopAttributes : List (Nat × LoopAttribute)
  cnFunctions : List (Cn.Function Sym Ctype)
  cnLemmata : List (Cn.Lemma Sym Ctype)
  cnPredicates : List (Cn.Predicate Sym Ctype)
  cnDatatypes : List (Cn.Datatype Sym)
  cnDeclSpecs : List (Nat × Sym × Cn.DeclSpec Identifier Cabs.TypeName)
  /-- `map sigma_cn_ident Symbol.sym`, as bindings in key order. -/
  cnIdents : List ((CnNamespace × Identifier) × Sym)

/-- A program: the startup function (`main`), if any, and its declarations. Lem:
`AilSyntax.ail_program 'a`. -/
abbrev Program (α : Type) := Option Sym × Sigma α

/-- Typed Ail: every expression annotated by its type category. -/
abbrev TypedProgram := Program GenTypeCategory

/-- A typed-Ail expression. -/
abbrev TypedExpression := Expression GenTypeCategory

/-- A typed-Ail statement. -/
abbrev TypedStatement := Statement GenTypeCategory

/-! ## Accessors -/

namespace Expression

variable {α : Type}

def annotation : Expression α → α
  | .mk a _ _ _ => a

def loc : Expression α → Loc
  | .mk _ _ l _ => l

def node : Expression α → ExpressionNode α
  | .mk _ _ _ n => n

end Expression

namespace Statement

variable {α : Type}

def loc : Statement α → Loc
  | .mk l _ _ _ => l

def node : Statement α → StatementNode α
  | .mk _ _ _ n => n

end Statement

end Silmaril.Cerberus.Ail
