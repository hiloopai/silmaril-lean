module

public import Silmaril.Cerberus.Ctype.Defs

/-! # Cerberus Cabs: the C abstract syntax of the parser

The types of Cerberus's `frontend/model/cabs.lem` and of the CN types it reaches in
`frontend/model/cn.lem`, at commit `b3e11ea334e95359907d4abf9194f0e7fedc6c6a`: 69 Lem
types, 285 constructors and 8 records (`export2/schema.json` of the oracle). Cabs is
what `C_parser_driver.parse_from_string` returns: the parse tree of a translation unit
after the lexer hack, with locations, before any desugaring. The unreachable auxiliary
`cabs_base_type_specifier` is not ported.

The port follows `Silmaril.Cerberus.Names`: types are `UpperCamelCase`, constructors
and fields `lowerCamelCase`, a Lean keyword gets a trailing `_`, a single-constructor
type has the constructor `mk`, and Lem's `x_` shapes are `XNode`. Lem's
`cabs_` prefixes and C11 section names are dropped: `cabs_expression_` is
`ExpressionNode`. `Silmaril.Cerberus.Cabs.Names` maps every Lem name, and the Lem
names are the wire tags. Locations, identifiers and attributes are the Core port's
`Loc`, `Identifier` and `Attributes`. CN types take Lem's parameters `'a` (names)
and `'ty` (types) as `α` and `τ`; Cabs instantiates them with `Identifier` and
`TypeName`.

Argument order is Lem's. Most types are nested inductives (through `List`, `Option`
and products), so they derive nothing; compare them through their wire encoding.
-/

@[expose] public section

namespace Silmaril.Cerberus

/-! ## CN

CN specifications come from magic comments `/*@ … @*/`, which Cerberus parses only
with the switch `SW_at_magic_comments`, off by default. No corpus document contains
them; they are ported so that Cabs is complete. -/

namespace Cn

/-- The signedness of a CN bit-vector type. Lem: `Cn.sign`. -/
inductive Sign where
  | unsigned
  | signed

/-- CN base types. Lem: `Cn.cn_base_type`. -/
inductive BaseType (α : Type) where
  | unit
  | bool
  | integer
  /-- A bit-vector type. -/
  | bits (sign : Sign) (width : Int)
  | real
  /-- Pointers. -/
  | loc
  | allocId
  | struct (tag : α)
  | record (fields : List (Identifier × BaseType α))
  | datatype (name : α)
  | map (key : BaseType α) (value : BaseType α)
  | list (elem : BaseType α)
  | tuple (elems : List (BaseType α))
  | set (elem : BaseType α)
  | userTypeName (name : α)
  | cTypedefName (name : α)

/-- CN binary operators. Lem: `Cn.cn_binop`. -/
inductive Binop where
  | add
  | sub
  | mul
  | div
  | mod
  | equal
  | inequal
  | lt
  | le
  | gt
  | ge
  | or
  | and
  | implies
  | mapGet
  | band
  | bor
  | bxor

/-- What a C atom in a CN expression names. Lem: `Cn.cn_c_kind`. -/
inductive CKind where
  | var
  | enum

/-- CN constants. Lem: `Cn.cn_const`. -/
inductive Const where
  | null
  | integer (n : Int)
  /-- A bit-vector constant with its sign and width. -/
  | bits (type : Sign × Int) (n : Int)
  | bool (b : Bool)
  | unit

mutual

/-- The shape of a CN pattern. Lem: `Cn.cn_pat_`. -/
inductive PatNode (α : Type) where
  | sym (x : α)
  | wild
  | constructor (ctor : α) (args : List (Identifier × Pat α))

/-- A CN pattern and its location. Lem: `Cn.cn_pat`. -/
inductive Pat (α : Type) where
  | mk (loc : Loc) (node : PatNode α)

end

mutual

/-- The shape of a CN expression. Lem: `Cn.cn_expr_`. -/
inductive ExprNode (α τ : Type) where
  | const (c : Const)
  | var (x : α)
  | list (elems : List (Expr α τ))
  | memberof (e : Expr α τ) (member : Identifier)
  | arrow (e : Expr α τ) (member : Identifier)
  | record (fields : List (Identifier × Expr α τ))
  | struct (tag : α) (fields : List (Identifier × Expr α τ))
  | memberUpdates (e : Expr α τ) (updates : List (Identifier × Expr α τ))
  | arrayIndexUpdates (e : Expr α τ) (updates : List (Expr α τ × Expr α τ))
  | binop (op : Binop) (lhs : Expr α τ) (rhs : Expr α τ)
  | sizeof (type : τ)
  | offsetof (tag : α) (member : Identifier)
  | memberShift (e : Expr α τ) (type : Option τ) (member : Identifier)
  | addr (x : α)
  | cast (type : BaseType α) (e : Expr α τ)
  | arrayShift (base : Expr α τ) (type : Option τ) (index : Expr α τ)
  | call (function : α) (args : List (Expr α τ))
  | cons (ctor : α) (args : List (Identifier × Expr α τ))
  | each (x : α) (type : BaseType α) (range : Int × Int) (body : Expr α τ)
  | let_ (x : α) (value : Expr α τ) (body : Expr α τ)
  | match_ (scrutinee : Expr α τ) (cases : List (Pat α × Expr α τ))
  | ite (cond : Expr α τ) (then_ : Expr α τ) (else_ : Expr α τ)
  | good (type : τ) (e : Expr α τ)
  | deref (e : Expr α τ)
  | valueOfCAtom (x : α) (kind : CKind)
  | unchanged (e : Expr α τ)
  | atEnv (e : Expr α τ) (env : String)
  | not (e : Expr α τ)
  | negate (e : Expr α τ)
  | default (type : BaseType α)
  | bnot (e : Expr α τ)

/-- A CN expression and its location. Lem: `Cn.cn_expr`. -/
inductive Expr (α τ : Type) where
  | mk (loc : Loc) (node : ExprNode α τ)

end

/-- A CN resource predicate. Lem: `Cn.cn_pred`. -/
inductive Pred (α τ : Type) where
  | owned (type : Option τ)
  | block (type : Option τ)
  | named (name : α)

/-- A CN resource. Lem: `Cn.cn_resource`. -/
inductive Resource (α τ : Type) where
  | pred (loc : Loc) (pred : Pred α τ) (args : List (Expr α τ))
  | each (x : α) (type : BaseType α) (guard : Expr α τ) (loc : Loc) (pred : Pred α τ)
      (args : List (Expr α τ))

/-- A CN assertion. Lem: `Cn.cn_assertion`. -/
inductive Assertion (α τ : Type) where
  | expr (e : Expr α τ)
  | quantified (x : α) (type : BaseType α) (guard : Expr α τ) (body : Expr α τ)

/-- A CN pre- or postcondition item. Lem: `Cn.cn_condition`. -/
inductive Condition (α τ : Type) where
  | letResource (loc : Loc) (x : α) (resource : Resource α τ)
  | letExpr (loc : Loc) (x : α) (e : Expr α τ)
  | constraint (loc : Loc) (assertion : Assertion α τ)

/-- A clause of a CN predicate. Lem: `Cn.cn_clause`. -/
inductive Clause (α τ : Type) where
  | letResource (loc : Loc) (x : α) (resource : Resource α τ) (rest : Clause α τ)
  | letExpr (loc : Loc) (x : α) (e : Expr α τ) (rest : Clause α τ)
  | assert (loc : Loc) (assertion : Assertion α τ) (rest : Clause α τ)
  | return_ (loc : Loc) (e : Expr α τ)

/-- The clauses of a CN predicate. Lem: `Cn.cn_clauses`. -/
inductive Clauses (α τ : Type) where
  | clause (loc : Loc) (clause : Clause α τ)
  | if_ (loc : Loc) (cond : Expr α τ) (then_ : Clause α τ) (else_ : Clauses α τ)

/-- The accesses of a CN function specification. Lem: `Cn.cn_acc_func`. -/
inductive AccFunc (α : Type) where
  | accesses (xs : List α)
  | mkFunction (x : α)

/-- A CN function specification. Lem: `Cn.cn_func_spec`. -/
structure FuncSpec (α τ : Type) where
  trusted : Option Loc
  accFunc : Option (Loc × AccFunc α)
  requires : Option (Loc × (List (α × BaseType α) × List (Condition α τ)))
  ensures : Option (Loc × (List (α × BaseType α) × List (Condition α τ)))

/-- A CN specification of a C function declaration. Lem: `Cn.cn_decl_spec`. -/
structure DeclSpec (α τ : Type) where
  loc : Loc
  name : α
  args : List (α × BaseType α)
  funcSpec : FuncSpec α τ

/-- A CN function. Lem: `Cn.cn_function`. -/
structure Function (α τ : Type) where
  magicLoc : Loc
  loc : Loc
  name : α
  attrs : List Identifier
  args : List (α × BaseType α)
  body : Option (Expr α τ)
  returnType : BaseType α

/-- A CN lemma. Lem: `Cn.cn_lemma`. -/
structure Lemma (α τ : Type) where
  magicLoc : Loc
  loc : Loc
  name : α
  args : List (α × BaseType α)
  requires : List (Condition α τ)
  ensures : List (Condition α τ)

/-- A CN predicate. Lem: `Cn.cn_predicate`. -/
structure Predicate (α τ : Type) where
  magicLoc : Loc
  loc : Loc
  name : α
  attrs : List Identifier
  output : Loc × BaseType α
  iargs : List (α × BaseType α)
  clauses : Option (Clauses α τ)

/-- A CN datatype. Lem: `Cn.cn_datatype`. -/
structure Datatype (α : Type) where
  magicLoc : Loc
  loc : Loc
  name : α
  cases : List (α × List (Identifier × BaseType α))

/-- A CN type synonym. Lem: `Cn.cn_type_synonym`. -/
structure TypeSynonym (α : Type) where
  magicLoc : Loc
  loc : Loc
  name : α
  rhs : BaseType α

end Cn

/-! ## Cabs -/

namespace Cabs

/-- An integer-constant suffix (STD §6.4.4.1). The lexer accepts `U`, `UL`, `ULL`, `L` and `LL` in
either case, but not mixed-case `lL` (`c_lexer.mll:531-552`). Lem: `Cabs.cabs_integer_suffix`. -/
inductive IntegerSuffix where
  /-- `u` or `U`. -/
  | u
  /-- `ul` and its spellings. -/
  | ul
  /-- `ull` and its spellings. -/
  | ull
  /-- `l` or `L`. -/
  | l
  /-- `ll` or `LL`. -/
  | ll

/-- An integer constant as written: the digits with their base prefix (`0x1F`, `017`, `0b101`),
without the suffix, and the suffix. The value is decoded only by `Cabs_to_ail`. Lem:
`Cabs.cabs_integer_constant`. -/
abbrev IntegerConstant := String × Option IntegerSuffix

/-- A floating-constant suffix (STD §6.4.4.2). Lem: `Cabs.cabs_floating_suffix`. -/
inductive FloatingSuffix where
  /-- `f` or `F`: `float`. -/
  | f
  /-- `l` or `L`: `long double`. -/
  | l

/-- A floating constant as written, without its suffix, and the suffix. Lem:
`Cabs.cabs_floating_constant`. -/
abbrev FloatingConstant := String × Option FloatingSuffix

/-- The prefix of a character constant (STD §6.4.4.4). Lem: `Cabs.cabs_character_prefix`. -/
inductive CharacterPrefix where
  /-- `L'…'`: `wchar_t`. -/
  | wide
  /-- `u'…'`: `char16_t`. -/
  | utf16
  /-- `U'…'`: `char32_t`. -/
  | utf32

/-- A character constant: its prefix and the raw text between the quotes, escapes undecoded
(`c_lexer.mll:562-569`). Lem: `Cabs.cabs_character_constant`. -/
abbrev CharacterConstant := Option CharacterPrefix × String

/-- A constant (STD §6.4.4). Enumeration constants are identifiers, not constants. Lem:
`Cabs.cabs_constant`. -/
inductive Constant where
  /-- An integer constant. -/
  | integer (c : IntegerConstant)
  /-- A floating constant. -/
  | floating (c : FloatingConstant)
  /-- A character constant. -/
  | character (c : CharacterConstant)

/-- The encoding prefix of a string literal (STD §6.4.5). Lem: `Cabs.cabs_encoding_prefix`. -/
inductive EncodingPrefix where
  /-- `u8"…"`. -/
  | utf8
  /-- `u"…"`. -/
  | utf16
  /-- `U"…"`. -/
  | utf32
  /-- `L"…"`. -/
  | wide

/-- A Lem `string` in a position where Cerberus keeps raw bytes: the s-char lexemes of
string literals and `asm` templates. Lem strings are OCaml byte strings, and a lexeme
of a non-ASCII character is one byte, so it need not be valid UTF-8. Valid UTF-8 is
`utf8` and prints as `($str "…")`; anything else is `bytes` and prints as
`($bytes "<lowercase hex>")`, the dialect extension of the Silmaril exporter. -/
inductive RawString where
  | utf8 (text : String)
  | bytes (data : ByteArray)

/-- A string literal after concatenation (STD §6.4.5, `c_parser.mly:1753-1773`): the first explicit
prefix, and one entry per adjacent literal with its region and its *s-char lexemes*. A lexeme is
one byte or one undecoded escape sequence (`\n`, `\x41`, `\123`), so non-ASCII text arrives one
byte at a time. Lem: `Cabs.cabs_string_literal`. -/
abbrev StringLiteral := Option EncodingPrefix × List (Loc × List RawString)

/-- The unary operators of `ExpressionNode.unary` (STD §6.5.3). Lem: `Cabs.cabs_unary_operator`. -/
inductive UnaryOperator where
  /-- `&`. -/
  | address
  /-- `*`. -/
  | indirection
  /-- Unary `+`. -/
  | plus
  /-- Unary `-`. -/
  | minus
  /-- `~`. -/
  | bnot
  /-- `!`. -/
  | not

/-- The binary operators (STD §6.5.5-14). Lem: `Cabs.cabs_binary_operator`. -/
inductive BinaryOperator where
  /-- `*`. -/
  | mul
  /-- `/`. -/
  | div
  /-- `%`. -/
  | mod
  /-- `+`. -/
  | add
  /-- `-`. -/
  | sub
  /-- `<<`. -/
  | shl
  /-- `>>`. -/
  | shr
  /-- `<`. -/
  | lt
  /-- `>`. -/
  | gt
  /-- `<=`. -/
  | le
  /-- `>=`. -/
  | ge
  /-- `==`. -/
  | eq
  /-- `!=`. -/
  | ne
  /-- `&`. -/
  | band
  /-- `^`. -/
  | bxor
  /-- `|`. -/
  | bor
  /-- `&&`. -/
  | and
  /-- `||`. -/
  | or

/-- The assignment operators (STD §6.5.16). Lem: `Cabs.cabs_assignment_operator`. -/
inductive AssignmentOperator where
  /-- `=`. -/
  | assign
  /-- `*=`. -/
  | mul
  /-- `/=`. -/
  | div
  /-- `%=`. -/
  | mod
  /-- `+=`. -/
  | add
  /-- `-=`. -/
  | sub
  /-- `<<=`. -/
  | shl
  /-- `>>=`. -/
  | shr
  /-- `&=`. -/
  | band
  /-- `^=`. -/
  | bxor
  /-- `|=`. -/
  | bor

/-- A storage-class specifier (STD §6.7.1). Lem: `Cabs.storage_class_specifier`. -/
inductive StorageClassSpecifier where
  /-- `typedef`. -/
  | typedef
  /-- `extern`. -/
  | extern
  /-- `static`. -/
  | static
  /-- `_Thread_local`. -/
  | threadLocal
  /-- `auto`. -/
  | auto
  /-- `register`. -/
  | register

/-- A type qualifier (STD §6.7.3). Lem: `Cabs.cabs_type_qualifier`. -/
inductive TypeQualifier where
  /-- `const`. -/
  | const
  /-- `restrict`. -/
  | restrict
  /-- `volatile`. -/
  | volatile
  /-- The qualifier `_Atomic`. -/
  | atomic

/-- A function specifier (STD §6.7.4). Lem: `Cabs.function_specifier`. -/
inductive FunctionSpecifier where
  /-- `inline`. -/
  | inline
  /-- `_Noreturn`. -/
  | noreturn

mutual

/-- The shape of an expression (STD §6.5), without its location. Lem: `Cabs.cabs_expression_`. -/
inductive ExpressionNode where
  /-- An identifier; its location is a point at its start (`c_parser.mly:495-497`). -/
  | ident (x : Identifier)
  /-- A constant. -/
  | const (c : Constant)
  /-- A string literal. -/
  | string (s : StringLiteral)
  /-- `_Generic(e, assocs)` (STD §6.5.1.1). -/
  | generic (controlling : Expression) (associations : List GenericAssociation)
  /-- `e1[e2]`. -/
  | subscript (array : Expression) (index : Expression)
  /-- A call `f(args)`. The attributes are produced only for CN magic comments. -/
  | call (function : Expression) (args : List Expression) (attrs : Option Attributes)
  /-- `e.member`. -/
  | memberof (e : Expression) (member : Identifier)
  /-- `e->member`. -/
  | memberofptr (e : Expression) (member : Identifier)
  /-- `e++`. -/
  | postincr (e : Expression)
  /-- `e--`. -/
  | postdecr (e : Expression)
  /-- A compound literal `(type){inits}` (STD §6.5.2.5). -/
  | compound (type : TypeName) (inits : List (Option (List Designator) × Initializer))
  /-- `++e`. -/
  | preincr (e : Expression)
  /-- `--e`. -/
  | predecr (e : Expression)
  /-- A unary operator other than `++`, `--`, `sizeof` and `_Alignof`. -/
  | unary (op : UnaryOperator) (e : Expression)
  /-- `sizeof e`. -/
  | sizeofExpr (e : Expression)
  /-- `sizeof(type)`. -/
  | sizeofType (type : TypeName)
  /-- `_Alignof(type)`. -/
  | alignof (type : TypeName)
  /-- `(type) e`. -/
  | cast (type : TypeName) (e : Expression)
  /-- A binary operator (STD §6.5.5-14). -/
  | binary (op : BinaryOperator) (lhs : Expression) (rhs : Expression)
  /-- `c ? a : b`. -/
  | cond (cond : Expression) (then_ : Expression) (else_ : Expression)
  /-- An assignment `lhs op= rhs` (STD §6.5.16). -/
  | assign (op : AssignmentOperator) (lhs : Expression) (rhs : Expression)
  /-- `e1, e2`. -/
  | comma (lhs : Expression) (rhs : Expression)
  /-- `assert(e)`: `assert` is a keyword in Cerberus. -/
  | assert (e : Expression)
  /-- `offsetof(type, member)`: `offsetof` is a keyword in Cerberus. -/
  | offsetof (type : TypeName) (member : Identifier)
  /-- `__cerb_va_start(ap, param)`. -/
  | vaStart (list : Expression) (param : Identifier)
  /-- `__cerb_va_copy(dst, src)`. -/
  | vaCopy (dst : Expression) (src : Expression)
  /-- `__cerb_va_arg(ap, type)`. -/
  | vaArg (list : Expression) (type : TypeName)
  /-- `__cerb_va_end(ap)`. -/
  | vaEnd (list : Expression)
  /-- `__cerb_printtype(e)` (Cerberus extension). -/
  | printType (e : Expression)
  /-- `__BMC_ASSUME(e)` (Cerberus-BMC extension). -/
  | bmcAssume (e : Expression)
  /-- GNU labels as values: `&&label`. -/
  | labelAddressGnu (label : Identifier)
  /-- A GNU statement expression `({ … })`. -/
  | gccStatement (body : List Statement)
  /-- The GNU conditional `c ?: b`; the lexer accepts `?:` only as one token. -/
  | condGnu (cond : Expression) (else_ : Expression)
  /-- A GNU builtin with a special syntax. -/
  | builtinGnu (builtin : GnuBuiltinFunction)

/-- The GNU builtins that take type names, so they are keywords. Lem:
`Cabs.gnu_builtin_function`. -/
inductive GnuBuiltinFunction where
  /-- `__builtin_types_compatible_p(t1, t2)`. -/
  | typesCompatibleP (t1 : TypeName) (t2 : TypeName)
  /-- `__builtin_choose_expr(c, a, b)`. -/
  | chooseExpr (cond : Expression) (then_ : Expression) (else_ : Expression)

/-- An expression and its location. Lem: `Cabs.cabs_expression`. -/
inductive Expression where
  /-- The location is the region of the whole expression; operators put a point cursor on the
    operator, which the wire format drops. -/
  | mk (loc : Loc) (node : ExpressionNode)

/-- A generic association of `_Generic` (STD §6.5.1.1). Lem: `Cabs.cabs_generic_association`. -/
inductive GenericAssociation where
  /-- `type: e`. -/
  | type_ (type : TypeName) (e : Expression)
  /-- `default: e`. -/
  | default (e : Expression)

/-- A declaration (STD §6.7). Lem: `Cabs.cabs_declaration`. -/
inductive Declaration where
  /-- Leading attributes, the specifiers and the init-declarators. The attribute declaration
    `[[…]];` becomes a dummy declaration of an identifier `test` (`c_parser.mly:850-856`). -/
  | base (attrs : Attributes) (specifiers : Specifiers) (declarators : List InitDeclarator)
  /-- `_Static_assert(e, "msg");`. -/
  | staticAssert (assertion : StaticAssertDeclaration)

/-- The declaration specifiers, sorted by kind: storage classes (`typedef` among them), type
specifiers as written (`long long` is two), type qualifiers, function specifiers and alignment
specifiers. Each list keeps the order that `concat_specs` builds
(`c_parser.mly:29-51`). Lem: `Cabs.specifiers`. -/
inductive Specifiers where
  | mk (storageClasses : List StorageClassSpecifier) (typeSpecifiers : List TypeSpecifier)
      (typeQualifiers : List TypeQualifier) (functionSpecifiers : List FunctionSpecifier)
      (alignmentSpecifiers : List AlignmentSpecifier)

/-- A declarator with its optional initializer. Lem: `Cabs.init_declarator`. -/
inductive InitDeclarator where
  /-- The region covers the declarator, any `asm` label and the initializer. -/
  | mk (loc : Loc) (declarator : Declarator) (init : Option Initializer)

/-- The shape of a type specifier (STD §6.7.2), without its location. Lem:
`Cabs.cabs_type_specifier_`. -/
inductive TypeSpecifierNode where
  /-- `void`. -/
  | void
  /-- `char`. -/
  | char
  /-- `short`. -/
  | short
  /-- `int`. -/
  | int
  /-- `long`. -/
  | long
  /-- `float`. -/
  | float
  /-- `double`. -/
  | double
  /-- `signed`. -/
  | signed
  /-- `unsigned`. -/
  | unsigned
  /-- `_Bool`. -/
  | bool
  /-- `_Complex` (parsed; rejected by the desugaring). -/
  | complex
  /-- The atomic type specifier `_Atomic(type)` (STD §6.7.2.4). -/
  | atomic (type : TypeName)
  /-- `struct tag { members }`; `none` members for a forward reference. An empty member list is the
    GNU empty struct. -/
  | struct (attrs : Attributes) (tag : Option Identifier)
      (members : Option (List StructDeclaration))
  /-- `union tag { members }`. -/
  | union (attrs : Attributes) (tag : Option Identifier) (members : Option (List StructDeclaration))
  /-- `enum tag { enumerators }`; the attributes of an enum are discarded by the parser. -/
  | enum (tag : Option Identifier) (enumerators : Option (List (Identifier × Option Expression)))
  /-- A typedef name; its identifier is a point (`c_parser.mly:455-459`). -/
  | name (name : Identifier)
  /-- GNU `typeof(e)`. -/
  | typeofExpr (e : Expression)
  /-- GNU `typeof(type)`. -/
  | typeofType (type : TypeName)

/-- A type specifier and its location. Lem: `Cabs.cabs_type_specifier`. -/
inductive TypeSpecifier where
  /-- A `struct` or `union` region runs to the end of the whole specifier
    (`c_parser.mly:971-992`). -/
  | mk (loc : Loc) (node : TypeSpecifierNode)

/-- A member declaration of a struct or union (STD §6.7.2.1). Lem: `Cabs.struct_declaration`. -/
inductive StructDeclaration where
  /-- Attributes, the specifier-qualifier list split by kind, and the member declarators. -/
  | member (attrs : Attributes) (typeSpecifiers : List TypeSpecifier)
      (typeQualifiers : List TypeQualifier) (alignmentSpecifiers : List AlignmentSpecifier)
      (declarators : List StructDeclarator)
  /-- A `_Static_assert` among the members. -/
  | staticAssert (assertion : StaticAssertDeclaration)

/-- A member declarator. Lem: `Cabs.struct_declarator`. -/
inductive StructDeclarator where
  /-- A plain member. -/
  | simple (declarator : Declarator)
  /-- A bit-field member; unnamed when the declarator is `none`. -/
  | bitfield (declarator : Option Declarator) (width : Expression)

/-- An alignment specifier (STD §6.7.5). Lem: `Cabs.alignment_specifier`. -/
inductive AlignmentSpecifier where
  /-- `_Alignas(type)`. -/
  | type_ (type : TypeName)
  /-- `_Alignas(e)`. -/
  | expr (e : Expression)

/-- A declarator (STD §6.7.6): its pointer part and its direct declarator. Lem:
`Cabs.declarator`. -/
inductive Declarator where
  /-- The pointer part is `none` without a leading `*`. -/
  | mk (pointer : Option PointerDeclarator) (direct : DirectDeclarator)

/-- A direct declarator (STD §6.7.6). Lem: `Cabs.direct_declarator`. -/
inductive DirectDeclarator where
  /-- The declared identifier and its attributes; the identifier is a region
    (`general_identifier`). -/
  | identifier (attrs : Attributes) (name : Identifier)
  /-- A parenthesized declarator. -/
  | declarator (inner : Declarator)
  /-- An array declarator. -/
  | array (inner : DirectDeclarator) (array : ArrayDeclarator)
  /-- A function declarator. A K&R identifier list in a declaration that is not a definition becomes
    an empty parameter list (`lexer_feedback.ml:117-120`). -/
  | function (inner : DirectDeclarator) (params : ParameterTypeList)

/-- The bracket part of an array declarator. Lem: `Cabs.array_declarator`. -/
inductive ArrayDeclarator where
  /-- The region starts at the direct declarator, identifier included (`c_parser.mly:1130-1150`);
    abstract array declarators have an unknown location. `isStatic` records the `static` keyword. -/
  | mk (loc : Loc) (qualifiers : List TypeQualifier) (isStatic : Bool)
      (size : Option ArrayDeclaratorSize)

/-- The size of an array declarator. Lem: `Cabs.array_declarator_size`. -/
inductive ArrayDeclaratorSize where
  /-- An expression. -/
  | expression (e : Expression)
  /-- `[*]`, a VLA of unspecified size. -/
  | asterisk

/-- A pointer declarator `* qualifiers` and the pointers it points through. Lem:
`Cabs.pointer_declarator`. -/
inductive PointerDeclarator where
  /-- The region runs from the `*` through the nested pointers. -/
  | mk (loc : Loc) (qualifiers : List TypeQualifier) (next : Option PointerDeclarator)

/-- A parameter type list (STD §6.7.6). Lem: `Cabs.parameter_type_list`. -/
inductive ParameterTypeList where
  /-- The parameters, and whether they end in `, ...`. -/
  | mk (params : List ParameterDeclaration) (variadic : Bool)

/-- A parameter declaration. Lem: `Cabs.parameter_declaration`. -/
inductive ParameterDeclaration where
  /-- A named parameter. -/
  | declarator (specifiers : Specifiers) (declarator : Declarator)
  /-- An unnamed parameter, with an optional abstract declarator. -/
  | abstract (specifiers : Specifiers) (declarator : Option AbstractDeclarator)

/-- A type name (STD §6.7.7). Lem: `Cabs.type_name`. -/
inductive TypeName where
  /-- The specifier-qualifier list split by kind, and the abstract declarator. -/
  | mk (typeSpecifiers : List TypeSpecifier) (typeQualifiers : List TypeQualifier)
      (alignmentSpecifiers : List AlignmentSpecifier) (declarator : Option AbstractDeclarator)

/-- An abstract declarator (STD §6.7.7). Lem: `Cabs.abstract_declarator`. -/
inductive AbstractDeclarator where
  /-- Pointers only. -/
  | pointer (pointer : PointerDeclarator)
  /-- Optional pointers and a direct abstract declarator. -/
  | direct (pointer : Option PointerDeclarator) (direct : DirectAbstractDeclarator)

/-- A direct abstract declarator. Lem: `Cabs.direct_abstract_declarator`. -/
inductive DirectAbstractDeclarator where
  /-- A parenthesized abstract declarator. -/
  | abstract (inner : AbstractDeclarator)
  /-- An array. -/
  | array (inner : Option DirectAbstractDeclarator) (array : ArrayDeclarator)
  /-- A function. -/
  | function (inner : Option DirectAbstractDeclarator) (params : ParameterTypeList)

/-- An initializer (STD §6.7.9). Lem: `Cabs.initializer_`. -/
inductive Initializer where
  /-- An assignment expression. -/
  | expr (e : Expression)
  /-- A braced list; the region includes the braces. Each item has an optional designation. -/
  | list (loc : Loc) (inits : List (Option (List Designator) × Initializer))

/-- A designator (STD §6.7.9). Lem: `Cabs.designator`. -/
inductive Designator where
  /-- `[e]`. -/
  | array (index : Expression)
  /-- `.member`. -/
  | member (member : Identifier)

/-- A static assertion (STD §6.7.10); the message is required. Lem:
`Cabs.static_assert_declaration`. -/
inductive StaticAssertDeclaration where
  /-- `_Static_assert(cond, message)`. -/
  | mk (cond : Expression) (message : StringLiteral)

/-- The shape of a statement (STD §6.8), without its location and attributes. Lem:
`Cabs.cabs_statement_`. -/
inductive StatementNode where
  /-- `label: s`; the region starts at the identifier. -/
  | label (label : Identifier) (s : Statement)
  /-- `case e: s`; the region starts at `case`. -/
  | case_ (e : Expression) (s : Statement)
  /-- `default: s`. -/
  | default (s : Statement)
  /-- A compound statement `{ items }`. -/
  | block (items : List Statement)
  /-- A declaration as a block item. -/
  | decl (d : Declaration)
  /-- The null statement `;`. Its region starts at the end of the previous token (Menhir's rule for
    a production that starts with an empty symbol). -/
  | null
  /-- An expression statement. -/
  | expr (e : Expression)
  /-- `if (cond) s1 else s2`; a dangling `else` binds to the nearest `if`. -/
  | if_ (cond : Expression) (then_ : Statement) (else_ : Option Statement)
  /-- `switch (e) s`. -/
  | switch (e : Expression) (s : Statement)
  /-- `while (cond) body`. -/
  | while_ (cond : Expression) (body : Statement)
  /-- `do body while (cond);`: the condition comes first. -/
  | do_ (cond : Expression) (body : Statement)
  /-- `for (init; cond; step) body`. -/
  | for_ (init : Option ForClause) (cond : Option Expression) (step : Option Expression)
      (body : Statement)
  /-- `goto label;`. -/
  | goto (label : Identifier)
  /-- `continue;`. -/
  | continue_
  /-- `break;`. -/
  | break_
  /-- `return e;`. -/
  | return_ (e : Option Expression)
  /-- The cppmem parallel composition `{-{ s1 ||| s2 }-}` (non-standard). -/
  | par (threads : List Statement)
  /-- GNU inline assembly: only the qualifiers and the template string are kept
    (`c_parser.mly:1472-1552`). -/
  | asm (isVolatile : Bool) (isInline : Bool) (templates : List (Loc × List RawString))
  /-- The GNU case range `case lo ... hi: s`. -/
  | caseRangeGnu (lo : Expression) (hi : Expression) (s : Statement)
  /-- A CN magic-comment marker; produced only with magic comments on. -/
  | marker (s : Statement)

/-- A statement, its location and its attributes. Lem: `Cabs.cabs_statement`. -/
inductive Statement where
  /-- Statement attributes are appended to the inner statement and do not widen its location
    (`c_parser.mly:68-70`). -/
  | mk (loc : Loc) (attrs : Attributes) (node : StatementNode)

/-- The first clause of a `for` statement. Lem: `Cabs.for_clause`. -/
inductive ForClause where
  /-- An expression. -/
  | expr (e : Expression)
  /-- A declaration; the region includes its `;`. -/
  | decl (loc : Loc) (d : Declaration)

end

/-- A function definition (STD §6.9.1). Lem: `Cabs.function_definition`. -/
structure FunctionDefinition where
  /-- From the leading `[[attributes]]` through the closing brace, and a stray `;` after it. -/
  loc : Loc
  /-- The attribute groups, in reverse order (`lexer_feedback.ml:132-137`). -/
  attrs : Attributes
  specifiers : Specifiers
  /-- K&R parameters without declarations are `int` parameters here. -/
  declarator : Declarator
  /-- The compound statement. -/
  body : Statement

/-- An external declaration (STD §6.9). The CN forms come only from magic comments, which are off by
default. Lem: `Cabs.external_declaration`. -/
inductive ExternalDeclaration where
  /-- A function definition. -/
  | func (f : FunctionDefinition)
  /-- A declaration. -/
  | decl (d : Declaration)
  /-- A top-level magic comment, before it is re-parsed. -/
  | magic (comment : Loc × String)
  /-- A CN function. -/
  | funcCn (f : Cn.Function Identifier TypeName)
  /-- A CN lemma. -/
  | lemmaCn (l : Cn.Lemma Identifier TypeName)
  /-- A CN predicate. -/
  | predCn (p : Cn.Predicate Identifier TypeName)
  /-- A CN datatype. -/
  | datatypeCn (d : Cn.Datatype Identifier)
  /-- A CN type synonym. -/
  | typeSynCn (t : Cn.TypeSynonym Identifier)
  /-- A CN function specification. -/
  | funSpecCn (s : Cn.DeclSpec Identifier TypeName)

/-- A translation unit (STD §6.9): the external declarations in source order, including the ten
`[[cerb::hidden]]` prototypes of `builtins.h`. Lem: `Cabs.translation_unit`. -/
structure TranslationUnit where
  declarations : List ExternalDeclaration

end Cabs

end Silmaril.Cerberus
