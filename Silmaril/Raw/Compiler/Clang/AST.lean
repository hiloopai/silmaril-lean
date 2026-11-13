module

public import Lean.Data.Json.Basic

/-! # A Lean model of Clang's JSON AST (the C subset)

The input of the Clang frontend is the output of

```
clang -x c -std=gnu11 -nostdinc -include cerb-prelude.h -Xclang -ast-dump=json -fsyntax-only X.i
```

with the clang pinned by the campaign (23.1.0, `ea7d852a`, sha256 recorded in the evaluator's
`tools/clang/SHA256SUMS`). Clang's `JSONNodeDumper` prints every node as one JSON object with an
`id`, a `kind` and the attributes of that kind; children are in `inner`. This file models that
output **exactly**: `Silmaril.Clang.Json` decodes a document into `Node` and encodes it back to
the same JSON value (up to key order), so the round trip checks the model on the whole corpus.

## Representation

* `Kind` is the closed list of node kinds the C subset uses (declarations, types, attributes,
  statements, expressions). An unknown kind is a decoding error, never a guess (fail-closed).
* `Node` is one header (`Header`: the attributes, each an `Option` because Clang prints most of
  them only when they hold) and the child arrays `inner` and `array_filler`. Every key that Clang
  prints for a kind of the subset has a field; an unknown key is a decoding error too.
* Types are kept as Clang prints them: `QualType` holds the `qualType` string, the
  `desugaredQualType` string when the type is sugared, and the `typeAliasDeclId` of a typedef.
  Type nodes (`BuiltinType`, `PointerType`, …) appear only as children of `TypedefDecl` and of
  other type nodes. Parsing the type strings into C types is the translation's job
  (`Silmaril.Clang.ToAil`).
* Source locations (`Loc`) follow Clang's delta encoding: a field is printed only when it differs
  from the previously printed location, so every field is optional; a location inside a macro
  expansion has a spelling and an expansion location.
* A `FullComment` and its entire subtree are opaque `Node.comment` values. Documentation has
  no C semantics; its raw JSON is preserved exactly and excluded from semantic child traversal.
* The associations of a `GenericSelectionExpr` have no `id` or `kind`: they are
  `Node.association` values, with their children.

Implicit conversions are explicit in Clang's AST (`ImplicitCastExpr` with its `castKind`): the
translation turns them into Ail conversions and never re-derives them.
-/

@[expose] public section

namespace Silmaril.Clang

/-- One source location as Clang prints it (all fields optional: delta encoding). -/
structure BareLoc where
  offset : Option Nat := none
  file : Option String := none
  line : Option Nat := none
  presumedFile : Option String := none
  presumedLine : Option Nat := none
  col : Option Nat := none
  tokLen : Option Nat := none
  /-- `"includedFrom": {"file": …}`. -/
  includedFrom : Option String := none
  isMacroArgExpansion : Option Bool := none
  deriving Repr, BEq, Inhabited

/-- A location: plain, or inside a macro expansion (`spellingLoc` / `expansionLoc`). -/
inductive Loc where
  | bare (l : BareLoc)
  | macro (spelling expansion : BareLoc)
  deriving Repr, BEq, Inhabited

/-- A source range (`begin`, `end`). -/
structure Range where
  begin : Loc
  «end» : Loc
  deriving Repr, BEq, Inhabited

/-- A type as Clang prints it: the spelling, the desugared spelling when it differs, and the id of
the typedef it names. -/
structure QualType where
  qualType : String
  desugaredQualType : Option String := none
  typeAliasDeclId : Option String := none
  deriving Repr, BEq, Inhabited

/-- The node kinds of the C subset. Unknown kinds are rejected by the decoder. -/
inductive Kind where
  -- declarations
  | translationUnitDecl | typedefDecl | recordDecl | fieldDecl | enumDecl | enumConstantDecl
  | functionDecl | parmVarDecl | varDecl | labelDecl | indirectFieldDecl | staticAssertDecl
  | fileScopeAsmDecl
  | emptyDecl
  -- types (children of TypedefDecl and of other types)
  | builtinType | pointerType | constantArrayType | incompleteArrayType | variableArrayType
  | recordType | enumType | typedefType | elaboratedType | parenType | functionProtoType
  | functionNoProtoType | qualType | decayedType | atomicType | complexType | vectorType
  -- attributes
  | builtinAttr | noThrowAttr | constAttr | pureAttr | formatAttr | allocSizeAttr | allocAlignAttr
  | alignedAttr | c11NoReturnAttr | availableOnlyInDefaultEvalMethodAttr | noInlineAttr
  | alwaysInlineAttr | unusedAttr | usedAttr | packedAttr | sectionAttr | weakAttr | aliasAttr
  | asmLabelAttr | returnsTwiceAttr | warnUnusedResultAttr | nonNullAttr | restrictAttr
  | modeAttr | transparentUnionAttr | constructorAttr | destructorAttr | cleanupAttr
  | visibilityAttr | gnuInlineAttr | coldAttr | hotAttr | noReturnAttr | deprecatedAttr
  | fallThroughAttr | noSanitizeAttr | maxFieldAlignmentAttr | mayAliasAttr | leafAttr
  -- statements
  | compoundStmt | declStmt | nullStmt | returnStmt | ifStmt | whileStmt | doStmt | forStmt
  | switchStmt | caseStmt | defaultStmt | breakStmt | continueStmt | gotoStmt | labelStmt
  | indirectGotoStmt | attributedStmt | gccAsmStmt
  -- expressions
  | implicitCastExpr | cStyleCastExpr | parenExpr | declRefExpr | binaryOperator
  | compoundAssignOperator | unaryOperator | conditionalOperator | binaryConditionalOperator
  | opaqueValueExpr | integerLiteral | characterLiteral | floatingLiteral | stringLiteral
  | callExpr | arraySubscriptExpr | memberExpr | initListExpr | implicitValueInitExpr
  | compoundLiteralExpr | unaryExprOrTypeTraitExpr | constantExpr | stmtExpr | vaArgExpr
  | predefinedExpr | offsetOfExpr | genericSelectionExpr | addrLabelExpr | atomicExpr
  | materializeTemporaryExpr | exprWithCleanups | designatedInitExpr | parenListExpr
  | chooseExpr | builtinBitCastExpr | imaginaryLiteral | recoveryExpr
  deriving DecidableEq, Repr, Inhabited

namespace Kind

/-- Every kind with its spelling in Clang's JSON. -/
def table : List (Kind × String) := [
  (.translationUnitDecl, "TranslationUnitDecl"), (.typedefDecl, "TypedefDecl"),
  (.recordDecl, "RecordDecl"), (.fieldDecl, "FieldDecl"), (.enumDecl, "EnumDecl"),
  (.enumConstantDecl, "EnumConstantDecl"), (.functionDecl, "FunctionDecl"),
  (.parmVarDecl, "ParmVarDecl"), (.varDecl, "VarDecl"), (.labelDecl, "LabelDecl"),
  (.indirectFieldDecl, "IndirectFieldDecl"), (.staticAssertDecl, "StaticAssertDecl"),
  (.fileScopeAsmDecl, "FileScopeAsmDecl"),
  (.emptyDecl, "EmptyDecl"),
  (.builtinType, "BuiltinType"), (.pointerType, "PointerType"),
  (.constantArrayType, "ConstantArrayType"), (.incompleteArrayType, "IncompleteArrayType"),
  (.variableArrayType, "VariableArrayType"), (.recordType, "RecordType"),
  (.enumType, "EnumType"), (.typedefType, "TypedefType"), (.elaboratedType, "ElaboratedType"),
  (.parenType, "ParenType"), (.functionProtoType, "FunctionProtoType"),
  (.functionNoProtoType, "FunctionNoProtoType"), (.qualType, "QualType"),
  (.decayedType, "DecayedType"), (.atomicType, "AtomicType"), (.complexType, "ComplexType"),
  (.vectorType, "VectorType"),
  (.builtinAttr, "BuiltinAttr"), (.noThrowAttr, "NoThrowAttr"), (.constAttr, "ConstAttr"),
  (.pureAttr, "PureAttr"), (.formatAttr, "FormatAttr"), (.allocSizeAttr, "AllocSizeAttr"),
  (.allocAlignAttr, "AllocAlignAttr"), (.alignedAttr, "AlignedAttr"),
  (.c11NoReturnAttr, "C11NoReturnAttr"),
  (.availableOnlyInDefaultEvalMethodAttr, "AvailableOnlyInDefaultEvalMethodAttr"),
  (.noInlineAttr, "NoInlineAttr"), (.alwaysInlineAttr, "AlwaysInlineAttr"),
  (.unusedAttr, "UnusedAttr"), (.usedAttr, "UsedAttr"), (.packedAttr, "PackedAttr"),
  (.sectionAttr, "SectionAttr"), (.weakAttr, "WeakAttr"), (.aliasAttr, "AliasAttr"),
  (.asmLabelAttr, "AsmLabelAttr"), (.returnsTwiceAttr, "ReturnsTwiceAttr"),
  (.warnUnusedResultAttr, "WarnUnusedResultAttr"), (.nonNullAttr, "NonNullAttr"),
  (.restrictAttr, "RestrictAttr"), (.modeAttr, "ModeAttr"),
  (.transparentUnionAttr, "TransparentUnionAttr"), (.constructorAttr, "ConstructorAttr"),
  (.destructorAttr, "DestructorAttr"), (.cleanupAttr, "CleanupAttr"),
  (.visibilityAttr, "VisibilityAttr"), (.gnuInlineAttr, "GNUInlineAttr"),
  (.coldAttr, "ColdAttr"), (.hotAttr, "HotAttr"), (.noReturnAttr, "NoReturnAttr"),
  (.deprecatedAttr, "DeprecatedAttr"),
  (.fallThroughAttr, "FallThroughAttr"), (.noSanitizeAttr, "NoSanitizeAttr"),
  (.mayAliasAttr, "MayAliasAttr"),
  (.leafAttr, "LeafAttr"),
  (.maxFieldAlignmentAttr, "MaxFieldAlignmentAttr"),
  (.compoundStmt, "CompoundStmt"), (.declStmt, "DeclStmt"), (.nullStmt, "NullStmt"),
  (.returnStmt, "ReturnStmt"), (.ifStmt, "IfStmt"), (.whileStmt, "WhileStmt"),
  (.doStmt, "DoStmt"), (.forStmt, "ForStmt"), (.switchStmt, "SwitchStmt"),
  (.caseStmt, "CaseStmt"), (.defaultStmt, "DefaultStmt"), (.breakStmt, "BreakStmt"),
  (.continueStmt, "ContinueStmt"), (.gotoStmt, "GotoStmt"), (.labelStmt, "LabelStmt"),
  (.indirectGotoStmt, "IndirectGotoStmt"), (.attributedStmt, "AttributedStmt"),
  (.gccAsmStmt, "GCCAsmStmt"),
  (.implicitCastExpr, "ImplicitCastExpr"), (.cStyleCastExpr, "CStyleCastExpr"),
  (.parenExpr, "ParenExpr"), (.declRefExpr, "DeclRefExpr"), (.binaryOperator, "BinaryOperator"),
  (.compoundAssignOperator, "CompoundAssignOperator"), (.unaryOperator, "UnaryOperator"),
  (.conditionalOperator, "ConditionalOperator"),
  (.binaryConditionalOperator, "BinaryConditionalOperator"),
  (.opaqueValueExpr, "OpaqueValueExpr"), (.integerLiteral, "IntegerLiteral"),
  (.characterLiteral, "CharacterLiteral"), (.floatingLiteral, "FloatingLiteral"),
  (.stringLiteral, "StringLiteral"), (.callExpr, "CallExpr"),
  (.arraySubscriptExpr, "ArraySubscriptExpr"), (.memberExpr, "MemberExpr"),
  (.initListExpr, "InitListExpr"), (.implicitValueInitExpr, "ImplicitValueInitExpr"),
  (.compoundLiteralExpr, "CompoundLiteralExpr"),
  (.unaryExprOrTypeTraitExpr, "UnaryExprOrTypeTraitExpr"), (.constantExpr, "ConstantExpr"),
  (.stmtExpr, "StmtExpr"), (.vaArgExpr, "VAArgExpr"), (.predefinedExpr, "PredefinedExpr"),
  (.offsetOfExpr, "OffsetOfExpr"), (.genericSelectionExpr, "GenericSelectionExpr"),
  (.addrLabelExpr, "AddrLabelExpr"), (.atomicExpr, "AtomicExpr"),
  (.materializeTemporaryExpr, "MaterializeTemporaryExpr"),
  (.exprWithCleanups, "ExprWithCleanups"), (.designatedInitExpr, "DesignatedInitExpr"),
  (.parenListExpr, "ParenListExpr"), (.chooseExpr, "ChooseExpr"),
  (.builtinBitCastExpr, "BuiltinBitCastExpr"), (.imaginaryLiteral, "ImaginaryLiteral"),
  (.recoveryExpr, "RecoveryExpr")]

def toString (k : Kind) : String :=
  match table.find? (·.1 == k) with
  | some (_, s) => s
  | none => "?"

def ofString? (s : String) : Option Kind :=
  (table.find? (·.2 == s)).map (·.1)

instance : ToString Kind := ⟨toString⟩

end Kind

/-- A reference to a declaration, as printed inside another node (`referencedDecl`, `decl`,
`field`): the declaration's id, kind, name and type. The kind is kept as a string: a reference
may name a kind outside the subset (it is checked where the declaration itself is printed). -/
structure DeclRef where
  id : String
  kind : String
  name : Option String := none
  type : Option QualType := none
  deriving Repr, BEq, Inhabited

/-- A literal's `value`: a string (integer, floating, string literals, `ConstantExpr`) or a number
(character literals). -/
inductive Value where
  | str (s : String)
  | int (n : Int)
  deriving Repr, BEq, Inhabited

/-- The attributes of one node. Each is `none` when Clang did not print it. -/
structure Header where
  id : String
  kind : Kind
  loc : Option Loc := none
  range : Option Range := none
  type : Option QualType := none
  valueCategory : Option String := none
  name : Option String := none
  mangledName : Option String := none
  storageClass : Option String := none
  /-- `VarDecl`: thread storage (`"static"` for `_Thread_local`/`__thread`, `"dynamic"`). -/
  tls : Option String := none
  isImplicit : Option Bool := none
  isUsed : Option Bool := none
  isReferenced : Option Bool := none
  previousDecl : Option String := none
  parentDeclContextId : Option String := none
  variadic : Option Bool := none
  inline : Option Bool := none
  /-- `VarDecl`: the initialisation style (`"c"`, `"call"`, `"list"`). -/
  init : Option String := none
  nrvo : Option Bool := none
  /-- `RecordDecl`: `"struct"` or `"union"`. -/
  tagUsed : Option String := none
  completeDefinition : Option Bool := none
  isBitfield : Option Bool := none
  /-- `ImplicitCastExpr`, `CStyleCastExpr`: the cast kind (`LValueToRValue`, `IntegralCast`, …). -/
  castKind : Option String := none
  isPartOfExplicitCast : Option Bool := none
  /-- `BinaryOperator`, `UnaryOperator`, `CompoundAssignOperator`: the operator spelling. -/
  opcode : Option String := none
  isPostfix : Option Bool := none
  canOverflow : Option Bool := none
  computeLHSType : Option QualType := none
  computeResultType : Option QualType := none
  value : Option Value := none
  referencedDecl : Option DeclRef := none
  nonOdrUseReason : Option String := none
  isArrow : Option Bool := none
  referencedMemberDecl : Option String := none
  /-- `UnaryExprOrTypeTraitExpr` on a type: the type. -/
  argType : Option QualType := none
  hasElse : Option Bool := none
  hasVar : Option Bool := none
  hasInit : Option Bool := none
  targetLabelDeclId : Option String := none
  declId : Option String := none
  /-- `ConstantArrayType`: the number of elements. -/
  size : Option Nat := none
  /-- `VectorType`: the number of lanes, and the kind of a non-generic vector (`altivec`, `neon`,
  …; absent for a GNU `vector_size` vector). -/
  numElements : Option Nat := none
  vectorKind : Option String := none
  /-- `RecordType`, `EnumType`, `TypedefType`: the declaration. -/
  decl : Option DeclRef := none
  /-- `ElaboratedType` in Clang 21: the tag declared by the type specifier.
  This reference is preserved separately from the underlying type's `decl`. -/
  ownedTagDecl : Option DeclRef := none
  isTagOwned : Option Bool := none
  cc : Option String := none
  implicit : Option Bool := none
  inherited : Option Bool := none
  /-- `InitListExpr` of a union: the initialised member. -/
  field : Option DeclRef := none
  storageDuration : Option String := none
  /-- `EnumDecl`: the fixed underlying type. -/
  fixedUnderlyingType : Option QualType := none
  /-- Qualifiers of a `QualType` node (`"const"`, `"volatile"`, …). -/
  qualifiers : Option String := none
  /-- `VisibilityAttr`: `"default"`, `"hidden"` or `"protected"`. -/
  visibility : Option String := none
  deriving Repr, Inhabited

/-- A node: its attributes, its children (`inner`) and, for an `InitListExpr`, the array filler
(`array_filler`). `none` and `some #[]` differ: Clang omits an empty `inner`. An absent child in a
fixed position (e.g. the missing condition of `for (;;)`) is printed `{}`: `Node.absent`. -/
inductive Node where
  | mk (h : Header) (inner : Option (Array Node)) (arrayFiller : Option (Array Node))
  /-- A complete `FullComment` subtree, preserved without interpreting its comment schema. -/
  | comment (raw : Lean.Json)
  /-- An association of a `GenericSelectionExpr`: Clang prints it with no `id` or `kind`, only
  its `associationKind` (`"case"` or `"default"`), whether it is `selected`, and its children
  (the type node of a `case`, then the expression). -/
  | association (associationKind : String) (selected : Option Bool) (inner : Option (Array Node))
  | absent
  deriving Inhabited

namespace Node

def header? : Node → Option Header
  | .mk h _ _ => some h
  | .comment _ | .association .. | .absent => none

/-- The semantic kind, `none` for an absent child, opaque documentation or a generic
association. -/
def kind? (n : Node) : Option Kind := n.header?.map (·.kind)

/-- The kind (`translationUnitDecl` when there is no header: test `kind?` first). -/
def kind (n : Node) : Kind := n.kind?.getD .translationUnitDecl

def isAbsent : Node → Bool
  | .absent => true
  | _ => false

/-- Whether this node is opaque documentation, rather than a C construct. -/
def isComment : Node → Bool
  | .comment _ => true
  | _ => false

/-- The semantic children (`inner`), excluding documentation; empty when absent or a comment.
The original array remains stored in `Node.mk` for exact JSON encoding. -/
def children : Node → Array Node
  | .mk _ i _ | .association _ _ i => (i.getD #[]).filter (!·.isComment)
  | .comment _ | .absent => #[]

def arrayFiller : Node → Option (Array Node)
  | .mk _ _ f => f
  | .comment _ | .association .. | .absent => none

end Node

end Silmaril.Clang
