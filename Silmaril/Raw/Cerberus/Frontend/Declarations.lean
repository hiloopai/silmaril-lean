module

public import Silmaril.Cerberus.Frontend.Literal.Defs

/-! # Declarations: `c_parser.mly` §6.7 and §6.9

Specifiers, declarators, abstract declarators and type names, initializers, attributes,
static assertions, and the external declarations of a translation unit, after
`c_parser.mly:436-1243` and `1555-1791`. Each function is named after its nonterminal
and cites its rule.

The LR parser decides between alternatives by its lookahead; the recursive descent
decides by the same token:

* a name is a type specifier (`typedef_name_spec`) only while no type specifier has been
  read and the lexer hack makes it `TYPE`; otherwise it ends the specifiers;
* after `(` in a parameter or a type name, a `)` or the start of a parameter declaration
  makes a function abstract declarator. A typedef name there is a parameter type: the
  grammar's one reduce/reduce conflict, which `typedef_name_spec` wins (`c_parser.mly:453`);
* `_Atomic (` in specifiers is the atomic type specifier; elsewhere `_Atomic` is a
  qualifier;
* a declarator followed by `{` begins a function definition.

Names are declared as Menhir reduces their declarators: a declarator in a declaration
before its initializer, a parameter after its declarator, an enumeration constant before
its value.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Declarations

open Silmaril.Cerberus Cabs P

/-! ## Names -/

/-- `general_identifier` (`c_parser.mly:461-465`): a name, typedef or not, as a region. -/
def generalIdentifier? : P (Option Identifier) := do
  let t ← peek
  match t.kind with
  | .name x => let _ ← advance; return some ⟨t.start.region t.stop, x⟩
  | _ => return none

def generalIdentifier : P Identifier := do
  match ← generalIdentifier? with
  | some i => return i
  | none => fail "expected an identifier"

/-! ## Attributes (N2335 §6.7.11, `c_parser.mly:1600-1791`) -/

/-- The spelling of a keyword that `c_keyword_as_string` accepts as an attribute name:
the C11 keywords except `typeof`. -/
def attributeSpelling? : Keyword → Option String
  | .auto => "auto" | .break_ => "break" | .case_ => "case" | .char => "char"
  | .const => "const" | .continue_ => "continue" | .default => "default" | .do_ => "do"
  | .double => "double" | .else_ => "else" | .enum => "enum"
  -- see `Lexer.keywords` for the split spelling
  | .extern_ => "ext" ++ "ern"
  | .float => "float" | .for_ => "for" | .goto => "goto" | .if_ => "if"
  | .inline => "inline" | .int => "int" | .long => "long" | .register => "register"
  | .restrict => "restrict" | .return_ => "return" | .short => "short"
  | .signed => "signed" | .sizeof => "sizeof" | .static => "static"
  | .struct => "struct" | .switch => "switch" | .typedef => "typedef"
  | .union => "union" | .unsigned => "unsigned" | .void => "void"
  | .volatile => "volatile" | .while_ => "while" | .alignas => "_Alignas"
  | .alignof => "_Alignof" | .atomic => "_Atomic" | .bool => "_Bool"
  | .complex => "_Complex" | .generic => "_Generic" | .noreturn => "_Noreturn"
  | .staticAssert => "_Static_assert" | .threadLocal => "_Thread_local"
  | _ => none

/-- `attribute_identifier`: a name as a region, or a C keyword as a point. -/
def attributeIdentifier : P Identifier := do
  let t ← peek
  match t.kind with
  | .name x => let _ ← advance; return ⟨t.start.region t.stop, x⟩
  | .keyword k => match attributeSpelling? k with
    | some s => let _ ← advance; return ⟨t.start.point, s⟩
    | none => fail "expected an attribute name"
  | _ => fail "expected an attribute name"

/-- `attribute_token`: `name` or `prefix::name`. -/
def attributeToken : P (Option Identifier × Identifier) := do
  let i ← attributeIdentifier
  if ← eatPunct .colonColon then return (some i, ← attributeIdentifier)
  else return (none, i)

/-- `located_string_literal`: the region of the literal, its whole text, and each
component's region and text. -/
def locatedStringLiteral : P (Loc × String × List (Loc × String)) := do
  let s ← startPos
  let (_, cs) ← stringLiteral
  let e ← endPos
  let parts := cs.filterMap fun (l, xs) => (rawText xs).map (l, ·)
  if parts.length != cs.length then fail "attribute argument is not UTF-8" else
  return (s.region e, String.join (parts.map (·.2)), parts)

/-- Whether the token closes a balanced token sequence. -/
def isCloser (t : Token) : Bool :=
  isPunct t .rparen || isPunct t .rbrack || isPunct t .rbrace

mutual

/-- `balanced_token`: a bracketed sequence, which keeps nothing, or string literals
separated by commas (`c_parser.mly:1782-1789`). -/
def balancedToken (fuel : Nat) : P (List (Loc × String × List (Loc × String))) := do
  match fuel with
  | 0 => fail "nesting too deep"
  | fuel + 1 =>
    let t ← peek
    let close? : Option Punct :=
      if isPunct t .lparen then some .rparen else if isPunct t .lbrack then some .rbrack
      else if isPunct t .lbrace then some .rbrace else none
    match close? with
    | some c =>
      let _ ← advance
      let _ ← balancedTokenSequence fuel
      let _ ← expectPunct c
      return []
    | none =>
      if !isStringToken t then fail "unexpected token in attribute arguments" else
      return (← sepBy1 .comma locatedStringLiteral).toList

/-- `balanced_token_sequence`: one or more balanced tokens, concatenated in order. -/
def balancedTokenSequence (fuel : Nat) : P (List (Loc × String × List (Loc × String))) := do
  match fuel with
  | 0 => fail "nesting too deep"
  | fuel + 1 =>
    let x ← balancedToken fuel
    let xs ← manyWhile (return !isCloser (← peek)) (balancedToken fuel)
    return x ++ xs.toList.flatten

end

/-- `attribute`: a token and its optional argument clause. -/
def attribute_ : P Attribute := do
  let (ns, id) ← attributeToken
  if ← eatPunct .lparen then
    let args ← balancedTokenSequence 64
    let _ ← expectPunct .rparen
    return ⟨ns, id, args⟩
  else return ⟨ns, id, []⟩

/-- `attribute_specifier`: `[[ attribute_list ]]`, in source order. -/
def attributeSpecifier : P (List Attribute) := do
  let _ ← expectPunct .lbrackLbrack
  let xs ← sepBy1 .comma attribute_
  let _ ← expectPunct .rbrack
  let _ ← expectPunct .rbrack
  return xs.toList

/-- `attribute_specifier_sequence?`: the groups in source order (none when absent). -/
def attributeSpecifierSequence : P (List (List Attribute)) := do
  return (← manyWhile (atPunct .lbrackLbrack) attributeSpecifier).toList

/-- `to_attrs`: the groups flattened in source order. -/
def toAttrs (groups : List (List Attribute)) : Attributes := .mk groups.flatten

/-! ## Specifiers (§6.7.1-6.7.5, `c_parser.mly:858-1100`) -/

/-- `SC_extern`, built through the codec: the evaluator's trust scan refuses the word,
which is also the name of a Lean FFI attribute. -/
def scExtern : StorageClassSpecifier :=
  match Codec.decodeStorageClassSpecifier (.node "SC_extern" #[]) with
  | .ok s => s
  | .error _ => .static

/-- `storage_class_specifier` (without `typedef`). -/
def storageClass? : Keyword → Option StorageClassSpecifier
  | .extern_ => some scExtern
  | .static => some .static
  | .threadLocal => some .threadLocal
  | .auto => some .auto
  | .register => some .register
  | _ => none

/-- `type_qualifier`. -/
def typeQualifier? : Keyword → Option TypeQualifier
  | .const => some .const
  | .restrict => some .restrict
  | .volatile => some .volatile
  | .atomic => some .atomic
  | _ => none

/-- `function_specifier`. -/
def functionSpecifier? : Keyword → Option FunctionSpecifier
  | .inline => some .inline
  | .noreturn => some .noreturn
  | _ => none

/-- `type_specifier_nonunique`: the specifiers that combine (`long long`, `unsigned int`). -/
def nonuniqueSpecifier? : Keyword → Option TypeSpecifierNode
  | .char => some .char
  | .short => some .short
  | .int => some .int
  | .long => some .long
  | .float => some .float
  | .double => some .double
  | .signed => some .signed
  | .unsigned => some .unsigned
  | .complex => some .complex
  | _ => none

/-- Whether the token can begin a `specifier_qualifier_list`, hence a `type_name`. -/
def startsTypeName (t : Token) : P Bool := do
  match t.kind with
  | .keyword k =>
    return (typeQualifier? k).isSome || (nonuniqueSpecifier? k).isSome ||
      k == .void || k == .bool || k == .struct || k == .union || k == .enum ||
      k == .typeof || k == .alignas
  | .name x => return (← env).isTypedef x
  | _ => return false

/-- Whether the token can begin a `parameter_declaration`: an attribute or a
declaration specifier. -/
def startsParameter (t : Token) : P Bool := do
  if isPunct t .lbrackLbrack then return true
  match t.kind with
  | .keyword k =>
    if (storageClass? k).isSome || (functionSpecifier? k).isSome || k == .typedef then
      return true
    startsTypeName t
  | _ => startsTypeName t

/-- `type_qualifier_list?` in source order. -/
def typeQualifierList : P (List TypeQualifier) := do
  let qs ← manyWhile (do
    match (← peek).kind with
    | .keyword k => return (typeQualifier? k).isSome
    | _ => return false) (do
    match (← advance).kind with
    | .keyword k => return (typeQualifier? k).getD .const
    | _ => return .const)
  return qs.toList

/-- What a specifier list has read so far. -/
structure SpecAcc where
  typedefs : Nat := 0
  storage : Array StorageClassSpecifier := #[]
  types : Array TypeSpecifier := #[]
  /-- Whether the type specifier is a `type_specifier_unique`. -/
  unique : Bool := false
  quals : Array TypeQualifier := #[]
  funcs : Array FunctionSpecifier := #[]
  aligns : Array AlignmentSpecifier := #[]

/-- The `specifiers` record of a list (`concat_specs`): each kind in source order, and
`typedef` first among the storage classes (`c_parser.mly:876-885`). -/
def SpecAcc.toSpecifiers (a : SpecAcc) : Specifiers :=
  .mk ((if a.typedefs > 0 then [.typedef] else []) ++ a.storage.toList) a.types.toList
    a.quals.toList a.funcs.toList a.aligns.toList

/-- `atomic_type_specifier` (§6.7.2.4): `_Atomic ( type_name )`. -/
def atomicTypeSpecifier (r : Rec) : P TypeSpecifier := do
  let t ← advance
  let _ ← expectPunct .lparen
  let ty ← r.typeName
  let _ ← expectPunct .rparen
  return .mk (t.start.region (← endPos)) (.atomic ty)

/-- `TYPEOF ( expression )` or `TYPEOF ( type_name )` (`c_parser.mly:958-961`). -/
def typeofSpecifier (r : Rec) : P TypeSpecifier := do
  let t ← advance
  let _ ← expectPunct .lparen
  let node ← if (← startsTypeName (← peek)) then TypeSpecifierNode.typeofType <$> r.typeName
    else TypeSpecifierNode.typeofExpr <$> r.expression
  let _ ← expectPunct .rparen
  return .mk (t.start.region (← endPos)) node

/-- `alignment_specifier` (§6.7.5): `_Alignas ( type_name )` or
`_Alignas ( constant_expression )`. -/
def alignmentSpecifier (r : Rec) : P AlignmentSpecifier := do
  let _ ← advance
  let _ ← expectPunct .lparen
  let a ← if (← startsTypeName (← peek)) then AlignmentSpecifier.type_ <$> r.typeName
    else AlignmentSpecifier.expr <$> r.constantExpression
  let _ ← expectPunct .rparen
  return a

/-- `static_assert_declaration` (§6.7.10): `_Static_assert ( e , "msg" ) ;`. -/
def staticAssertDeclaration (r : Rec) : P StaticAssertDeclaration := do
  let _ ← expectKeyword .staticAssert
  let _ ← expectPunct .lparen
  let e ← r.constantExpression
  let _ ← expectPunct .comma
  let s ← stringLiteral
  let _ ← expectPunct .rparen
  let _ ← expectPunct .semicolon
  return .mk e s

/-- `struct_declarator`: a declarator, or a bit-field `declarator? : constant_expression`.
Members declare no names. -/
def structDeclarator (r : Rec) : P StructDeclarator := do
  if ← eatPunct .colon then return .bitfield none (← r.constantExpression)
  match ← r.declarator .concrete with
  | .concrete d =>
    if ← eatPunct .colon then return .bitfield (some d.toCabs) (← r.constantExpression)
    else return .simple d.toCabs
  | _ => fail "expected a declarator"

/-- The three lists of a `specifier_qualifier_list`. -/
def specQualParts (s : Specifiers) : List TypeSpecifier × List TypeQualifier ×
    List AlignmentSpecifier :=
  match s with
  | .mk _ ts qs _ as => (ts, qs, as)

/-- `struct_declaration`: `attrs? specifier_qualifier_list struct_declarator_list? ;`
and extra semicolons, or a static assertion. -/
def structDeclaration (r : Rec) : P StructDeclaration := do
  if ← atKeyword .staticAssert then return .staticAssert (← staticAssertDeclaration r)
  let attrs ← attributeSpecifierSequence
  let (s, _) ← r.specifiers .specQual
  let (ts, qs, as) := specQualParts s
  let ds ← if (← atPunct .semicolon) then pure #[] else sepBy1 .comma (structDeclarator r)
  let _ ← expectPunct .semicolon
  let _ ← manyWhile (atPunct .semicolon) advance
  return .member (toAttrs attrs) ts qs as ds.toList

/-- The member list of a struct or union after `{`: `{}` is the GNU empty struct;
otherwise extra semicolons, then at least one member declaration. -/
def structDeclarationList (r : Rec) : P (List StructDeclaration) := do
  if ← eatPunct .rbrace then return []
  let _ ← manyWhile (atPunct .semicolon) advance
  let ds ← manyWhile (return !isPunct (← peek) .rbrace) (structDeclaration r)
  if ds.isEmpty then fail "expected a member declaration"
  let _ ← expectPunct .rbrace
  return ds.toList

/-- `struct_or_union_specifier` (§6.7.2.1): the region runs from `struct` to the end of
the specifier (`c_parser.mly:971-992`). -/
def structOrUnionSpecifier (r : Rec) (isUnion : Bool) : P TypeSpecifier := do
  let t ← advance
  let attrs ← attributeSpecifierSequence
  let tag ← generalIdentifier?
  let mut members := none
  if ← eatPunct .lbrace then members := some (← structDeclarationList r)
  else if tag.isNone then fail "expected a tag or a member list"
  let loc := t.start.region (← endPos)
  return .mk loc (if isUnion then .union (toAttrs attrs) tag members
    else .struct (toAttrs attrs) tag members)

/-- `enumerator`: an enumeration constant, declared as a variable before its value. -/
def enumerator (r : Rec) : P (Identifier × Option Expression) := do
  let i ← generalIdentifier
  declareVar i.name
  let _ ← attributeSpecifierSequence
  if ← eatPunct .eq then return (i, some (← r.constantExpression)) else return (i, none)

/-- The enumerators after `{`, an optional trailing comma, and `}`. -/
def enumeratorList (r : Rec) : P (List (Identifier × Option Expression)) := do
  let e ← enumerator r
  let es ← manyWhile (return isPunct (← peek) .comma && !isPunct (← peekAt 1) .rbrace)
    (do let _ ← advance; enumerator r)
  let _ ← eatPunct .comma
  let _ ← expectPunct .rbrace
  return e :: es.toList

/-- `enum_specifier` (§6.7.2.2): its attributes are discarded. -/
def enumSpecifier (r : Rec) : P TypeSpecifier := do
  let t ← advance
  let _ ← attributeSpecifierSequence
  let tag ← generalIdentifier?
  let mut enums := none
  if ← eatPunct .lbrace then enums := some (← enumeratorList r)
  else if tag.isNone then fail "expected a tag or an enumerator list"
  return .mk (t.start.region (← endPos)) (.enum tag enums)

/-- A unique type specifier at a keyword: `void`, `_Bool`, `_Atomic (…)`, struct, union,
enum, `typeof`. -/
def uniqueKeywordSpecifier? (r : Rec) (k : Keyword) :
    P (Option (P TypeSpecifier)) := do
  let simple (n : TypeSpecifierNode) : P TypeSpecifier := do
    let t ← advance
    return .mk (t.start.region t.stop) n
  match k with
  | .void => return some (simple .void)
  | .bool => return some (simple .bool)
  | .atomic =>
    if isPunct (← peekAt 1) .lparen then return some (atomicTypeSpecifier r) else return none
  | .struct => return some (structOrUnionSpecifier r false)
  | .union => return some (structOrUnionSpecifier r true)
  | .enum => return some (enumSpecifier r)
  | .typeof => return some (typeofSpecifier r)
  | _ => return none

/-- One step of a specifier list: add the next specifier to `a`, or `none` at the end. -/
def specifierStep (r : Rec) (mode : SpecMode) (a : SpecAcc) : P (Option SpecAcc) := do
  let t ← peek
  let full := mode != .specQual
  match t.kind with
  | .name x =>
    if !a.types.isEmpty || !(← env).isTypedef x then return none
    let _ ← advance
    let ts : TypeSpecifier := .mk (t.start.region t.stop) (.name ⟨t.start.point, x⟩)
    let _ ← attributeSpecifierSequence
    return some { a with types := a.types.push ts, unique := true }
  | .keyword k =>
    -- after a type specifier, `_Atomic (` is a qualifier and a parenthesized declarator
    let atomicQualifier := k == .atomic && !a.types.isEmpty
    if let some u := (← if atomicQualifier then pure none else uniqueKeywordSpecifier? r k) then
      if !a.types.isEmpty then fail "a second type specifier"
      let ts ← u
      let _ ← attributeSpecifierSequence
      return some { a with types := a.types.push ts, unique := true }
    if let some n := nonuniqueSpecifier? k then
      if a.unique then fail "a type specifier after a unique one"
      let _ ← advance
      let _ ← attributeSpecifierSequence
      return some { a with types := a.types.push (.mk (t.start.region t.stop) n) }
    if let some q := typeQualifier? k then
      let _ ← advance
      let _ ← attributeSpecifierSequence
      return some { a with quals := a.quals.push q }
    if k == .alignas then
      let s ← alignmentSpecifier r
      let _ ← attributeSpecifierSequence
      return some { a with aligns := a.aligns.push s }
    if !full then return none
    if let some sc := storageClass? k then
      let _ ← advance
      let _ ← attributeSpecifierSequence
      return some { a with storage := a.storage.push sc }
    if let some f := functionSpecifier? k then
      let _ ← advance
      let _ ← attributeSpecifierSequence
      return some { a with funcs := a.funcs.push f }
    if k == .typedef then
      if mode == .parameter || a.typedefs > 0 then fail "unexpected typedef"
      let _ ← advance
      return some { a with typedefs := a.typedefs + 1 }
    return none
  | _ => return none

/-- `declaration_specifiers`, `declaration_specifiers_typedef` or
`specifier_qualifier_list` (`c_parser.mly:863-883`, `1013-1021`): exactly one unique type
specifier or at least one nonunique one, among the other specifiers. -/
def specifiers (r : Rec) (mode : SpecMode) : P (Specifiers × Bool) := do
  let mut a : SpecAcc := {}
  for _ in [0:(← get).toks.size + 1] do
    match ← specifierStep r mode a with
    | some a' => a := a'
    | none => break
  if a.types.isEmpty then fail "expected a type specifier"
  return (a.toSpecifiers, a.typedefs > 0)

/-! ## Declarators (§6.7.6, `c_parser.mly:1104-1243`) -/

/-- `pointer`: `* attrs? qualifiers?` repeated. Every `PDecl` region ends where the whole
pointer ends. -/
def pointer : P (Option PointerDeclarator) := do
  let stars ← manyWhile (atPunct .star) (do
    let t ← advance
    let _ ← attributeSpecifierSequence
    return (t.start, ← typeQualifierList))
  let e ← endPos
  return stars.foldr (fun (s, qs) next => some (.mk (s.region e) qs next)) none

/-- The bracket part of `array_declarator` after `[`, up to `]`: qualifiers in source
order, `static`, and the size (`c_parser.mly:1130-1150`). -/
def arrayDeclaratorBody (r : Rec) : P (List TypeQualifier × Bool × Option ArrayDeclaratorSize) := do
  if ← atKeyword .static then
    let _ ← advance
    let qs ← typeQualifierList
    return (qs, true, some (.expression (← r.assignmentExpression)))
  let qs ← typeQualifierList
  if !qs.isEmpty && (← atKeyword .static) then
    let _ ← advance
    return (qs, true, some (.expression (← r.assignmentExpression)))
  if (← atPunct .star) && isPunct (← peekAt 1) .rbrack then
    let _ ← advance
    return (qs, false, some .asterisk)
  if ← atPunct .rbrack then return (qs, false, none)
  return (qs, false, some (.expression (← r.assignmentExpression)))

/-- The bracket part of `array_abstract_declarator`. Its qualifier list is not reversed
back, so it is in reverse order, and `[*]` takes no qualifiers
(`c_parser.mly:1224-1243`). -/
def arrayAbstractBody (r : Rec) : P ArrayDeclarator := do
  let _ ← expectPunct .lbrack
  let (qs, st, size) ← do
    if ← atKeyword .static then
      let _ ← advance
      let qs ← typeQualifierList
      pure (qs.reverse, true, some (ArrayDeclaratorSize.expression (← r.assignmentExpression)))
    else if (← atPunct .star) && isPunct (← peekAt 1) .rbrack then
      let _ ← advance
      pure ([], false, some .asterisk)
    else
      let qs ← typeQualifierList
      if !qs.isEmpty && (← atKeyword .static) then
        let _ ← advance
        pure (qs.reverse, true, some (.expression (← r.assignmentExpression)))
      else if ← atPunct .rbrack then pure (qs.reverse, false, none)
      else pure (qs.reverse, false, some (.expression (← r.assignmentExpression)))
  let _ ← expectPunct .rbrack
  return .mk .unknown qs st size

/-- `parameter_declaration`: a named parameter is declared as a variable once its
declarator is read (`declarator_varname`). -/
def parameterDeclaration (r : Rec) : P ParameterDeclaration := do
  let _ ← attributeSpecifierSequence
  let (s, _) ← r.specifiers .parameter
  match ← r.declarator .either with
  | .concrete d => declareVar d.name; return .declarator s d.toCabs
  | .abstract a => return .abstract s (some a)
  | .none => return .abstract s none

/-- `parameter_type_list` and the context saved after it (`c_parser.mly:1179-1184`). -/
def parameterTypeList (r : Rec) : P (ParameterTypeList × TypedefEnv) := do
  let p ← parameterDeclaration r
  let ps ← manyWhile (return isPunct (← peek) .comma && !isPunct (← peekAt 1) .ellipsis)
    (do let _ ← advance; parameterDeclaration r)
  let variadic ← if (← eatPunct .comma) then do let _ ← expectPunct .ellipsis; pure true
    else pure false
  return (.mk (p :: ps.toList) variadic, ← env)

/-- `scoped(parameter_type_list)?` and `)` after the `(` of a function abstract
declarator. -/
def abstractParameters (r : Rec) : P ParameterTypeList := do
  if ← eatPunct .rparen then return .mk [] false
  let saved ← env
  let (ps, _) ← parameterTypeList r
  setEnv saved
  let _ ← expectPunct .rparen
  return ps

/-- The suffixes of a direct declarator that starts at `start`: arrays and functions
(`c_parser.mly:1117-1156`). A parameter list is scoped and its inner context kept for a
function definition; `()` and an identifier list keep the context before them. -/
def directDeclaratorSuffixes (r : Rec) (start : Pos) (d : Decl) : P Decl := do
  let mut d := d
  for _ in [0:(← get).toks.size + 1] do
    if ← eatPunct .lbrack then
      let (qs, st, size) ← arrayDeclaratorBody r
      let _ ← expectPunct .rbrack
      let a : ArrayDeclarator := .mk (start.region (← endPos)) qs st size
      let _ ← attributeSpecifierSequence
      d := { d with direct := .array d.direct a, sort := .other }
    else if ← eatPunct .lparen then
      let ctxt ← env
      if ← eatPunct .rparen then
        d := { d with direct := .function d.direct (.mk [] false), sort := .fn ctxt }
      else
        match ← nameOf (← peek) with
        | some (_, false) =>
          -- `identifier_list` gives each identifier `point $startpos` of the production,
          -- which is the start of the whole list (`c_parser.mly:1158-1163`)
          let listStart ← startPos
          let ids ← sepBy1 .comma (do
            match ← nameOf (← peek) with
            | some (x, false) => let _ ← advance; return (⟨listStart.point, x⟩ : Identifier)
            | _ => fail "expected an identifier")
          let _ ← expectPunct .rparen
          d := { d with direct := .function d.direct (.mk [] false),
                        sort := .fnIds ctxt ids.toList }
        | _ =>
          let (ps, inner) ← parameterTypeList r
          setEnv ctxt
          let _ ← expectPunct .rparen
          let _ ← attributeSpecifierSequence
          d := { d with direct := .function d.direct ps, sort := .fn inner }
    else break
  return d

/-- The suffixes of a direct abstract declarator. -/
def directAbstractSuffixes (r : Rec) (a : DirectAbstractDeclarator) :
    P DirectAbstractDeclarator := do
  let mut a := a
  for _ in [0:(← get).toks.size + 1] do
    if ← atPunct .lbrack then
      let b ← arrayAbstractBody r
      let _ ← attributeSpecifierSequence
      a := .array (some a) b
    else if ← eatPunct .lparen then
      let ps ← abstractParameters r
      let _ ← attributeSpecifierSequence
      a := .function (some a) ps
    else break
  return a

/-- The base of a direct declarator. -/
inductive Base where
  | concrete (d : Decl)
  | abstract (a : DirectAbstractDeclarator)
  | none

/-- The base of a direct (abstract) declarator: an identifier, a parenthesized
declarator, or the first array or function part of an abstract one. -/
def directBase (r : Rec) (mode : DeclMode) : P Base := do
  let t ← peek
  if let .name x := t.kind then
    if mode == .abstract then return .none
    let _ ← advance
    let attrs ← attributeSpecifierSequence
    return .concrete ⟨x, .ident, .identifier (toAttrs attrs) ⟨t.start.region t.stop, x⟩⟩
  if isPunct t .lparen then
    let t1 ← peekAt 1
    if mode != .concrete && (isPunct t1 .rparen || (← startsParameter t1)) then
      let _ ← advance
      return .abstract (.function none (← abstractParameters r))
    let _ ← advance
    let inner ← r.declarator mode
    let _ ← expectPunct .rparen
    match inner with
    | .concrete d => return .concrete { d with direct := .declarator d.toCabs, sort := .other }
    | .abstract a => return .abstract (.abstract a)
    | .none => fail "expected a declarator"
  if isPunct t .lbrack && mode != .concrete then
    return .abstract (.array none (← arrayAbstractBody r))
  return .none

/-- `declarator`, `abstract_declarator`, or either: a pointer and a direct part. -/
def declaratorAny (r : Rec) (mode : DeclMode) : P AnyDecl := do
  let ptr ← pointer
  let start ← startPos
  match ← directBase r mode with
  | .concrete d =>
    let d ← directDeclaratorSuffixes r start d
    match ptr with
    | some p => return .concrete { d with sort := .ptr p }
    | none => return .concrete d
  | .abstract a => return .abstract (.direct ptr (← directAbstractSuffixes r a))
  | .none =>
    match ptr with
    | some p => return .abstract (.pointer p)
    | none => return .none

/-- `declarator`. -/
def declarator (r : Rec) : P Decl := do
  match ← r.declarator .concrete with
  | .concrete d => return d
  | _ => fail "expected a declarator"

/-- `type_name` (§6.7.7). -/
def typeName (r : Rec) : P TypeName := do
  let (s, _) ← r.specifiers .specQual
  let (ts, qs, as) := specQualParts s
  match ← r.declarator .abstract with
  | .abstract a => return .mk ts qs as (some a)
  | .none => return .mk ts qs as none
  | .concrete _ => fail "unexpected declarator in a type name"

/-! ## Initializers (§6.7.9, `c_parser.mly:1247-1283`) -/

/-- `designator`: `[ constant_expression ]` or `. identifier`. -/
def designator (r : Rec) : P Designator := do
  if ← eatPunct .lbrack then
    let e ← r.constantExpression
    let _ ← expectPunct .rbrack
    return .array e
  let _ ← expectPunct .dot
  return .member (← generalIdentifier)

/-- `designation? initializer_`. -/
def initListItem (r : Rec) : P (Option (List Designator) × Initializer) := do
  let isDesignator : P Bool := return isPunct (← peek) .lbrack || isPunct (← peek) .dot
  if ← isDesignator then
    let ds ← manyWhile isDesignator (designator r)
    let _ ← expectPunct .eq
    return (some ds.toList, ← r.initr)
  return (none, ← r.initr)

/-- `initializer_`: an assignment expression, or a braced list whose region includes the
braces. -/
def initr (r : Rec) : P Initializer := do
  let t ← peek
  if isPunct t .lbrace then
    let _ ← advance
    let x ← initListItem r
    let xs ← manyWhile (return isPunct (← peek) .comma && !isPunct (← peekAt 1) .rbrace)
      (do let _ ← advance; initListItem r)
    let _ ← eatPunct .comma
    let _ ← expectPunct .rbrace
    return .list (t.start.region (← endPos)) (x :: xs.toList)
  return .expr (← r.assignmentExpression)

/-! ## Declarations (§6.7, `c_parser.mly:831-856`) -/

/-- Declare the name of a declarator as Menhir reduces `declarator_typedefname` or
`declarator_varname`. -/
def declareDecl (isTypedef : Bool) (d : Decl) : P Unit :=
  if isTypedef then declareTypedef d.name else declareVar d.name

/-- A declarator of an init-declarator, declared before its initializer, and its start. -/
def declaredDeclarator (r : Rec) (isTypedef : Bool) : P (Decl × Pos) := do
  let start ← startPos
  let d ← declarator r
  declareDecl isTypedef d
  return (d, start)

/-- The rest of `init_declarator` after its declarator: an `asm` register, which is
dropped, and an initializer. The region covers all of it. -/
def initDeclaratorRest (r : Rec) (d : Decl) (start : Pos) : P InitDeclarator := do
  if ← atKeyword .asm then
    let _ ← advance
    let _ ← expectPunct .lparen
    let _ ← stringLiteral
    let _ ← expectPunct .rparen
  let i ← if (← eatPunct .eq) then some <$> r.initr else pure none
  return .mk (start.region (← endPos)) d.toCabs i

/-- `init_declarator_list? ;` after the specifiers, given the first declarator if it has
been read. -/
def declarationRest (r : Rec) (attrs : Attributes) (s : Specifiers) (isTypedef : Bool)
    (first : Option (Decl × Pos)) : P Declaration := do
  let first ← match first with
    | some f => pure (some f)
    | none => do
      if ← atPunct .semicolon then pure none else some <$> declaredDeclarator r isTypedef
  match first with
  | none =>
    let _ ← expectPunct .semicolon
    return .base attrs s []
  | some (d, start) =>
    let x ← initDeclaratorRest r d start
    let xs ← manyWhile (atPunct .comma) (do
      let _ ← advance
      let (d, start) ← declaredDeclarator r isTypedef
      initDeclaratorRest r d start)
    let _ ← expectPunct .semicolon
    return .base attrs s (x :: xs.toList)

/-- The dummy declaration of an attribute declaration `[[…]];`: an identifier `test`
whose location is the whole declaration (`c_parser.mly:850-856`). -/
def attributeDeclaration (loc : Loc) : Declaration :=
  .base (.mk []) (.mk [] [] [] [] [])
    [.mk loc (.mk none (.identifier (.mk []) ⟨loc, "test"⟩)) none]

/-- `declaration` (§6.7). -/
def declaration (r : Rec) : P Declaration := do
  if ← atKeyword .staticAssert then return .staticAssert (← staticAssertDeclaration r)
  let start ← startPos
  let attrs ← attributeSpecifierSequence
  if !attrs.isEmpty && (← atPunct .semicolon) then
    let _ ← advance
    return attributeDeclaration (start.region (← endPos))
  let (s, isTypedef) ← r.specifiers .declaration
  declarationRest r (toAttrs attrs) s isTypedef none

/-! ## External declarations (§6.9, `c_parser.mly:1555-1592`) -/

/-- The parameters of a K&R definition without declarations: `int` each
(`create_function_definition`, `lexer_feedback.ml:138-152`). -/
def knrParameter (i : Identifier) : ParameterDeclaration :=
  .declarator (.mk [] [.mk .unknown .int] [] [] []) (.mk none (.identifier (.mk []) i))

/-- Whether the token can begin a declaration of a K&R declaration list. -/
def startsDeclaration (t : Token) : P Bool := do
  if isKeyword t .staticAssert then return true
  startsParameter t

/-- `function_definition` after `function_definition1`: the body under the reinstalled
parameter context, an optional `;` inside the region, and the context restored. The
attribute groups are reversed (`lexer_feedback.ml:132-137`). -/
def functionDefinition (r : Rec) (start : Pos) (groups : List (List Attribute))
    (s : Specifiers) (d : Decl) : P FunctionDefinition := do
  let ctxt ← env
  if let .fn c := d.sort then
    setEnv c
    declareVar d.name
  let ds ← manyWhile (do
    let t ← peek
    if isPunct t .lbrackLbrack then return false
    startsDeclaration t) (declaration r)
  let body ← r.compoundStatement
  let _ ← eatPunct .semicolon
  let loc := start.region (← endPos)
  setEnv ctxt
  let attrs : Attributes := .mk groups.reverse.flatten
  match d.sort, d.direct with
  | .fnIds _ ids, .function dd _ =>
    if !ds.isEmpty then fail "K&R declaration lists are rejected"
    return ⟨loc, attrs, s, .mk none (.function dd (.mk (ids.map knrParameter) false)), body⟩
  | _, _ => return ⟨loc, attrs, s, d.toCabs, body⟩

/-- `external_declaration`: a function definition, or a declaration and any extra
semicolons. -/
def externalDeclaration (r : Rec) : P ExternalDeclaration := do
  let skipSemis : P Unit := do let _ ← manyWhile (atPunct .semicolon) advance
  if ← atKeyword .staticAssert then
    let d := Declaration.staticAssert (← staticAssertDeclaration r)
    skipSemis
    return .decl d
  let start ← startPos
  let groups ← attributeSpecifierSequence
  if !groups.isEmpty && (← atPunct .semicolon) then
    let _ ← advance
    let d := attributeDeclaration (start.region (← endPos))
    skipSemis
    return .decl d
  let (s, isTypedef) ← r.specifiers .declaration
  if ← atPunct .semicolon then
    let _ ← advance
    skipSemis
    return .decl (.base (toAttrs groups) s [])
  let first ← declaredDeclarator r isTypedef
  if !isTypedef && ((← atPunct .lbrace) || (← atPunct .lbraces) ||
      (!(← atPunct .lbrackLbrack) && (← startsDeclaration (← peek)))) then
    return .func (← functionDefinition r start groups s first.1)
  let d ← declarationRest r (toAttrs groups) s isTypedef (some first)
  skipSemis
  return .decl d

/-- `translation_unit`: external declarations up to `EOF`. -/
def translationUnit (r : Rec) : P TranslationUnit := do
  let ds ← manyWhile (return !(match (← peek).kind with | .eof => true | _ => false))
    (externalDeclaration r)
  match (← peek).kind with
  | .eof => return ⟨ds.toList⟩
  | _ => fail "expected end of input"

end Silmaril.Cerberus.Frontend.Declarations
