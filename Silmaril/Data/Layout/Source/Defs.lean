module

public import Silmaril.Data.Layout.Defs

/-!
# C record definitions as text: a lexer, a grammar relation and a parser

The source layer of the C record-layout slice. A *record source* is a sequence of top-level
`struct` and `union` definitions written in a small, explicitly bounded subset of C11; its
abstract syntax is the existing declaration model `Silmaril.Data.Layout.Env` (a list of
`Decl`s). Nothing here computes a layout: target data models and the psABI placement rule are
applied later (`Silmaril.Data.Layout.Record`).

* `lex`: characters to `Token`s (identifiers, decimal literals, punctuation). It skips white
  space and `//`/`/* */` comments. It is total and fuel-bounded (one step per character), and
  is part of the specification: `Parses` is stated over its output.
* `Spec`, `Declarator`, `Suffix`, `DeclList`, `Members`, `RecordDef`, `TransUnit`: the grammar,
  as inductive relations on token lists (input, value, remaining input).
* `checkScope`: the static conditions the grammar does not express (below).
* `Parses src env`: `src` lexes to a token list that the grammar derives as `env`, and `env`
  passes `checkScope`. This is the relation the macro certifies.
* `parse`: an executable recursive-descent parser with explicit rejection messages; it is
  sound for `Parses` (`Silmaril.Data.Layout.Source.parse_sound` in `Thms`).

## The accepted subset

```
unit      ::= record*
record    ::= ("struct" | "union") NAME "{" member+ "}" ";"
member    ::= spec declarator ("," declarator)* ";"
spec      ::= scalar | "struct" NAME | "union" NAME
declarator::= "*"* NAME ("[" DECIMAL "]")*
```

`scalar` is one of the spellings in `scalarSpellings`: the standard integer types in their
common spellings (`unsigned long int`, …), `_Bool`, `float`, `double`, `long double`,
`void` (only useful behind a pointer), and the fixed-width typedef names of `<stdint.h>` and
`<stddef.h>` (`uint32_t`, `size_t`, …), which are treated as built-in names because no
preprocessor runs.

`checkScope` requires that tags are distinct (C has one tag namespace for structs and
unions), member names are distinct within a record, every member of record or array type
names a record *defined earlier* in the same source (so the type is complete and a record
cannot contain itself), no member has type `void`, and array lengths are positive. Pointers
may name any tag (incomplete types are allowed behind pointers).

## Rejected, with a message

Bit-fields, `_Alignas`/`alignas`, attributes and `#pragma`/other preprocessor lines, type
qualifiers, `typedef`, `enum`, storage classes, flexible and zero-length arrays, function
declarators, anonymous members and record definitions nested inside a member, initializers,
forward declarations, `_Complex`, `__int128`, `_BitInt`, non-decimal or suffixed literals and
non-ASCII characters outside comments. Accepting none of them is a choice of scope, not a
claim that they are uninteresting: bit-fields already have an open goal in
`Silmaril.Data.Layout.Thms`.
-/

@[expose] public section

namespace Silmaril.Data.Layout.Source

open Silmaril.Data.Layout

/-! ## Tokens and the lexer -/

/-- A token: identifier or keyword, decimal literal, or a single punctuation character. -/
inductive Token where
  | ident (name : String)
  | num (value : Nat)
  | punct (c : Char)
  deriving DecidableEq, Repr, Inhabited

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'

def isIdentCont (c : Char) : Bool := c.isAlphanum || c == '_'

/-- The characters after a `//` comment: from the next newline on. -/
def skipLine : List Char → List Char
  | [] => []
  | '\n' :: cs => cs
  | _ :: cs => skipLine cs

/-- The characters after the `*/` that closes a block comment (`none`: unterminated). -/
def skipBlock : List Char → Option (List Char)
  | [] => none
  | '*' :: '/' :: cs => some cs
  | _ :: cs => skipBlock cs

/-- Decimal value of a non-empty digit string (`none` otherwise, e.g. `0x10` or `2u`). -/
def decimal? (cs : List Char) : Option Nat :=
  if cs ≠ [] ∧ cs.all Char.isDigit then
    some (cs.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0)
  else none

/-- One step per character; `fuel` is the input length plus one. -/
def lexAux : Nat → List Char → Except String (List Token)
  | 0, _ => .error "lexer fuel exhausted"
  | _ + 1, [] => .ok []
  | fuel + 1, c :: cs =>
    if c == ' ' || c == '\n' || c == '\t' || c == '\r' then lexAux fuel cs
    else if c == '/' && cs.head? == some '/' then lexAux fuel (skipLine cs)
    else if c == '/' && cs.head? == some '*' then
      match skipBlock (cs.drop 1) with
      | none => .error "unterminated block comment"
      | some rest => lexAux fuel rest
    else if isIdentStart c then
      let (w, rest) := cs.span isIdentCont
      match lexAux fuel rest with
      | .ok ts => .ok (.ident (String.ofList (c :: w)) :: ts)
      | .error e => .error e
    else if c.isDigit then
      let (w, rest) := cs.span isIdentCont
      match decimal? (c :: w) with
      | none =>
        .error s!"unsupported literal `{String.ofList (c :: w)}`: only decimal array lengths"
      | some n => match lexAux fuel rest with
        | .ok ts => .ok (.num n :: ts)
        | .error e => .error e
    else if c.toNat < 128 && c.toNat > 32 then
      match lexAux fuel cs with
      | .ok ts => .ok (.punct c :: ts)
      | .error e => .error e
    else .error s!"unsupported character (code point {c.toNat})"

/-- Tokens of a source text. -/
def lex (src : String) : Except String (List Token) :=
  lexAux (src.length + 1) src.toList

/-! ## Names and scalar spellings -/

/-- `t` behind a `<stdint.h>`/`<stddef.h>` typedef name. -/
def stdTypedef (name : String) (k : IntKind) (s : Sign) : CTy := .typedef name (.int k s)

/-- Accepted scalar type spellings, longest first (the parser takes the first match). -/
def scalarSpellings : List (List String × CTy) := [
  (["unsigned", "long", "long", "int"], .int .longLong .unsigned),
  (["signed", "long", "long", "int"], .int .longLong .signed),
  (["unsigned", "long", "long"], .int .longLong .unsigned),
  (["signed", "long", "long"], .int .longLong .signed),
  (["long", "long", "int"], .int .longLong .signed),
  (["unsigned", "long", "int"], .int .long .unsigned),
  (["signed", "long", "int"], .int .long .signed),
  (["unsigned", "short", "int"], .int .short .unsigned),
  (["signed", "short", "int"], .int .short .signed),
  (["long", "long"], .int .longLong .signed),
  (["long", "int"], .int .long .signed),
  (["long", "double"], .float .longDouble),
  (["unsigned", "long"], .int .long .unsigned),
  (["signed", "long"], .int .long .signed),
  (["short", "int"], .int .short .signed),
  (["unsigned", "short"], .int .short .unsigned),
  (["signed", "short"], .int .short .signed),
  (["unsigned", "int"], .int .int .unsigned),
  (["signed", "int"], .int .int .signed),
  (["unsigned", "char"], .int .char .unsigned),
  (["signed", "char"], .int .char .signed),
  (["char"], .int .char .plain),
  (["short"], .int .short .signed),
  (["int"], .int .int .signed),
  (["long"], .int .long .signed),
  (["unsigned"], .int .int .unsigned),
  (["signed"], .int .int .signed),
  (["_Bool"], .bool),
  (["float"], .float .float),
  (["double"], .float .double),
  (["void"], .void),
  (["int8_t"], stdTypedef "int8_t" (.exact 1) .signed),
  (["int16_t"], stdTypedef "int16_t" (.exact 2) .signed),
  (["int32_t"], stdTypedef "int32_t" (.exact 4) .signed),
  (["int64_t"], stdTypedef "int64_t" (.exact 8) .signed),
  (["uint8_t"], stdTypedef "uint8_t" (.exact 1) .unsigned),
  (["uint16_t"], stdTypedef "uint16_t" (.exact 2) .unsigned),
  (["uint32_t"], stdTypedef "uint32_t" (.exact 4) .unsigned),
  (["uint64_t"], stdTypedef "uint64_t" (.exact 8) .unsigned),
  (["size_t"], stdTypedef "size_t" .size .unsigned),
  (["ptrdiff_t"], stdTypedef "ptrdiff_t" .ptrdiff .signed),
  (["intptr_t"], stdTypedef "intptr_t" .intptr .signed),
  (["uintptr_t"], stdTypedef "uintptr_t" .intptr .unsigned)]

/-- Words the subset recognizes but rejects, with the reason. -/
def unsupportedWords : List (String × String) := [
  ("typedef", "typedef declarations"), ("enum", "enumerations"),
  ("const", "type qualifiers"), ("volatile", "type qualifiers"),
  ("restrict", "type qualifiers"), ("_Atomic", "atomic types"),
  ("_Alignas", "alignment specifiers"), ("alignas", "alignment specifiers"),
  ("__attribute__", "attributes"), ("__attribute", "attributes"),
  ("__declspec", "attributes"), ("__extension__", "GNU extensions"),
  ("static", "storage-class specifiers"), ("extern", "storage-class specifiers"),
  ("register", "storage-class specifiers"), ("auto", "storage-class specifiers"),
  ("_Thread_local", "storage-class specifiers"), ("thread_local", "storage-class specifiers"),
  ("inline", "function specifiers"), ("_Noreturn", "function specifiers"),
  ("_Complex", "complex types"), ("_Imaginary", "imaginary types"),
  ("__int128", "128-bit integers"), ("_BitInt", "bit-precise integers"),
  ("bool", "the C23 `bool` keyword (write `_Bool`)"),
  ("_Decimal32", "decimal floating types"), ("_Decimal64", "decimal floating types"),
  ("_Decimal128", "decimal floating types"), ("_Float16", "extended floating types"),
  ("__fp16", "extended floating types"), ("__float128", "extended floating types"),
  ("_Static_assert", "static assertions"), ("static_assert", "static assertions"),
  ("typeof", "typeof"), ("__typeof__", "typeof"), ("typeof_unqual", "typeof"),
  ("asm", "inline assembly"), ("__asm__", "inline assembly")]

/-- Other C keywords: they cannot be names, and no rule accepts them. -/
def otherKeywords : List String :=
  ["break", "case", "continue", "default", "do", "else", "for", "goto", "if", "return",
   "sizeof", "switch", "while", "_Alignof", "alignof", "_Generic", "constexpr", "false",
   "true", "nullptr", "struct", "union"]

/-- Reserved words: no member or tag may be called this. -/
def reserved (w : String) : Bool :=
  scalarSpellings.any (fun e => e.1.contains w) || unsupportedWords.any (·.1 == w) ||
    otherKeywords.contains w

/-- A C identifier that is not a reserved word. -/
def isName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => isIdentStart c && cs.all isIdentCont && !reserved s

/-- `struct` or `union`. -/
def kindOfWord? : String → Option Kind
  | "struct" => some .struct
  | "union" => some .union
  | _ => none

/-- The record type `struct tag` or `union tag`. -/
def recordTy : Kind → String → CTy
  | .struct, tag => .struct tag
  | .union, tag => .union tag

/-! ## The grammar -/

/-- `ts = ws.map .ident ++ r`, as a function: strip the words `ws` off the front. -/
def stripWords : List String → List Token → Option (List Token)
  | [], ts => some ts
  | w :: ws, .ident v :: ts => if w = v then stripWords ws ts else none
  | _ :: _, _ => none

/-- A type specifier: a scalar spelling, or a struct or union named by tag. -/
inductive Spec : List Token → CTy → List Token → Prop
  | scalar {ws : List String} {t : CTy} {r : List Token} :
      (ws, t) ∈ scalarSpellings → Spec (ws.map .ident ++ r) t r
  | record {w tag : String} {k : Kind} {r : List Token} :
      kindOfWord? w = some k → isName tag = true →
      Spec (.ident w :: .ident tag :: r) (recordTy k tag) r

/-- Array suffixes: `t x[a][b]` is an `a`-array of `b`-arrays of `t`. -/
inductive Suffix : CTy → List Token → CTy → List Token → Prop
  | done {t : CTy} {r : List Token} : Suffix t r t r
  | array {t t' : CTy} {n : Nat} {ts r : List Token} :
      0 < n → Suffix t ts t' r →
      Suffix t (.punct '[' :: .num n :: .punct ']' :: ts) (.array t' n) r

/-- A declarator: pointer stars, the member name, array suffixes. -/
inductive Declarator : CTy → List Token → Field → List Token → Prop
  | ptr {t : CTy} {ts : List Token} {f : Field} {r : List Token} :
      Declarator (.ptr t) ts f r → Declarator t (.punct '*' :: ts) f r
  | name {t t' : CTy} {n : String} {ts r : List Token} :
      isName n = true → Suffix t ts t' r →
      Declarator t (.ident n :: ts) { name := n, ty := t' } r

/-- Comma-separated declarators sharing one specifier, up to and including the `;`. -/
inductive DeclList : CTy → List Token → List Field → List Token → Prop
  | last {t : CTy} {ts r : List Token} {f : Field} :
      Declarator t ts f (.punct ';' :: r) → DeclList t ts [f] r
  | more {t : CTy} {ts r₁ r : List Token} {f : Field} {fs : List Field} :
      Declarator t ts f (.punct ',' :: r₁) → DeclList t r₁ fs r → DeclList t ts (f :: fs) r

/-- Member declarations, up to and including the closing `}`. -/
inductive Members : List Token → List Field → List Token → Prop
  | close {r : List Token} : Members (.punct '}' :: r) [] r
  | decl {ts r₁ r₂ r : List Token} {t : CTy} {fs gs : List Field} :
      Spec ts t r₁ → DeclList t r₁ fs r₂ → Members r₂ gs r → Members ts (fs ++ gs) r

/-- A top-level `struct` or `union` definition with at least one member. -/
inductive RecordDef : List Token → Decl → List Token → Prop
  | mk {w tag : String} {k : Kind} {ms r : List Token} {fs : List Field} :
      kindOfWord? w = some k → isName tag = true → Members ms fs (.punct ';' :: r) →
      fs ≠ [] →
      RecordDef (.ident w :: .ident tag :: .punct '{' :: ms) { kind := k, tag, fields := fs } r

/-- A whole source: record definitions until the end of input. -/
inductive TransUnit : List Token → Env → Prop
  | nil : TransUnit [] []
  | cons {ts r : List Token} {d : Decl} {ds : Env} :
      RecordDef ts d r → TransUnit r ds → TransUnit ts (d :: ds)

/-! ## Static conditions -/

/-- A member type is complete given the tags defined so far: records and array elements are
defined earlier, no `void` object. Pointers may point to anything. -/
def objectOk (seen : List (Kind × String)) : CTy → Bool
  | .void => false
  | .struct tag => seen.contains (.struct, tag)
  | .union tag => seen.contains (.union, tag)
  | .array e n => 0 < n && objectOk seen e
  | .typedef _ t => objectOk seen t
  | _ => true

/-- Static conditions on a parsed source, given the tags defined before it. -/
def checkScope (seen : List (Kind × String)) : Env → Except String Unit
  | [] => .ok ()
  | d :: ds =>
    if seen.any (·.2 == d.tag) then .error s!"tag `{d.tag}` is defined twice"
    else if !(d.fields.map (·.name)).Nodup then
      .error s!"`{d.tag}` has two members with the same name"
    else match d.fields.find? (fun f => !objectOk seen f.ty) with
      | some f => .error s!"member `{f.name}` of `{d.tag}` has an incomplete or void type \
          (records must be defined before they are used by value)"
      | none => checkScope ((d.kind, d.tag) :: seen) ds

/-- The parsing relation: `src` lexes to tokens the grammar derives as `env`, and `env`
passes the static conditions. -/
def Parses (src : String) (env : Env) : Prop :=
  ∃ ts, lex src = .ok ts ∧ TransUnit ts env ∧ checkScope [] env = .ok ()

/-! ## The parser -/

/-- The first scalar spelling that prefixes the tokens. -/
def matchScalar : List (List String × CTy) → List Token → Option (CTy × List Token)
  | [], _ => none
  | (ws, t) :: rest, ts => match stripWords ws ts with
    | some r => some (t, r)
    | none => matchScalar rest ts

/-- Why the next token cannot start a type. -/
def specError : List Token → String
  | .ident w :: _ => match unsupportedWords.find? (·.1 == w) with
    | some (_, why) => s!"unsupported C feature: {why} (`{w}`)"
    | none => s!"unknown type name `{w}`"
  | .punct '#' :: _ => "unsupported C feature: preprocessor directives (`#`)"
  | .punct c :: _ => s!"expected a type, found `{c}`"
  | .num n :: _ => s!"expected a type, found `{n}`"
  | [] => "unexpected end of input, expected a type"

def parseSpec : List Token → Except String (CTy × List Token)
  | .ident w :: .ident tag :: r =>
    match kindOfWord? w with
    | some k => if isName tag then .ok (recordTy k tag, r)
      else .error s!"`{tag}` is not a valid tag name"
    | none => match matchScalar scalarSpellings (.ident w :: .ident tag :: r) with
      | some p => .ok p
      | none => .error (specError (.ident w :: .ident tag :: r))
  | .ident w :: .punct '{' :: r =>
    if (kindOfWord? w).isSome then .error "unsupported C feature: anonymous structs and unions"
    else match matchScalar scalarSpellings (.ident w :: .punct '{' :: r) with
      | some p => .ok p
      | none => .error (specError (.ident w :: .punct '{' :: r))
  | ts => match matchScalar scalarSpellings ts with
    | some p => .ok p
    | none => .error (specError ts)

def parseSuffix (t : CTy) : List Token → Except String (CTy × List Token)
  | .punct '[' :: .num n :: .punct ']' :: ts =>
    if 0 < n then match parseSuffix t ts with
      | .ok (t', r) => .ok (.array t' n, r)
      | .error e => .error e
    else .error "unsupported C feature: zero-length arrays"
  | .punct '[' :: .punct ']' :: _ => .error "unsupported C feature: flexible array members"
  | .punct '[' :: _ => .error "array lengths must be decimal literals"
  | .punct ':' :: _ => .error "unsupported C feature: bit-fields"
  | .punct '(' :: _ => .error "unsupported C feature: function declarators and attributes"
  | .punct '=' :: _ => .error "unsupported C feature: initializers"
  | ts => .ok (t, ts)

def parseDeclarator (t : CTy) : List Token → Except String (Field × List Token)
  | .punct '*' :: ts => parseDeclarator (.ptr t) ts
  | .ident n :: ts =>
    if isName n then match parseSuffix t ts with
      | .ok (t', r) => .ok ({ name := n, ty := t' }, r)
      | .error e => .error e
    else .error s!"`{n}` cannot be a member name"
  | .punct '{' :: _ => .error "unsupported C feature: record definitions inside a member \
      (define the record at top level)"
  | .punct '(' :: _ =>
    .error "unsupported C feature: function pointers and parenthesized declarators"
  | .punct ';' :: _ => .error "a member needs a name (anonymous members are not supported)"
  | _ => .error "expected a member name"

def parseDeclList (t : CTy) : Nat → List Token → Except String (List Field × List Token)
  | 0, _ => .error "parser fuel exhausted"
  | fuel + 1, ts => match parseDeclarator t ts with
    | .error e => .error e
    | .ok (f, .punct ';' :: r) => .ok ([f], r)
    | .ok (f, .punct ',' :: r) => match parseDeclList t fuel r with
      | .ok (fs, r') => .ok (f :: fs, r')
      | .error e => .error e
    | .ok (f, .punct ':' :: _) => .error s!"unsupported C feature: bit-fields (member `{f.name}`)"
    | .ok (f, _) => .error s!"expected `;` or `,` after member `{f.name}`"

def parseMembers : Nat → List Token → Except String (List Field × List Token)
  | 0, _ => .error "parser fuel exhausted"
  | _ + 1, .punct '}' :: r => .ok ([], r)
  | fuel + 1, ts => match parseSpec ts with
    | .error e => .error e
    | .ok (t, r₁) => match parseDeclList t fuel r₁ with
      | .error e => .error e
      | .ok (fs, r₂) => match parseMembers fuel r₂ with
        | .error e => .error e
        | .ok (gs, r) => .ok (fs ++ gs, r)

def parseRecord (fuel : Nat) : List Token → Except String (Decl × List Token)
  | .ident w :: .ident tag :: .punct '{' :: ms =>
    match kindOfWord? w with
    | none => .error s!"expected `struct` or `union`, found `{w}`"
    | some k =>
      if !isName tag then .error s!"`{tag}` is not a valid tag name" else
      match parseMembers fuel ms with
      | .error e => .error e
      | .ok ([], _) => .error s!"`{tag}` has no members (empty records are a GNU extension)"
      | .ok (f :: fs, .punct ';' :: r) => .ok ({ kind := k, tag, fields := f :: fs }, r)
      | .ok (_, .ident w :: _) => match unsupportedWords.find? (·.1 == w) with
        | some (_, why) => .error s!"unsupported C feature: {why} (`{w}`)"
        | none => .error s!"expected `;` after the definition of `{tag}` \
            (declaring objects is not supported)"
      | .ok (_, _) => .error s!"expected `;` after the definition of `{tag}` \
          (declaring objects is not supported)"
  | .ident _ :: .ident tag :: .punct ';' :: _ =>
    .error s!"unsupported C feature: forward declarations (`{tag}`)"
  | .punct '#' :: _ => .error "unsupported C feature: preprocessor directives (`#`)"
  | .ident w :: _ => match unsupportedWords.find? (·.1 == w) with
    | some (_, why) => .error s!"unsupported C feature: {why} (`{w}`)"
    | none => .error s!"expected a struct or union definition, found `{w}`"
  | _ => .error "expected a struct or union definition"

def parseUnit : Nat → List Token → Except String Env
  | 0, _ => .error "parser fuel exhausted"
  | _ + 1, [] => .ok []
  | fuel + 1, ts => match parseRecord fuel ts with
    | .error e => .error e
    | .ok (d, r) => match parseUnit fuel r with
      | .error e => .error e
      | .ok ds => .ok (d :: ds)

/-- Parse a record source: lex, parse, check scopes. Fuel is the token count plus one. -/
def parse (src : String) : Except String Env :=
  match lex src with
  | .error e => .error e
  | .ok ts => match parseUnit (ts.length + 1) ts with
    | .error e => .error e
    | .ok env => match checkScope [] env with
      | .error e => .error e
      | .ok () => .ok env

end Silmaril.Data.Layout.Source
