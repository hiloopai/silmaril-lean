module

public import Silmaril.Compiler.Clang.AST.Defs
public import Silmaril.Compiler.Clang.Bitfield.Defs
public import Silmaril.Compiler.Clang.Builtin.Defs
public import Silmaril.Compiler.Clang.Type.Defs
public import Silmaril.Compiler.Clang.Vector.Defs
public import Silmaril.Compiler.Clang.Complex.Defs
public import Silmaril.Compiler.Clang.Stack.Defs
public import Silmaril.Cerberus.Ail.Syntax.Defs
public import Std.Data.HashMap
public import Std.Data.HashSet

/-! # Clang AST → typed Ail

The translation of the Clang frontend: a `TranslationUnitDecl` of
`Silmaril.Clang.AST` to `Silmaril.Cerberus.Ail.TypedProgram`, the entry point the Cerberus route
uses, so everything downstream (csem's C0/C1/C2 semantics, the `checkC0`/`checkC1` validators,
ccomp's Ail → Mir, the proved backend) is unchanged.

Rules (campaign `cfront-clang`, brief.md):

* **Pure.** No IO of any kind; the translation is a function of the Clang AST only. It never calls
  Cerberus, never reads Cerberus's Ail, and imports nothing of Cerberus's frontend
  (`Silmaril.Cerberus.Frontend`, the Cabs parser) or of the compiler (`Silmaril.Compile`).
* **Fail-closed.** A construct the translation does not handle is an `.error` naming it; never a
  guess, never a silently dropped node.
* **Clang's conversions are kept.** Clang has already inserted the implicit conversions and
  integer promotions (`ImplicitCastExpr` with its `castKind`); the translation turns each into the
  corresponding typed-Ail form (`AilErvalue`, `AilEarray_decay`, `AilEfunction_decay`, `AilEcast`,
  …) and never re-derives them.
* **Typed Ail as Cerberus prints it.** The result must decode, print and compile like an oracle
  document (`cerb-oracle --level tail`): `Silmaril.Cerberus.Ail.Codec.printTailDocument`.
  Matching Cerberus's own desugaring (e.g. `for` → `while`, symbol order) makes the differential
  comparison (`ail_agree`) exact.

## Declarations (this file)

* **Types.** Every type is read from its spelling (`Silmaril.Clang.Type`) and resolved here:
  builtin specifiers to Cerberus's integer and floating types (LP64, `char` signed), typedef names
  through the typedefs seen so far (the type a typedef names, never the typedef itself, as in
  Cerberus's Ail), and Cerberus's builtin typedefs of `cerb-prelude.h` (`__cerbty_size_t` …) and
  Clang's own sugar (`__size_t`, `__ptrdiff_t`) to Cerberus's `Size_t`, `Ptrdiff_t`, `IntN_t` ….
* **Symbols** are numbered by first occurrence in the translation unit (never from Clang's node
  ids, which are pointers). One symbol per entity: a redeclaration (`previousDecl`) reuses it.
* **Skipped**: Clang's implicit declarations (builtin typedefs, implicitly declared library
  functions) and the declarations of `cerb-prelude.h`, which Cerberus has built in.
  `Node.children` also excludes opaque documentation comments; their contents never enter
  translation or affect symbol numbering.
* **Sigma.** Declarations in order of first declaration, with the latest declaration's type;
  object definitions (initialisers, and the zero constant of a tentative definition, STD
  §6.9.2#2); function definitions; struct and union definitions; the external identifiers
  (external linkage only, in key order) and the typedef symbols. The startup symbol is a defined
  external function `main`.

## Statements and expressions

The expression/statement and aggregate-initializer translators are reused from an earlier candidate translator.
Struct/union members are resolved by declaration id and checked against the operand's tag.
Block and for scopes restore visible typedefs and tags while retaining each tag's definition
in sigma. Enum constants use Clang's evaluated values with layout guards. Bit-fields use
checked storage-unit lowering; anonymous members get synthesized member names; packed
structs use checked byte layouts; flexible-array initializers remain fail-closed. GNU vectors
are lane structs whose operators are calls of synthesized functions (`Silmaril.Clang.Vector`).

Baseline: the stub rejected every program, so the campaign starts trivially sound.
-/

@[expose] public section

namespace Silmaril.Clang.ToAil

open Silmaril.Cerberus Ail

/-! ## State -/

/-- The digest of every symbol of a translation (Cerberus uses the MD5 of the C file, which the
frontend does not see; any fixed digest distinct from the runtime library's works). -/
def digest : Digest :=
  ⟨[0x63, 0x66, 0x72, 0x6f, 0x6e, 0x74, 0x2d, 0x63, 0x6c, 0x61, 0x6e, 0x67, 0x00, 0x00, 0x00, 0x01]⟩

/-- An entity with external or internal linkage (a function or an object at file scope). -/
structure Global where
  sym : Sym
  name : String
  isFunction : Bool
  /-- Internal linkage (`static`): not an external identifier. -/
  isStatic : Bool
  /-- The first declaration was a definition (Cerberus's `Decl_function` flag is its negation). -/
  firstIsDefinition : Bool
  decl : Declaration
  kind : IdKind
  /-- An object with an initialiser. -/
  hasObjectDefinition : Bool := false
  inline_ : Bool := false
  noreturn : Bool := false
  /-- A block-scope `static` object (no linkage; Cerberus declares it in sigma where it meets it). -/
  blockScope : Bool := false
  /-- Created on demand for a direct library builtin call. -/
  libraryBuiltin : Bool := false
  /-- Preserve type attributes for prototype checks when a libc symbol is reused. -/
  functionSpelling : Option String := none

/-- An unnamed struct, union or enum not yet named by a type spelling. -/
structure PendingTag where
  keyword : String
  /-- The column of its location, which Clang's `(unnamed at FILE:LINE:COL)` ends with. -/
  col : Option Nat
  sym : Sym
  declId : String

/-- A body that partial translation omitted; the function remains declared. -/
structure SkippedFunction where
  name : String
  reason : String
  deriving Repr

/-- Original members of a byte-layout struct, in initializer order. -/
structure PackedField where
  name : Identifier
  off : Nat
  ty : Ctype

structure PackedRecord where
  fields : Array PackedField
  size : Nat
  align : Nat

/-- An object declared with more than its type's natural alignment, stored as a wrapper struct
whose one member carries the alignment. -/
structure AlignedObject where
  tag : Sym
  member : Identifier
  align : Nat
  ty : Ctype

/-- What an ordinary identifier declared at block scope or as a parameter names, for the
bound of a variable-length array, which Clang spells by name only. -/
inductive LocalName where
  /-- An object of automatic storage duration and its type. -/
  | object (s : Sym) (t : Ctype)
  | typedefName
  /-- A static or extern object, a function or an enumerator. -/
  | other

/-- A function that uses the dynamic stack (`Silmaril.Clang.Stack`). -/
structure StackFrame where
  /-- The local holding the top at the function's entry. -/
  base : Sym
  ret : Ctype
  /-- Whether the function declares variable-length arrays (else it calls `alloca`). -/
  vla : Bool

structure St where
  /-- Only body failures may be recovered; declaration errors are always fatal. -/
  partialBodies : Bool := false
  skippedFunctions : Array SkippedFunction := #[]
  next : Nat := 0
  /-- Clang declaration id → symbol: globals, their redeclarations, parameters, tags. -/
  declSyms : Std.HashMap String Sym := {}
  globals : Array Global := #[]
  /-- Symbol number → index in `globals`. -/
  globalIdx : Std.HashMap Nat Nat := {}
  typedefs : Std.HashMap String (Qualifiers × Ctype) := {}
  typedefDeclTypes : Std.HashMap String (Qualifiers × Ctype) := {}
  typedefSyms : Array Sym := #[]
  /-- Stronger alignment carried by a GNU aligned typedef (its size stays unchanged). -/
  typedefAligns : Std.HashMap String Nat := {}
  /-- Explicit object/member alignment, for GNU alignof on an expression. -/
  declAligns : Std.HashMap String Nat := {}
  /-- `struct S`, `union (unnamed at …)`, `enum E` → the tag's symbol. -/
  tags : Std.HashMap String Sym := {}
  /-- Tags declared in the current lexical scope, distinct from visible outer tags. -/
  scopeTags : Std.HashSet String := {}
  localScope : Bool := false
  /-- Field declaration ids identify members independently of their spelling. -/
  fields : Std.HashMap String (Sym × Identifier) := {}
  /-- Unnamed tags not yet named by a spelling, innermost last. -/
  pending : List PendingTag := []
  /-- An anonymous struct or union member's (implicit) field declaration id → the member name
  it is given. -/
  anonMembers : Std.HashMap String String := {}
  /-- Tag symbol number → its definition (struct and union). -/
  tagDefIdx : Std.HashMap Nat TagDefinition := {}
  /-- Original fields of structs represented by one byte array. -/
  packedRecords : Std.HashMap Nat PackedRecord := {}
  /-- Object symbol number → the wrapper struct that carries its declared alignment. -/
  alignedObjects : Std.HashMap Nat AlignedObject := {}
  /-- Records whose alignment was requested (gcc's `TYPE_USER_ALIGN`), which C11 `_Alignof`
  of the type reports in full. -/
  userAligned : Std.HashSet Nat := {}
  tagDefs : Array (Sym × (Cerberus.Loc × Attributes × TagDefinition)) := #[]
  objectDefinitions : Array (Sym × TypedExpression) := #[]
  functionDefinitions : Array (Sym × FunctionDefinition GenTypeCategory) := #[]
  /-- Enumerator declaration id → its value. -/
  enumConsts : Std.HashMap String Int := {}
  /-- Enum tag symbol number (a defined enum) → whether gcc's and Clang's integer type for it is
  signed (`int`: some enumerator is negative) rather than `unsigned int`. -/
  enumSigned : Std.HashMap Nat Bool := {}
  /-- Symbol numbers of objects declared `register`. -/
  registers : Std.HashSet Nat := {}
  /-- Parameter symbol number → the qualifiers its function's declaration gives it (Cerberus
  types a parameter as its function's declaration does). -/
  paramQuals : Std.HashMap Nat Qualifiers := {}
  /-- Label declaration id → the label's symbol (per function). -/
  labels : Std.HashMap String Sym := {}
  /-- Enclosing loops, innermost first: the label a `continue` jumps to (none when the loop has
  no `continue`). -/
  loops : List (Option Sym) := []
  /-- Fresh synthetic opaque-value id → a lifted statement-expression result. -/
  liftedValues : Std.HashMap String TypedExpression := {}
  /-- Bit-field declaration id → where it is stored (`Silmaril.Clang.Bitfield`). -/
  bitfields : Std.HashMap String Bitfield.Field := {}
  /-- Struct symbol number (a struct with bit-fields) → what its initialiser lists initialise, in
  order: an ordinary member or a named bit-field. -/
  bitSlots : Std.HashMap Nat (Array (Identifier ⊕ Bitfield.Field)) := {}
  /-- GNU vectors (`Silmaril.Clang.Vector`): a lane type and lane count, or a bit cast's pair of
  types (`pun/…`) → its lane struct or union. -/
  vectorTags : Std.HashMap String Sym := {}
  /-- A lane struct's symbol number → its lane type and lane count. -/
  vectorLanes : Std.HashMap Nat (Ctype × Nat) := {}
  /-- Synthesized vector operations: operator and types → the function's symbol. -/
  vectorHelpers : Std.HashMap String Sym := {}
  /-- Synthesized complex pair tags, keyed by component type. -/
  complexTags : Std.HashMap String Sym := {}
  /-- Complex pair tag number → real component type. -/
  complexParts : Std.HashMap Nat Ctype := {}
  /-- Synthesized functions of semantic builtins (`Silmaril.Clang.Builtin`): builtin and
  operand types → the function's symbol. -/
  builtinHelpers : Std.HashMap String Sym := {}
  /-- Translating the initialiser of an object of static storage duration, which must stay a
  constant expression (no synthesized call). -/
  staticInit : Bool := false
  /-- The ordinary identifiers in scope in the current function, innermost declaration. -/
  localNames : Std.HashMap String LocalName := {}
  /-- The current function's use of the dynamic stack. -/
  stack : Option StackFrame := none
  /-- The arena and its top (`Silmaril.Clang.Stack`), once used. -/
  arena : Option (Sym × Sym) := none
  /-- End marks of the variable-length arrays in scope, innermost first. -/
  stackMarks : List Sym := []
  /-- A variable-length array's pointer (symbol number) → its element type and length local. -/
  vlas : Std.HashMap Nat (Qualifiers × Ctype × Sym) := {}

abbrev M := StateT St (Except String)

def fresh (d : SymbolDescription) : M Sym :=
  modifyGet fun st => (⟨digest, st.next, d⟩, { st with next := st.next + 1 })

def freshNat : M Nat := modifyGet fun st => (st.next, { st with next := st.next + 1 })

/-- Lexical type names are restored when a block or for declaration leaves scope.
Tag definitions and declaration-id bindings remain in sigma for expressions already translated. -/
def withScope {α : Type} (action : M α) : M α := do
  let saved ← get
  modify fun st => { st with scopeTags := {}, localScope := true }
  let result ← action
  modify fun st => { st with
    typedefs := saved.typedefs, typedefAligns := saved.typedefAligns, tags := saved.tags,
    pending := saved.pending, scopeTags := saved.scopeTags, localScope := saved.localScope,
    localNames := saved.localNames, stackMarks := saved.stackMarks }
  return result

def noQuals : Qualifiers := ⟨false, false, false⟩

def noAttrs : Attributes := .mk []

def quals (q : Type.Quals) : Qualifiers := ⟨q.const, q.restrict, q.volatile⟩

def qunion (a b : Qualifiers) : Qualifiers :=
  ⟨a.const || b.const, a.restrict || b.restrict, a.volatile || b.volatile⟩

def ct (n : CtypeNode) : Ctype := .mk [] n

def intTy (t : IntegerType) : Ctype := ct (.basic (.integer t))

/-! ## Types -/

/-- Builtin specifiers in Clang's spelling. -/
def builtinType : String → Option CtypeNode
  | "void" => some .void
  | "char" => some (.basic (.integer .char))
  | "signed char" => some (.basic (.integer (.signed .ichar)))
  | "unsigned char" => some (.basic (.integer (.unsigned .ichar)))
  | "short" => some (.basic (.integer (.signed .short)))
  | "unsigned short" => some (.basic (.integer (.unsigned .short)))
  | "int" => some (.basic (.integer (.signed .int)))
  | "unsigned int" => some (.basic (.integer (.unsigned .int)))
  | "long" => some (.basic (.integer (.signed .long)))
  | "unsigned long" => some (.basic (.integer (.unsigned .long)))
  | "long long" => some (.basic (.integer (.signed .longLong)))
  | "unsigned long long" => some (.basic (.integer (.unsigned .longLong)))
  | "_Bool" => some (.basic (.integer .bool))
  | "float" => some (.basic (.floating (.realFloating .float)))
  | "double" => some (.basic (.floating (.realFloating .double)))
  | "long double" => some (.basic (.floating (.realFloating .longDouble)))
  | _ => none

/-- Cerberus's builtin typedefs (`cerb-prelude.h` declares them for Clang) and Clang's sugar for
the types of `sizeof` and pointer subtraction. -/
def builtinTypedef : String → Option IntegerType
  | "__cerbty_uint16_t" => some (.unsigned (.intN 16))
  | "__cerbty_uint32_t" => some (.unsigned (.intN 32))
  | "__cerbty_uint64_t" => some (.unsigned (.intN 64))
  | "__cerbty_size_t" => some .size
  | "__cerbty_ptrdiff_t" => some .ptrdiff
  | "__cerbty_intptr_t" => some (.signed .intptr)
  | "__cerbty_uintptr_t" => some (.unsigned .intptr)
  | "__cerbty_intmax_t" => some (.signed .intmax)
  | "__cerbty_uintmax_t" => some (.unsigned .intmax)
  | "__cerbty_wchar_t" => some .wchar
  | "__size_t" => some .size
  | "__ptrdiff_t" => some .ptrdiff
  | _ => none

/-- The declarations of `cerb-prelude.h` other than the typedefs. -/
def preludeFunctions : List String :=
  ["__cerb_va_start", "__cerb_va_copy", "__cerb_va_end", "__cerb_va_arg_ptr"]

/-- Name an unnamed tag by its spelling `(unnamed at FILE:LINE:COL)`: the innermost pending
unnamed tag of the same keyword, whose column must match. -/
def bindUnnamed (keyword key spelling : String) : M Sym := do
  let st ← get
  let col := (String.ofList spelling.toList.dropLast).splitOn ":" |>.getLast? |>.bind (·.toNat?)
  -- the innermost one that matches: an unnamed tag is named by the declarators that follow it
  match st.pending.find? fun p => p.keyword == keyword && p.col == col with
  | some p =>
    set { st with pending := st.pending.filter (·.declId != p.declId),
                  tags := st.tags.insert key p.sym }
    return p.sym
  | none => throw s!"cannot identify the tag {key}"

def tagSym (keyword name : String) : M Sym := do
  let key := keyword ++ " " ++ name
  if let some s := (← get).tags[key]? then return s
  -- an anonymous member's tag is known from its member declaration
  if (name.splitOn "::").length > 1 then throw s!"unknown anonymous member type {key}"
  if name.startsWith "(" then bindUnnamed keyword key name
  else
    -- a reference before any declaration (`struct S *p;`) declares the tag
    let s ← fresh (.id name)
    modify fun st => { st with tags := st.tags.insert key s }
    return s

/-- The lane struct of a GNU vector of `n` lanes of `t`, defined on first use. -/
def vectorTag (t : Ctype) (n : Nat) : M Sym := do
  let .mk _ node := t
  let t := ct node
  let size ← match Vector.laneSize t with
    | .ok k => pure k
    | .error e => throw e
  unless n > 0 do throw "a vector of no lanes"
  let key := s!"{reprStr node}/{n}"
  let st ← get
  if let some s := st.vectorTags[key]? then return s
  let s ← fresh (.id s!"__cfront_vector{st.vectorTags.size}")
  -- gcc's alignment of the vector, never weaker than ccomp's of a lane
  let natural ← match Bitfield.sizeAlign {} t with
    | .ok (_, a) => pure a
    | .error e => throw e
  let d := TagDefinition.struct (Vector.members t n (max (n * size) natural)) none
  modify fun st => { st with
    vectorTags := st.vectorTags.insert key s, vectorLanes := st.vectorLanes.insert s.number (t, n),
    tagDefIdx := st.tagDefIdx.insert s.number d, tagDefs := st.tagDefs.push (s, (.unknown, noAttrs, d)) }
  return s

/-- Complex types have two real components; unsupported component types reject here. -/
def complexTag (word : String) : M Sym := do
  let t ← match word with
    | "float" => pure (ct (.basic (.floating (.realFloating .float))))
    | "double" => pure (ct (.basic (.floating (.realFloating .double))))
    | _ => throw s!"complex component type {word} is not supported"
  if let some s := (← get).complexTags[word]? then return s
  let s ← fresh (.id s!"__cfront_complex_{word}")
  let d := TagDefinition.struct (Complex.members t) none
  modify fun st => { st with
    complexTags := st.complexTags.insert word s, complexParts := st.complexParts.insert s.number t,
    tagDefIdx := st.tagDefIdx.insert s.number d, tagDefs := st.tagDefs.push (s, (.unknown, noAttrs, d)) }
  return s

def leafType : Type.Leaf → M (Qualifiers × Ctype)
  | .builtin w => do
    if w.startsWith "_Complex " then
      return (noQuals, ct (.struct (← complexTag (String.ofList (w.toList.drop 9)))))
    match builtinType w with
    | some n => return (noQuals, ct n)
    | none => throw s!"type specifier {w} is not supported"
  | .typedefName n => do
    if let some it := builtinTypedef n then return (noQuals, intTy it)
    match (← get).typedefs[n]? with
    | some t => return t
    | none => throw s!"unknown typedef name {n}"
  | .tag kw n => do
    let s ← tagSym kw n
    match kw with
    | "struct" => return (noQuals, ct (.struct s))
    | "union" => return (noQuals, ct (.union s))
    | _ => return (noQuals, intTy (.enum s))
  | .vector n l => do
    let (q, t) ← leafType l
    unless q == noQuals do throw "a vector of qualified lanes"
    return (noQuals, ct (.struct (← vectorTag t n)))

/-- Width in bits and signedness of an integer type (LP64, `char` signed). -/
def intShape : IntegerType → Except String (Nat × Bool)
  | .char => return (8, true)
  | .bool => return (1, false)
  | .signed b => return (← baseBits b, true)
  | .unsigned b => return (← baseBits b, false)
  | .enum _ => return (32, true)
  | .size => return (64, false)
  | .ptrdiff => return (64, true)
  | _ => throw "integer type"
where
  baseBits : IntegerBaseType → Except String Nat
    | .ichar => return 8 | .short => return 16 | .int => return 32 | .long => return 64
    | .longLong => return 64 | .intN n => return n | .intptr => return 64 | .intmax => return 64
    | _ => throw "integer type"

/-- The value `v` converted to an integer type (STD §6.3.1.3, modulo for signed types as gcc). -/
def wrap (it : IntegerType) (v : Int) : Except String Int := do
  if it == .bool then return if v == 0 then 0 else 1
  let (w, s) ← intShape it
  let m : Int := 2 ^ w
  let r := v % m
  let r := if r < 0 then r + m else r
  return if s && r ≥ 2 ^ (w - 1) then r - m else r

/-- Clang's folded layout constants are usable only where its LP64 layout agrees
with the Ail consumer. The pinned consumer stores float and long double in eight
bytes; reject folds depending on those types instead of mixing layouts. Pointee
layout does not affect a pointer's size. Fuel also rejects recursive aggregates.
A packed byte layout is checked through its original members. -/
def checkFoldedType : Nat → Ctype → M Unit
  | 0, _ => throw "folded constant: recursive layout"
  | fuel + 1, .mk _ ty => do
    match ty with
    | .basic (.integer _) | .pointer _ _ => pure ()
    | .basic (.floating (.realFloating .double)) => pure ()
    | .array t (some _) => checkFoldedType fuel t
    | .struct s | .union s =>
      if let some r := (← get).packedRecords[s.number]? then
        return ← r.fields.forM fun f => checkFoldedType fuel f.ty
      match (← get).tagDefIdx[s.number]? with
      | some (.struct ms fam) =>
        if ms.isEmpty then throw "folded constant: empty struct layout"
        ms.forM fun (_, (_, _, _, t)) => checkFoldedType fuel t
        if let some (.mk _ _ _ t) := fam then checkFoldedType fuel t
      | some (.union ms) =>
        if ms.isEmpty then throw "folded constant: empty union layout"
        ms.forM fun (_, (_, _, _, t)) => checkFoldedType fuel t
      | none => throw "folded constant: incomplete record layout"
    | _ => throw "folded constant: layout differs or is unsupported"

/-- A value while evaluating an array bound: an integer of width `w` and signedness `s`, or an
address relative to the null pointer (`&((T *)0)->m` folds to `m`'s offset) as a pointer to or an
lvalue of a type. -/
inductive BoundVal where
  | int (v : Int) (w : Nat) (s : Bool)
  | ptr (t : Ctype) (off : Int)
  | lval (t : Ctype) (off : Int)

/-- ccomp's size and alignment of a type whose layout an array bound depends on; the layout must
agree with Clang's (`checkFoldedType`), since Clang accepted the program by its own. -/
def boundLayout (t : Ctype) : M (Nat × Nat) := do
  checkFoldedType 64 t
  match Bitfield.sizeAlign (← get).tagDefIdx t with
  | .ok r => return r
  | .error e => throw s!"array bound: {e}"

/-- An integer of an operation's type: unsigned arithmetic wraps, signed overflow is rejected. -/
def boundInt (v : Int) (w : Nat) (s : Bool) : M BoundVal := do
  if s then
    unless -2 ^ (w - 1) ≤ v && v < 2 ^ (w - 1) do throw "array bound: signed overflow"
    return .int v w s
  else return .int (v % 2 ^ w) w s

/-- The type of a decimal literal with a suffix (STD §6.4.4.1#5, LP64). -/
def literalShape (n : Nat) : String → M (Nat × Bool)
  | "" => if n < 2 ^ 31 then return (32, true) else if n < 2 ^ 63 then return (64, true)
    else throw "array bound: literal out of range"
  | "U" => return if n < 2 ^ 32 then (32, false) else (64, false)
  | "L" | "LL" => if n < 2 ^ 63 then return (64, true) else throw "array bound: literal out of range"
  | "UL" | "LU" | "ULL" | "LLU" => return (64, false)
  | sfx => throw s!"array bound: integer suffix {sfx}"

/-- The integer promotions and usual arithmetic conversions on widths and signedness (LP64:
every type narrower than `int` promotes to `int`). -/
def promoteShape (w : Nat) (s : Bool) : Nat × Bool := if w < 32 then (32, true) else (w, s)

def commonShape (a b : Nat × Bool) : Nat × Bool :=
  let (wa, sa) := promoteShape a.1 a.2
  let (wb, sb) := promoteShape b.1 b.2
  if sa == sb then (max wa wb, sa)
  else
    let (wu, ws) := if sa then (wb, wa) else (wa, wb)
    if wu ≥ ws then (wu, false) else (ws, true)

/-- A member of a struct or union: its offset and type. -/
def memberAt (t : Ctype) (m : String) : M (Nat × Ctype) := do
  let _ ← boundLayout t
  let defs := (← get).tagDefIdx
  match t with
  | .mk _ (.struct s) =>
    if let some r := (← get).packedRecords[s.number]? then
      let some f := r.fields.find? (·.name.name == m) | throw s!"array bound: no member {m}"
      return (f.off, f.ty)
    let some (.struct ms fam) := defs[s.number]? | throw "array bound: incomplete struct"
    let (offs, _, _) ← match Bitfield.structLayout defs ms fam with
      | .ok r => pure r
      | .error e => throw s!"array bound: {e}"
    match (ms.zip offs).find? (·.1.1.name == m) with
    | some ((_, (_, _, _, mt)), off) => return (off, mt)
    | none => throw s!"array bound: no member {m}"
  | .mk _ (.union s) =>
    let some (.union ms) := defs[s.number]? | throw "array bound: incomplete union"
    match ms.find? (·.1.name == m) with
    | some (_, (_, _, _, mt)) => return (0, mt)
    | none => throw s!"array bound: no member {m}"
  | _ => throw s!"array bound: member {m} of a non-record type"

/-- Aligned aliases in a function type need an ABI representation Ail lacks. -/
partial def hasAlignedAlias : Type.TypeSpelling → M Bool
  | .leaf _ (.typedefName name) => return (← get).typedefAligns.contains name
  | .pointer _ t | .array t _ | .arrayExpr t _ => hasAlignedAlias t
  | .function r ps _ => do
    if ← hasAlignedAlias r then return true
    for p in ps.getD [] do
      if ← hasAlignedAlias p then return true
    return false
  | _ => return false

mutual

/-- A type spelling as Cerberus's qualified C type: the qualifiers of an array are those of its
element type. -/
partial def resolve : Type.TypeSpelling → M (Qualifiers × Ctype)
  | .leaf q l => do
    let (q', t) ← leafType l
    return (qunion (quals q) q', t)
  | .pointer q t => do
    let (q', t') ← resolve t
    return (quals q, ct (.pointer q' t'))
  | .array e n => do
    let (q', t') ← resolve e
    return (q', ct (.array t' (n.map Int.ofNat)))
  | .arrayExpr e b => do
    let (q', t') ← resolve e
    let .int v _ _ ← boundValue b | throw "array bound: not an integer"
    unless v > 0 do throw s!"array bound: size {v}"
    return (q', ct (.array t' (some v)))
  | .function r ps v => do
    if ← hasAlignedAlias (.function r ps v) then
      throw "aligned typedef in a function type is not supported"
    let r' ← resolve r
    match ps with
    | none => return (noQuals, ct (.functionNoParams r'))
    | some ps =>
      let ps' ← ps.mapM fun p => do
        let (q, t) ← resolve p
        pure (q, t, false)
      return (noQuals, ct (.function r' ps' v))

/-- Evaluate an array bound as gcc and Clang fold it, with ccomp's layout where it agrees with
theirs (`boundLayout`). -/
partial def boundValue : Type.BoundExpr → M BoundVal
  | .num n sfx => do
    let (w, s) ← literalShape n sfx
    return .int n w s
  | .sizeofType t => do
    let (_, t) ← resolve t
    return .int (← boundLayout t).1 64 false
  | .cast t e => do
    let (_, t) ← resolve t
    let v ← boundValue e
    match t, v with
    | .mk _ (.basic (.integer it)), .int x .. | .mk _ (.basic (.integer it)), .ptr _ x => do
      let (w, s) ← intShape it
      return .int (← wrap it x) w s
    | .mk _ (.pointer _ p), .int x .. | .mk _ (.pointer _ p), .ptr _ x => return .ptr p x
    | _, _ => throw "array bound: unsupported cast"
  | .addrOf e => do
    let .lval t off ← boundValue e | throw "array bound: & of a non-lvalue"
    return .ptr t off
  | .member e arrow m => do
    let (t, off) ← match arrow, ← boundValue e with
      | true, .ptr t off | false, .lval t off => pure (t, off)
      | _, _ => throw s!"array bound: member {m} of a non-record"
    let (moff, mt) ← memberAt t m
    return .lval mt (off + moff)
  | .neg e => do
    let .int x w s ← boundValue e | throw "array bound: - of a non-integer"
    let (w, s) := promoteShape w s
    boundInt (-x) w s
  | .binary op a b => do
    match op, ← boundValue a, ← boundValue b with
    | '-', .ptr t x, .ptr _ y =>
      -- `(char *)&((T *)0)->m - (char *)0`: Clang accepted the difference, so the pointees are
      -- compatible; the result is a `ptrdiff_t` (STD §6.5.6#9), exact as gcc divides it
      let (sz, _) ← boundLayout t
      unless sz > 0 && (x - y) % sz == 0 do throw "array bound: inexact pointer difference"
      boundInt ((x - y) / sz) 64 true
    | _, .int x wa sa, .int y wb sb =>
      let (w, s) := commonShape (wa, sa) (wb, sb)
      -- both operands converted to the common type
      let x := if s then x else x % 2 ^ w
      let y := if s then y else y % 2 ^ w
      match op with
      | '+' => boundInt (x + y) w s
      | '-' => boundInt (x - y) w s
      | '*' => boundInt (x * y) w s
      | '/' => if y == 0 then throw "array bound: division by zero" else boundInt (x.tdiv y) w s
      | '%' => if y == 0 then throw "array bound: division by zero" else boundInt (x.tmod y) w s
      | _ => throw s!"array bound: operator {op}"
    | _, _, _ => throw "array bound: arithmetic on a non-integer"
  | .var x => throw s!"array bound {x}: a variable-length array is not supported here"

end

def parseType (s : String) : M (Qualifiers × Ctype) := do
  match Type.parse s with
  | .ok t => resolve t
  | .error e => throw e

def headerType (h : Header) : M (Qualifiers × Ctype) := do
  let some t := h.type | throw s!"{h.kind} {h.id} has no type"
  if let some id := t.typeAliasDeclId then
    if let some (q, ty) := (← get).typedefDeclTypes[id]? then
      match Type.parse t.qualType with
      | .ok (.leaf extra (.typedefName _)) => return (qunion (quals extra) q, ty)
      | _ => throw s!"typedef reference with an unsupported spelling {t.qualType}"
  -- GNU typeof operands need not be type spellings (e.g. `typeof (x++)`). Clang
  -- supplies their resolved type; do not evaluate the operand or guess its type.
  -- Try the spelling first to retain typedef sugar in ordinary types. A resolved
  -- variable-length or otherwise unsupported type still fails in parseType.
  try parseType t.qualType catch err =>
    if (t.qualType.splitOn " ").contains "typeof" then
      if let some resolved := t.desugaredQualType then return ← parseType resolved
    throw err

/-! ## Expressions and statements -/

def isAttr (n : Node) : Bool := (n.kind?.map fun k => (Kind.toString k).endsWith "Attr").getD false

/-- The tag a typedef's type node names, if it is a struct, union or enum. -/
partial def namedTag? (n : Node) : Option DeclRef :=
  match n.kind? with
  | some .recordType | some .enumType => n.header?.bind (·.decl)
  | some .elaboratedType => n.children[0]?.bind namedTag?
  | _ => none


def stmt (n : StatementNode GenTypeCategory) : TypedStatement :=
  .mk .unknown ⟨false, none⟩ noAttrs n

def rvalue (t : GenType) (n : ExpressionNode GenTypeCategory) : TypedExpression :=
  .mk (.rvalue t) [] .unknown n

def mkExpr (a : GenTypeCategory) (n : ExpressionNode GenTypeCategory) : TypedExpression :=
  .mk a [] .unknown n

def intGen (t : IntegerType) : GenType := .basic (.integer (.concrete t))

def int_ : GenType := intGen (.signed .int)

/-- The type of an rvalue of a C type (its qualifiers dropped, STD §6.3.2.1#2). -/
def genOf : Ctype → Except String GenType
  | .mk _ .void => return .void
  | .mk _ (.basic (.integer it)) => return intGen it
  | .mk _ (.basic (.floating ft)) => return .basic (.floating ft)
  | .mk _ (.pointer q t) => return .pointer q t
  | .mk _ (.array e n) => return .array e n
  | .mk _ (.function r ps v) => return .function r ps v
  | .mk _ (.functionNoParams r) => return .functionNoParams r
  | .mk _ (.struct s) => return .struct s
  | .mk _ (.union s) => return .union s
  | _ => throw "an expression of an unsupported type"

/-- A function type as Cerberus's declarations and designators carry it: the parameters'
`const` and `volatile` are not part of it (STD §6.7.6.3#15), `restrict` is kept. -/
def functionType : Ctype → Ctype
  | .mk as (.function r ps v) =>
    .mk as (.function r (ps.map fun (q, t, _) => ({ noQuals with restrict := q.restrict }, t, false)) v)
  | t => t

/-- The annotation of an expression of Clang's type and value category. A function designator
is an rvalue of function type, as in Cerberus's typing. -/
def annotOf (h : Header) (isRegister : Bool := false) : M GenTypeCategory := do
  let (q, t) ← headerType h
  match t with
  | .mk _ (.function ..) | .mk _ (.functionNoParams _) => return .rvalue (← genOf (functionType t))
  | _ =>
    if h.valueCategory == some "lvalue" then return .lvalue q t isRegister
    else return .rvalue (← genOf t)

/-- The type of an integer constant (STD §6.4.4.1#5, LP64): the first of the candidates of its
suffix and base that can represent it. -/
def constantType (v : Nat) (decimal : Bool) (sfx : Option IntegerSuffix) : Option IntegerType :=
  let cands : List IntegerType := match sfx, decimal with
    | none, true => [.signed .int, .signed .long, .signed .longLong]
    | none, false => [.signed .int, .unsigned .int, .signed .long, .unsigned .long,
        .signed .longLong, .unsigned .longLong]
    | some .u, _ => [.unsigned .int, .unsigned .long, .unsigned .longLong]
    | some .l, true => [.signed .long, .signed .longLong]
    | some .l, false => [.signed .long, .unsigned .long, .signed .longLong, .unsigned .longLong]
    | some .ul, _ => [.unsigned .long, .unsigned .longLong]
    | some .ll, true => [.signed .longLong]
    | some .ll, false => [.signed .longLong, .unsigned .longLong]
    | some .ull, _ => [.unsigned .longLong]
  cands.find? fun t => v < match t with
    | .signed .int => 2 ^ 31 | .unsigned .int => 2 ^ 32
    | .signed _ => 2 ^ 63 | _ => 2 ^ 64

def suffixesOfLength : Nat → List (Option IntegerSuffix)
  | 0 => [none] | 1 => [some .u, some .l] | 2 => [some .ul, some .ll] | 3 => [some .ull]
  | _ => []

/-- The suffix an integer literal was written with, which Cerberus keeps and Clang's JSON does
not print: the first spelling of the value, decimal then hexadecimal (with up to three leading
zeros) then octal, whose length is the token's length `tok` and whose type is Clang's. -/
def literalSuffix (t : IntegerType) (v : Nat) (tok : Option Nat) : Except String (Option IntegerSuffix) := do
  let dec := (toString v).length
  let hex := 2 + (Nat.toDigits 16 v).length
  let oct := 1 + (Nat.toDigits 8 v).length
  let spellings : List (Nat × Bool) :=
    [(dec, true), (hex, false), (hex + 1, false), (hex + 2, false), (hex + 3, false), (oct, false)]
  if let some n := tok then
    for (len, decimal) in spellings do
      if n ≥ len then
        for sfx in suffixesOfLength (n - len) do
          if constantType v decimal sfx == some t then return sfx
  -- otherwise the shortest suffix that gives a decimal or hexadecimal literal its type
  for sfx in [none, some .u, some .l, some .ul, some .ll, some .ull] do
    if constantType v true sfx == some t || constantType v false sfx == some t then return sfx
  throw "integer literal of an unexpected type"

/-- A node that begins inside a macro expansion. -/
def isMacro (h : Header) : Bool :=
  match h.range.map (·.begin) with
  | some (Clang.Loc.macro ..) => true
  | _ => false

/-- The length of the token a node starts with. -/
def tokLen (h : Header) : Option Nat :=
  match h.range.map (·.begin) with
  | some (Clang.Loc.bare l) => l.tokLen
  | some (Clang.Loc.macro s _) => s.tokLen
  | none => none

def basisOf (v : Int) : Basis := if v == 0 then .octal else .decimal

def intConst (v : Int) : TypedExpression :=
  rvalue int_ (.const (.integer (.iconstant v (basisOf v) none)))

def integerLiteral (h : Header) : M TypedExpression := do
  let some (.str vs) := h.value | throw s!"IntegerLiteral {h.id} without a value"
  let some v := vs.toNat? | throw s!"IntegerLiteral {h.id}: value {vs}"
  let (_, .mk _ (.basic (.integer it))) ← headerType h
    | throw s!"IntegerLiteral {h.id} of a non-integer type"
  let suffix ← literalSuffix it v (tokLen h)
  return rvalue (intGen it) (.const (.integer (.iconstant v (basisOf v) suffix)))

/-- An octal escape without leading zeros (Clang prints three digits; the source usually has
the shortest form, which Cerberus keeps). -/
def octalEscape (v : Nat) : String :=
  "\\" ++ String.ofList (Nat.toDigits 8 v)

/-- The spelling of a character of a character constant: the character, an escape, or its octal
escape. -/
def charLexeme (v : Nat) : String :=
  match v with
  | 10 => "\\n" | 9 => "\\t" | 13 => "\\r" | 0 => "\\0" | 92 => "\\\\" | 39 => "\\'"
  | 34 => "\\\""
  | _ => if 32 ≤ v && v < 127 then String.singleton (Char.ofNat v) else octalEscape v

/-- A spelling of exactly `len` characters, between the quotes, of a character constant of value
`v` (no reduction modulo 256): the character itself, a simple escape, an octal escape or a hex
escape with leading zeros; above 127, the character in UTF-8 (`L'Ä'`, Clang's input charset). -/
def charSpelling (v len : Nat) : Option String :=
  let simple : List (Nat × Char) := [(10, 'n'), (9, 't'), (13, 'r'), (7, 'a'), (8, 'b'), (12, 'f'),
    (11, 'v'), (27, 'e'), (92, '\\'), (39, '\''), (34, '"'), (63, '?')]
  let digits (b d : Nat) : String :=
    let ds := Nat.toDigits b v
    String.ofList (List.replicate (d - ds.length) '0' ++ ds)
  if 128 ≤ v && v < 0x110000 && !(0xD800 ≤ v && v < 0xE000) && (Char.ofNat v).utf8Size == len then
    some (String.singleton (Char.ofNat v))
  else if len == 1 then
    if 32 ≤ v && v < 127 && v != 39 && v != 92 then some (String.singleton (Char.ofNat v)) else none
  else if len == 2 && v != 0 && (simple.lookup v).isSome then
    (simple.lookup v).map fun c => String.ofList ['\\', c]
  else if 2 ≤ len && len ≤ 4 && v < 8 ^ (len - 1) then some ("\\" ++ digits 8 (len - 1))
  else if 3 ≤ len && v < 16 ^ (len - 2) then some ("\\x" ++ digits 16 (len - 2))
  else none

/-- A character constant of Clang's value: plain (`int`, as in C) or wide (`L'…'`, of `wchar_t`,
which is `int` here). Clang's JSON omits the prefix, so the token's length decides: a constant is
wide when its token spells its value with `L` and cannot spell it without. Below 128 both have the
same value; from 128 on a plain constant is a negative `char`, which Clang prints sign-extended to
32 bits (`'\xff'` is 4294967295, `L'\xff'` 255). -/
def characterLiteral (h : Header) : M TypedExpression := do
  let some (.int v) := h.value | throw s!"CharacterLiteral {h.id} without a value"
  let (_, t) ← headerType h
  unless t matches .mk _ (.basic (.integer (.signed .int))) do
    throw s!"CharacterLiteral {h.id} of type other than int (a wide or multi-byte constant)"
  if let some n := tokLen h then
    if 0 ≤ v && v < 2 ^ 31 && n ≥ 4 then
      let plain := v < 128 && (charSpelling v.toNat (n - 2)).isSome
      if let some lx := charSpelling v.toNat (n - 3) then
        if !plain then return rvalue int_ (.const (.character (some .wide, .utf8 lx)))
  let b ← if 0 ≤ v && v < 128 then pure v.toNat
    else if -128 ≤ v && v < 0 then pure (v + 256).toNat
    else if 2 ^ 32 - 128 ≤ v && v < 2 ^ 32 then pure (v - 2 ^ 32 + 256).toNat
    else throw s!"CharacterLiteral {h.id}: value {v} is not a byte"
  -- a negative `char` is a raw byte, an octal escape or a hex escape
  if 128 ≤ b && !(tokLen h == some 3 || ((tokLen h).bind fun n => charSpelling b (n - 2)).isSome) then
    throw s!"CharacterLiteral {h.id}: value {v} of a token of length {tokLen h}"
  return rvalue int_ (.const (.character (none, .utf8 (charLexeme b))))

/-- A decimal floating constant as Clang prints it (`d.dddE±x`): its digits `m` and the power of
ten `e` of its last digit. -/
def decimalParts (text : String) : Option (Nat × Int) := do
  let cs := text.toList
  let mant := cs.takeWhile fun c => c.isDigit || c == '.'
  let rest := cs.drop mant.length
  let ip := mant.takeWhile Char.isDigit
  let fp := match mant.drop ip.length with
    | '.' :: r => r
    | _ => []
  if mant.length != ip.length + (if fp.isEmpty && !mant.contains '.' then 0 else fp.length + 1) then none
  if ip.isEmpty && fp.isEmpty then none
  let m := (ip ++ fp).foldl (fun a c => a * 10 + (c.toNat - 48)) 0
  let x : Int ← match rest with
    | [] => some 0
    | c :: es =>
      if c != 'e' && c != 'E' then none
      let (neg, ds) := match es with
        | '-' :: r => (true, r)
        | '+' :: r => (false, r)
        | r => (false, r)
      if ds.isEmpty || !ds.all Char.isDigit then none
      let v : Int := ds.foldl (fun a c => a * 10 + (c.toNat - 48)) 0
      some (if neg then -v else v)
  return (m, x - fp.length)

/-- The binary32 value nearest to `m · 10 ^ e` (ties to even) as `q · 2 ^ E`, `q < 2 ^ 24`. -/
def binary32 (m : Nat) (e : Int) : Option (Nat × Int) := do
  if m == 0 then return (0, 0)
  let (num, den) := if e ≥ 0 then (m * 10 ^ e.toNat, 1) else (m, 10 ^ e.natAbs)
  let scaled (x : Int) : Nat × Nat :=
    if x ≥ 0 then (num, den * 2 ^ x.toNat) else (num * 2 ^ x.natAbs, den)
  let mut x : Int := (num.log2 : Int) - den.log2 - 23
  for _ in [0:4] do
    let (n, d) := scaled x
    if n / d ≥ 2 ^ 24 then x := x + 1
    else if n / d < 2 ^ 23 then x := x - 1
  if x < -149 then x := -149
  let (n, d) := scaled x
  let q := n / d
  let r := n % d
  let q := if 2 * r > d || (2 * r == d && q % 2 == 1) then q + 1 else q
  let (q, y) := if q == 2 ^ 24 then (2 ^ 23, x + 1) else (q, x)
  if y > 104 then none
  return (q, y)

def floatingLiteral (h : Header) : M TypedExpression := do
  let some (.str text) := h.value | throw s!"FloatingLiteral {h.id} without a value"
  let (_, t) ← headerType h
  let .mk _ (.basic (.floating (.realFloating ft))) := t
    | throw s!"FloatingLiteral {h.id} of a non-floating type"
  -- Clang prints the value in decimal, digits with an optional fraction and exponent
  let ok := text.toList.all fun c => c.isDigit || c == '.' || c == 'E' || c == 'e' || c == '+' || c == '-'
  unless ok && (text.toList.head?.map Char.isDigit).getD false do
    throw s!"FloatingLiteral {h.id}: value {text}"
  let suffix : Option FloatingSuffix := match ft with
    | .float => some .f | .double => none | .longDouble => some .l
  -- Clang prints a `float` with the digits that identify it as a float, not its exact value:
  -- its exact value in hexadecimal (`double`s are printed with 17 digits, which are exact)
  -- (unless the token is as long as Clang's text with the suffix: then it is that decimal)
  let asWritten := tokLen h == some (text.length + 1)
  let text ← if ft == .float && !asWritten then
      match decimalParts text >>= fun (m, e) => binary32 m e with
      | some (q, x) => pure s!"0x{String.ofList (Nat.toDigits 16 q)}p{x}"
      | none => throw s!"FloatingLiteral {h.id}: value {text}"
    else pure text
  return rvalue (← genOf t) (.const (.floating (text, suffix)))

/-- The lexemes of a string literal as Clang prints it (between double quotes, with C escapes):
one character or one escape sequence each. -/
partial def stringLexemes (cs : List Char) (acc : Array Cabs.RawString) (full : Bool := false) :
    Except String (Array Cabs.RawString) :=
  match cs with
  | [] => return acc
  | '\\' :: c :: rest =>
    if '0' ≤ c && c ≤ '7' then
      let ds := (c :: rest).take 3 |>.takeWhile fun d => '0' ≤ d && d ≤ '7'
      -- Clang prints every octal escape with three digits; the source usually has the shortest
      -- (a lexeme is one escape, so a following digit is not absorbed), unless `full`
      let ds' := match ds.dropWhile (· == '0') with
        | [] => ['0']
        | r => if full then ds else r
      stringLexemes ((c :: rest).drop ds.length) (acc.push (.utf8 (String.ofList ('\\' :: ds')))) full
    else if c == 'x' then
      -- Clang prints a wide code unit above 255 in upper-case hex; sources mostly use lower case
      let ds := rest.takeWhile Char.isHexDigit
      stringLexemes (rest.drop ds.length) (acc.push (.utf8 (String.ofList ('\\' :: 'x' :: ds.map Char.toLower)))) full
    else if "ntrabfve\\'\"?".toList.contains c then
      stringLexemes rest (acc.push (.utf8 (String.ofList ['\\', c]))) full
    else throw s!"string literal: escape \\{c}"
  -- Clang ends a hex escape followed by a hex digit with `""` (`L"\x100""a"`)
  | '"' :: '"' :: rest => stringLexemes rest acc full
  | c :: rest =>
    if c.toNat < 128 then stringLexemes rest (acc.push (.utf8 (String.singleton c))) full
    else throw "string literal: a non-ASCII character"

/-- The code units a string literal's lexemes denote (STD §6.4.4.4, §6.4.5).
Wide array initializers retain the full escape value; byte strings reduce it modulo 256. -/
partial def lexemeBytes (lx : List Cabs.RawString) (wide : Bool := false) : Except String (List Nat) :=
  lx.mapM fun
    | .utf8 t => match t.toList with
      | ['\\', c] => match c with
        | 'n' => pure 10 | 't' => pure 9 | 'r' => pure 13 | 'a' => pure 7 | 'b' => pure 8
        | 'f' => pure 12 | 'v' => pure 11 | 'e' => pure 27 | '\\' => pure 92 | '\'' => pure 39
        | '"' => pure 34 | '?' => pure 63
        | d => if '0' ≤ d && d ≤ '7' then pure (d.toNat - 48) else throw "escape"
      | '\\' :: 'x' :: ds =>
        let v := ds.foldl (fun a d => a * 16 + (if d.isDigit then d.toNat - 48
          else d.toLower.toNat - 87)) 0
        pure (if wide then v else v % 256)
      | '\\' :: ds =>
        let v := ds.foldl (fun a d => a * 8 + (d.toNat - 48)) 0
        pure (if wide then v else v % 256)
      | [c] => pure c.toNat
      | _ => throw "lexeme"
    | .bytes _ => throw "lexeme"

/-- The length of a token of a string literal with these lexemes and `p` prefix characters. -/
def spelledLength (lx : List Cabs.RawString) (p : Nat) : Nat :=
  lx.foldl (fun n r => match r with | .utf8 x => n + x.length | _ => n) (p + 2)

/-- The pieces of a wide string literal, one per source token as Cerberus keeps them, from the
lengths of its first and last tokens (Clang gives no others): the first piece, the middle tokens
as one piece, the last piece. One piece when the lengths do not split the lexemes. -/
def widePieces (h : Header) (lx : List Cabs.RawString) : List (Cerberus.Loc × List Cabs.RawString) :=
  let whole : List (Cerberus.Loc × List Cabs.RawString) := [(.unknown, lx)]
  match h.range with
  | some ⟨.bare b, .bare e⟩ =>
    match b.offset, e.offset, b.tokLen, e.tokLen with
    | some bo, some eo, some bl, some el =>
      if bo == eo then whole else
      -- each length fixes the split (a lexeme has a character); the prefix is usually on the
      -- first token only
      let split (p : Nat) (l : Nat) (len : Nat → Nat) : Option Nat :=
        (List.range (lx.length + 1)).find? fun k => len k + p == l
      let cuts := [(1, 0), (1, 1), (0, 0), (0, 1)].filterMap fun (pb, pe) => do
        let k ← split pb bl fun k => spelledLength (lx.take k) 0
        let j ← split pe el fun j => spelledLength (lx.drop j) 0
        if k ≤ j then some (k, j) else none
      match cuts with
      | (k, j) :: _ =>
        if k < j then [(.unknown, lx.take k), (.unknown, (lx.drop k).take (j - k)), (.unknown, lx.drop j)]
        else [(.unknown, lx.take k), (.unknown, lx.drop k)]
      | [] => whole
    | _, _, _, _ => whole
  | _ => whole

/-- A string literal: its lexemes and its array type. A byte string has Clang's element type (a
string initialising a signed/unsigned char array has that array's). A wide string `L"…"` has
`int` elements (`wchar_t`) and keeps its pieces (`widePieces`); `u`/`U` strings reject. -/
def stringLiteral (h : Header) : M (StringLiteral × Ctype) := do
  let some (.str v) := h.value | throw s!"StringLiteral {h.id} without a value"
  let (_, t) ← headerType h
  let .mk _ (.array (.mk _ (.basic (.integer it))) (some _)) := t
    | throw s!"StringLiteral {h.id}: only byte and L strings are supported"
  let wide := it == .wchar || it == .signed .int
  unless wide || it == .char || it == .signed .ichar || it == .unsigned .ichar do
    throw s!"StringLiteral {h.id}: only byte and L strings are supported"
  if wide && !v.startsWith "L\"" then throw s!"StringLiteral {h.id}: an L string expected"
  let cs := if wide then v.toList.drop 1 else v.toList
  unless cs.head? == some '"' && cs.getLast? == some '"' && cs.length ≥ 2 do
    throw s!"StringLiteral {h.id}: value {v}"
  let lx ← stringLexemes (cs.drop 1).dropLast #[]
  -- three-digit octal escapes when they, not the shortest, have the token's length
  let lx3 ← stringLexemes (cs.drop 1).dropLast #[] (full := true)
  if wide then
    let values ← lexemeBytes lx.toList (wide := true)
    if values.any (· > 2147483647) then throw s!"StringLiteral {h.id}: code unit outside signed wchar_t"
    let ps := widePieces h lx.toList
    let ps := if ps.length == 1 then widePieces h lx3.toList else ps
    return ((some .wide, ps), t)
  let lx := if tokLen h == some (spelledLength lx3.toList 0) && tokLen h != some (spelledLength lx.toList 0)
    then lx3 else lx
  return ((none, [(.unknown, lx.toList)]), t)

/-! ### Integer constant expressions (case labels, enumerators) -/

def typeInt (h : Header) : M IntegerType := do
  match ← headerType h with
  | (_, .mk _ (.basic (.integer it))) => return it
  | _ => throw s!"{h.kind} {h.id}: not of integer type"

/-- The 64-bit two's complement representation of an integer. -/
def bits (v : Int) : Nat := (v % 2 ^ 64 + 2 ^ 64).toNat % 2 ^ 64

/-- Check layout-dependent subexpressions before accepting Clang's integer value.
The JSON for offsetof omits the member path, so it cannot yet be checked. -/
partial def checkFoldedLayout (n : Node) : M Unit := do
  if let some h := n.header? then
    if h.kind == .offsetOfExpr then throw "folded constant: offsetof is not supported"
    if h.kind == .unaryExprOrTypeTraitExpr then
      let (_, t) ← match h.argType with
        | some t => parseType t.qualType
        | none => match n.children with
          | #[e] =>
            let some eh := e.header? | throw "folded constant: absent operand"
            headerType eh
          | _ => throw "folded constant: one operand expected"
      checkFoldedType 64 t
  n.children.forM checkFoldedLayout

/-- Clang and gcc at -O0 disagree on constant_p of a const local. Restrict calls in
choose conditions to the literal and mutable-variable forms on which they agree. -/
partial def checkChooseCondition (n : Node) : M Unit := do
  if n.kind? == some .callExpr then
    let #[f, a] := n.children | throw "ChooseExpr condition: unsupported call"
    let rec peel (n : Node) : Node := match n.kind?, n.children with
      | some .parenExpr, #[e] | some .implicitCastExpr, #[e] => peel e
      | _, _ => n
    let some r := (peel f).header?.bind (·.referencedDecl)
      | throw "ChooseExpr condition: direct constant_p expected"
    unless r.name == some "__builtin_constant_p" do
      throw "ChooseExpr condition: only literal or mutable-variable constant_p is supported"
    if [Kind.integerLiteral, .characterLiteral, .floatingLiteral, .stringLiteral].contains a.kind then
      return
    let a := peel a
    let some h := a.header? | throw "ChooseExpr condition: absent constant_p argument"
    let some r := h.referencedDecl | throw "ChooseExpr condition: unsupported constant_p argument"
    let (q, _) ← headerType h
    unless h.kind == .declRefExpr && ["VarDecl", "ParmVarDecl"].contains r.kind &&
        !q.const && !q.volatile do
      throw "ChooseExpr condition: constant_p argument may differ between gcc and Clang"
    return
  n.children.forM checkChooseCondition

/-- GNU choose-expr has no usual conversions between its alternatives. Clang gives its
condition as a folded integer ConstantExpr; only the chosen operand is evaluated. -/
def chooseOperand (n : Node) : M Node := do
  let #[c, a, b] := n.children | throw "ChooseExpr: three operands expected"
  let some h := c.header? | throw "ChooseExpr: absent condition"
  unless h.kind == .constantExpr do throw "ChooseExpr: folded condition expected"
  let _ ← typeInt h
  checkFoldedLayout c
  checkChooseCondition c
  let some (.str v) := h.value | throw "ChooseExpr: integer condition expected"
  let some v := v.toInt? | throw "ChooseExpr: integer condition expected"
  return if v == 0 then b else a

/-- The value of an integer constant expression (Clang's implicit conversions are applied). -/
partial def constInt (n : Node) : M Int := do
  let some h := n.header? | throw "absent constant expression"
  let one : M Node := match n.children with
    | #[e] => pure e
    | _ => throw s!"{h.kind} {h.id}: one operand expected"
  match h.kind with
  | .integerLiteral =>
    let some (.str vs) := h.value | throw s!"IntegerLiteral {h.id} without a value"
    let some v := vs.toNat? | throw s!"IntegerLiteral {h.id}: value {vs}"
    wrap (← typeInt h) v
  | .characterLiteral =>
    -- Clang prints the `int` value of a negative `char` constant sign-extended to 32 bits
    let some (.int v) := h.value | throw s!"CharacterLiteral {h.id} without a value"
    wrap (← typeInt h) v
  | .parenExpr => constInt (← one)
  | .chooseExpr => constInt (← chooseOperand n)
  | .constantExpr =>
    -- Clang has evaluated integer constant expressions, including sizeof of a
    -- record with a flexible member. Array bounds are already folded in qualType.
    -- Keep the integer conversion at this node (and at enclosing casts).
    checkFoldedLayout n
    match h.value with
    | some (.str text) =>
      let some v := text.toInt? | throw s!"ConstantExpr {h.id}: non-integer value {text}"
      wrap (← typeInt h) v
    | some (.int v) => wrap (← typeInt h) v
    | none => constInt (← one)
  | .implicitCastExpr | .cStyleCastExpr =>
    if h.castKind == some "IntegralCast" || h.castKind == some "NoOp" then
      wrap (← typeInt h) (← constInt (← one))
    else throw s!"constant expression: cast {h.castKind}"
  | .declRefExpr =>
    let some r := h.referencedDecl | throw s!"DeclRefExpr {h.id} without a declaration"
    match (← get).enumConsts[r.id]? with
    | some v => return v
    | none => throw s!"constant expression: {r.name.getD r.id} is not an enumerator"
  | .unaryOperator =>
    let v ← constInt (← one)
    let it ← typeInt h
    match h.opcode with
    | some "-" => wrap it (-v)
    | some "+" => return v
    | some "~" => wrap it (-v - 1)
    | some "!" => return if v == 0 then 1 else 0
    | o => throw s!"constant expression: unary {o}"
  | .binaryOperator =>
    let #[a, b] := n.children | throw s!"BinaryOperator {h.id}: two operands expected"
    let it ← typeInt h
    let x ← constInt a
    let y ← constInt b
    let bool (c : Bool) : M Int := return if c then 1 else 0
    match h.opcode with
    | some "+" => wrap it (x + y)
    | some "-" => wrap it (x - y)
    | some "*" => wrap it (x * y)
    | some "/" => if y == 0 then throw "division by zero" else wrap it (x.tdiv y)
    | some "%" => if y == 0 then throw "division by zero" else wrap it (x.tmod y)
    | some "<<" => if y < 0 || y ≥ 64 then throw "shift" else wrap it (x * 2 ^ y.toNat)
    | some ">>" => if y < 0 || y ≥ 64 then throw "shift" else wrap it (x / 2 ^ y.toNat)
    | some "&" => wrap it (Int.ofNat (bits x &&& bits y))
    | some "|" => wrap it (Int.ofNat (bits x ||| bits y))
    | some "^" => wrap it (Int.ofNat (bits x ^^^ bits y))
    | some "<" => bool (x < y) | some ">" => bool (x > y) | some "<=" => bool (x ≤ y)
    | some ">=" => bool (x ≥ y) | some "==" => bool (x == y) | some "!=" => bool (x != y)
    | some "&&" => bool (x != 0 && y != 0) | some "||" => bool (x != 0 || y != 0)
    | o => throw s!"constant expression: binary {o}"
  | .conditionalOperator =>
    let #[c, a, b] := n.children | throw s!"ConditionalOperator {h.id}: three operands expected"
    if (← constInt c) != 0 then constInt a else constInt b
  | k => throw s!"constant expression: {k}"

/-- Attributes that only request diagnostics, emission or optimization. ModeAttr is
accepted separately only where Clang has already resolved an integer scalar type. -/
def neutralAttr (k : Kind) : Bool :=
  [Kind.usedAttr, .unusedAttr, .deprecatedAttr, .noInlineAttr, .alwaysInlineAttr,
   .availableOnlyInDefaultEvalMethodAttr].contains k

/-- The maximum alignment requested on this declaration. Clang represents GNU
`aligned` without arguments by one absent child; its x86-64 default is 16. -/
def alignedAttrs (n : Node) : M (Option Nat) := do
  let mut a := none
  for c in n.children do
    if c.kind? == some .alignedAttr then
      let k ← match c.children with
        | #[.absent] => pure 16
        | #[e] => do
          let v ← constInt e
          unless v > 0 do throw "alignment must be positive"
          pure v.toNat
        | _ => throw "alignment without an integer expression"
      unless k > 0 && k &&& (k - 1) == 0 do throw "alignment must be a power of two"
      a := some (max (a.getD 0) k)
  return a

partial def spellingAlignment : Type.TypeSpelling → M (Option Nat)
  | .leaf _ (.typedefName name) => return (← get).typedefAligns[name]?
  | .array t _ | .arrayExpr t _ => spellingAlignment t
  | _ => return none

def headerAlignment (h : Header) : M (Option Nat) := do
  let some t := h.type | throw "alignment: missing type"
  -- Match headerType's GNU typeof fallback. Its operand can be an expression
  -- rather than a type spelling; Clang supplies the resolved type without
  -- evaluating that operand. Ordinary typedef spellings keep their sugar.
  try spellingAlignment (← Type.parse t.qualType) catch err =>
    if (t.qualType.splitOn " ").contains "typeof" then
      if let some resolved := t.desugaredQualType then
        return ← spellingAlignment (← Type.parse resolved)
    throw err

def maxAlignment (a b : Option Nat) : Option Nat :=
  match a, b with
  | none, none => none
  | _, _ => some (max (a.getD 0) (b.getD 0))

/-- Clang's mode attribute has already changed the scalar type in qualType.
Vector, complex and unsupported integer modes still fail in the type parser. -/
def checkMode (t : Ctype) : M Unit := do
  unless t matches .mk _ (.basic (.integer _)) do
    throw "mode attribute on a non-integer scalar is not supported"

/-- A declaration's alignment for the declaration itself, and an alignment above the type's
natural one, which the declaration cannot carry (see `alignedWrapper`). -/
def objectAlignment (n : Node) (h : Header) (t : Ctype) : M (Option Alignment × Option Nat) := do
  for c in n.children do
    if isAttr c then
      if c.kind == .modeAttr then checkMode t
      else unless c.kind == .alignedAttr || neutralAttr c.kind do
        throw s!"{h.kind} {h.name.getD "(unnamed)"}: attribute {c.kind} is not supported"
  let a := maxAlignment (← alignedAttrs n) (← headerAlignment h)
  if let some k := a then
    -- Storage may retain natural alignment even when GNU expression alignof
    -- observes a weaker explicit declaration alignment.
    checkFoldedType 64 t
    let (_, natural) ← Bitfield.sizeAlign (← get).tagDefIdx t
    modify fun st => { st with declAligns := st.declAligns.insert h.id k }
    -- The current consumer drops object/binding alignment, so a request for stronger
    -- storage alignment goes to a wrapper struct.
    if k > natural then return (none, some k)
    return (some (.integer (max k natural)), none)
  return (none, none)

/-- The wrapper of an object of type `t` declared with alignment `k` above `t`'s natural one.
The consumer drops a declaration's alignment but keeps a member's (struct layout), so the
object is a struct whose one member, of type `t`, has alignment `k`; every reference to the
object names that member. Its size is `t`'s rounded up to `k`, padding no reference reaches. -/
def alignedWrapper (name : String) (k : Nat) (t : Ctype) : M AlignedObject := do
  let rec element : Ctype → Ctype
    | .mk _ (.array e _) => element e
    | t => t
  match element t with
  | .mk _ (.struct s) | .mk _ (.union s) =>
    if (← get).packedRecords.contains s.number then
      throw "over-aligned object of a packed record type is not supported"
    match (← get).tagDefIdx[s.number]? with
    | some (.struct _ (some _)) =>
      throw "over-aligned object with a flexible array member is not supported"
    | none => throw "over-aligned object of an incomplete type"
    | _ => pure ()
  | _ => pure ()
  if t matches .mk _ (.array _ none) then throw "over-aligned object of an incomplete array type"
  let tag ← fresh (.id s!"__cfront_aligned_{name}")
  let member := Identifier.mk .unknown "__cfront_aligned"
  let d := TagDefinition.struct [(member, (noAttrs, some (.integer k), noQuals, t))] none
  let (_, a) ← Bitfield.sizeAlign ((← get).tagDefIdx.insert tag.number d) (ct (.struct tag))
  unless a == k do throw "over-aligned object: wrapper alignment differs"
  modify fun st => { st with
    tagDefIdx := st.tagDefIdx.insert tag.number d, tagDefs := st.tagDefs.push (tag, (.unknown, noAttrs, d)) }
  return { tag, member, align := k, ty := t }

/-- The initialiser of a wrapped object: its one member's. -/
def wrapInit (w : AlignedObject) (e : TypedExpression) : TypedExpression :=
  rvalue (.struct w.tag) (.struct w.tag [(w.member, some e)])

/-- Frozen ccomp aligns a frame slot relative to a frame base that is only 16-byte
aligned, so an automatic object of a type aligned more strictly (a record, a GCC
vector's lane struct, or an array of one, aligned above 16) would not get its
alignment. Reject such objects. -/
def checkFrameAlignment (what : String) (t : Ctype) : M Unit := do
  let t := match t with | .mk _ (.array e none) => e | t => t
  if let .ok (_, a) := Bitfield.sizeAlign (← get).tagDefIdx t then
    if a > 16 then
      throw s!"{what}: automatic storage aligned to {a} bytes (above the 16-byte frame alignment) is not supported"

/-- GNU alignof on an object observes a declaration's stronger alignment; C11
alignof on a type observes an aligned typedef. Other expressions use their type. -/
partial def expressionAlignment (n : Node) : M (Option Nat) := do
  if n.kind? == some .parenExpr then
    if let #[e] := n.children then return ← expressionAlignment e
  if let some h := n.header? then
    if let some r := h.referencedDecl then
      if let some a := (← get).declAligns[r.id]? then return some a
    if let some id := h.referencedMemberDecl then
      if let some a := (← get).declAligns[id]? then return some a
    return ← headerAlignment h
  return none

/-! ### Expressions -/

/-- Implicit conversions that Cerberus's typed Ail leaves implicit: the usual arithmetic
conversions and promotions, conversions as if by assignment (STD §6.5.16.1), of a null pointer
constant, between object pointer types, and qualification changes. The consumer converts each
operand from its own type at its use (as for Cerberus's Ail), so dropping them loses nothing. -/
def implicitConversions : List String :=
  ["IntegralCast", "IntegralToFloating", "FloatingToIntegral", "FloatingCast",
    "IntegralToBoolean", "FloatingToBoolean", "PointerToBoolean", "NoOp", "BitCast",
    "NullToPointer"]

def arithmeticOp : String → Option ArithmeticOperator
  | "*" => some .mul | "/" => some .div | "%" => some .mod | "+" => some .add | "-" => some .sub
  | "<<" => some .shl | ">>" => some .shr | "&" => some .band | "^" => some .bxor | "|" => some .bor
  | _ => none

def binaryOp (o : String) : Option BinaryOperator :=
  match arithmeticOp o with
  | some a => some (.arithmetic a)
  | none => match o with
    | "," => some .comma | "&&" => some .and | "||" => some .or | "<" => some .lt
    | ">" => some .gt | "<=" => some .le | ">=" => some .ge | "==" => some .eq | "!=" => some .ne
    | _ => none

/-- The global of a symbol. -/
def globalOf? (s : Sym) : M (Option Global) := do
  let st ← get
  return (st.globalIdx[s.number]?).bind (st.globals[·]?)

/-- The annotation of `*p`: the object type `p` points to (Cerberus's typing, which can differ
from Clang's in qualifiers, see the array decay), else Clang's. -/
def derefAnnot (p clang : GenTypeCategory) : GenTypeCategory :=
  match p, clang with
  | .rvalue (.pointer q t), .lvalue .. => .lvalue q t false
  | _, _ => clang

/-- A node without its parentheses and (for an rvalue operand) lvalue conversion. -/
partial def stripParens (n : Node) : Node :=
  match n.kind?, n.children with
  | some .parenExpr, #[e] => stripParens e
  | some .implicitCastExpr, #[e] =>
    if n.header?.bind (·.castKind) == some "LValueToRValue" then stripParens e else n
  | _, _ => n

/-- A node without its parentheses and implicit conversions. -/
partial def stripCasts (n : Node) : Node :=
  match n.kind?, n.children with
  | some .parenExpr, #[e] | some .implicitCastExpr, #[e] => stripCasts e
  | _, _ => n

/-- The name of the function a call calls directly. -/
def calleeName? (n : Node) : Option String :=
  match n.children[0]? with
  | some f => match f.kind?, f.children with
    | some .implicitCastExpr, #[d] =>
      if d.kind? == some .declRefExpr then d.header?.bind (·.referencedDecl) |>.bind (·.name) else none
    | _, _ => none
  | none => none

/-- `va_arg(ap, T)` as `cerb-prelude.h` spells it for Clang, `*(T *)__cerb_va_arg_ptr(ap,
sizeof(T))`: the `va_list` operand and the dereference (of type `T`). -/
def vaArg? (n : Node) : Option (Node × Header) := do
  let u := stripParens n
  guard (u.kind? == some .unaryOperator && u.header?.bind (·.opcode) == some "*")
  let c ← match u.children with
    | #[c] => some (stripParens c)
    | _ => none
  guard (c.kind? == some .cStyleCastExpr)
  let call ← match c.children with
    | #[x] => some x
    | _ => none
  guard (call.kind? == some .callExpr && calleeName? call == some "__cerb_va_arg_ptr")
  let ap ← call.children[1]?
  return (ap, ← u.header?)

/-- The value of an enumerator, or `none`. -/
def enumConst? (r : DeclRef) : M (Option Int) := return (← get).enumConsts[r.id]?

/-- The value an object of type `t` is initialised to when no initialiser is given for it (STD
§6.7.9#10), as Cerberus's desugaring of initialiser lists spells it. -/
partial def zeroInit (t : Ctype) : M TypedExpression := do
  match t with
  | .mk _ (.basic (.integer _)) => return intConst 0
  | .mk _ (.basic (.floating ft)) => return rvalue (.basic (.floating ft)) (.const (.floating ("0.0", none)))
  | .mk _ (.pointer _ _) => return rvalue (.pointer noQuals (ct .void)) (.const .null)
  | .mk _ (.array e (some k)) =>
    let z ← zeroInit e
    return rvalue (.array e (some k)) (.array false e (List.replicate k.toNat (some z)))
  | .mk _ (.struct s) => match (← get).tagDefIdx[s.number]? with
    | some (.struct ms none) => return rvalue (.struct s) (.struct s (← ms.mapM fun (x, (_, _, _, t)) => do
        pure (x, some (← zeroInit t))))
    | _ => throw "zero initialisation of an incomplete struct or one with a flexible array member"
  | .mk _ (.union s) => match (← get).tagDefIdx[s.number]? with
    | some (.union ((x, (_, _, _, t)) :: _)) => return rvalue (.union s) (.union s x (some (← zeroInit t)))
    | _ => throw "zero initialisation of an incomplete union"
  | _ => throw "zero initialisation of an unsupported type"

/-! ### Bit-fields -/

/-- The bit-field a member access designates (parentheses stripped): the field, the operand of
the access and whether it is `->`. -/
partial def bitfieldAccess? (n : Node) : M (Option (Bitfield.Field × Node × Bool)) := do
  match n.kind?, n.children with
  | some .parenExpr, #[e] => bitfieldAccess? e
  | some .memberExpr, #[b] =>
    let some h := n.header? | return none
    let some d := h.referencedMemberDecl | return none
    let some f := (← get).bitfields[d]? | return none
    let some (owner, field) := (← get).fields[d]? | throw "bit-field references an unknown field"
    unless h.name == some field.name do throw "bit-field name differs from its field declaration"
    let some bh := b.header? | throw "bit-field without an operand"
    let (_, bt) ← headerType bh
    let aggregate ← if h.isArrow == some true then
        match bt with
        | .mk _ (.pointer _ t) => pure t
        | _ => throw "arrow bit-field access requires a pointer"
      else pure bt
    match aggregate with
    | .mk _ (.struct s) | .mk _ (.union s) =>
      unless s.number == owner.number do throw "bit-field belongs to another tag"
    | _ => throw "bit-field access requires a struct or union"
    return some (f, b, h.isArrow == some true)
  | _, _ => return none

/-- An expression without side effects, which a bit-field write may evaluate more than once. -/
partial def sideEffectFree (n : Node) : Bool :=
  let ok := n.children.all sideEffectFree
  match n.kind?, n.header?.bind (·.opcode) with
  | some .declRefExpr, _ | some .integerLiteral, _ | some .characterLiteral, _ => true
  | some .parenExpr, _ | some .implicitCastExpr, _ | some .cStyleCastExpr, _ | some .memberExpr, _
  | some .arraySubscriptExpr, _ => ok
  | some .unaryOperator, some o => ["*", "&", "-", "+", "~", "!"].contains o && ok
  | some .binaryOperator, some o => o != "=" && ok
  | _, _ => false

/-- An initialiser that may be evaluated once per element it initialises: no side effects. -/
partial def repeatSafe (n : Node) : Bool :=
  match n.kind? with
  | some .initListExpr => n.children.all repeatSafe
  | some .floatingLiteral | some .stringLiteral | some .implicitValueInitExpr => true
  | _ => sideEffectFree n

/-- The Clang ids of `n` and its descendants, with their nodes, appended to `acc`. -/
partial def nodeIds (n : Node) (acc : Array (String × Node)) : Array (String × Node) :=
  let acc := match n.header? with
    | some h => acc.push (h.id, n)
    | none => acc
  n.children.foldl (fun acc c => nodeIds c acc) acc

/-- Clang's semantic form of a GNU range designator (`[a ... b] = v`) repeats the node of `v` in
every element it initialises, but gcc evaluates `v` once. The translation initialises each
element from its own copy, so a node shared by two elements must be `repeatSafe`. -/
def checkRangeInits (elems : Array Node) : Except String Unit := do
  let mut owner : Std.HashMap String Nat := {}
  for i in [0:elems.size] do
    for (id, x) in nodeIds elems[i]! #[] do
      match owner[id]? with
      | some j =>
        if j != i && !repeatSafe x then
          throw "a range designator's initialiser with side effects (gcc evaluates it once)"
      | none => owner := owner.insert id i

/-- An expression whose value is a bit-field's (a read or an assignment to it). Clang's
conversions of such a value are kept explicit: a bit-field narrower than `int` promotes to
`int` even when its declared type is `unsigned int` (STD §6.3.1.1#2), which the declared type
the translation gives the value does not say. -/
partial def bitfieldValued (n : Node) : M Bool := do
  let n := stripParens n
  if (← bitfieldAccess? n).isSome then return true
  let operand : M Bool := match n.children[0]? with
    | some a => return (← bitfieldAccess? a).isSome
    | none => return false
  match n.kind?, n.header?.bind (·.opcode) with
  | some .binaryOperator, some "=" | some .compoundAssignOperator, _ => operand
  | some .unaryOperator, some "++" | some .unaryOperator, some "--" => operand
  | some .binaryOperator, some "," => match n.children[1]? with
    | some b => bitfieldValued b
    | none => return false
  | _, _ => return false

/-- The bit-field whose value `n` is, a read of it or an assignment to it. -/
partial def bitfieldValue? (n : Node) : M (Option Bitfield.Field) := do
  if let (some .parenExpr, #[e]) := (n.kind?, n.children) then return ← bitfieldValue? e
  let target : M (Option Bitfield.Field) := match n.children[0]? with
    | some a => return (← bitfieldAccess? a).map (·.1)
    | none => return none
  match n.kind?, n.header?.bind (·.opcode), n.header?.bind (·.castKind) with
  | some .implicitCastExpr, _, some "LValueToRValue" | some .binaryOperator, some "=", _
  | some .compoundAssignOperator, _, _ | some .unaryOperator, some "++", _
  | some .unaryOperator, some "--", _ => target
  | _, _, _ => return none

/-- The wide bit-field (`Bitfield.Field.wide`) whose value `n` is, a read of it or an assignment
to it. gcc and Clang agree on that value, not on arithmetic with it (`wideType?`). -/
partial def wideValue? (n : Node) : M (Option Bitfield.Field) :=
  return (← bitfieldValue? n).filter (·.wide)

/-- gcc's type of an operand, where it can differ from Clang's. gcc gives a bit-field wider than
`int` and narrower than its type a type of the field's width (its reading of DR 315), which no
promotion widens, so arithmetic with it is computed in that width; Clang computes in the declared
type. -/
inductive GccOperand where
  /-- gcc's `w`-bit integer type (`32 < w < 64`) of a wide bit-field. -/
  | wide (w : Nat) (signed : Bool)
  /-- An integer type that promotes to `int` or `unsigned int`. -/
  | narrow
  /-- A 64-bit integer type. -/
  | full (signed : Bool)
  /-- Not an integer: a floating, pointer or other operand. -/
  | other
  /-- An integer type not classified here. -/
  | unknown
  deriving BEq

/-- The type of gcc's usual arithmetic conversions of two operands, one of them wide: gcc's
`c_common_type` ranks integer types by precision, the unsigned one on a tie. Not wide (`other`)
when neither is. -/
def GccOperand.common : GccOperand → GccOperand → GccOperand
  | .wide w s, .wide v t => if w == v then .wide w (s && t) else if w > v then .wide w s else .wide v t
  | .wide w s, .narrow | .narrow, .wide w s => .wide w s
  | .wide .., .full t | .full t, .wide .. => .full t
  | .wide .., .unknown | .unknown, .wide .. => .unknown
  | _, _ => .other

def GccOperand.isWide : GccOperand → Bool
  | .wide .. => true
  | _ => false

def GccOperand.describe : GccOperand → String
  | .wide w s => s!"{if s then "signed" else "unsigned"} {w}-bit"
  | .narrow => "int"
  | .full s => s!"{if s then "signed" else "unsigned"} 64-bit"
  | .other => "non-integer"
  | .unknown => "unclassified integer"

/-- Whether the program has a wide bit-field (`Bitfield.Field.wide`). -/
def anyWide : M Bool := return (← get).bitfields.fold (fun w _ f => w || f.wide) false

mutual

/-- gcc's type of the value of `n` when it is a wide bit-field type: the value of a wide
bit-field, or arithmetic (`+ - * / % & | ^ << >>`, unary `- + ~`, `?:`) whose gcc type is one. -/
partial def wideType? (n : Node) : M (Option (Nat × Bool)) := do
  unless ← anyWide do return none
  if let (some .parenExpr, #[e]) := (n.kind?, n.children) then return ← wideType? e
  if n.kind? == some .chooseExpr then return ← wideType? (← chooseOperand n)
  if let some f ← wideValue? n then return some (f.width, f.signed)
  let wide : GccOperand → Option (Nat × Bool)
    | .wide w s => some (w, s)
    | _ => none
  match n.kind?, n.header?.bind (·.opcode), n.children with
  | some .binaryOperator, some o, #[a, b] =>
    if o == "<<" || o == ">>" then return wide (← gccOperand a)
    if (arithmeticOp o).isSome then return wide ((← gccOperand a).common (← gccOperand b))
    return none
  | some .unaryOperator, some o, #[a] =>
    if ["-", "+", "~"].contains o then return wide (← gccOperand a) else return none
  | some .conditionalOperator, _, #[_, a, b] => return wide ((← gccOperand a).common (← gccOperand b))
  -- gcc keeps the type of a statement expression's value and of `_Generic`'s selection
  | some .stmtExpr, _, #[c] => match c.children.back? with
    | some e => wideType? e
    | none => return none
  | some .genericSelectionExpr, _, cs =>
    match cs.filter (fun | .association _ (some true) _ => true | _ => false) with
    | #[a] => match a.children.back? with
      | some e => wideType? e
      | none => return none
    | _ => return none
  | _, _, _ => return none

/-- gcc's type of an operand of an operator as Clang gives it, before Clang's implicit integral
conversions (gcc converts to its own common type instead). -/
partial def gccOperand (n : Node) : M GccOperand := do
  let rec peel (n : Node) : Node := match n.kind?, n.children with
    | some .parenExpr, #[e] => peel e
    | some .implicitCastExpr, #[e] => if n.header?.bind (·.castKind) == some "IntegralCast" then peel e else n
    | _, _ => n
  let n := peel n
  if let some (w, s) ← wideType? n then return .wide w s
  -- a bit-field narrower than `int` promotes to `int` whatever its type (Clang converts it
  -- from its declared type in one step)
  if let some f ← bitfieldValue? n then
    return if f.width ≤ 32 then .narrow else if f.width == 64 then .full f.signed else .unknown
  let some h := n.header? | return .other
  let t : Option Ctype ← try
      let (_, t) ← headerType h
      pure (some t)
    catch _ => pure none
  match t with
  | some (.mk _ (.basic (.integer it))) =>
    match Bitfield.intSize it, intShape it with
    | .ok s, shape =>
      if s ≤ 4 then return .narrow
      match s, shape with
      | 8, .ok (_, sg) => return .full sg
      | _, _ => return .unknown
    | .error _, _ => return .unknown
  | some _ => return .other
  | none => return .unknown

end

/-- Clang's integer computation type of an operator (the type of `h`), which must be gcc's `g`
when that is a 64-bit or wide type: a 64-bit type of `g`'s signedness. -/
def wideComputation (h : Header) (g : GccOperand) : M IntegerType := do
  let (_, t) ← headerType h
  let .mk _ (.basic (.integer it)) := t
    | throw s!"{h.kind}: gcc's {g.describe} computation, Clang's of a non-integer type (gcc and Clang differ)"
  let (bits, s) ← intShape it
  match g with
  | .wide _ sg | .full sg =>
    unless bits == 64 && s == sg do
      throw s!"{h.kind}: gcc's {g.describe} computation, Clang's {bits}-bit (gcc and Clang differ)"
  | _ => throw s!"{h.kind}: gcc's {g.describe} operand of a wide bit-field (gcc and Clang differ)"
  return it

/-- The operands of a binary operator or the branches of `?:` (`a`, `b`, as Clang gives them,
translated as `ea`, `eb`), as gcc converts them when one has a wide bit-field type (`wideType?`):
to its common type `g` (`GccOperand.common`), which must agree with Clang's computation type
(of `h`). A wide `g` reduces each operand of another type to it (`Bitfield.reduce`); its result
needs no reduction after `/ % & | ^ >>`, a comparison or `?:`, whose operands are then in its
range. `none` when no operand is wide. -/
def wideOperands (h : Header) (a b : Node) (ea eb : TypedExpression) :
    M (Option (GccOperand × TypedExpression × TypedExpression)) := do
  unless ← anyWide do return none
  let ga ← gccOperand a
  let gb ← gccOperand b
  unless ga.isWide || gb.isWide do return none
  let g := ga.common gb
  match g with
  | .wide w s =>
    let it ← wideComputation h g
    let conv (gx : GccOperand) (e : TypedExpression) := if gx == g then e else Bitfield.reduce w s it e
    return some (g, conv ga ea, conv gb eb)
  | .full _ => let _ ← wideComputation h g; return some (g, ea, eb)
  | .other => return some (g, ea, eb)
  | _ => throw s!"{h.kind}: an operand of a wide bit-field and an {g.describe} one (gcc and Clang differ)"

/-- `e`, an operator's result of Clang's type (of `h`), reduced to gcc's wide type `g`, if it
is one. -/
def wideResult (h : Header) (g : GccOperand) (e : TypedExpression) : M TypedExpression := do
  let .wide w s := g | return e
  return Bitfield.reduce w s (← wideComputation h g) e

/-- The constant a bit-field initialiser is, if it is one. -/
def bitConst? (c : Node) : M (Option Int) := do
  let c := match c.kind?, c.header?.bind (·.castKind), c.children with
    | some .implicitCastExpr, some "IntegralToBoolean", #[e] => e
    | _, _, _ => c
  try return some (← constInt c) catch _ => return none

/-- Types with an established byte layout in the Ail consumer. `float` and `double` members
are accessed in place (an unaligned load or store of the member's own type); `float` takes
the consumer's eight bytes, so layout queries of such a record reject (`checkFoldedType`).
Long double, flexible arrays and nested bit-fields are not supported. -/
partial def checkPackedType (fuel : Nat) (t : Ctype) : M Unit := do
  match fuel, t with
  | 0, _ => throw "packed: recursive layout"
  | _, .mk _ (.basic (.integer _)) | _, .mk _ (.pointer ..) => pure ()
  | _, .mk _ (.basic (.floating (.realFloating .float)))
  | _, .mk _ (.basic (.floating (.realFloating .double))) => pure ()
  | fuel + 1, .mk _ (.array e (some _)) => checkPackedType fuel e
  | fuel + 1, .mk _ (.struct tag) =>
    if (← get).bitSlots.contains tag.number then throw "packed: nested bit-fields are not supported"
    let some (.struct ms none) := (← get).tagDefIdx[tag.number]?
      | throw "packed: incomplete or flexible nested record"
    for (_, (_, _, _, mt)) in ms do checkPackedType fuel mt
  | _, _ => throw "packed: only integers, float, double, pointers, fixed arrays and structs are supported"

/-- A byte of a packed initializer: a constant, or byte `i` of the value of an integer
initializer `n` of type `it`. -/
inductive PackedByte where
  | const (b : Nat)
  | part (n : Node) (it : IntegerType) (i : Nat)

/-- Whether an expression reads a `volatile` object (or one whose type is unknown). -/
partial def readsVolatile (n : Node) : M Bool := do
  if n.kind? == some .implicitValueInitExpr then return false
  if n.kind? == some .implicitCastExpr && n.header?.bind (·.castKind) == some "LValueToRValue" then
    let some ch := n.children[0]?.bind (·.header?) | return true
    let q ← try pure (some (← headerType ch).1) catch _ => pure none
    unless q.any (!·.volatile) do return true
  n.children.anyM readsVolatile

/-- Object bytes, little endian. Missing elements are zero. Pointer relocations and floating
values other than zero reject. Outside a static initializer, an integer member's value may be
an expression without side effects or volatile reads, which each of its bytes evaluates; no
other expression is duplicated or discarded. -/
partial def packedBytes (t : Ctype) (n : Node) : M (Array PackedByte) := do
  let (sz, _) ← Bitfield.sizeAlign (← get).tagDefIdx t
  if n.kind? == some .implicitValueInitExpr then return Array.replicate sz (.const 0)
  match t with
  | .mk _ (.basic (.integer it)) =>
    let some value ← bitConst? n | do
      if (← get).staticInit || !sideEffectFree n || (← readsVolatile n) then
        throw "packed initializer: integer constant expected"
      return (Array.range sz).map (.part n it)
    let v ← wrap it value
    return (Array.range sz).map fun i => .const ((bits v >>> (8 * i)) &&& 255)
  | .mk _ (.basic (.floating _)) =>
    -- Only a zero literal: no IEEE byte encoder here (a negative zero is not a literal).
    let n := stripCasts n
    let zero ← match n.kind?, n.header? with
      | some .floatingLiteral, some { value := some (.str text), .. } =>
        pure ((decimalParts text).map (·.1 == 0) |>.getD false)
      | some .integerLiteral, _ => pure ((← constInt n) == 0)
      | _, _ => pure false
    unless zero do throw "packed initializer: floating constant is not supported"
    return Array.replicate sz (.const 0)
  | .mk _ (.pointer ..) =>
    -- Only the null pointer has a relocatable-free representation here.
    let n := stripCasts n
    unless (← constInt n) == 0 do throw "packed initializer: pointer relocation is not supported"
    return Array.replicate sz (.const 0)
  | .mk _ (.array e (some count)) =>
    let (es, _) ← Bitfield.sizeAlign (← get).tagDefIdx e
    if n.kind? == some .stringLiteral then
      unless e matches .mk _ (.basic (.integer .char)) do
        throw "packed initializer: string of a non-character array"
      let some h := n.header? | throw "packed initializer: absent string"
      let (str, _) ← stringLiteral h
      let bs ← lexemeBytes (str.2.flatMap (·.2))
      return ((bs.take count.toNat) ++ List.replicate (count.toNat - bs.length) 0).toArray.map .const
    unless n.kind? == some .initListExpr do throw "packed initializer: array list expected"
    let cs := match n.arrayFiller with | some af => af.extract 1 af.size | none => n.children
    if cs.size > count.toNat then throw "packed initializer: too many array elements"
    let mut bs := #[]
    for c in cs do bs := bs ++ (← packedBytes e c)
    return bs ++ Array.replicate ((count.toNat - cs.size) * es) (.const 0)
  | .mk _ (.struct tag) =>
    -- a compound literal of the member's struct type is its initializer list
    let n ← match (stripCasts n).kind?, (stripCasts n).children with
      | some .compoundLiteralExpr, #[l] =>
        match l.kind?, l.header? with
        | some .initListExpr, some lh => do
          let (_, lt) ← headerType lh
          match lt with
          | .mk _ (.struct s) => pure (if s.number == tag.number then l else n)
          | _ => pure n
        | _, _ => pure n
      | _, _ => pure n
    -- a complex pair initialised by a scalar (`{ 0 }` elides the pair's braces): only a zero,
    -- checked as the real part, gives the pair's bytes
    if n.kind? != some .initListExpr then
      if let some part := (← get).complexParts[tag.number]? then
        unless (← packedBytes part n).all (· matches .const 0) do
          throw "packed initializer: complex scalar other than zero is not supported"
        return Array.replicate sz (.const 0)
    unless n.kind? == some .initListExpr do throw "packed initializer: constant struct list expected"
    let fs ← match (← get).packedRecords[tag.number]? with
      | some r => pure r.fields
      | none => do
        let defs := (← get).tagDefIdx
        let some (.struct ms none) := defs[tag.number]? | throw "packed initializer: struct layout"
        let (offs, _, _) ← Bitfield.structLayout defs ms none
        pure ((ms.zip offs).map fun ((x, (_, _, _, mt)), off) => PackedField.mk x off mt).toArray
    if n.children.size > fs.size then throw "packed initializer: too many struct members"
    let mut bs := Array.replicate sz (.const 0)
    for (f, i) in fs.zipIdx do
      if let some c := n.children[i]? then
        let vs ← packedBytes f.ty c
        for (v, j) in vs.zipIdx do bs := bs.set! (f.off + j) v
    return bs
  | _ => throw "packed initializer: unsupported type"

/-- Cerberus's limits builtins (its `limits.h` spells `INT_MAX` as `__cerbvar_INT_MAX`, …), which
Cerberus reads as `IConstantMax`/`IConstantMin` constants and the prelude defines as
`#define __cerbvar_NAME BODY`: the name, the value and the constant. -/
def limitBuiltins : List (String × Int × Bool × IntegerType) :=
  [("SCHAR_MIN", -128, false, .signed .ichar), ("SCHAR_MAX", 127, true, .signed .ichar),
   ("UCHAR_MAX", 255, true, .unsigned .ichar),
   ("SHRT_MIN", -32768, false, .signed .short), ("SHRT_MAX", 32767, true, .signed .short),
   ("USHRT_MAX", 65535, true, .unsigned .short),
   ("INT_MIN", -2147483648, false, .signed .int), ("INT_MAX", 2147483647, true, .signed .int),
   ("UINT_MAX", 4294967295, true, .unsigned .int),
   ("LONG_MIN", -9223372036854775808, false, .signed .long),
   ("LONG_MAX", 9223372036854775807, true, .signed .long),
   ("ULONG_MAX", 18446744073709551615, true, .unsigned .long)]

/-- A node that is the whole body of a prelude limits macro, as Cerberus's constant. The .i has
no macros of its own, so a macro expansion is the prelude's: the node begins at the first token of
the body (just after `#define ` and the name, whose length is the expansion's token length), ends
in the same expansion, and has the builtin's value. -/
def limitConst (n : Node) (h : Header) : M (Option TypedExpression) := do
  let some ⟨.macro s e, .macro _ e'⟩ := h.range | return none
  let some l := e.tokLen | return none
  unless e.offset.isSome && e.offset == e'.offset && s.col == some (l + 10) do return none
  let some v ← tryCatch (some <$> constInt n) fun _ => pure none | return none
  let some (_, _, mx, t) := limitBuiltins.find? fun (x, w, _) => ("__cerbvar_" ++ x).length == l && w == v
    | return none
  return some (rvalue (intGen t) (.const (.integer (if mx then .max t else .min t))))

/-- Library builtin prototypes on the supported LP64 target. Only direct calls are lowered;
semantic intrinsics and unknown names have no entry. -/
def libraryBuiltin? : String → Option (String × String)
  | "__builtin_abort" => some ("abort", "void (void)")
  | "__builtin_exit" => some ("exit", "void (int)")
  | "__builtin_memcpy" => some ("memcpy", "void *(void *restrict, const void *restrict, __size_t)")
  | "__builtin_memmove" => some ("memmove", "void *(void *, const void *, __size_t)")
  | "__builtin_memset" => some ("memset", "void *(void *, int, __size_t)")
  | "__builtin_memcmp" => some ("memcmp", "int (const void *, const void *, __size_t)")
  | "__builtin_strlen" => some ("strlen", "__size_t (const char *)")
  | "__builtin_strcmp" => some ("strcmp", "int (const char *, const char *)")
  | "__builtin_strncmp" => some ("strncmp", "int (const char *, const char *, __size_t)")
  | "__builtin_strcpy" => some ("strcpy", "char *(char *restrict, const char *restrict)")
  | "__builtin_memchr" => some ("memchr", "void *(const void *, int, __size_t)")
  | "__builtin_strncpy" => some ("strncpy", "char *(char *restrict, const char *restrict, __size_t)")
  | "__builtin_strcat" => some ("strcat", "char *(char *restrict, const char *restrict)")
  | "__builtin_strncat" => some ("strncat", "char *(char *restrict, const char *restrict, __size_t)")
  | "__builtin_strchr" => some ("strchr", "char *(const char *, int)")
  | "__builtin_strrchr" => some ("strrchr", "char *(const char *, int)")
  | "__builtin_strstr" => some ("strstr", "char *(const char *, const char *)")
  | "__builtin_sprintf" => some ("sprintf", "int (char *restrict, const char *restrict, ...)")
  | "__builtin_snprintf" => some ("snprintf", "int (char *restrict, __size_t, const char *restrict, ...)")
  | "__builtin_fprintf" => some ("fprintf", "int (struct _IO_FILE *restrict, const char *restrict, ...)")
  | "__builtin_fputs" => some ("fputs", "int (const char *restrict, struct _IO_FILE *restrict)")
  | "__builtin_abs" => some ("abs", "int (int)")
  | "__builtin_fabs" => some ("fabs", "double (double)")
  | "__builtin_fabsf" => some ("fabsf", "float (float)")
  | "__builtin_printf" => some ("printf", "int (const char *restrict, ...)")
  | "__builtin_puts" => some ("puts", "int (const char *)")
  | "__builtin_putchar" => some ("putchar", "int (int)")
  | "__builtin_malloc" => some ("malloc", "void *(__size_t)")
  | "__builtin_free" => some ("free", "void (void *)")
  | "__builtin_calloc" => some ("calloc", "void *(__size_t, __size_t)")
  | "__builtin_realloc" => some ("realloc", "void *(void *, __size_t)")
  | _ => none

/-- A comparison key for the simple library prototypes. `size_t` and `unsigned long` are the
same LP64 type. Parameter qualifiers do not enter a function type; pointee qualifiers do.
Other shapes fail closed. -/
partial def libraryTypeKey : Ctype → Option String
  | .mk [] .void => some "v"
  | .mk [] (.basic (.integer it)) => match it with
    | .char => some "c"
    | .signed .int => some "i"
    | .unsigned .long | .size => some "z"
    | _ => none
  | .mk [] (.basic (.floating (.realFloating .float))) => some "f32"
  | .mk [] (.basic (.floating (.realFloating .double))) => some "f64"
  | .mk [] (.struct s) => some s!"s{s.number}"
  | .mk [] (.pointer q t) => do
    let k ← libraryTypeKey t
    return s!"p{q.const}:{q.volatile}:{q.restrict}({k})"
  | .mk [] (.function (q, r) ps v) => do
    guard (q == noQuals)
    let r ← libraryTypeKey r
    let ps ← ps.mapM fun (_, t, _) => libraryTypeKey t
    return s!"f{v}({String.intercalate "," ps})->{r}"
  | _ => none

/-- The general type parser drops attributes. For library prototypes, only the known
noreturn suffix of abort/exit may be erased; calling-convention or type-changing attributes
must not disappear before the prototype comparison. -/
def checkLibrarySpelling (name spelling : String) : M Unit := do
  let spelling := if ["abort", "exit"].contains name then
    spelling.replace " __attribute__((noreturn))" "" else spelling
  if (spelling.splitOn "__attribute__").length > 1 then
    throw s!"{name}: attributed library prototype is not supported"

/-- Check both the builtin's reference type and any existing libc declaration. This is a
restricted type comparison, not merely a name rewrite. -/
def checkLibraryType (name : String) (actual expected : Ctype) : M Unit := do
  let some a := libraryTypeKey actual | throw s!"{name}: unsupported library prototype"
  let some b := libraryTypeKey expected | throw s!"{name}: unsupported expected library prototype"
  unless a == b do throw s!"{name}: library prototype mismatch"

/-- Like the implicit-declaration path, create a sigma declaration on demand from the
referenced FunctionDecl (its expression may have `<builtin fn type>`). An ordinary libc
prototype already seen must agree; it supplies the same entity. -/
def libraryFunction (r : DeclRef) (name prototype : String) : M TypedExpression := do
  unless r.kind == "FunctionDecl" do throw "library builtin: FunctionDecl expected"
  let some ty := r.type | throw s!"{name}: library builtin without a prototype"
  checkLibrarySpelling name ty.qualType
  let (_, actual) ← parseType ty.qualType
  let (_, expected) ← parseType prototype
  checkLibraryType name actual expected
  let .mk _ (.function ret ps v) := expected | throw "library builtin: function expected"
  let known := (← get).globals.find? fun g => g.name == name && !g.blockScope
  let s ← match known with
    | some g =>
      unless g.isFunction && !g.isStatic do throw s!"{name}: library builtin conflicts with declaration"
      if let some spelling := g.functionSpelling then checkLibrarySpelling name spelling
      let .function _ gr gps gv _ _ := g.decl | throw "library builtin: function expected"
      checkLibraryType name (ct (.function gr gps gv)) expected
      pure g.sym
    | none =>
      let s ← fresh (.id name)
      let noreturn := name == "abort" || name == "exit"
      let g : Global := { sym := s, name, isFunction := true, isStatic := false,
                          firstIsDefinition := false, decl := .function true ret ps v false noreturn,
                          kind := .declaration, noreturn, libraryBuiltin := true }
      modify fun st => { st with globals := st.globals.push g,
                                 globalIdx := st.globalIdx.insert s.number st.globals.size }
      pure s
  return mkExpr (.rvalue (.pointer noQuals expected))
    (.functionDecay (mkExpr (.rvalue (.function ret ps v)) (.ident s)))

/-- Builtins whose result needs no runtime helper. Unknown names have no lowering. -/
def scalarBuiltin? : String → Option String
  | "__builtin_constant_p" => some "int ()"
  | "__builtin_classify_type" => some "int ()"
  | "__builtin_expect" => some "long (long, long)"
  | "__builtin_expect_with_probability" => some "long (long, long, double)"
  | _ => none

/-- A conservative proof that an argument is constant. `constant_p` never evaluates its
argument; failure to prove constancy returns zero, as permitted by the builtin contract.
String and floating literals are constants too (not just integer constant expressions). -/
def builtinConstant (n : Node) : M Bool := do
  let n := stripCasts n
  if n.kind? == some .stringLiteral || n.kind? == some .floatingLiteral then return true
  try
    let _ ← constInt n
    return true
  catch _ => return false

/-- A floating operand that gcc folds to a constant (a `REAL_CST`) at -O0: a floating literal,
`__builtin_inf`/`huge_val`/`nan` (and the `f` forms), an integer constant expression, and casts
and unary `-`/`+` of these. Binary operators are left out: gcc declines to fold some (an overflow to
infinity, a NaN from non-NaN operands). -/
partial def foldedFloating (n : Node) : M Bool := do
  match n.kind?, n.children with
  | some .floatingLiteral, _ => return true
  | some .parenExpr, #[e] => foldedFloating e
  | some .implicitCastExpr, #[e] | some .cStyleCastExpr, #[e] =>
    if ["FloatingCast", "IntegralToFloating", "FloatingToIntegral", "NoOp"].contains
        ((n.header?.bind (·.castKind)).getD "") then foldedFloating e
    else builtinConstant n
  | some .unaryOperator, #[e] =>
    if ["-", "+"].contains ((n.header?.bind (·.opcode)).getD "") then foldedFloating e
    else builtinConstant n
  | some .callExpr, #[_] =>
    return ["__builtin_inf", "__builtin_inff", "__builtin_huge_val", "__builtin_huge_valf"].contains
      ((calleeName? n).getD "")
  | some .callExpr, #[_, a] =>
    -- gcc folds `nan` of a payload string it parses: only the default, `""`, is taken here
    let s := stripCasts a
    return ["__builtin_nan", "__builtin_nanf"].contains ((calleeName? n).getD "") &&
      s.kind? == some .stringLiteral && (s.header?.bind (·.value)) == some (.str "\"\"")
  | _, _ => builtinConstant n

/-- A value that no folding by gcc makes constant: every evaluation loads a variable or calls a
function (through casts, unary operators, members, subscripts and floating `+ - * /`, which
IEEE arithmetic never folds to a constant), or assigns. Integer arithmetic is left out: gcc
folds `x * 0` or `x - x` to a constant. -/
partial def runtimeValue (n : Node) : Bool :=
  let op := (n.header?.bind (·.opcode)).getD ""
  let ty := n.header?.bind (·.type)
  let real := fun (q : String) => q == "float" || q == "double"
  let floating := ty.any fun t => real t.qualType || t.desugaredQualType.any real
  -- reading a volatile object is a side effect
  let volatileRead := ty.any fun t => (t.qualType.splitOn " ").contains "volatile"
  match n.kind?, n.children with
  | some .declRefExpr, _ =>
    (n.header?.bind (·.referencedDecl)).any fun r => r.kind == "VarDecl" || r.kind == "ParmVarDecl"
  | some .parenExpr, #[e] | some .implicitCastExpr, #[e] | some .cStyleCastExpr, #[e] => runtimeValue e
  | some .memberExpr, #[e] => volatileRead || runtimeValue e
  | some .arraySubscriptExpr, #[b, _] => volatileRead || runtimeValue b
  | some .unaryOperator, #[e] =>
    op == "*" && volatileRead || ["*", "-", "+", "~", "!"].contains op && runtimeValue e ||
      ["++", "--"].contains op
  | some .callExpr, _ => !((calleeName? n).getD "").startsWith "__builtin"
  | some .compoundAssignOperator, _ => true
  | some .binaryOperator, #[a, b] =>
    op == "=" || floating && ["+", "-", "*", "/"].contains op && (runtimeValue a || runtimeValue b)
  | _, _ => false

/-- gcc's `__builtin_constant_p` at -O0, which is `fold_builtin_constant_p` on the argument as
the front end folded it: 1 for a constant (`builtinConstant`, `foldedFloating`), 0 for a
`runtimeValue` or the address of a variable (a pointer, not a string literal). Any other
argument rejects: gcc's folding may make it constant (`x * 0`, `0 && f()`, a conditional), and
the 0 the builtin's contract would allow is not gcc's answer. A `sizeof` is checked at the
call. -/
partial def gccConstantP (n : Node) : M Bool := do
  if (← builtinConstant n) || (← foldedFloating n) then return true
  let s := stripCasts n
  let address := s.kind? == some .unaryOperator && s.header?.bind (·.opcode) == some "&" &&
    s.children.all runtimeValue
  if runtimeValue s || address then return false
  throw "__builtin_constant_p: an argument that gcc's folding may make constant"

/-- gcc's `__builtin_classify_type` class (its `enum type_class`) of an operand of type `t`, as
Clang converted it: integer 1, pointer 5, real 8, struct 12, union 13. `_Bool`, enumerations,
GNU vectors (lane structs here), `long double` and other types reject. -/
def classifyType (t : Ctype) : M Int := do
  match t with
  | .mk _ (.basic (.integer it)) => match it with
    | .bool | .enum _ => throw "classify_type: a _Bool or enumerated operand"
    | _ => return 1
  | .mk _ (.basic (.floating (.realFloating .float)))
  | .mk _ (.basic (.floating (.realFloating .double))) => return 8
  | .mk _ (.pointer _ _) => return 5
  | .mk _ (.struct s) =>
    if ((← get).vectorLanes[s.number]?).isSome then throw "classify_type: a vector operand"
    if ((← get).complexParts[s.number]?).isSome then return 9
    return 12
  | .mk _ (.union _) => return 13
  | _ => throw "classify_type: an operand of an unsupported type"

/-- The typed `__builtin_{s,u}{add,sub,mul}{,l,ll}_overflow` forms: their operand type. -/
def typedOverflow? (name : String) : Option String :=
  let ops := ["add", "sub", "mul"]
  let widths := [("", "int"), ("l", "long"), ("ll", "long long")]
  let forms := ops.flatMap fun o => widths.flatMap fun (w, t) =>
    [(s!"__builtin_s{o}{w}_overflow", t), (s!"__builtin_u{o}{w}_overflow", s!"unsigned {t}")]
  (forms.find? (·.1 == name)).map (·.2)

/-- Semantic builtins (`Silmaril.Clang.Builtin`): the referenced prototype Clang gives each and
the call's type. Clang types the generic ones (`int ()`, `_Bool ()`) by their operands. Names
without an entry (the `long double` forms, which ccomp does not support, among them) reject. -/
def semanticBuiltin? (name : String) : Option (String × String) :=
  match name with
  | "__builtin_isgreater" | "__builtin_isgreaterequal" | "__builtin_isless"
  | "__builtin_islessequal" | "__builtin_islessgreater" | "__builtin_isunordered"
  | "__builtin_isnan" | "__builtin_isinf" | "__builtin_isfinite" | "__builtin_signbit" =>
    some ("int ()", "int")
  | "__builtin_add_overflow" | "__builtin_sub_overflow" | "__builtin_mul_overflow" =>
    some ("_Bool ()", "_Bool")
  | "__builtin_inf" | "__builtin_huge_val" => some ("double (void)", "double")
  | "__builtin_inff" | "__builtin_huge_valf" => some ("float (void)", "float")
  | "__builtin_nan" => some ("double (const char *)", "double")
  | "__builtin_nanf" => some ("float (const char *)", "float")
  | "__builtin_copysign" => some ("double (double, double)", "double")
  | "__builtin_copysignf" => some ("float (float, float)", "float")
  | "__builtin_prefetch" => some ("void (const void *, ...)", "void")
  | _ => (typedOverflow? name).map fun t => (s!"_Bool (const {t}, const {t}, {t} *)", "_Bool")

/-- A designator of the synthesized function `key` of a semantic builtin, a static definition of
type `ret (ps)` whose body `body` makes from its parameters and `locals` fresh locals, defined on
first use. -/
def builtinHelper (key : String) (ret : Ctype) (ps : List Ctype) (locals : Nat)
    (body : List Sym → List Sym → Option TypedStatement) : M TypedExpression := do
  if (← get).staticInit then
    throw s!"__builtin_{(key.splitOn "/").head!} in a static initialiser (not a constant expression)"
  let params := ps.map (noQuals, ·, false)
  let st ← get
  let sym ← match st.builtinHelpers[key]? with
    | some s => pure s
    | none => do
      let name := s!"__cfront_builtin{st.builtinHelpers.size}"
      let sym ← fresh (.id name)
      let psyms ← ps.mapM fun _ => fresh .none
      let lsyms ← (List.range locals).mapM fun _ => fresh .none
      let some b := body psyms lsyms | throw s!"builtin {key}: no lowering"
      let marker ← freshNat
      let g : Global :=
        { sym, name, isFunction := true, isStatic := true, firstIsDefinition := true,
          decl := .function false (noQuals, ret) params false false false, kind := .definition }
      let fd : FunctionDefinition GenTypeCategory :=
        { loc := .unknown, marker, attrs := noAttrs, params := psyms, body := b }
      modify fun st => { st with
        globals := st.globals.push g, globalIdx := st.globalIdx.insert sym.number st.globals.size,
        functionDefinitions := st.functionDefinitions.push (sym, fd),
        builtinHelpers := st.builtinHelpers.insert key sym }
      pure sym
  let f := mkExpr (.rvalue (.function (noQuals, ret) params false)) (.ident sym)
  return mkExpr (.rvalue (.pointer noQuals (ct (.function (noQuals, ret) params false)))) (.functionDecay f)

/-- A floating type of a semantic builtin's operand: `float` (true) or `double` (false). -/
def builtinFloating (name : String) : Ctype → M Bool
  | .mk _ (.basic (.floating (.realFloating .float))) => return true
  | .mk _ (.basic (.floating (.realFloating .double))) => return false
  | _ => throw s!"{name}: an operand of a type other than float or double"

/-- An integer operand type of an overflow builtin, with its width and signedness. -/
def overflowInt (name : String) : Ctype → M (Nat × Bool)
  | .mk _ (.basic (.integer it)) => do
    match it with
    | .bool | .enum _ => throw s!"{name}: a _Bool or enumerated operand"
    | _ => match intShape it with
      | .ok (w, s) => if w ≤ 64 then return (w, s) else throw s!"{name}: an integer wider than 64 bits"
      | .error e => throw s!"{name}: {e}"
  | _ => throw s!"{name}: a non-integer operand"

/-- Parentheses and the function decay inserted by Clang preserve a direct callee. Explicit
casts, address-taking and computed designators do not qualify for builtin lowering. -/
partial def directFunctionRef? (n : Node) : Option DeclRef := do
  match n.kind?, n.children with
  | some .declRefExpr, _ => n.header?.bind (·.referencedDecl)
  | some .parenExpr, #[e] => directFunctionRef? e
  | some .implicitCastExpr, #[e] =>
    guard (["BuiltinFnToFnPtr", "FunctionToPointerDecay"].contains
      ((n.header?.bind (·.castKind)).getD ""))
    directFunctionRef? e
  | _, _ => none

/-- A function that the program calls without declaring it (gnu11 accepts this, as gcc does):
Clang declares it implicitly, with its library prototype when it is a library builtin
(`double ldexp(double, int)`) and as `int f()` otherwise. That declaration is not in the JSON
(an implicit builtin's is skipped as Clang's own): it becomes a declaration of sigma, of the
type of the reference, like an explicit declaration of that type. Clang's own `__` builtins
have no definition to link to, and `assert` is Cerberus's keyword (`assertCall?`). -/
def implicitFunction (r : DeclRef) : M Unit := do
  let some name := r.name | return
  if name == "assert" then throw "assert used as a value is not supported"
  if name.startsWith "__" then return
  if (← get).globals.any fun g => g.name == name && !g.blockScope then
    throw s!"{name}: an implicit declaration that Clang does not link to the earlier declaration"
  let some ty := r.type | throw s!"implicit declaration of {name} without a type"
  let (ret, ps, v) ← match (← parseType ty.qualType).2 with
    | .mk _ (.function r ps v) =>
      pure (r, ps.map fun (q, t, b) => ({ noQuals with restrict := q.restrict }, t, b), v)
    | .mk _ (.functionNoParams r) => pure (r, [], false)
    | _ => throw s!"implicit declaration of {name}: not a function type"
  let s ← fresh (.id name)
  let g : Global := { sym := s, name, isFunction := true, isStatic := false,
                      firstIsDefinition := false, decl := .function true ret ps v false false,
                      kind := .declaration }
  modify fun st => { st with declSyms := st.declSyms.insert r.id s,
                             globals := st.globals.push g,
                             globalIdx := st.globalIdx.insert s.number st.globals.size }

/-! ### Dynamic stack storage (`Silmaril.Clang.Stack`) -/

def localBinding (q : Qualifiers) (t : Ctype) (isRegister : Bool) :
    (Cerberus.Loc × StorageDuration × Bool) × Option Alignment × Qualifiers × Ctype :=
  ((.unknown, .automatic, isRegister), none, q, t)

partial def boundVariable : Type.BoundExpr → Bool
  | .var _ => true
  | .cast _ e | .addrOf e | .member e _ _ | .neg e => boundVariable e
  | .binary _ a b => boundVariable a || boundVariable b
  | _ => false

/-- The element and the bound of a variable-length array's type spelling. -/
def vlaSpelling? (s : String) : Option (Type.TypeSpelling × Type.BoundExpr) :=
  match Type.parse s with
  | .ok (.arrayExpr e b) => if boundVariable b then some (e, b) else none
  | _ => none

/-- Whether a function body declares a variable-length array, and whether it calls `alloca`. -/
partial def stackUses (n : Node) : Bool × Bool :=
  let own : Bool × Bool := match n.header? with
    | some h =>
      (h.kind == .varDecl && (h.type.bind fun t => vlaSpelling? t.qualType).isSome,
       h.kind == .declRefExpr && (h.referencedDecl.bind (·.name)) == some "__builtin_alloca")
    | none => (false, false)
  n.children.foldl (fun (v, a) c => let (v', a') := stackUses c; (v || v', a || a')) own

/-- The arena and its top, declared on first use. -/
def ensureArena : M (Sym × Sym) := do
  if let some a := (← get).arena then return a
  let arena ← fresh (.id "__cfront_stack")
  let top ← fresh (.id "__cfront_top")
  -- The arena has no initialiser: ccomp zero-fills a static object without one, and a list of
  -- its million zeros would be the bulk of the program. The top is a tentative definition.
  let gs : List Global :=
    [{ sym := arena, name := "__cfront_stack", isFunction := false, isStatic := true,
       firstIsDefinition := true, decl := .object (.static, false) none noQuals Stack.arenaType,
       kind := .definition },
     { sym := top, name := "__cfront_top", isFunction := false, isStatic := true,
       firstIsDefinition := false, decl := .object (.static, false) none noQuals Builtin.ulT,
       kind := .tentative }]
  for g in gs do
    if (← get).globals.any (·.name == g.name) then throw s!"{g.name} is declared by the program"
    modify fun st => { st with globals := st.globals.push g,
                               globalIdx := st.globalIdx.insert g.sym.number st.globals.size }
  modify fun st => { st with arena := some (arena, top) }
  return (arena, top)

/-- `push(bytes)`: a `char *` to a fresh block of the arena. -/
def stackPush (bytes : TypedExpression) : M TypedExpression := do
  let (arena, top) ← ensureArena
  let f ← builtinHelper "stack/push" (Builtin.ptrT Stack.charT) [Builtin.ulT] 3 (Stack.push arena top)
  return Builtin.rv (Builtin.ptrT Stack.charT) (.call f [bytes])

/-- `__cfront_top = base;` of the current function. -/
def stackRestore (f : StackFrame) : M TypedStatement := do
  let (_, top) ← ensureArena
  return Stack.assign Builtin.ulT top (Builtin.get Builtin.ulT f.base)

def shapeType : Nat × Bool → M Ctype
  | (32, true) => return intTy (.signed .int)
  | (32, false) => return intTy (.unsigned .int)
  | (64, true) => return intTy (.signed .long)
  | (64, false) => return intTy (.unsigned .long)
  | (w, _) => throw s!"variable-length array bound: a {w}-bit integer"

/-- The typedef names of a type spelling. -/
partial def spellingTypedefs : Type.TypeSpelling → List String
  | .leaf _ (.typedefName x) => [x]
  | .leaf _ _ => []
  | .pointer _ t | .array t _ | .arrayExpr t _ => spellingTypedefs t
  | .function r ps _ => spellingTypedefs r ++ (ps.getD []).flatMap spellingTypedefs

/-- The value of a variable-length array's bound and its type's width and signedness: integer
literals, integer objects of the function, `sizeof(type)`, unary `-` and `+ - * / %`, with the
usual arithmetic conversions as explicit casts. The names are resolved in the function's
scopes (`LocalName`); a name outside them, or a type name that an object hides, rejects. -/
partial def vlaBound : Type.BoundExpr → M (TypedExpression × Nat × Bool)
  | .num n sfx => do
    let (w, s) ← literalShape n sfx
    let sfx' : Option IntegerSuffix ← match sfx with
      | "" => pure none
      | "U" => pure (some .u)
      | "L" => pure (some .l)
      | "LL" => pure (some .ll)
      | "UL" | "LU" => pure (some .ul)
      | "ULL" | "LLU" => pure (some .ull)
      | x => throw s!"variable-length array bound: integer suffix {x}"
    let t ← shapeType (w, s)
    return (Builtin.rv t (.const (.integer (.iconstant n (basisOf n) sfx'))), w, s)
  | .var x => do
    match (← get).localNames[x]? with
    | some (.object s t) =>
      let .mk _ (.basic (.integer it)) := t
        | throw s!"variable-length array bound: {x} is not an integer"
      if it matches .enum _ then throw s!"variable-length array bound: {x} of an enum type"
      let (w, sg) ← intShape it
      return (Builtin.get t s, w, sg)
    | _ => throw s!"variable-length array bound: {x} is not an object of the function"
  | .sizeofType ts => do
    for x in spellingTypedefs ts do
      match (← get).localNames[x]? with
      | none | some .typedefName => pure ()
      | _ => throw s!"variable-length array bound: sizeof({x}) of a hidden type name"
    let (q, t) ← resolve ts
    return (Builtin.rv Builtin.ulT (.sizeof q t), 64, false)
  | .neg e => do
    let (x, w, s) ← vlaBound e
    let (w, s) := promoteShape w s
    let t ← shapeType (w, s)
    return (Builtin.rv t (.unary .minus (Builtin.cast t x)), w, s)
  | .binary op a b => do
    let (x, wa, sa) ← vlaBound a
    let (y, wb, sb) ← vlaBound b
    let (w, s) := commonShape (wa, sa) (wb, sb)
    let t ← shapeType (w, s)
    let o : ArithmeticOperator ← match op with
      | '+' => pure .add
      | '-' => pure .sub
      | '*' => pure .mul
      | '/' => pure .div
      | '%' => pure .mod
      | _ => throw s!"variable-length array bound: operator {op}"
    return (Builtin.arith t o (Builtin.cast t x) (Builtin.cast t y), w, s)
  | _ => throw "variable-length array bound: an unsupported form"

/-- A variable-length array `T a[e]`: a pointer `a` to a block of the arena, its length and its
end mark, as `Silmaril.Clang.Stack` describes. -/
def vlaDecl (c : Node) (h : Header) (name : String) (elem : Type.TypeSpelling)
    (bound : Type.BoundExpr) : M (Bindings × List TypedStatement) := do
  let some f := (← get).stack | throw s!"variable-length array {name} outside a function body"
  unless f.vla do throw s!"variable-length array {name} in a function that calls alloca"
  if h.storageClass.isSome then throw s!"variable-length array {name} with a storage class"
  if h.init.isSome || !c.children.isEmpty then
    throw s!"variable-length array {name} with an initialiser or attributes"
  let (q, t) ← resolve elem
  let (size, natural) ← match Bitfield.sizeAlign (← get).tagDefIdx t with
    | .ok r => pure r
    | .error e => throw s!"variable-length array {name}: {e}"
  -- an aligned typedef raises the element's alignment above its type's (the arena block is
  -- only 16-aligned)
  let align := max natural ((← spellingAlignment elem).getD 0)
  unless 0 < size && align ≤ 16 do
    throw s!"variable-length array {name}: element of size {size} and alignment {align}"
  let (e, _, _) ← vlaBound bound
  let (_, top) ← ensureArena
  let mark := (← get).stackMarks.head?.getD f.base
  let a ← fresh (.id name)
  let len ← fresh .none
  let stop ← fresh .none
  let pt := ct (.pointer q t)
  let bytes := Builtin.arith Builtin.ulT .mul (Builtin.get Builtin.ulT len)
    (Builtin.rv Builtin.ulT (.sizeof q t))
  let p ← stackPush bytes
  modify fun st => { st with
    declSyms := st.declSyms.insert h.id a, vlas := st.vlas.insert a.number (q, t, len),
    stackMarks := stop :: st.stackMarks, localNames := st.localNames.insert name .other }
  let bs : Bindings := [(len, localBinding noQuals Builtin.ulT false),
    (a, localBinding noQuals pt false), (stop, localBinding noQuals Builtin.ulT false)]
  return (bs,
    [Stack.assign Builtin.ulT top (Builtin.get Builtin.ulT mark),
     stmt (.declaration [(len, some (Builtin.cast Builtin.ulT e))]),
     stmt (.declaration [(a, some (Builtin.cast pt p))]),
     stmt (.declaration [(stop, some (Builtin.get Builtin.ulT top))])])

/-- The variable-length array that `n` names (through parentheses): its pointer, element and
length. -/
def vlaRef? (n : Node) : M (Option (Sym × Qualifiers × Ctype × Sym)) := do
  let n := stripParens n
  unless n.kind? == some .declRefExpr do return none
  let some r := n.header?.bind (·.referencedDecl) | return none
  let some s := (← get).declSyms[r.id]? | return none
  return (← get).vlas[s.number]?.map fun (q, t, len) => (s, q, t, len)

/-! ### Expressions and initialisers -/

/-! ### GNU vectors (`Silmaril.Clang.Vector`) -/

/-- Whether a node's type is spelled with a GNU vector, directly or under typedef sugar. -/
def mentionsVector (n : Node) : Bool :=
  let has := fun (s : String) => (s.splitOn "__vector_size__").length > 1
  match n.header?.bind (·.type) with
  | some t => has t.qualType || t.desugaredQualType.any has
  | none => false

/-- The element type of a (multidimensional) array type, or the type itself. -/
partial def arrayElem : Ctype → Ctype
  | .mk _ (.array e _) => arrayElem e
  | t => t

/-- Whether a type, or the element type of an array, is a record whose alignment was requested. -/
def userAlignedType (t : Ctype) : M Bool := do
  match arrayElem t with
  | .mk _ (.struct s) | .mk _ (.union s) => return (← get).userAligned.contains s.number
  | _ => return false

/-- The lane struct, lane type and lane count of a vector type. -/
def vectorOf? (t : Ctype) : M (Option (Sym × Ctype × Nat)) := do
  match t with
  | .mk _ (.struct s) => return ((← get).vectorLanes[s.number]?).map fun (lt, n) => (s, lt, n)
  | _ => return none

/-- The vector type of an expression's annotation. -/
def vectorAnnot? : GenTypeCategory → M (Option (Sym × Ctype × Nat))
  | .lvalue _ t _ => vectorOf? t
  | .rvalue (.struct s) => vectorOf? (ct (.struct s))
  | _ => return none

/-- A vector operand of a synthesized operation: an rvalue of the vector type `s`. -/
def vectorOperand (s : Sym) (e : TypedExpression) : M Unit := do
  match e.annotation with
  | .rvalue (.struct s') => unless s'.number == s.number do throw "vector operands of two types"
  | _ => throw "a vector operand that is not an rvalue of the vector type"

/-- A designator of the synthesized function `key`, a static definition of type `ret (ps)` whose
body `body` makes from its parameters and a local, defined on first use. -/
def vectorHelper (key : String) (ret : Ctype) (ps : List Ctype)
    (body : List Sym → Sym → TypedStatement) : M TypedExpression := do
  if (← get).staticInit then
    throw "a vector operation in a static initialiser (not a constant expression)"
  let params := ps.map (noQuals, ·, false)
  let st ← get
  let sym ← match st.vectorHelpers[key]? with
    | some s => pure s
    | none => do
      let name := s!"__cfront_vector_op{st.vectorHelpers.size}"
      let sym ← fresh (.id name)
      let psyms ← ps.mapM fun _ => fresh .none
      let local_ ← fresh .none
      let marker ← freshNat
      let g : Global :=
        { sym, name, isFunction := true, isStatic := true, firstIsDefinition := true,
          decl := .function false (noQuals, ret) params false false false, kind := .definition }
      let fd : FunctionDefinition GenTypeCategory :=
        { loc := .unknown, marker, attrs := noAttrs, params := psyms, body := body psyms local_ }
      modify fun st => { st with
        globals := st.globals.push g, globalIdx := st.globalIdx.insert sym.number st.globals.size,
        functionDefinitions := st.functionDefinitions.push (sym, fd),
        vectorHelpers := st.vectorHelpers.insert key sym }
      pure sym
  let f := mkExpr (.rvalue (.function (noQuals, ret) params false)) (.ident sym)
  return mkExpr (.rvalue (.pointer noQuals (ct (.function (noQuals, ret) params false)))) (.functionDecay f)

/-- A call of a synthesized vector operation. -/
def vectorCall (key : String) (ret : Ctype) (ps : List Ctype)
    (body : List Sym → Sym → TypedStatement) (args : List TypedExpression) : M TypedExpression := do
  let f ← vectorHelper key ret ps body
  return mkExpr (.rvalue (← genOf ret)) (.call f args)

/-- Whether the bytes of a value of a scalar type mean in ccomp what they mean in gcc: integers,
`double` and pointers, not `float` (8 bytes in ccomp), `long double` or `_Bool`. -/
def punnableScalar : Ctype → Bool
  | .mk _ (.basic (.integer .bool)) | .mk _ (.basic (.integer (.enum _))) => false
  | .mk _ (.basic (.integer _)) | .mk _ (.basic (.floating (.realFloating .double))) => true
  | .mk _ (.pointer ..) => true
  | _ => false

/-- A bit cast between a vector and a type of the same size: the bytes of `x` (of type `src`)
as a `dst`, through a union of the two (`Vector.bitcast`). -/
def vectorBitcast (src dst : Ctype) (x : TypedExpression) : M TypedExpression := do
  let lanesOf := fun (t : Ctype) => do
    match ← vectorOf? t with
    | some (_, lt, _) => pure lt
    | none => pure t
  unless punnableScalar (← lanesOf src) && punnableScalar (← lanesOf dst) do
    throw "a bit cast of a vector of float lanes, or of a type other than an integer, double or pointer"
  let defs := (← get).tagDefIdx
  let size := fun (t : Ctype) => match Bitfield.sizeAlign defs t with
    | .ok (k, _) => pure k
    | .error e => throw s!"vector bit cast: {e}"
  unless (← size src) == (← size dst) do throw "a vector bit cast between types of different sizes"
  let types := s!"{reprStr src}/{reprStr dst}"
  let st ← get
  let u ← match st.vectorTags[s!"pun/{types}"]? with
    | some u => pure u
    | none => do
      let u ← fresh (.id s!"__cfront_vector_pun{st.vectorTags.size}")
      let d := TagDefinition.union (Vector.punMembers src dst)
      modify fun st => { st with
        vectorTags := st.vectorTags.insert s!"pun/{types}" u, tagDefIdx := st.tagDefIdx.insert u.number d,
        tagDefs := st.tagDefs.push (u, (.unknown, noAttrs, d)) }
      pure u
  vectorCall s!"cast/{types}" dst [src] (fun ps l => match ps with
    | [a] => Vector.bitcast u src dst a l
    | _ => Vector.stmt .skip) [x]

/-- The synthetic tag and component type of a complex pair. -/
def complexOf? : Ctype → M (Option (Sym × Ctype))
  | .mk _ (.struct s) => return ((← get).complexParts[s.number]?).map (s, ·)
  | _ => return none

def complexAnnot? : GenTypeCategory → M (Option (Sym × Ctype))
  | .lvalue _ t _ => complexOf? t
  | .rvalue (.struct s) => complexOf? (ct (.struct s))
  | _ => return none

/-- Reuse the synthesized-function machinery with a disjoint key namespace. -/
def complexCall (key : String) (ret : Ctype) (ps : List Ctype)
    (body : List Sym → TypedStatement) (args : List TypedExpression) : M TypedExpression := do
  if (← get).staticInit then throw "a complex operation in a static initializer"
  vectorCall ("complex/" ++ key) ret ps (fun ps _ => body ps) args

/-- Whether a layout contains a complex pair (pointees do not affect a pointer's layout). -/
def containsComplex : Nat → Ctype → M Bool
  | 0, _ => throw "complex layout: nesting limit"
  | fuel + 1, .mk _ ty => do
    if (← get).complexParts.isEmpty then return false
    match ty with
    | .array t _ => containsComplex fuel t
    | .struct s | .union s =>
      if (← get).complexParts.contains s.number then return true
      match (← get).tagDefIdx[s.number]? with
      | some (.struct ms _) | some (.union ms) =>
        ms.anyM fun (_, (_, _, _, t)) => containsComplex fuel t
      | none => return false
    | _ => return false

/-- Whether a type contains a packed byte layout, whose original members can make its
layout differ from Clang's (`checkFoldedType`). -/
def containsPacked : Nat → Ctype → M Bool
  | 0, _ => throw "packed layout: nesting limit"
  | fuel + 1, .mk _ ty => do
    if (← get).packedRecords.isEmpty then return false
    match ty with
    | .array t _ => containsPacked fuel t
    | .struct s | .union s =>
      if (← get).packedRecords.contains s.number then return true
      match (← get).tagDefIdx[s.number]? with
      | some (.struct ms _) | some (.union ms) =>
        ms.anyM fun (_, (_, _, _, t)) => containsPacked fuel t
      | none => return false
    | _ => return false

/-- A complex condition tests both components and evaluates the value once. -/
def condition (e : TypedExpression) : M TypedExpression := do
  let some (s, t) ← complexAnnot? e.annotation | return e
  complexCall s!"truth/{s.number}" Builtin.intT [ct (.struct s)] (fun ps => match ps with
    | [a] => Complex.truth s t a
    | _ => stmt .skip) [e]

/-- Clang prints the desugared spelling for a complex typedef's expressions. -/
def mentionsComplex (n : Node) : Bool :=
  let has := fun (s : String) => (s.splitOn "_Complex").length > 1
  n.header?.any fun h => h.type.any fun t => has t.qualType || t.desugaredQualType.any has

mutual

/-- The storage unit of a bit-field access, given its operand. A write (`reuse`) evaluates the
operand more than once, so it must have no side effects. -/
partial def bitfieldUnit (f : Bitfield.Field) (b : Node) (arrow reuse : Bool) : M TypedExpression := do
  if reuse && !sideEffectFree b then
    throw s!"bit-field {f.name} written through an operand with side effects"
  let e ← expr b
  let q ← match e.annotation, arrow with
    | .lvalue q _ _, false => pure q
    | .rvalue (.pointer q _), true => pure q
    | _, _ => throw s!"bit-field {f.name} of a struct rvalue"
  return f.unitLvalue q e arrow

/-- A cast (castKind `k`) to or from a GNU vector, or none if neither type is one: a vector's
own type (`NoOp`, or a `BitCast` between one vector type), a broadcast (`VectorSplat`), or a
reinterpretation (`BitCast`). Any other conversion of a vector is rejected. -/
partial def vectorCast? (h : Header) (k : String) (e : Node) : M (Option TypedExpression) := do
  let some eh := e.header? | throw "absent cast operand"
  let (_, dst) ← headerType h
  let (_, src) ← headerType eh
  let vd ← vectorOf? dst
  let vs ← vectorOf? src
  if vd.isNone && vs.isNone then return none
  match k, vd, vs with
  | "VectorSplat", some (s, lt, n), none =>
    let x ← expr e
    return some (← vectorCall s!"splat/{s.number}" dst [lt] (fun ps r => match ps with
      | [a] => Vector.splat s lt n a r
      | _ => Vector.stmt .skip) [x])
  | "BitCast", some (a, _, _), some (b, _, _) | "NoOp", some (a, _, _), some (b, _, _) =>
    let x ← expr e
    if a.number == b.number then return some x
    unless k == "BitCast" do throw "a NoOp conversion between vector types"
    vectorOperand b x
    return some (← vectorBitcast src dst x)
  | "BitCast", _, _ =>
    let x ← expr e
    match x.annotation with
    | .rvalue _ => return some (← vectorBitcast src dst x)
    | _ => throw "a vector bit cast of an lvalue"
  | k, _, _ => throw s!"the conversion {k} of a vector"

/-- The right operand of a shift. A scalar count of a vector shift is splat by Clang into an
`int` vector with no typedef (`ext_vector_type`), which has no lane struct: it is splat into the
shifted operand's own vector type instead, so every lane is shifted by the scalar, as gcc's are
(a count outside the lane width is undefined in both). -/
partial def shiftCount (a b : Node) : M TypedExpression := do
  if let (some .implicitCastExpr, some bh, #[x], some ah) := (b.kind?, b.header?, b.children, a.header?) then
    if bh.castKind == some "VectorSplat" then
      let (_, at_) ← headerType ah
      if let some (s, lt, n) ← vectorOf? at_ then
        let .mk _ (.basic (.integer _)) := lt | throw "a shift of a vector of non-integer lanes"
        return ← vectorCall s!"splat/{s.number}" (ct (.struct s)) [lt] (fun ps r => match ps with
          | [p] => Vector.splat s lt n p r
          | _ => Vector.stmt .skip) [Builtin.cast lt (← expr x)]
  expr b

/-- A binary operator on vectors (both of one vector type, after Clang's conversions), or none
if no operand is a vector. -/
partial def vectorBinary? (h : Header) (o : String) (ea eb : TypedExpression) :
    M (Option TypedExpression) := do
  let va ← vectorAnnot? ea.annotation
  let vb ← vectorAnnot? eb.annotation
  if va.isNone && vb.isNone then return none
  let some (s, t, n) := va | throw s!"the vector operator {o} with a scalar left operand"
  vectorOperand s ea
  vectorOperand s eb
  let vt := ct (.struct s)
  match arithmeticOp o, binaryOp o with
  | some op, _ =>
    return some (← vectorCall s!"{o}/{s.number}" vt [vt, vt] (fun ps r => match ps with
      | [a, b] => Vector.binary s t n op a b r
      | _ => Vector.stmt .skip) [ea, eb])
  | none, some bop =>
    unless ["<", ">", "<=", ">=", "==", "!="].contains o do throw s!"the vector operator {o}"
    let (_, mt) ← headerType h
    let some (m, mlt, mn) ← vectorOf? mt | throw s!"vector comparison {o} without a vector type"
    -- the mask lanes: a signed integer type of the operands' lane size
    let .mk _ (.basic (.integer mit)) := mlt | throw "a vector comparison of non-integer lanes"
    let (_, signed) ← intShape mit
    let sameSize := match Vector.laneSize mlt, Vector.laneSize t with
      | .ok a, .ok b => a == b
      | _, _ => false
    unless mn == n && signed && sameSize do
      throw "a vector comparison of an unexpected type"
    return some (← vectorCall s!"{o}/{s.number}/{m.number}" mt [vt, vt] (fun ps r => match ps with
      | [a, b] => Vector.compare s t n m mlt bop a b r
      | _ => Vector.stmt .skip) [ea, eb])
  | none, none => throw s!"the vector operator {o}"

/-- Only listed real/complex conversions are accepted; no struct casts escape to Ail. -/
partial def complexCast? (h : Header) (k : String) (e : Node) : M (Option TypedExpression) := do
  let some eh := e.header? | throw "absent complex conversion operand"
  let (_, dst) ← headerType h
  let (_, src) ← headerType eh
  let vd ← complexOf? dst
  let vs ← complexOf? src
  if vd.isNone && vs.isNone then return none
  let x ← expr e
  match k, vd, vs with
  | "FloatingRealToComplex", some (s, t), none =>
    return some ((if (← get).staticInit then Complex.initValue else Complex.value) s
      (Builtin.cast t x) (Complex.zero t))
  | "FloatingComplexCast", some (d, dt), some (s, st) =>
    return some (← complexCall s!"cast/{s.number}/{d.number}" dst [src] (fun ps => match ps with
      | [a] => Complex.convert s st d dt a
      | _ => stmt .skip) [x])
  | "FloatingComplexToReal", none, some (s, t) =>
    return some (← complexCall s!"real/{s.number}/{reprStr dst}" dst [src] (fun ps => match ps with
      | [a] => Builtin.ret (Builtin.cast dst (Complex.part s t a false))
      | _ => stmt .skip) [x])
  | "FloatingComplexToBoolean", none, some _ =>
    return some (Builtin.cast dst (← condition x))
  | "NoOp", some (d, _), some (s, _) =>
    unless d.number == s.number do throw "complex NoOp conversion between different types"
    return some x
  | _, _, _ => throw s!"complex conversion {k} is not supported"

/-- Componentwise arithmetic and comparisons; multiplication and division need separate
IEEE exceptional-value algorithms and reject until those are validated. -/
partial def complexBinary? (o : String) (ea eb : TypedExpression) : M (Option TypedExpression) := do
  let va ← complexAnnot? ea.annotation
  let vb ← complexAnnot? eb.annotation
  if va.isNone && vb.isNone then return none
  let some (s, t) := va.orElse (fun _ => vb) | throw "complex operand expected"
  if let some (sa, _) := va then
    unless sa.number == s.number do throw "different complex operand types"
  if let some (sb, _) := vb then
    unless sb.number == s.number do throw "different complex operand types"
  unless ["+", "-", "==", "!="].contains o do throw s!"complex operator {o} is not supported"
  let vt := ct (.struct s)
  let left := va.isSome
  let right := vb.isSome
  let ps := [if left then vt else t, if right then vt else t]
  let ret := if o == "==" || o == "!=" then Builtin.intT else vt
  let arg := fun (pair : Bool) (x : TypedExpression) => if pair then x else Builtin.cast t x
  return some (← complexCall s!"{o}/{s.number}/{left}/{right}" ret ps (fun ps => match ps with
    | [a, b] =>
      let part := fun (pair : Bool) (x : Sym) (im : Bool) =>
        if pair then Complex.part s t x im else if im then Complex.zero t else Builtin.get t x
      if o == "==" || o == "!=" then
        let op : BinaryOperator := if o == "==" then .eq else .ne
        Builtin.ret (Builtin.test (if o == "==" then .and else .or)
          (Builtin.test op (part left a false) (part right b false))
          (Builtin.test op (part left a true) (part right b true)))
      else
        let op : ArithmeticOperator := if o == "+" then .add else .sub
        -- A real operand has no imaginary component: do not add a synthetic zero,
        -- which would change the sign of a zero imaginary component.
        let im := if left && right then Builtin.arith t op (part true a true) (part true b true)
          else if left then part true a true
          else if o == "+" then part true b true
          else Vector.rv t (.unary .minus (part true b true))
        Builtin.ret (Complex.value s (Builtin.arith t op (part left a false) (part right b false)) im)
    | _ => stmt .skip) [arg left ea, arg right eb])

partial def expr (n : Node) : M TypedExpression := do
  let some h := n.header? | throw "absent expression"
  if h.kind == .chooseExpr then return ← expr (← chooseOperand n)
  -- a value of gcc's type of a wide bit-field (`wideType?`) is converted, passed or computed
  -- with by the operators that reduce to that type; any other use rejects
  unless h.kind == .implicitCastExpr || h.kind == .cStyleCastExpr || h.kind == .parenExpr ||
      h.kind == .callExpr || h.kind == .conditionalOperator ||
      (h.kind == .binaryOperator && h.opcode != some ",") ||
      (h.kind == .unaryOperator && ["-", "+", "~", "!"].contains (h.opcode.getD "")) do
    for c in n.children do
      if let some f ← wideValue? c then
        throw s!"the {f.width}-bit field {f.name} of a {f.tyBits}-bit type in {h.kind} (gcc and Clang differ)"
      if let some (w, _) ← wideType? c then
        throw s!"a value of gcc's {w}-bit type of a bit-field in {h.kind} (gcc and Clang differ)"
  let one : M Node := match n.children with
    | #[e] => pure e
    | _ => throw s!"{h.kind} {h.id}: one operand expected"
  let two : M (Node × Node) := match n.children with
    | #[a, b] => pure (a, b)
    | _ => throw s!"{h.kind} {h.id}: two operands expected"
  if h.kind == .integerLiteral || h.kind == .parenExpr then
    if let some c ← limitConst n h then return c
  match h.kind with
  | .opaqueValueExpr =>
    match (← get).liftedValues[h.id]? with
    | some e => return e
    | none => throw "OpaqueValueExpr outside a lowered statement expression"
  | .integerLiteral => integerLiteral h
  | .characterLiteral => characterLiteral h
  | .floatingLiteral => floatingLiteral h
  | .imaginaryLiteral =>
    let (_, t) ← headerType h
    let some (s, rt) ← complexOf? t | throw "imaginary literal without a complex type"
    return (if (← get).staticInit then Complex.initValue else Complex.value) s
      (Complex.zero rt) (Builtin.cast rt (← expr (← one)))
  | .stringLiteral =>
    let (s, t) ← stringLiteral h
    return mkExpr (.lvalue noQuals t false) (.str s)
  | .parenExpr | .constantExpr | .exprWithCleanups | .materializeTemporaryExpr => expr (← one)
  | .genericSelectionExpr =>
    -- Clang has resolved the selection (STD §6.5.1.1): the result is the selected
    -- association's expression (its last child), and the controlling expression is not
    -- evaluated. Cerberus keeps every association (`AilEgeneric`), but ccomp lowers that
    -- only as an rvalue, and a selected lvalue or function designator is valid C.
    let sel := n.children.filter fun
      | .association _ (some true) _ => true
      | _ => false
    let #[a] := sel | throw s!"GenericSelectionExpr {h.id}: one selected association expected"
    let some e := a.children.back? | throw s!"GenericSelectionExpr {h.id}: absent association"
    expr e
  | .predefinedExpr =>
    -- `__func__`/`__FUNCTION__` (STD §6.4.2.2): Clang gives the function's name as the
    -- string literal child; Ail reads it as that literal (an unmodifiable char array)
    let e ← one
    unless (e.header?.map (·.kind)) == some .stringLiteral do
      throw s!"PredefinedExpr {h.id}: a string literal operand expected"
    expr e
  | .compoundLiteralExpr =>
    let (q, t) ← headerType h
    if (← get).localScope then checkFrameAlignment "compound literal" t
    return mkExpr (.lvalue q t false) (.compound q t (← initializer t (← one)))
  | .declRefExpr =>
    let some r := h.referencedDecl | throw s!"DeclRefExpr {h.id} without a declaration"
    if (libraryBuiltin? (r.name.getD "")).isSome ||
        (scalarBuiltin? (r.name.getD "")).isSome || (semanticBuiltin? (r.name.getD "")).isSome then
      throw "library builtin used outside a supported direct call"
    if let some v ← enumConst? r then return intConst v
    if r.kind == "FunctionDecl" && !(← get).declSyms.contains r.id then implicitFunction r
    let some s := (← get).declSyms[r.id]? | throw s!"DeclRefExpr {h.id}: unknown {r.kind} {r.name.getD r.id}"
    if (← get).vlas.contains s.number then
      throw s!"variable-length array {r.name.getD r.id} used other than by decay or sizeof"
    -- a function designator has the type of the function's declaration in sigma (Cerberus):
    -- `int f();` is a function of no parameters there
    if let some g ← globalOf? s then
      if let .function _ ret ps v _ _ := g.decl then
        if g.isFunction then return mkExpr (.rvalue (.function ret ps v)) (.ident s)
    let a ← annotOf h ((← get).registers.contains s.number)
    if let some w := (← get).alignedObjects[s.number]? then
      let .lvalue q _ _ := a | throw "over-aligned object: an lvalue expected"
      return mkExpr a (.memberof (mkExpr (.lvalue q (ct (.struct w.tag)) false) (.ident s)) w.member)
    match a, (← get).paramQuals[s.number]? with
    | .lvalue _ t r, some q => return mkExpr (.lvalue q t r) (.ident s)
    | _, _ => return mkExpr a (.ident s)
  | .implicitCastExpr =>
    let e ← one
    match h.castKind with
    | some "LValueToRValue" =>
      if let some (f, b, arrow) ← bitfieldAccess? e then
        return f.read (← bitfieldUnit f b arrow false)
      if let some (ap, d) := vaArg? e then
        let (_, t) ← headerType d
        return mkExpr (.rvalue (← genOf t)) (.vaArg (← expr ap) t)
      return mkExpr (← annotOf h) (.rvalue (← expr e))
    | some "ArrayToPointerDecay" =>
      -- a variable-length array is its pointer
      if let some (s, q, t, _) ← vlaRef? e then
        let pt := ct (.pointer q t)
        return Builtin.load pt (mkExpr (.lvalue noQuals pt false) (.ident s))
      -- Cerberus's decay drops the array's qualifiers: `const int a[]` decays to `int *`
      let a ← expr e
      match a.annotation with
      | .lvalue _ (.mk _ (.array t _)) _ | .rvalue (.array t _) =>
        return mkExpr (.rvalue (.pointer noQuals t)) (.arrayDecay a)
      | _ => throw s!"ArrayToPointerDecay {h.id} of a non-array"
    | some "FunctionToPointerDecay" | some "BuiltinFnToFnPtr" =>
      let a ← expr e
      match a.annotation with
      | .rvalue (.function r ps v) =>
        return mkExpr (.rvalue (.pointer noQuals (ct (.function r ps v)))) (.functionDecay a)
      | _ =>
        let (_, t) ← headerType h
        let t := match t with
          | .mk as (.pointer q f) => Ctype.mk as (.pointer q (functionType f))
          | t => t
        return mkExpr (.rvalue (← genOf t)) (.functionDecay a)
    | some "ToVoid" =>
      -- GNU: `c ? f() : 0` converts the non-void operand to void, as `(void)0` would
      return mkExpr (.rvalue .void) (.cast noQuals (ct .void) (← expr e))
    | some k =>
      if mentionsComplex n || mentionsComplex e then
        if let some r ← complexCast? h k e then return r
      if mentionsVector n || mentionsVector e then
        if let some r ← vectorCast? h k e then return r
      if implicitConversions.contains k then
        if ← bitfieldValued e then
          let (q, t) ← headerType h
          return mkExpr (.rvalue (← genOf t)) (.cast q t (← expr e))
        expr e
      else throw s!"implicit conversion {k} is not supported"
    | none => throw s!"ImplicitCastExpr {h.id} without a cast kind"
  | .cStyleCastExpr =>
    -- `NULL` (`__cerbvar_NULL`, a Cerberus builtin, which the prelude defines as `((void *)0)`);
    -- a null constant cast to any other type in a macro (`((T *)0)->m`) keeps its type
    if mentionsComplex n || n.children.any mentionsComplex then
      let some k := h.castKind | throw "complex cast without a cast kind"
      if let some r ← complexCast? h k (← one) then return r
    if mentionsVector n || n.children.any mentionsVector then
      let some k := h.castKind | throw s!"CStyleCastExpr {h.id} without a cast kind"
      if let some r ← vectorCast? h k (← one) then return r
    let (q, t) ← headerType h
    if h.castKind == some "NullToPointer" && isMacro h then
      if let .mk _ (.pointer ⟨false, false, false⟩ (.mk _ .void)) := t then
        if let #[z] := n.children then
          if z.kind? == some .integerLiteral then
            return rvalue (.pointer noQuals (ct .void)) (.const .null)
    return mkExpr (.rvalue (← genOf t)) (.cast q t (← expr (← one)))
  | .unaryOperator =>
    if h.opcode == some "++" || h.opcode == some "--" then
      if let some (f, b, arrow) ← bitfieldAccess? (← one) then
        let u ← bitfieldUnit f b arrow true
        let incr := h.opcode == some "++"
        if h.isPostfix != some true then return f.assign u (f.step u incr)
        if f.ty == .bool then throw s!"postfix {h.opcode.getD ""} of the _Bool bit-field {f.name}"
        return f.postfix u incr
    let a ← expr (← one)
    if let some (s, t) ← complexAnnot? a.annotation then
      match h.opcode with
      | some "&" => pure ()
      | some "+" => return a
      | some "__real" | some "__imag" =>
        let im := h.opcode == some "__imag"
        match a.annotation with
        | .lvalue q _ reg =>
          return mkExpr (.lvalue q t reg) (.memberof a (Complex.component im))
        | .rvalue _ =>
          return ← complexCall s!"part/{s.number}/{im}" t [ct (.struct s)] (fun ps => match ps with
            | [x] => Builtin.ret (Complex.part s t x im)
            | _ => stmt .skip) [a]
      | some "-" | some "~" =>
        return ← complexCall s!"unary/{s.number}/{h.opcode}" (ct (.struct s)) [ct (.struct s)]
          (fun ps => match ps with
            | [x] => Complex.unary s t (h.opcode == some "~") x
            | _ => stmt .skip) [a]
      | some "!" => return Builtin.test .eq (← condition a) (intConst 0)
      | o => throw s!"complex unary operator {o} is not supported"
    if let some (s, t, k) ← vectorAnnot? a.annotation then
      let vt := ct (.struct s)
      match h.opcode with
      | some "&" => pure ()
      | some "+" => return a
      | some "-" | some "~" =>
        vectorOperand s a
        let op : UnaryOperator := if h.opcode == some "-" then .minus else .bnot
        -- a key of its own: binary `-` on the same vector type is `-/{s.number}`
        return ← vectorCall s!"unary/{h.opcode.getD ""}/{s.number}" vt [vt] (fun ps r => match ps with
          | [x] => Vector.unary s t k op x r
          | _ => Vector.stmt .skip) [a]
      | o => throw s!"the vector operator {o.getD ""}"
    let ann ← annotOf h
    match h.opcode, h.isPostfix with
    | some "-", _ => wideResult h (← gccOperand (← one)) (mkExpr ann (.unary .minus a))
    | some "+", _ => return mkExpr ann (.unary .plus a)
    | some "~", _ => wideResult h (← gccOperand (← one)) (mkExpr ann (.unary .bnot a))
    -- typed from the operand's (Cerberus's) typing, which can differ from Clang's in qualifiers
    | some "&", _ => match a.annotation with
      | .lvalue q t _ => return mkExpr (.rvalue (.pointer q t)) (.unary .address a)
      | _ => return mkExpr ann (.unary .address a)
    | some "*", _ => return mkExpr (derefAnnot a.annotation ann) (.unary .indirection a)
    -- Cerberus: `!e` is `0 == e`, `++e` is `e += 1`
    | some "!", _ => return mkExpr ann (.binary (intConst 0) .eq a)
    | some "++", some true => return mkExpr ann (.unary .postfixIncr a)
    | some "--", some true => return mkExpr ann (.unary .postfixDecr a)
    | some "++", _ => return mkExpr ann (.compoundAssign a .add (intConst 1))
    | some "--", _ => return mkExpr ann (.compoundAssign a .sub (intConst 1))
    | o, _ => throw s!"unary operator {o} is not supported"
  | .binaryOperator =>
    let (a, b) ← two
    let some o := h.opcode | throw s!"BinaryOperator {h.id} without an operator"
    if o == "=" then
      if let some (f, base, arrow) ← bitfieldAccess? a then
        let u ← bitfieldUnit f base arrow true
        return f.assign u (← expr b)
    let ea ← expr a
    let eb ← if o == "<<" || o == ">>" then shiftCount a b else expr b
    if o == "&&" || o == "||" then
      return mkExpr (← annotOf h) (.binary (← condition ea) (if o == "&&" then .and else .or) (← condition eb))
    if o != "=" && o != "," then
      if let some r ← complexBinary? o ea eb then return r
      if let some r ← vectorBinary? h o ea eb then return r
    let ann ← annotOf h
    if o == "=" then return mkExpr ann (.assign ea eb)
    let some op := binaryOp o | throw s!"binary operator {o} is not supported"
    if o == "&&" || o == "||" || o == "," then return mkExpr ann (.binary ea op eb)
    if o == "<<" || o == ">>" then
      -- of the left operand's type, unconverted
      let e := mkExpr ann (.binary ea op eb)
      return ← if o == "<<" then wideResult h (← gccOperand a) e else pure e
    -- Clang's computation type: the result's, or a comparison's converted operands'
    let some ch := (if (arithmeticOp o).isSome then some h else a.header?)
      | throw s!"BinaryOperator {h.id}: an operand without a type"
    match ← wideOperands ch a b ea eb with
    | some (g, ea, eb) =>
      let e := mkExpr ann (.binary ea op eb)
      if ["+", "-", "*"].contains o then wideResult ch g e else return e
    | none => return mkExpr ann (.binary ea op eb)
  | .compoundAssignOperator =>
    let (a, b) ← two
    let some o := h.opcode | throw s!"CompoundAssignOperator {h.id} without an operator"
    let some aop := arithmeticOp (String.ofList o.toList.dropLast)
      | throw s!"compound assignment {o} is not supported"
    if let some (f, base, arrow) ← bitfieldAccess? a then
      -- `x op= v` is `x = (T)((CLT)x op v)`. gcc evaluates `v` before it reads `x`: a `v`
      -- with side effects comes first, `v op (CLT)x`, so only for a commutative `op`
      let first := !sideEffectFree b
      if first && ![ArithmeticOperator.add, .mul, .band, .bor, .bxor].contains aop then
        throw s!"compound assignment {o} to bit-field {f.name} with side effects"
      -- gcc converts the right operand to the field's width: only operations that agree modulo it
      if f.wide && !["+=", "-=", "*=", "&=", "|=", "^="].contains o then
        throw s!"{o} on the {f.width}-bit field {f.name} of a {f.tyBits}-bit type (gcc and Clang differ)"
      let (some lt, some rt) := (h.computeLHSType, h.computeResultType)
        | throw s!"CompoundAssignOperator {h.id} without computation types"
      let (_, lt) ← parseType lt.qualType
      let (_, rt) ← parseType rt.qualType
      let u ← bitfieldUnit f base arrow true
      let x := mkExpr (.rvalue (← genOf lt)) (.cast noQuals lt (f.read u))
      let v ← expr b
      let (l, r) := if first then (v, x) else (x, v)
      return f.assign u (mkExpr (.rvalue (← genOf rt)) (.binary l (.arithmetic aop) r))
    let ea ← expr a
    let eb ← if o == "<<=" || o == ">>=" then shiftCount a b else expr b
    if (← complexAnnot? ea.annotation).isSome || (← complexAnnot? eb.annotation).isSome then
      throw s!"complex compound assignment {o} is not supported"
    if let some (s, t, k) ← vectorAnnot? ea.annotation then
      -- `a op= b` is `f(&a, b)`, `f` assigning `a op b` lane-wise through the pointer
      let .lvalue q _ _ := ea.annotation | throw s!"vector compound assignment {o} to an rvalue"
      unless q == noQuals do throw s!"vector compound assignment {o} to a qualified lvalue"
      vectorOperand s eb
      let vt := ct (.struct s)
      let pt := ct (.pointer noQuals vt)
      let addr := mkExpr (.rvalue (.pointer noQuals vt)) (.unary .address ea)
      return ← vectorCall s!"{o}/{s.number}" vt [pt, vt] (fun ps _ => match ps with
        | [p, x] => Vector.assignOp s t k aop p x
        | _ => Vector.stmt .skip) [addr, eb]
    if (← vectorAnnot? eb.annotation).isSome then throw s!"compound assignment {o} of a vector to a scalar"
    return mkExpr (← annotOf h) (.compoundAssign ea aop eb)
  | .conditionalOperator =>
    let #[c, a, b] := n.children | throw s!"ConditionalOperator {h.id}: three operands expected"
    let ec ← condition (← expr c)
    if (← vectorAnnot? ec.annotation).isSome then throw "a vector condition"
    let ea ← expr a
    let eb ← expr b
    let (ea, eb) := match ← wideOperands h a b ea eb with
      | some (_, ea, eb) => (ea, eb)
      | none => (ea, eb)
    return mkExpr (← annotOf h) (.cond ec (some ea) eb)
  | .binaryConditionalOperator =>
    -- GNU `c ?: b`: the condition, its value as a condition and as the result, the alternative;
    -- Cerberus's `cond c none b` (only when the value is the result unconverted)
    let #[c, oc, oa, b] := n.children
      | throw s!"BinaryConditionalOperator {h.id}: four children expected"
    unless oc.kind? == some .opaqueValueExpr && oa.kind? == some .opaqueValueExpr do
      throw s!"BinaryConditionalOperator {h.id}: a converted operand is not supported"
    let ec ← expr c
    if (← complexAnnot? ec.annotation).isSome then throw "complex GNU conditional is not supported"
    return mkExpr (← annotOf h) (.cond ec none (← expr b))
  | .callExpr =>
    let some f := n.children[0]? | throw s!"CallExpr {h.id} without a callee"
    -- Cerberus's `va_*` builtins, which `cerb-prelude.h` declares as functions for Clang
    match calleeName? n, n.children.toList.drop 1 with
    | some "__cerb_va_start", [ap, last] =>
      -- the last parameter, as a variadic argument: under its promotion
      let some r := (stripCasts last).header?.bind (·.referencedDecl)
        | throw "va_start: the last parameter expected"
      let some x := (← get).declSyms[r.id]? | throw "va_start: unknown parameter"
      return mkExpr (← annotOf h) (.vaStart (← expr ap) x)
    | some "__cerb_va_copy", [d, s'] => return mkExpr (← annotOf h) (.vaCopy (← expr d) (← expr s'))
    | some "__cerb_va_end", [ap] => return mkExpr (← annotOf h) (.vaEnd (← expr ap))
    | some x, _ => if x.startsWith "__cerb_va_" then throw s!"{x} outside its pattern"
    | none, _ => pure ()
    if let some r := directFunctionRef? f then
      let name := r.name.getD ""
      if name == "__builtin_alloca" then
        unless r.kind == "FunctionDecl" &&
            (r.type.map (·.qualType)) == some "void *(__size_t)" do
          throw "__builtin_alloca: builtin prototype mismatch"
        if (← get).declSyms.contains r.id then throw "__builtin_alloca: an explicit declaration"
        let some fr := (← get).stack | throw "__builtin_alloca outside a function body"
        if fr.vla then throw "__builtin_alloca in a function with variable-length arrays"
        let [arg] := n.children.toList.drop 1 | throw "__builtin_alloca: one argument expected"
        let (_, rt) ← headerType h
        return Builtin.cast rt (← stackPush (Builtin.cast Builtin.ulT (← expr arg)))
      if ["__builtin_conj", "__builtin_conjf", "__builtin_creal", "__builtin_crealf",
          "__builtin_cimag", "__builtin_cimagf"].contains name then
        let [arg] := n.children.toList.drop 1 | throw "complex builtin expects one argument"
        let x ← expr arg
        let some (s, t) ← complexAnnot? x.annotation | throw "complex builtin argument type"
        let isFloat := name.endsWith "f"
        let rt := if isFloat then ct (.basic (.floating (.realFloating .float)))
          else ct (.basic (.floating (.realFloating .double)))
        unless reprStr t == reprStr rt do throw "complex builtin component type mismatch"
        let conjugate := name.startsWith "__builtin_conj"
        let word := if isFloat then "float" else "double"
        let prototype := s!"{if conjugate then "_Complex " else ""}{word} (_Complex {word})"
        unless r.kind == "FunctionDecl" && (r.type.map (·.qualType)) == some prototype do
          throw "complex builtin prototype mismatch"
        if (← get).declSyms.contains r.id then throw "complex builtin explicitly declared"
        let ret := if conjugate then ct (.struct s) else t
        let (_, result) ← headerType h
        unless reprStr ret == reprStr result do throw "complex builtin result type mismatch"
        let im := name.startsWith "__builtin_cimag"
        return ← complexCall s!"builtin/{name}/{s.number}" ret [ct (.struct s)]
          (fun ps => match ps with
            | [a] => if conjugate then Complex.unary s t true a
              else Builtin.ret (Complex.part s t a im)
            | _ => stmt .skip) [x]
      if let some prototype := scalarBuiltin? name then
        unless r.kind == "FunctionDecl" && (r.type.map (·.qualType)) == some prototype do
          throw s!"{name}: builtin prototype mismatch"
        if (← get).declSyms.contains r.id then
          throw s!"{name}: an explicit declaration is not supported"
        let resultType := if name.startsWith "__builtin_expect" then "long" else "int"
        unless (h.type.map (·.qualType)) == some resultType do
          throw s!"{name}: builtin result type mismatch"
        match name, n.children.toList.drop 1 with
        | "__builtin_constant_p", [arg] =>
          let s := stripCasts arg
          if s.kind? == some .unaryExprOrTypeTraitExpr then
            -- gcc folds sizeof and alignof of a complete type; translating checks the type
            let _ ← expr s
            return intConst 1
          return intConst (if ← gccConstantP arg then 1 else 0)
        | "__builtin_classify_type", [arg] =>
          -- like gcc, the operand is not evaluated: only its converted type matters
          let some ah := arg.header? | throw "classify_type: an absent argument"
          return intConst (← classifyType (← headerType ah).2)
        | "__builtin_expect", [arg, expected] =>
          let _ ← constInt expected
          let (q, t) ← headerType h
          return mkExpr (← annotOf h) (.cast q t (← expr arg))
        | "__builtin_expect_with_probability", [arg, expected, probability] =>
          let _ ← constInt expected
          -- Do not discard an evaluated or unsupported probability expression.
          unless (stripCasts probability).kind? == some .floatingLiteral do
            throw "expect_with_probability: a floating literal probability expected"
          let (q, t) ← headerType h
          return mkExpr (← annotOf h) (.cast q t (← expr arg))
        | _, _ => throw s!"{name}: unsupported arguments"
      if let some (prototype, resultType) := semanticBuiltin? name then
        unless r.kind == "FunctionDecl" && (r.type.map (·.qualType)) == some prototype do
          throw s!"{name}: builtin prototype mismatch"
        if (← get).declSyms.contains r.id then
          throw s!"{name}: an explicit declaration is not supported"
        unless (h.type.map (·.qualType)) == some resultType do
          throw s!"{name}: builtin result type mismatch"
        return ← semanticCall h (String.ofList (name.toList.drop 10)) (n.children.toList.drop 1)
    let ef ← match directFunctionRef? f with
      | some r => match libraryBuiltin? (r.name.getD "") with
        | some (name, prototype) => libraryFunction r name prototype
        | none => expr f
      | none => expr f
    let args ← (n.children.extract 1 n.children.size).toList.mapM expr
    return mkExpr (← annotOf h) (.call ef args)
  | .arraySubscriptExpr =>
    -- `a[i]` is `*(a + i)` (STD §6.5.2.1#2)
    let (a, b) ← two
    let ea ← expr a
    if let some (_, t, k) ← vectorAnnot? ea.annotation then
      -- a lane of a vector: a constant index only
      let i ← constInt b
      unless 0 ≤ i && i < k do throw s!"lane {i} of a vector of {k} lanes"
      let ann ← match ea.annotation with
        | .lvalue q _ _ => pure (GenTypeCategory.lvalue q t false)
        | _ => pure (.rvalue (← genOf t))
      return mkExpr ann (.memberof ea (Vector.lane i.toNat))
    let eb ← expr b
    let pt ← match ea.annotation, eb.annotation with
      | t@(.rvalue (.pointer ..)), _ => pure t
      | _, t@(.rvalue (.pointer ..)) => pure t
      | _, _ => throw s!"ArraySubscriptExpr {h.id}: no pointer operand"
    return mkExpr (derefAnnot pt (← annotOf h))
      (.unary .indirection (mkExpr pt (.binary ea (.arithmetic .add) eb)))
  | .memberExpr =>
    if let some (f, _, _) ← bitfieldAccess? n then
      throw s!"bit-field {f.name} used as an object (address, or an unsupported operator)"
    let some m := h.name | throw s!"MemberExpr {h.id} without a member name"
    -- Clang spells `a.x` through an anonymous member as `a.<anonymous>.x`
    let m ← if !m.isEmpty then pure m else
      match h.referencedMemberDecl.bind ((← get).anonMembers[·]?) with
      | some x => pure x
      | none => throw s!"MemberExpr {h.id}: an unknown anonymous member"
    let e ← expr (← one)
    let some id := h.referencedMemberDecl | throw "MemberExpr without a field declaration"
    let some (owner, x) := (← get).fields[id]? | throw "MemberExpr references an unknown field"
    unless x.name == m do throw "MemberExpr name differs from its field declaration"
    let aggregate ← if h.isArrow == some true then
        match e.annotation with
        | .rvalue (.pointer _ t) => pure t
        | _ => throw "arrow member access requires a pointer"
      else match e.annotation with
        | .lvalue _ t _ => pure t
        | .rvalue (.struct s) => pure (ct (.struct s))
        | .rvalue (.union s) => pure (ct (.union s))
        | _ => throw "member access requires a struct or union"
    match aggregate with
    | .mk _ (.struct s) | .mk _ (.union s) =>
      unless s.number == owner.number do throw "MemberExpr field belongs to another tag"
    | _ => throw "member access requires a struct or union"
    -- a struct value lives in a frame temporary, whose array members' addresses can escape
    if h.isArrow != some true && e.annotation matches .rvalue _ then
      checkFrameAlignment "member of a struct value" aggregate
    if let some r := (← get).packedRecords[owner.number]? then
      let some f := r.fields.find? (·.name.name == x.name) | throw "packed: unknown member"
      let ann ← annotOf h
      let .lvalue q mt reg := ann | throw "packed: rvalue member access is not supported"
      let ptr ← if h.isArrow == some true then pure e else
        match e.annotation with
        | .lvalue aq aggregateTy false => pure (rvalue (.pointer aq aggregateTy) (.unary .address e))
        | _ => throw "packed: member access requires an addressable lvalue"
      let byte := ct (.basic (.integer (.unsigned .ichar)))
      let bp := rvalue (.pointer q byte) (.cast noQuals (ct (.pointer q byte)) ptr)
      let addr := rvalue (.pointer q byte) (.binary bp (.arithmetic .add) (intConst f.off))
      let typed := rvalue (.pointer q mt) (.cast noQuals (ct (.pointer q mt)) addr)
      return mkExpr (.lvalue q mt reg) (.unary .indirection typed)
    return mkExpr (← annotOf h) (if h.isArrow == some true then .memberofptr e x else .memberof e x)
  | .unaryExprOrTypeTraitExpr =>
    -- `sizeof a` of a variable-length array: its length times its element's size
    if h.argType.isNone && h.name == some "sizeof" then
      if let some (_, q, t, len) ← vlaRef? (← one) then
        let (_, rt) ← headerType h
        return Builtin.cast rt (Builtin.arith Builtin.ulT .mul (Builtin.get Builtin.ulT len)
          (Builtin.rv Builtin.ulT (.sizeof q t)))
    let (q, t) ← match h.argType with
      | some at_ => parseType at_.qualType
      | none =>
        let e ← one
        let some eh := e.header? | throw "sizeof of an absent expression"
        -- an lvalue operand's type as Cerberus types it (qualifiers can differ from Clang's)
        let a : Option TypedExpression ← tryCatch (some <$> expr e) fun _ => pure none
        match a with
        | some x => match x.annotation with
          | .lvalue q t _ => pure (q, t)
          | _ => headerType eh
        | none => headerType eh
    if (← containsComplex 64 t) || (← containsPacked 64 t) then checkFoldedType 64 t
    match h.name with
    -- Cerberus types `sizeof e` as `sizeof` of the type of `e`
    | some "sizeof" => return mkExpr (← annotOf h) (.sizeof q t)
    | some "alignof" | some "_Alignof" | some "__alignof" =>
      let a ← match h.argType with
        | some at_ => do spellingAlignment (← Type.parse at_.qualType)
        | none => expressionAlignment (← one)
      if let some a := a then
        return mkExpr (← annotOf h) (.const (.integer (.iconstant a .decimal (some .ul))))
      -- gcc's C11 `_Alignof` of a type (Clang's `alignof` with an argType) is the ABI minimum
      -- (`min_align_of_type`): at most 16 on x86-64 without AVX unless the alignment was
      -- requested. Above 16 only a vector wider than 16 bytes, or an array of them, and a
      -- record with a requested alignment (`userAligned`), or an array of them, are known.
      if h.name == some "alignof" && h.argType.isSome then
        let (_, al) ← Bitfield.sizeAlign (← get).tagDefIdx t
        if al > 16 && !(← userAlignedType t) then
          unless (← vectorOf? (arrayElem t)).isSome do
            throw "_Alignof of a type aligned above 16 bytes (gcc's ABI minimum) is not supported"
          return mkExpr (← annotOf h) (.const (.integer (.iconstant 16 .decimal (some .ul))))
      return mkExpr (← annotOf h) (.alignof q t)
    | k => throw s!"{k.getD "type trait"} is not supported"
  | k => throw s!"expression {k} is not supported yet"

/-- A call of the semantic builtin `__builtin_<name>` (prototype and result type checked), of type
Clang's `h`, with Clang's arguments. -/
partial def semanticCall (h : Header) (name : String) (args : List Node) : M TypedExpression := do
  let typeOf := fun (a : Node) => do
    let some ah := a.header? | throw s!"{name}: an absent argument"
    return (← headerType ah).2
  let call := fun (f : TypedExpression) (xs : List TypedExpression) => do
    return mkExpr (← annotOf h) (.call f xs)
  let (_, rt) ← headerType h
  match name, args with
  | "isgreater", [a, b] | "isgreaterequal", [a, b] | "isless", [a, b]
  | "islessequal", [a, b] | "islessgreater", [a, b] | "isunordered", [a, b] =>
    let t ← typeOf a
    let _ ← builtinFloating name t
    unless reprStr t == reprStr (← typeOf b) do throw s!"{name}: operands of two types"
    let f ← builtinHelper s!"{name}/{reprStr t}" Builtin.intT [t, t] 0 fun ps _ => match ps with
      | [x, y] => Builtin.compare name t x y
      | _ => none
    call f [Builtin.cast t (← expr a), Builtin.cast t (← expr b)]
  | "isnan", [a] | "isinf", [a] | "isfinite", [a] | "signbit", [a] =>
    let t ← typeOf a
    let isFloat ← builtinFloating name t
    let f ← builtinHelper s!"{name}/{reprStr t}" Builtin.intT [t] 1 fun ps ls => match ps, ls with
      | [x], [d] => Builtin.classify name t isFloat x d
      | _, _ => none
    let v ← call f [Builtin.cast t (← expr a)]
    -- gcc folds these on a constant operand, with other values than it computes for a value:
    -- the signbit of a float is 1 (INT_MIN computed), isinf of -infinity is -1 (1 computed)
    if name == "isinf" && (← foldedFloating a) then
      let neg := Builtin.test .lt (Builtin.cast t (← expr a)) (Builtin.cast t (Builtin.int 0))
      let sign := Builtin.cond Builtin.intT neg (Builtin.int (-1)) (Builtin.int 1)
      return Builtin.cond Builtin.intT v sign (Builtin.int 0)
    unless name == "signbit" && isFloat do return v
    if ← foldedFloating a then return Builtin.test .ne v (Builtin.int 0)
    unless runtimeValue a do throw "signbit: a float operand that gcc's folding may make constant"
    return v
  | "inf", [] | "inff", [] | "huge_val", [] | "huge_valf", [] =>
    -- IEEE division (Annex F), a constant expression: +infinity
    let sfx : Option FloatingSuffix := if (← builtinFloating name rt) then some .f else none
    let c := fun (x : String) => Builtin.rv rt (.const (.floating (x, sfx)))
    return Builtin.arith rt .div (c "1.0") (c "0.0")
  | "nan", [a] | "nanf", [a] =>
    let _ ← builtinFloating name rt
    -- only gcc's default NaN: other payload strings are rejected
    let s := stripCasts a
    unless s.kind? == some .stringLiteral && (s.header?.bind (·.value)) == some (.str "\"\"") do
      throw s!"{name}: an argument other than \"\""
    let f ← builtinHelper s!"{name}/{reprStr rt}" rt [] 1 fun _ ls => match ls with
      | [d] => some (Builtin.nan rt d)
      | _ => none
    call f []
  | "copysign", [a, b] | "copysignf", [a, b] =>
    let _ ← builtinFloating name rt
    let f ← builtinHelper s!"{name}/{reprStr rt}" rt [rt, rt] 2 fun ps ls => match ps, ls with
      | [x, y], [dx, dy] => some (Builtin.copysign rt x y dx dy)
      | _, _ => none
    call f [Builtin.cast rt (← expr a), Builtin.cast rt (← expr b)]
  | "prefetch", p :: rest =>
    unless rest.length ≤ 2 do throw "prefetch: too many arguments"
    for c in rest do
      let _ ← constInt c
    return mkExpr (.rvalue .void) (.cast noQuals (ct .void) (← expr p))
  | _, [a, b, r] =>
    let op ← match name with
      | "add_overflow" | "sub_overflow" | "mul_overflow" => pure (String.ofList (name.toList.take 3))
      | _ =>
        if (typedOverflow? s!"__builtin_{name}").isSome then pure (String.ofList ((name.toList.drop 1).take 3))
        else throw s!"__builtin_{name}: unsupported arguments"
    let at_ ← typeOf a
    let bt ← typeOf b
    let .mk _ (.pointer rq rt') ← typeOf r | throw s!"{name}: a result that is not a pointer"
    let _ ← overflowInt name at_
    let _ ← overflowInt name bt
    let (w, rs) ← overflowInt name rt'
    if rq.const then throw s!"{name}: a const result"
    let rmax := if rs then 2 ^ (w - 1) - 1 else 2 ^ w - 1
    let core ← builtinHelper "overflow-core" Builtin.intT Builtin.coreParams Builtin.coreLocals
      Builtin.overflowCore
    let key := s!"{op}_overflow/{reprStr at_}/{reprStr bt}/{rq.const}{rq.volatile}{rq.restrict}/{reprStr rt'}"
    let rp : Ctype := ct (.pointer rq rt')
    let f ← builtinHelper key Builtin.boolT [at_, bt, rp] 2 fun ps ls => match ps, ls with
      | [x, y, z], [wv, o] => some (Builtin.overflow op core at_ bt rt' rq rs rmax x y z wv o)
      | _, _ => none
    call f [Builtin.cast at_ (← expr a), Builtin.cast bt (← expr b), ← expr r]
  | _, _ => throw s!"__builtin_{name}: unsupported arguments"

/-- The initialiser of an object of type `t`: an expression, an initialiser list (Clang's
semantic form: every member or element in order, `ImplicitValueInitExpr` for the missing ones),
or a string literal initialising a character array. -/
partial def initializer (t : Ctype) (n : Node) : M TypedExpression := do
  let some h := n.header? | throw "absent initialiser"
  match h.kind, t with
  | .implicitValueInitExpr, _ => zeroInit t
  | .stringLiteral, .mk _ (.array e@(.mk _ (.basic (.integer it))) (some k)) =>
    if it == .wchar || it == .signed .int then
      let some (.str value) := h.value | throw "wide string without a value"
      let (_, lt) ← headerType h
      let .mk _ (.array (.mk _ (.basic (.integer lit))) (some _)) := lt
        | throw "wide string without an integer array type"
      unless (lit == .wchar || lit == .signed .int) && value.startsWith "L\"" && value.endsWith "\"" do
        throw "wide array initializer: an L string of int or wchar_t expected"
      let lx ← stringLexemes (value.toList.drop 2).dropLast #[]
      let values ← lexemeBytes lx.toList (wide := true)
      if values.any (· > 2147483647) then throw "wide string code unit outside signed wchar_t"
      let given := (values.take k.toNat).map fun v => some (Builtin.cast e (intConst v))
      let pad := List.replicate (k.toNat - values.length) (some (Builtin.cast e (intConst 0)))
      return rvalue (.array e (some k)) (.array false e (given ++ pad))
    unless it == .char || it == .signed .ichar || it == .unsigned .ichar do
      throw "string initialisation of a non-character array"
    -- `char s[] = "…"`: Cerberus desugars it to an array of its characters
    let (s, _) ← stringLiteral h
    let lx := s.2.flatMap (·.2)
    let _ ← lexemeBytes lx
    let ge := intGen it
    let chars := lx.map fun l => some (rvalue ge (.cast noQuals e (rvalue int_ (.const (.character (none, l))))))
    let pad := List.replicate (k.toNat - min k.toNat chars.length) (some (rvalue ge (.cast noQuals e (intConst 0))))
    return rvalue (.array e (some k)) (.array true e ((chars.take k.toNat) ++ pad))
  | .initListExpr, .mk _ (.array e (some k)) =>
    let elems := match n.arrayFiller with
      | some af => af.extract 1 af.size
      | none => n.children
    if elems.size > k.toNat then throw "initialiser list longer than its array"
    match checkRangeInits elems with
    | .error err => throw err
    | .ok () => pure ()
    let given ← elems.toList.mapM (initializer e)
    let rest ← (List.replicate (k.toNat - elems.size) ()).mapM fun _ => zeroInit e
    return rvalue (.array e (some k)) (.array false e ((given ++ rest).map some))
  | .initListExpr, .mk _ (.struct s) =>
    if (← get).complexParts.contains s.number then
      match n.children with
      | #[] => return ← zeroInit t
      | #[c] => return ← initializer t c
      | _ => throw "complex initializer with multiple elements (Clang and gcc differ)"
    if (← get).vectorLanes.contains s.number && n.children.any mentionsVector then
      throw "a vector initialised from vectors"
    let some (.struct ms none) := (← get).tagDefIdx[s.number]?
      | throw "initialiser list of an incomplete struct or one with a flexible array member"
    let cs := n.children
    if let some r := (← get).packedRecords[s.number]? then
      let bs ← packedBytes t n
      let byte := ct (.basic (.integer (.unsigned .ichar)))
      -- a nonconstant value is translated once (keyed by the offset of its first byte)
      let mut values : Std.HashMap Nat TypedExpression := {}
      let mut es := #[]
      for (b, k) in bs.zipIdx do
        match b with
        | .const v => es := es.push (Bitfield.uconst (.unsigned .ichar) v)
        | .part c it i =>
          let v ← match values[k - i]? with
            | some v => pure v
            | none => pure (Bitfield.castTo (.unsigned .long) (Bitfield.castTo it (← expr c)))
          values := values.insert (k - i) v
          es := es.push (Bitfield.castTo (.unsigned .ichar)
            (if i == 0 then v else Bitfield.bin (.unsigned .long) v .shr (Bitfield.intC (8 * i))))
      let arr := rvalue (.array byte (some r.size)) (.array false byte (es.toList.map some))
      return rvalue (.struct s) (.struct s [(Identifier.mk .unknown "__cfront_bytes", some arr)])
    if let some slots := (← get).bitSlots[s.number]? then
      -- bit-fields: each storage unit is initialised to the bits of its fields, a constant
      -- where they are constants
      if cs.size > slots.size then throw "initialiser list longer than its struct"
      let mut plain : Std.HashMap String Node := {}
      let mut units : Std.HashMap String (Nat × Array TypedExpression × IntegerType) := {}
      for (sl, i) in slots.zipIdx do
        let c? := cs[i]?
        match sl with
        | .inl x => if let some c := c? then plain := plain.insert x.name c
        | .inr f =>
          let (k, ds, w) := units.getD f.unit.name (0, #[], f.work)
          let (k, ds) ← match c? with
            | none => pure (k, ds)
            | some c =>
              if c.kind? == some .implicitValueInitExpr then pure (k, ds)
              else match ← bitConst? c with
                | some v => pure (k ||| f.constBits v, ds)
                | none => pure (k, ds.push (f.toBits (← expr c)))
          units := units.insert f.unit.name (k, ds, w)
      let mut out := #[]
      for (x, (_, _, _, mt)) in ms do
        match plain[x.name]?, units[x.name]? with
        | some c, _ => out := out.push (x, some (← initializer mt c))
        | none, some (k, ds, w) =>
          out := out.push (x, some (ds.foldl (fun acc d => Bitfield.bin w acc .bor d) (Bitfield.uconst w k)))
        | none, none => out := out.push (x, some (← zeroInit mt))
      return rvalue (.struct s) (.struct s out.toList)
    if cs.size > ms.length then throw "initialiser list longer than its struct"
    let mut out := #[]
    for ((x, (_, _, _, mt)), i) in ms.zipIdx do
      match cs[i]? with
      | some c => out := out.push (x, some (← initializer mt c))
      | none => out := out.push (x, some (← zeroInit mt))
    return rvalue (.struct s) (.struct s out.toList)
  | .initListExpr, .mk _ (.union s) =>
    let some (.union ms) := (← get).tagDefIdx[s.number]? | throw "initialiser list of an incomplete union"
    match h.field, n.children with
    | some f, #[c] =>
      let some (owner, field) := (← get).fields[f.id]? | throw "unknown union initialiser field"
      unless owner.number == s.number do throw "union initialiser field belongs to another tag"
      if let some bf := (← get).bitfields[f.id]? then
        -- a bit-field: its storage member, initialised to the bits of the value
        let v ← match ← bitConst? c with
          | some v => pure (Bitfield.uconst bf.work (bf.constBits v))
          | none => pure (bf.toBits (← expr c))
        return rvalue (.union s) (.union s bf.unit (some (Bitfield.castTo bf.unitTy v)))
      -- an anonymous member's (implicit) field, named "" by Clang, has its given name here
      let some (x, (_, _, _, mt)) := ms.find? (·.1.name == field.name) | throw "union member"
      return rvalue (.union s) (.union s x (some (← initializer mt c)))
    | _, #[] => zeroInit t
    | _, _ => throw "union initialiser"
  | .initListExpr, _ => match n.children with
    | #[c] => initializer t c
    | _ => throw "initialiser list of a scalar"
  | _, _ => expr n

end

/-- The initialiser of an object of static storage duration: no synthesized call. -/
def staticInitializer (t : Ctype) (n : Node) : M TypedExpression := do
  let saved := (← get).staticInit
  modify fun st => { st with staticInit := true }
  let e ← tryCatch (initializer t n) fun err => do
    modify fun st => { st with staticInit := saved }
    throw err
  modify fun st => { st with staticInit := saved }
  return e

/-! ### Tags and typedefs (file and block scope) -/

/-- The column a declaration's location is printed with (the expansion's, inside a macro). -/
def locCol (h : Header) : Option Nat :=
  match h.loc with
  | some (.bare l) => l.col
  | some (.macro _ e) => e.col
  | none => none

/-- A struct, union or enum declaration: its symbol (a redeclaration's is its first
declaration's), and for an unnamed one, a pending tag that the next spelling names. -/
def tagDecl (keyword : String) (h : Header) : M Sym := do
  let st ← get
  if let some p := h.previousDecl then
    if let some s := st.declSyms[p]? then
      modify fun st => { st with declSyms := st.declSyms.insert h.id s }
      return s
  match h.name with
  | some name =>
    let key := keyword ++ " " ++ name
    -- A new declaration in this block may hide a visible outer tag. Redeclarations
    -- were resolved by previousDecl above and keep their original identity.
    let s ← if st.localScope && !st.scopeTags.contains key then fresh (.id name)
      else tagSym keyword name
    modify fun st => { st with
      declSyms := st.declSyms.insert h.id s,
      tags := st.tags.insert key s, scopeTags := st.scopeTags.insert key }
    return s
  | none =>
    let s ← fresh .none
    modify fun st => { st with declSyms := st.declSyms.insert h.id s,
                               pending := { keyword, col := locCol h, sym := s, declId := h.id } ::
                                 st.pending }
    return s

/-- Compare every ordinary member offset, total size and aggregate alignment.
Packing that changes any of them needs a different Ail representation. Bit-fields
are rejected before this check, rather than reusing the unpacked placement. The
record's own alignment (`recordAlign`, 0 without one) applies to both layouts. -/
def checkPacking (kw : String) (recordPacked : Bool) (packedFields : List String)
    (requested : Std.HashMap String Nat) (recordAlign : Nat)
    (members : Array (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype))) : M Unit := do
  let defs := (← get).tagDefIdx
  let mut normalOff := 0
  let mut packedOff := 0
  let mut normalAlign := 0
  let mut packedAlign := 0
  let mut normalSize := 0
  let mut packedSize := 0
  for (x, (_, al, _, t)) in members do
    checkFoldedType 64 t
    let (sz, natural) ← Bitfield.sizeAlign defs t
    let a ← Bitfield.memberAlign defs al natural
    let b := if recordPacked || packedFields.contains x.name then
        max (requested[x.name]?.getD 0) 1
      else a
    normalAlign := max normalAlign a
    packedAlign := max packedAlign b
    if kw == "struct" then
      normalOff := Bitfield.roundUp normalOff a
      packedOff := Bitfield.roundUp packedOff b
      unless normalOff == packedOff do throw "packed attribute changes a member offset"
      normalOff := normalOff + sz
      packedOff := packedOff + sz
      normalSize := normalOff
      packedSize := packedOff
    else
      normalSize := max normalSize sz
      packedSize := max packedSize sz
  normalAlign := max normalAlign recordAlign
  packedAlign := max packedAlign recordAlign
  unless normalAlign > 0 && normalAlign == packedAlign &&
      Bitfield.roundUp normalSize normalAlign == Bitfield.roundUp packedSize packedAlign do
    throw "packed attribute changes record size or alignment"

/-- The supported SysV packing rule: packed fields have byte alignment unless
explicitly aligned; other fields keep their ordinary alignment. -/
def byteRecord (s : Sym) (recordPacked : Bool) (packedFields : List String)
    (requested : Std.HashMap String Nat)
    (members : Array (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype))) :
    M (Array (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype))) := do
  let defs := (← get).tagDefIdx
  let mut off := 0
  let mut align := 1
  let mut fs := #[]
  for (x, (_, al, _, t)) in members do
    checkPackedType 64 t
    let (sz, natural) ← Bitfield.sizeAlign defs t
    let a ← if recordPacked || packedFields.contains x.name then
        pure (max 1 (requested[x.name]?.getD 0))
      else Bitfield.memberAlign defs al natural
    off := Bitfield.roundUp off a
    fs := fs.push (PackedField.mk x off t)
    off := off + sz
    align := max align a
  let size := Bitfield.roundUp off align
  if size == 0 then throw "packed: empty record is not supported"
  let byte := ct (.basic (.integer (.unsigned .ichar)))
  let ms := #[(Identifier.mk .unknown "__cfront_bytes",
    (noAttrs, some (Alignment.integer align), noQuals, ct (.array byte (some size))))]
  let (_, actualSize, actualAlign) ← Bitfield.structLayout defs ms.toList none
  unless actualSize == size && actualAlign == align do throw "packed: byte layout mismatch"
  modify fun st => { st with packedRecords := st.packedRecords.insert s.number ⟨fs, size, align⟩ }
  return ms

/-- A record aligned to `k` above its natural alignment: the first member, at offset 0
in a struct as in a union (a bit-field storage unit after their layout), carries
alignment `k`. The other offsets are unchanged and the record's size rounds up to `k`,
so objects, arrays and enclosing records of the type are laid out by its alignment,
as gcc lays them out. -/
def alignRecord (kw : String) (k : Nat)
    (members : Array (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype))) :
    M (Array (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype))) := do
  let defs := (← get).tagDefIdx
  let mut natural := 0
  for (_, (_, al, _, t)) in members do
    let t := match t with | .mk _ (.array e none) => e | t => t
    checkFoldedType 64 t
    let (_, a) ← Bitfield.sizeAlign defs t
    natural := max natural (← Bitfield.memberAlign defs al a)
  if k ≤ natural then return members
  let some (x, (as, _, q, t)) := members[0]? | throw s!"aligned empty {kw} is not supported"
  if t matches .mk _ (.array _ none) then throw "aligned record of a flexible array member only"
  return members.set! 0 (x, (as, some (.integer k), q, t))

mutual

partial def recordDecl (n : Node) (h : Header) : M Unit := do
  let some kw := h.tagUsed | throw s!"RecordDecl {h.id} without tagUsed"
  unless kw == "struct" || kw == "union" do throw s!"RecordDecl {h.id}: {kw}"
  let s ← tagDecl kw h
  unless h.completeDefinition == some true do
    unless n.children.all (fun c => c.kind? == some .packedAttr || neutralAttr c.kind) do
      throw s!"RecordDecl {h.id}: children of a declaration"
    return
  if (← get).tagDefIdx.contains s.number then
    throw s!"{kw} {h.name.getD "(unnamed)"} defined twice (tag scopes are not supported)"
  let mut items : Array Bitfield.Item := #[]
  let mut hasBits := false
  -- the names of the record's members, which a member name given to an anonymous one avoids
  let names := n.children.filterMap fun c => c.header?.bind (·.name)
  let mut anon := 0
  -- the record declared by the previous child, if it is one
  let mut prev : Option Header := none
  let recordPacked := n.children.any (·.kind? == some .packedAttr)
  let mut packedFields := []
  let mut requested : Std.HashMap String Nat := {}
  -- gcc's TYPE_USER_ALIGN, from the members (a subset of gcc's: a packed member's weaker
  -- request and a bit-field's are not counted, so `_Alignof` rejects rather than differs)
  let mut userAlign := false
  for c in n.children do
    let some ch := c.header? | throw s!"RecordDecl {h.id}: absent child"
    let before := prev
    prev := none
    match ch.kind with
    | .fieldDecl =>
      if ch.isBitfield == some true then
        let fname := ch.name.getD "(unnamed)"
        let (q, t) ← headerType ch
        if (← headerAlignment ch).isSome then throw "aligned typedef on a bit-field is not supported"
        let .mk _ (.basic (.integer it)) := t | throw s!"bit-field {fname} of a non-integer type"
        let #[we] := c.children | throw s!"bit-field {fname}: a width (only) expected"
        let w ← constInt we
        let (_, signed) ← match it with
          | .enum e =>
            -- gcc and Clang give the enum `unsigned int` unless an enumerator is negative, and
            -- the field that signedness; Cerberus's enum is `int`, which agrees on every value
            -- of a narrower unsigned field
            let some sg := (← get).enumSigned[e.number]?
              | throw s!"bit-field {fname} of an incomplete enumerated type"
            if !sg && w ≥ 32 then throw s!"bit-field {fname}: 32 bits of an unsigned enumerated type"
            pure (32, sg)
          | _ => intShape it
        if let some name := ch.name then
          modify fun st => { st with fields := st.fields.insert ch.id (s, Identifier.mk .unknown name) }
        items := items.push (.bit ch.id ch.name it signed w.toNat q.volatile)
        hasBits := true
        continue
      let some fname := ch.name | do
        -- an anonymous struct or union member (STD §6.7.2.1#13): Clang declares the unnamed
        -- record and then an implicit unnamed field of its type, and spells an access to one of
        -- its members as an access through that field; the field is given a member name
        let some rh := before | throw s!"RecordDecl {h.id}: an unnamed member without its record"
        let some rkw := rh.tagUsed | throw s!"RecordDecl {rh.id} without tagUsed"
        let some key := ch.type.map (·.qualType) | throw s!"FieldDecl {ch.id} without a type"
        unless ch.isImplicit == some true && rh.name.isNone && rh.completeDefinition == some true &&
            c.children.isEmpty && key.startsWith (rkw ++ " ") do
          throw s!"RecordDecl {h.id}: unnamed member {key} is not supported"
        let some sym := (← get).declSyms[rh.id]? | throw s!"RecordDecl {rh.id} without a symbol"
        let x := s!"__cfront_anon{anon}"
        anon := anon + 1
        if names.contains x then throw s!"RecordDecl {h.id}: a member is named {x}"
        modify fun st => { st with tags := st.tags.insert key sym,
                                   pending := st.pending.filter (·.declId != rh.id),
                                   anonMembers := st.anonMembers.insert ch.id x,
                                   fields := st.fields.insert ch.id (s, Identifier.mk .unknown x) }
        let t := ct (if rkw == "struct" then .struct sym else .union sym)
        if ← userAlignedType t then userAlign := true
        items := items.push (.member ch.id (Identifier.mk .unknown x) (noAttrs, none, noQuals, t))
        continue
      let (q, t) ← headerType ch
      let a := maxAlignment (← alignedAttrs c) (← headerAlignment ch)
      for attr in c.children do
        if attr.kind == .modeAttr then checkMode t
        else unless attr.kind == .alignedAttr || attr.kind == .packedAttr || neutralAttr attr.kind do
          throw s!"member {fname}: child {attr.kind} is not supported"
      if c.children.any (·.kind? == some .packedAttr) then packedFields := fname :: packedFields
      -- Packing suppresses a typedef's natural alignment; only an explicit
      -- field alignment can strengthen a packed member.
      if let some k ← alignedAttrs c then requested := requested.insert fname k
      let align ← match a with
        | none => pure none
        | some k => do
          checkFoldedType 64 t
          if t matches .mk _ (.array _ none) then
            throw "aligned flexible array member is not supported"
          let (_, natural) ← Bitfield.sizeAlign (← get).tagDefIdx t
          let k := max k natural
          modify fun st => { st with declAligns := st.declAligns.insert ch.id k }
          pure (some (Alignment.integer k))
      -- gcc ignores a weaker request on an unpacked member; an equal one is still requested
      if let some k := a then
        if let .ok (_, natural) := Bitfield.sizeAlign (← get).tagDefIdx t then
          if k ≥ natural && !packedFields.contains fname && !recordPacked then userAlign := true
      if ← userAlignedType t then userAlign := true
      let field := Identifier.mk .unknown fname
      modify fun st => { st with fields := st.fields.insert ch.id (s, field) }
      items := items.push (.member ch.id field (noAttrs, align, q, t))
    | .packedAttr | .alignedAttr => pure ()
    | .recordDecl => recordDecl c ch; prev := some ch
    -- an anonymous member's members: accesses to them are spelled through the member
    | .indirectFieldDecl => unless ch.isImplicit == some true do throw s!"IndirectFieldDecl {ch.id}"
    | .enumDecl => enumDecl c ch
    -- Alias analysis annotations do not change layout or accesses in Ail's memory model.
    -- Other attributes (including packed/aligned) still pass through their own checks.
    | .mayAliasAttr =>
      unless c.children.isEmpty do throw "MayAliasAttr: unexpected children"
    -- `#pragma pack(n)`: Clang's JSON does not give `n`, so the layout is unknown
    | .maxFieldAlignmentAttr =>
      throw s!"{kw} {h.name.getD "(unnamed)"}: #pragma pack (the packing is not in Clang's JSON)"
    | k =>
      unless neutralAttr k do throw s!"RecordDecl {h.id}: member {k} is not supported"
  let mut members := items.filterMap fun | .member _ x m => some (x, m) | .bit .. => none
  -- `struct S { … } __attribute__((aligned(k)))`: the type's alignment, not a declaration's
  let recordAlign ← alignedAttrs n
  if userAlign || recordAlign.isSome then
    modify fun st => { st with userAligned := st.userAligned.insert s.number }
  if recordPacked || !packedFields.isEmpty then
    if hasBits then throw "packing a record with bit-fields is not supported"
    -- Keep ordinary Ail when packing leaves layout unchanged. Otherwise only
    -- structs with an established byte layout can use the synthesized form.
    try checkPacking kw recordPacked packedFields requested (recordAlign.getD 0) members
    catch reason =>
      unless kw == "struct" do throw reason
      if recordAlign.isSome then throw "aligned record with a packed byte layout is not supported"
      members ← byteRecord s recordPacked packedFields requested members
    for c in n.children do
      if let some ch := c.header? then
        if ch.kind == .fieldDecl &&
            (recordPacked || packedFields.contains (ch.name.getD "")) then
          let a := max 1 (requested[ch.name.getD ""]?.getD 0)
          modify fun st => { st with declAligns := st.declAligns.insert ch.id a }
  if hasBits && kw == "union" then
    let (ms, fields) ← match Bitfield.unionLayout items with
      | .ok r => pure r
      | .error e => throw s!"union {h.name.getD "(unnamed)"}: {e}"
    members := ms
    modify fun st => { st with bitfields := fields.foldl (fun m (d, f) => m.insert d f) st.bitfields }
  else if hasBits then
    let (ms, fields) ← match Bitfield.layout (← get).tagDefIdx items with
      | .ok r => pure r
      | .error e => throw s!"struct {h.name.getD "(unnamed)"}: {e}"
    members := ms
    let fieldOf : Std.HashMap String Bitfield.Field := Std.HashMap.ofList fields.toList
    let slots ← items.filterMapM fun
      | .member d x _ => pure (some (match fieldOf[d]? with
        | some f => Sum.inr f  -- absorbed into a storage unit
        | none => Sum.inl x))
      | .bit _ none .. => pure none
      | .bit d (some n) .. => match fieldOf[d]? with
        | some f => pure (some (Sum.inr f))
        | none => throw s!"bit-field {n} without storage"
    modify fun st => { st with bitfields := fields.foldl (fun m (d, f) => m.insert d f) st.bitfields,
                               bitSlots := st.bitSlots.insert s.number slots }
  if let some k := recordAlign then
    members ← alignRecord kw k members
  let def_ ← if kw == "struct" then
      -- a last member of incomplete array type is a flexible array member
      match members.back? with
      | some (x, (as, none, q, .mk _ (.array e none))) =>
        pure (TagDefinition.struct members.pop.toList (some (.mk as x q e)))
      | _ => pure (TagDefinition.struct members.toList none)
    else pure (TagDefinition.union members.toList)
  modify fun st => { st with tagDefIdx := st.tagDefIdx.insert s.number def_,
                             tagDefs := st.tagDefs.push (s, (.unknown, noAttrs, def_)) }

partial def enumDecl (n : Node) (h : Header) : M Unit := do
  if h.fixedUnderlyingType.isSome then throw s!"enum with a fixed underlying type is not supported"
  let s ← tagDecl "enum" h
  -- enumerators: the value of the initialiser, or one more than the previous one (STD §6.7.2.2#3)
  let mut next : Int := 0
  let mut negative := false
  for c in n.children do
    let some ch := c.header? | throw s!"EnumDecl {h.id}: absent child"
    if ch.kind == .recordDecl then recordDecl c ch
    else if ch.kind == .enumDecl then enumDecl c ch
    else do
      unless ch.kind == .enumConstantDecl do throw s!"EnumDecl {h.id}: child {ch.kind}"
      let v ← match c.children with
        | #[] => pure next
        | #[e] => constInt e
        | _ => throw s!"enumerator {ch.name.getD ch.id}: unexpected children"
      unless -2147483648 ≤ v && v ≤ 2147483647 do throw s!"enumerator {ch.name.getD ch.id}: value {v}"
      modify fun st => { st with enumConsts := st.enumConsts.insert ch.id v }
      if let some x := ch.name then
        modify fun st => { st with localNames := st.localNames.insert x .other }
      negative := negative || v < 0
      next := v + 1
  -- a definition (an enumerator list is never empty)
  unless n.children.isEmpty do
    modify fun st => { st with enumSigned := st.enumSigned.insert s.number negative }

end

/-- A typedef; at block scope (`global := false`) it is not one of sigma's typedef symbols. -/
def typedefDecl (n : Node) (h : Header) (global : Bool := true) : M Unit := do
  let some name := h.name | throw s!"TypedefDecl {h.id} without a name"
  if name.startsWith "__cerbty_" then return
  -- `typedef struct { … } T;` names the unnamed struct `struct T` in Clang's spellings
  -- `may_alias` changes alias analysis, not the represented type or its layout.
  -- `mode` on an integer or vector type is checked below: Clang's spelling has it applied
  -- (`mode(QI)` on `int` spells `signed char`, `mode(HI)` on an `int` vector `short` lanes)
  for c in n.children do
    if c.kind? == some .mayAliasAttr && !c.children.isEmpty then
      throw "MayAliasAttr: unexpected children"
    if isAttr c && c.kind != .alignedAttr && c.kind != .modeAttr &&
        !neutralAttr c.kind && c.kind != .mayAliasAttr then
      throw s!"TypedefDecl {name}: attribute {c.kind} is not supported"
  let mut direct : Option (Qualifiers × Ctype) := none
  if let some ty := h.type then
    if let some r := n.children[0]?.bind namedTag? then
      let st ← get
      if let some p := st.pending.find? (·.declId == r.id) then
        let key := p.keyword ++ " " ++ name
        if ty.qualType == key then
          -- A typedef and a tag have separate C namespaces. The declaration id
          -- disambiguates an anonymous typedef even when its printed tag name is
          -- already used by a visible tag or another anonymous typedef.
          direct := some (noQuals, match p.keyword with
            | "struct" => ct (.struct p.sym)
            | "union" => ct (.union p.sym)
            | _ => intTy (.enum p.sym))
          set { st with pending := st.pending.filter (·.declId != r.id),
                        tags := if st.tags.contains key then st.tags else st.tags.insert key p.sym }
  let t ← match direct with
    | some t => pure t
    | none => headerType h
  if n.children.any (·.kind? == some .modeAttr) then
    -- (an enumerated type's spelling would not show its mode)
    match t.2 with
    | .mk _ (.basic (.integer (.enum _))) => throw s!"TypedefDecl {name}: mode attribute on an enum"
    | .mk _ (.basic (.integer _)) => pure ()
    | t => unless (← vectorOf? t).isSome do
        throw s!"TypedefDecl {name}: mode attribute on a type other than an integer or a vector"
  modify fun st => { st with typedefDeclTypes := st.typedefDeclTypes.insert h.id t }
  let a := maxAlignment (← alignedAttrs n) (← headerAlignment h)
  if h.previousDecl.isSome && (← get).typedefs.contains name then
    unless (← get).typedefAligns[name]? == a do throw "typedef redeclaration changes alignment"
    return
  modify fun st => { st with typedefAligns := st.typedefAligns.erase name }
  if let some k := a then
    checkFoldedType 64 t.2
    let (_, natural) ← Bitfield.sizeAlign (← get).tagDefIdx t.2
    if k < natural then throw "typedef alignment weaker than its type is not supported"
    modify fun st => { st with typedefAligns := st.typedefAligns.insert name k }
  let s ← fresh (.id name)
  modify fun st => { st with typedefs := st.typedefs.insert name t,
                             typedefSyms := if global then st.typedefSyms.push s else st.typedefSyms }

/-! ### Declarations with linkage -/

def setGlobal (g : Global) : M Unit :=
  modify fun st => match st.globalIdx[g.sym.number]? with
    | some i => { st with globals := st.globals.set! i g }
    | none => { st with globals := st.globals.push g, globalIdx := st.globalIdx.insert g.sym.number st.globals.size }

/-- The symbol of a declaration with linkage: its earlier declaration's, or a new one. -/
def entitySym (h : Header) (name : String) : M (Sym × Bool) := do
  let st ← get
  if let some p := h.previousDecl then
    if let some s := st.declSyms[p]? then
      modify fun st => { st with declSyms := st.declSyms.insert h.id s }
      return (s, false)
  if let some g := st.globals.find? fun g => g.name == name && !g.blockScope then
    if g.libraryBuiltin then
      modify fun st => { st with declSyms := st.declSyms.insert h.id g.sym }
      return (g.sym, false)
    throw s!"{name}: a redeclaration that Clang does not link to the earlier declaration"
  let s ← fresh (.id name)
  modify fun st => { st with declSyms := (st.declSyms.insert h.id s) }
  -- a redeclaration of an implicit (skipped) declaration: references to it are to this entity
  if let some p := h.previousDecl then
    modify fun st => { st with declSyms := st.declSyms.insert p s }
  return (s, true)

def upgrade (old new : IdKind) : IdKind :=
  match old, new with
  | .definition, _ | _, .definition => .definition
  | .tentative, _ | _, .tentative => .tentative
  | _, _ => .declaration

/-- A block-scope prototype declares an entity with linkage in sigma, without a runtime
statement. Compatible redeclarations keep an existing definition and its symbol. -/
def blockFunctionDecl (n : Node) (h : Header) : M Unit := do
  let some name := h.name | throw "block-scope function without a name"
  unless h.storageClass.isNone || h.storageClass == some "extern" do
    throw "block-scope function: external linkage expected"
  if h.inline == some true then throw "block-scope inline function is not supported"
  for c in n.children do
    unless c.kind? == some .parmVarDecl ||
        [Kind.builtinAttr, .noThrowAttr, .constAttr, .pureAttr, .c11NoReturnAttr, .noReturnAttr].contains c.kind do
      throw s!"block-scope function {name}: child {c.kind} is not supported"
    if c.kind? == some .parmVarDecl && !c.children.isEmpty then
      throw "block-scope function: parameter declarations with children are not supported"
  if let some ty := h.type then checkLibrarySpelling name ty.qualType
  let (_, fty) ← headerType h
  let .mk _ (.function ret ps v) := fty | throw "block-scope function: prototype expected"
  -- Use the restricted comparison key so unfamiliar prototype shapes fail closed.
  let some _ := libraryTypeKey fty | throw "block-scope function: unsupported prototype"
  let (sym, _) ← entitySym h name
  if let some g ← globalOf? sym then
    unless g.isFunction do throw s!"{name} redeclared as a function"
    let .function _ r ps₀ v₀ _ _ := g.decl | throw "block-scope function: function expected"
    checkLibraryType name fty (ct (.function r ps₀ v₀))
    return
  let ps := ps.map fun (q, t, r) => ({ noQuals with restrict := q.restrict }, t, r)
  setGlobal {
    sym := sym
    name := name
    isFunction := true
    isStatic := false
    firstIsDefinition := false
    decl := .function true ret ps v false (n.children.any fun c =>
      c.kind? == some .c11NoReturnAttr || c.kind? == some .noReturnAttr)
    kind := .declaration
    functionSpelling := h.type.map (·.qualType) }

def varDecl (n : Node) (h : Header) : M Unit := do
  let some name := h.name | throw s!"VarDecl {h.id} without a name"
  if h.tls.isSome then throw s!"thread-local {name} is not supported"
  let (q, t) ← headerType h
  let inits := n.children.filter (!isAttr ·)
  let (align, over) ← objectAlignment n h t
  let isExtern := h.storageClass == some "extern"
  let hasInit := h.init.isSome
  unless (hasInit && inits.size == 1) || (!hasInit && inits.isEmpty) do
    throw s!"VarDecl {name}: unexpected children"
  let (sym, _) ← entitySym h name
  let old ← globalOf? sym
  -- references already translated name the object as declared before: every declaration of
  -- a wrapped object, and only those, must ask for the same alignment of the same type
  let wrapped ← match over, (← get).alignedObjects[sym.number]? with
    | some k, none =>
      if old.isSome then throw s!"{name}: alignment raised above natural by a redeclaration"
      if isExtern then throw s!"{name}: over-aligned extern declaration is not supported"
      let w ← alignedWrapper name k t
      modify fun st => { st with alignedObjects := st.alignedObjects.insert sym.number w }
      pure (some w)
    | some k, some w =>
      unless k == w.align && reprStr t == reprStr w.ty do
        throw s!"{name}: redeclaration changes an over-aligned object"
      pure (some w)
    | none, some _ => throw s!"{name}: redeclaration of an over-aligned object without its alignment"
    | none, none => pure none
  let kind : IdKind := if hasInit then .definition else if isExtern then .declaration else .tentative
  let g : Global := match old with
    | some g => g
    | none => { sym, name, isFunction := false, isStatic := h.storageClass == some "static",
                firstIsDefinition := hasInit, decl := .object (.static, false) none q t,
                kind := .declaration }
  if g.isFunction then throw s!"{name} redeclared as an object"
  if hasInit then
    if g.hasObjectDefinition then throw s!"{name} defined twice"
    let e ← staticInitializer t inits[0]!
    let e := match wrapped with
      | some w => wrapInit w e
      | none => e
    modify fun st => { st with objectDefinitions := st.objectDefinitions.push (sym, e) }
  let align := match g.decl, align with
    | .object _ (some (.integer a)) _ _, some (.integer b) => some (.integer (max a b))
    | .object _ a _ _, none => a
    | _, a => a
  let t := match wrapped with
    | some w => ct (.struct w.tag)
    | none => t
  setGlobal { g with
    decl := .object (.static, false) align q t, kind := upgrade g.kind kind
    hasObjectDefinition := g.hasObjectDefinition || hasInit }

/-! ### Statements -/

/-- A `continue` of this loop body (not of a nested loop). -/
partial def hasContinue (n : Node) : Bool :=
  match n.kind? with
  | some .continueStmt => true
  | some .whileStmt | some .doStmt | some .forStmt | none => false
  | _ => n.children.any hasContinue

def isStatementKind (k : Kind) : Bool :=
  [Kind.compoundStmt, .declStmt, .nullStmt, .returnStmt, .ifStmt, .whileStmt, .doStmt, .forStmt,
    .switchStmt, .caseStmt, .defaultStmt, .breakStmt, .continueStmt, .gotoStmt, .labelStmt,
    .indirectGotoStmt, .attributedStmt, .gccAsmStmt].contains k

/-- The `LabelStmt`s of a function body, in order. -/
partial def labelsOf (n : Node) (acc : Array Header) : Array Header :=
  let acc := match n.header? with
    | some h => if h.kind == .labelStmt then acc.push h else acc
    | none => acc
  n.children.foldl (fun a c => labelsOf c a) acc

/-- The symbol of a label: every label of the function is numbered before its body. -/
def labelSym (declId : String) : M Sym := do
  if let some s := (← get).labels[declId]? then return s
  let s ← fresh .none
  modify fun st => { st with labels := st.labels.insert declId s }
  return s

/-- Whether a subtree contains an evaluated statement expression. `sizeof` is left to the
ordinary expression translator, which does not evaluate its operand. -/
partial def hasStmtExpr (n : Node) : Bool :=
  n.kind? == some .stmtExpr ||
    (n.kind? != some .unaryExprOrTypeTraitExpr && n.children.any hasStmtExpr)

/-- Whether a statement expression's block has a jump that lifting could retarget: a `break` or
`continue` whose loop or `switch` is outside the block (a lifted loop test runs inside a new Ail
loop), labels and `case`/`default` of an outside `switch` (jumps into the block, which GCC
forbids), computed gotos and label addresses. `return` and `goto` leave the block as in C: GCC
permits jumping out of a statement expression. -/
partial def stmtExprJump (n : Node) (inLoop inSwitch : Bool := false) : Bool :=
  match n.kind? with
  | some .breakStmt => !(inLoop || inSwitch)
  | some .continueStmt => !inLoop
  | some .caseStmt | some .defaultStmt => !inSwitch || n.children.any (stmtExprJump · inLoop inSwitch)
  | some .labelStmt | some .indirectGotoStmt | some .addrLabelExpr => true
  | some k =>
    let inLoop := inLoop || [Kind.whileStmt, .doStmt, .forStmt].contains k
    n.children.any (stmtExprJump · inLoop (inSwitch || k == .switchStmt))
  | none => n.children.any (stmtExprJump · inLoop inSwitch)

/-- An assignment target whose address needs no evaluation before or after a lifted RHS. -/
partial def simpleTarget (n : Node) : Bool :=
  n.kind? == some .declRefExpr ||
    (n.kind? == some .parenExpr && n.children.size == 1 && n.children.all simpleTarget)

/-- A root statement expression whose value is discarded (parentheses and casts to `void`,
written or implicit as in a `?:` with a void operand, may surround it). -/
partial def discardedStmtExpr (n : Node) : Node :=
  match n.kind?, n.children with
  | some .parenExpr, #[e] => discardedStmtExpr e
  | some .cStyleCastExpr, #[e] | some .implicitCastExpr, #[e] =>
    if n.header?.bind (·.castKind) == some "ToVoid" then discardedStmtExpr e else n
  | _, _ => n

/-- An operand of a discarded `?:`, without the conversion to `void` that Clang inserts when
the other operand is void. -/
def voidOperand (n : Node) : Node :=
  match n.kind?, n.children with
  | some .implicitCastExpr, #[e] => if n.header?.bind (·.castKind) == some "ToVoid" then e else n
  | _, _ => n

/-- A statement after the lifted prefix of its full expression, in a block of its own. -/
def prefixed (bs : Bindings) (pre : List TypedStatement) (s : TypedStatement) : TypedStatement :=
  if pre.isEmpty then s else stmt (.block bs (pre ++ [s]))

/-- A lifted value must be an object: Ail has no temporaries of other types. -/
def liftedObject (t : Ctype) : M Unit :=
  match t with
  | .mk _ .void | .mk _ (.array ..) | .mk _ (.function ..) | .mk _ (.functionNoParams _) =>
    throw "StmtExpr: result must be an object value"
  | _ => pure ()

/-- An assignment of a lifted value to its fresh automatic temporary. -/
def liftedStore (sym : Sym) (t : Ctype) (e : TypedExpression) : M TypedStatement := do
  let dst := mkExpr (.lvalue noQuals t false) (.ident sym)
  return stmt (.expr (rvalue (← genOf t) (.assign dst e)))

/-- The node that reads a lifted temporary back in the residual expression: a synthetic opaque
value matched by a fresh internal id, never by a source name or Clang's pointer-valued ids. -/
def liftedRef (h : Header) (sym : Sym) (t : Ctype) : M Node := do
  let refId := "cfront.stmtExpr." ++ toString sym.number
  let val := rvalue (← genOf t) (.rvalue (mkExpr (.lvalue noQuals t false) (.ident sym)))
  modify fun st => { st with liftedValues := st.liftedValues.insert refId val }
  return .mk { h with id := refId, kind := .opaqueValueExpr } none none

/-- The operand of `assert(e)`, Cerberus's keyword (`AilEassert`), which its `assert.h` does not
define: Clang calls an implicitly declared `int assert()` (or the program's own `assert`, which
is a function call). Only a statement: `assert` has type `void`. -/
def assertCall? (n : Node) : M (Option Node) := do
  if n.kind? != some .callExpr || calleeName? n != some "assert" then return none
  let some f := n.children[0]? | return none
  let some r := (stripCasts f).header?.bind (·.referencedDecl) | return none
  if r.kind != "FunctionDecl" || (← get).declSyms.contains r.id then return none
  let #[_, a] := n.children | throw "assert: one operand expected"
  return some a


mutual

/-- A block-scope declaration statement: its bindings and its `AilSdeclaration` (none for a
declaration of typedefs only). -/
partial def declStmt (n : Node) : M (Bindings × List TypedStatement) := do
  let mut bs : Bindings := []
  let mut ds : Array (Sym × Option TypedExpression) := #[]
  let mut ss : List TypedStatement := []
  for c in n.children do
    let some h := c.header? | throw "absent declaration"
    match h.kind with
    | .varDecl =>
      let some name := h.name | throw s!"VarDecl {h.id} without a name"
      if h.tls.isSome then throw s!"thread-local {name} is not supported"
      if h.storageClass == some "extern" then
        -- the entity with linkage: an earlier declaration's (whose type stays), or a new one of
        -- sigma; no statement in the block
        if h.init.isSome then throw s!"block-scope extern {name} with an initialiser"
        let syms := (← get).declSyms
        let known := h.previousDecl.any syms.contains
        if known && !(c.children.any isAttr) && (← headerAlignment h).isNone then
          let _ ← entitySym h name
        else varDecl c h
        modify fun st => { st with localNames := st.localNames.insert name .other }
        continue
      if let some (elem, bound) := h.type.bind fun t => vlaSpelling? t.qualType then
        let (vbs, vss) ← vlaDecl c h name elem bound
        if !ds.isEmpty then ss := ss ++ [stmt (.declaration ds.toList)]
        ds := #[]
        bs := bs ++ vbs
        ss := ss ++ vss
        continue
      let (q, t) ← headerType h
      let (align, over) ← objectAlignment c h t
      let inits := c.children.filter (!isAttr ·)
      let reg := h.storageClass == some "register"
      let isStatic := h.storageClass == some "static"
      if let some k := over then
        if reg then throw s!"{name}: over-aligned register object is not supported"
        -- ccomp's frame base is only 16-aligned
        if !isStatic && k > 16 then
          throw s!"{name}: automatic storage aligned to {k} bytes (above the 16-byte frame alignment) is not supported"
      let wrapped ← over.mapM (alignedWrapper name · t)
      let declTy := match wrapped with
        | some w => ct (.struct w.tag)
        | none => t
      let wrap := fun (e : TypedExpression) => match wrapped with
        | some w => wrapInit w e
        | none => e
      if isStatic then
        -- a block-scope static object is an object of sigma, declared and defined here, with no
        -- statement in the block
        let s ← fresh (.id name)
        modify fun st => { st with declSyms := st.declSyms.insert h.id s }
        if let some w := wrapped then
          modify fun st => { st with alignedObjects := st.alignedObjects.insert s.number w }
        let hasInit := h.init.isSome
        match h.init, inits with
        | some _, #[e] =>
          let e := wrap (← staticInitializer t e)
          modify fun st => { st with objectDefinitions := st.objectDefinitions.push (s, e) }
        | none, #[] => pure ()
        | _, _ => throw s!"VarDecl {name}: unexpected children"
        let kind : IdKind := if hasInit then .definition else .tentative
        let g : Global :=
          { sym := s, name, isFunction := false, isStatic := true, firstIsDefinition := hasInit,
            decl := .object (.static, false) align q declTy, kind, hasObjectDefinition := hasInit,
            blockScope := true }
        modify fun st => { st with globals := st.globals.push g,
                                   globalIdx := st.globalIdx.insert s.number st.globals.size,
                                   localNames := st.localNames.insert name .other }
        continue
      checkFrameAlignment name declTy
      let s ← fresh (.id name)
      modify fun st => { st with declSyms := st.declSyms.insert h.id s,
                                 registers := if reg then st.registers.insert s.number else st.registers,
                                 -- a wrapped object is a struct in the Ail: a bound naming it rejects
                                 localNames := st.localNames.insert name
                                   (if wrapped.isSome then .other else .object s t) }
      if let some w := wrapped then
        modify fun st => { st with alignedObjects := st.alignedObjects.insert s.number w }
      bs := bs ++ [(s, ((.unknown, .automatic, reg), align, q, declTy))]
      match h.init, inits with
      | some _, #[e] =>
        let (ebs, pre, e) ← liftFullExpr e
        bs := bs ++ ebs
        if !pre.isEmpty then
          if !ds.isEmpty then ss := ss ++ [stmt (.declaration ds.toList)]
          ds := #[]
          ss := ss ++ pre
        ds := ds.push (s, some (wrap (← initializer t e)))
      | none, #[] => ds := ds.push (s, none)
      | _, _ => throw s!"VarDecl {name}: unexpected children"
    | .functionDecl =>
      blockFunctionDecl c h
      if let some x := h.name then modify fun st => { st with localNames := st.localNames.insert x .other }
    | .typedefDecl =>
      typedefDecl c h (global := false)
      if let some x := h.name then
        modify fun st => { st with localNames := st.localNames.insert x .typedefName }
    -- a static assertion has no run-time effect; Clang has checked it (a false one is an error)
    | .staticAssertDecl => continue
    | .recordDecl => recordDecl c h
    | .enumDecl => enumDecl c h
    | k => throw s!"block-scope {k} is not supported"
  return (bs, ss ++ if ds.isEmpty then [] else [stmt (.declaration ds.toList)])


/-- Lift only a single, unconditionally evaluated path of a full expression. The residual
AST keeps Clang's conversions; its synthetic opaque value is matched by a fresh internal id,
never by a source name or Clang's pointer-valued ids. Ordinary expressions are unchanged. -/
partial def liftFullExpr (n : Node) : M (Bindings × List TypedStatement × Node) := do
  if !hasStmtExpr n then return ([], [], n)
  let some h := n.header? | throw "StmtExpr: absent full expression"
  if h.kind == .stmtExpr then return ← withScope do
    let #[body] := n.children | throw "StmtExpr: one block expected"
    unless body.kind? == some .compoundStmt do throw "StmtExpr: block expected"
    if stmtExprJump body then throw "StmtExpr: a label, or a break, continue or case outside its own statements, is not supported"
    let some last := body.children.back? | throw "StmtExpr: void value is not supported"
    if isStatementKind last.kind then throw "StmtExpr: final expression expected"
    -- Resolve the result after local declarations: it can name a tag defined in the block.
    let (bs, ss) ← block body.children.pop
    let (_, t) ← headerType h
    liftedObject t
    let sym ← fresh .none
    let (ebs, pre, last) ← liftFullExpr last
    let store ← liftedStore sym t (← expr last)
    let inner := stmt (.block (bs ++ ebs) (ss ++ pre ++ [store]))
    return ([(sym, localBinding noQuals t false)],
      [stmt (.declaration [(sym, none)]), inner], ← liftedRef h sym t)
  let cs := n.children
  match h.kind, h.opcode, cs with
  | .binaryOperator, some ",", #[a, b] =>
    -- the left operand is sequenced before the right one: it runs first, its value discarded
    let sa ← statement a
    let (bs, pre, b) ← liftFullExpr b
    return (bs, sa :: pre, b)
  | .binaryOperator, some op, #[a, b] =>
    if op == "&&" || op == "||" then
      -- the left operand is evaluated first; the right one only when the left does not decide,
      -- so a lifted right operand goes into a temporary set under an `if`
      let (abs, apre, a) ← liftFullExpr a
      unless hasStmtExpr b do return (abs, apre, .mk h (some #[a, b]) n.arrayFiller)
      let (_, t) ← headerType h
      let sym ← fresh .none
      let (bbs, bpre, b) ← liftFullExpr b
      let ea ← condition (← expr a)
      let eb ← condition (← expr b)
      let known ← liftedStore sym t (intConst (if op == "&&" then 0 else 1))
      let tested ← liftedStore sym t (mkExpr (← annotOf h) (.binary (intConst 0) .ne eb))
      let right := stmt (.block bbs (bpre ++ [tested]))
      let s := if op == "&&" then stmt (.if_ ea right known) else stmt (.if_ ea known right)
      return (abs ++ [(sym, localBinding noQuals t false)],
        apre ++ [stmt (.declaration [(sym, none)]), s], ← liftedRef h sym t)
    pure ()
  | .conditionalOperator, _, #[c, a, b] =>
    -- the condition is evaluated first, then exactly one operand: lifted operands go into a
    -- temporary set under an `if`
    let (cbs, cpre, c) ← liftFullExpr c
    unless hasStmtExpr a || hasStmtExpr b do
      return (cbs, cpre, .mk h (some #[c, a, b]) n.arrayFiller)
    let (_, t) ← headerType h
    liftedObject t
    let sym ← fresh .none
    let ec ← condition (← expr c)
    let arm (x : Node) : M TypedStatement := do
      let (xbs, xpre, x) ← liftFullExpr x
      return stmt (.block xbs (xpre ++ [← liftedStore sym t (← expr x)]))
    let s := stmt (.if_ ec (← arm a) (← arm b))
    return (cbs ++ [(sym, localBinding noQuals t false)],
      cpre ++ [stmt (.declaration [(sym, none)]), s], ← liftedRef h sym t)
  | _, _, _ => pure ()
  let i ← match h.kind, cs with
    | .parenExpr, #[_] | .implicitCastExpr, #[_] | .cStyleCastExpr, #[_] => pure 0
    | .unaryOperator, #[_] =>
      if ["+", "-", "~", "!", "*"].contains (h.opcode.getD "") then pure 0
      else throw "StmtExpr: unsupported evaluation position"
    | .binaryOperator, #[a, _] =>
      if h.opcode == some "=" && simpleTarget a then pure 1
      else throw "StmtExpr: unsupported evaluation position"
    | _, _ => throw "StmtExpr: unsupported evaluation position"
  let (bs, pre, e) ← liftFullExpr cs[i]!
  return (bs, pre, .mk h (some (cs.set! i e)) n.arrayFiller)

/-- Run a full expression's prefix within its own block, then its consuming statement. -/
partial def fullExprStatement (n : Node) (consume : TypedExpression → TypedStatement) : M TypedStatement := do
  let (bs, pre, e) ← liftFullExpr n
  return prefixed bs pre (consume (← expr e))

/-- A statement as the statements it is spliced into a block as: Cerberus's desugaring of `for`
with an expression (or no) initialiser is the initialiser's statement and a `while`. -/
partial def statements (n : Node) : M (Bindings × List TypedStatement) := do
  let some h := n.header? | throw "absent statement"
  match h.kind with
  | .declStmt => declStmt n
  | .forStmt =>
    let (bs, ss, ownScope) ← forStmt n h
    if ownScope then return ([], [stmt (.block bs ss)])
    return (bs, ss)
  | _ => return ([], [← statement n])

/-- A `for` as Cerberus desugars it: the bindings and statements of its block, and whether that
block is a scope of its own (a declaration initialiser) where it is a statement of a block. -/
partial def forStmt (n : Node) (h : Header) : M (Bindings × List TypedStatement × Bool) := withScope do
  let #[init, condVar, cond, inc, body] := n.children | throw s!"ForStmt {h.id}: five children expected"
  unless condVar.isAbsent do throw "for with a condition variable"
  -- Cerberus's numbering (loop ids share the symbol counter, which the normal form keeps):
  -- the continue label, the initialiser, the loop id and one more, then the body
  let cont ← fresh .none
  let (bs, pre) ← match init with
    | .absent => pure ([], [])
    | i =>
      if i.kind? == some .declStmt then declStmt i
      else do pure ([], [← statement i])
  let loopId ← freshNat
  let _ ← freshNat
  let (cbs, cpre, c) ← match cond with
    | .absent => pure ([], [], none)
    | c => do let (cbs, cpre, c) ← liftFullExpr c; pure (cbs, cpre, some (← condition (← expr c)))
  modify fun st => { st with loops := some cont :: st.loops }
  -- a body that is a `for` is spliced into the loop's body block, its own block included
  let (bbs, bss) ← match body.kind?, body.header? with
    | some .compoundStmt, _ => block body.children
    | some .forStmt, some bh => do
      let (bs, ss, _) ← forStmt body bh
      pure (bs, ss)
    | _, _ => do pure ([], [← statement body])
  modify fun st => { st with loops := st.loops.drop 1 }
  let step ← match inc with
    | .absent => pure (stmt .skip)
    | i => statement i
  let iteration := stmt (.block bbs (bss ++ [stmt (.label cont step (some (.loopContinue loopId)))]))
  -- A lifted test runs at the start of every iteration, after the previous step.
  let w := if cpre.isEmpty then stmt (.while_ (c.getD (intConst 1)) iteration loopId)
    else stmt (.while_ (intConst 1) (stmt (.block cbs (cpre ++
      [stmt (.if_ (c.getD (intConst 1)) iteration (stmt .break_))]))) loopId)
  return (bs, pre ++ [w], init.kind? == some .declStmt)

/-- A `while` or `do` body and the loop id: a `continue` in it is a jump to a label after it
(Cerberus's desugaring), made only when the body has one; Cerberus numbers that label, the body,
the loop id and one more. -/
partial def loopBody (body : Node) : M (TypedStatement × Nat) := do
  let cont ← if hasContinue body then some <$> fresh .none else pure none
  modify fun st => { st with loops := cont :: st.loops }
  let b ← statement body
  modify fun st => { st with loops := st.loops.drop 1 }
  let loopId ← freshNat
  let _ ← freshNat
  match cont with
  | some l => return (stmt (.block [] [b, stmt (.label l (stmt .skip) (some (.loopContinue loopId)))]), loopId)
  | none => return (b, loopId)

partial def statement (n : Node) : M TypedStatement := do
  let some h := n.header? | throw "absent statement"
  if let some a ← assertCall? n then
    return ← fullExprStatement a (fun e => stmt (.expr (mkExpr (.rvalue .void) (.assert e))))
  unless isStatementKind h.kind do
    let root := discardedStmtExpr n
    -- A discarded full expression with a statement expression: its operators with sequenced
    -- operands as the equivalent statements, so that void operands need no temporary.
    if hasStmtExpr root then
      match root.kind?, root.header?.bind (·.opcode), root.children with
      | some .stmtExpr, _, #[body] =>
        if stmtExprJump body then throw "StmtExpr: a label, or a break, continue or case outside its own statements, is not supported"
        unless body.kind? == some .compoundStmt do throw "StmtExpr: block expected"
        return ← statement body
      | some .stmtExpr, _, _ => throw "StmtExpr: one block expected"
      | some .conditionalOperator, _, #[c, a, b] =>
        let (bs, pre, c) ← liftFullExpr c
        return prefixed bs pre
          (stmt (.if_ (← condition (← expr c)) (← statement (voidOperand a)) (← statement (voidOperand b))))
      | some .binaryOperator, some "&&", #[a, b] =>
        let (bs, pre, a) ← liftFullExpr a
        return prefixed bs pre (stmt (.if_ (← condition (← expr a)) (← statement b) (stmt .skip)))
      | some .binaryOperator, some "||", #[a, b] =>
        let (bs, pre, a) ← liftFullExpr a
        return prefixed bs pre (stmt (.if_ (← condition (← expr a)) (stmt .skip) (← statement b)))
      | some .binaryOperator, some ",", #[a, b] =>
        return stmt (.block [] [← statement a, ← statement b])
      | _, _, _ => pure ()
    return ← fullExprStatement n (fun e => stmt (.expr e))
  match h.kind with
  | .compoundStmt => withScope do
    let (bs, ss) ← block n.children
    return stmt (.block bs ss)
  | .declStmt | .forStmt =>
    let (bs, ss) ← statements n
    match bs, ss with
    | [], [s] => return s
    | _, _ => return stmt (.block bs ss)
  | .nullStmt => return stmt .skip
  | .attributedStmt =>
    -- Fallthrough is a diagnostic annotation on a null statement. Do not drop
    -- arbitrary statement attributes: others can change execution semantics.
    let cs := n.children
    let some body := cs.back? | throw "AttributedStmt without a statement"
    let attrs := cs.pop
    unless !attrs.isEmpty && attrs.all (·.kind? == some .fallThroughAttr) &&
        body.kind? == some .nullStmt do
      throw "AttributedStmt: only fallthrough on a null statement is supported"
    statement body
  | .returnStmt =>
    -- a function that uses the dynamic stack restores its top after the value is computed
    let some f := (← get).stack | match n.children with
      | #[] => return stmt .returnVoid
      | #[e] => fullExprStatement e (fun e => stmt (.return_ e))
      | _ => throw s!"ReturnStmt {h.id}: at most one operand expected"
    let restore ← stackRestore f
    match n.children with
    | #[] => return stmt (.block [] [restore, stmt .returnVoid])
    | #[e] =>
      if f.ret matches .mk _ .void then
        return ← fullExprStatement e (fun e => stmt (.block [] [stmt (.expr e), restore, stmt .returnVoid]))
      let tmp ← fresh .none
      let value := mkExpr (.rvalue (← genOf f.ret))
        (.rvalue (mkExpr (.lvalue noQuals f.ret false) (.ident tmp)))
      fullExprStatement e (fun e => stmt (.block [(tmp, localBinding noQuals f.ret false)]
        [stmt (.declaration [(tmp, some e)]), restore, stmt (.return_ value)]))
    | _ => throw s!"ReturnStmt {h.id}: at most one operand expected"
  | .ifStmt =>
    match n.children with
    | #[c, a] =>
      let (bs, pre, c) ← liftFullExpr c
      return prefixed bs pre (stmt (.if_ (← condition (← expr c)) (← statement a) (stmt .skip)))
    | #[c, a, b] =>
      let (bs, pre, c) ← liftFullExpr c
      return prefixed bs pre (stmt (.if_ (← condition (← expr c)) (← statement a) (← statement b)))
    | _ => throw s!"IfStmt {h.id}: unexpected children"
  | .whileStmt =>
    let #[c, body] := n.children | throw s!"WhileStmt {h.id}: two children expected"
    let (bs, pre, c) ← liftFullExpr c
    let ec ← condition (← expr c)
    let (b, loopId) ← loopBody body
    if pre.isEmpty then return stmt (.while_ ec b loopId)
    -- The prefix runs on every test, including after `continue` in the original body.
    return stmt (.while_ (intConst 1)
      (stmt (.block bs (pre ++ [stmt (.if_ ec b (stmt .break_))]))) loopId)
  | .doStmt =>
    let #[body, c] := n.children | throw s!"DoStmt {h.id}: two children expected"
    let (b, loopId) ← loopBody body
    let (bs, pre, c) ← liftFullExpr c
    if pre.isEmpty then return stmt (.do_ b (← condition (← expr c)) loopId)
    -- a lifted test runs after the body, also after a `continue` (a jump to the body's end)
    let test := prefixed bs pre (stmt (.if_ (← condition (← expr c)) (stmt .skip) (stmt .break_)))
    return stmt (.while_ (intConst 1) (stmt (.block [] [b, test])) loopId)
  | .switchStmt =>
    let #[c, body] := n.children | throw s!"SwitchStmt {h.id}: two children expected"
    -- gcc converts the case constants to the wide type, Clang to the declared one
    if (← gccOperand c).isWide then
      throw s!"SwitchStmt {h.id} on a value of a wide bit-field type (gcc and Clang differ)"
    return stmt (.switch (← expr c) (← statement body))
  | .caseStmt =>
    let #[v, body] := n.children | throw s!"CaseStmt {h.id}: two children expected (no case ranges)"
    return stmt (.case_ (← constInt v) (← statement body))
  | .defaultStmt =>
    let #[body] := n.children | throw s!"DefaultStmt {h.id}: one child expected"
    return stmt (.default (← statement body))
  | .breakStmt => return stmt .break_
  | .continueStmt =>
    match (← get).loops with
    | some cont :: _ => return stmt (.goto cont)
    | _ => throw "continue outside a loop"
  | .labelStmt =>
    let some d := h.declId | throw s!"LabelStmt {h.id}: declaration expected"
    let #[body] := n.children | throw s!"LabelStmt {h.id}: one child expected"
    let l ← labelSym d
    return stmt (.label l (← statement body) none)
  | .gotoStmt =>
    let some d := h.targetLabelDeclId | throw s!"GotoStmt {h.id} without a target"
    return stmt (.goto (← labelSym d))
  | k => throw s!"statement {k} is not supported yet"

/-- The bindings and statements of a block's items. -/
partial def block (items : Array Node) : M (Bindings × List TypedStatement) := do
  let mut bs : Bindings := []
  let mut ss : Array TypedStatement := #[]
  for c in items do
    let (b, s) ← statements c
    bs := bs ++ b
    ss := ss ++ s.toArray
  return (bs, ss.toList)

end

/-! ## Declarations -/

/-- Function ABIs do not carry typedef alignment in Ail. Reject an aligned
alias in a signature rather than silently losing parameter alignment. -/
partial def checkSignatureAlignment : Type.TypeSpelling → M Unit
  | .leaf _ (.typedefName name) => do
    if (← get).typedefAligns.contains name then
      throw "aligned typedef in a function signature is not supported"
  | .pointer _ t | .array t _ | .arrayExpr t _ => checkSignatureAlignment t
  | .function r ps _ => do
    checkSignatureAlignment r
    (ps.getD []).forM checkSignatureAlignment
  | _ => pure ()

/-- A lower bound for the spelling of the complete array suffixes in a type, before
resolving typedefs. Even a large bound may be a one-character macro, so each costs only `[x]`.
Typedef-hidden arrays contribute nothing. -/
def parameterArraySuffix : Type.TypeSpelling → Nat
  | .array e (some _) => 3 + parameterArraySuffix e
  | _ => 0

/-- A pointer parameter can be an adjusted array parameter. Clang's JSON omits
the original array bound, including its entry-time side effects (`int a[i++]`).
Accept only declarators ending at the name, or at a `]` at most three characters after it:
`[]`, or a bound of one or two characters (`[8]`, `[16]`, `[n]`). Every C expression with a side
effect other than a volatile read (`a=b`, `i++`, `f()`) is at least three characters long, so such
a bound has none; a volatile read in it (`int a[v]`) is not made. A direct function pointer cannot
be an adjusted array (C forbids arrays of functions); its trailing prototype therefore needs no
bound check. Explicit inner array dimensions contribute at least three characters each;
subtract only that minimum before checking the omitted outer bound. Other suffixes fail
closed, including longer fixed bounds indistinguishable from VLAs. Only definitions evaluate parameter bounds; prototype declarations do not. -/
def checkParameterBound (h : Header) (t : Ctype) : M Unit := do
  match t with
  | .mk _ (.pointer _ (.mk _ (.function ..)))
  | .mk _ (.pointer _ (.mk _ (.functionNoParams ..))) => return
  | .mk _ (.pointer ..) => pure ()
  | _ => return
  let fail : M Unit := throw s!"parameter {h.name.getD "(unnamed)"}: original array bound is absent from Clang JSON"
  let some _ := h.name | fail
  let some loc := h.loc | fail
  let some range := h.range | fail
  -- Macro spelling positions may belong to different tokens or files; they
  -- cannot establish that the original declarator has no bound.
  let .bare loc := loc | fail
  let .bare last := range.end | fail
  let (some start, some stop, some len) := (loc.offset, last.offset, loc.tokLen) | fail
  -- Only the length of what lies between the name and `]` is known, not its contents: at most
  -- three characters (`[`, then a bound of at most two). Unknown or inconsistent locations
  -- reject as well.
  let suffix := match h.type.map fun ty => Type.parse ty.qualType with
    | some (.ok (.pointer _ e)) => parameterArraySuffix e
    | _ => 0
  unless stop == start || (start + len < stop && stop ≤ start + len + suffix + 3 && last.tokLen == some 1) do
    fail

def functionDecl (n : Node) (h : Header) : M Unit := do
  let some name := h.name | throw s!"FunctionDecl {h.id} without a name"
  if preludeFunctions.contains name then return
  if let some t := h.type then checkSignatureAlignment (← Type.parse t.qualType)
  let (_, fty) ← headerType h
  if let some g := (← get).globals.find? fun g => g.name == name && g.libraryBuiltin then
    if h.storageClass == some "static" then throw s!"{name}: library builtin with internal linkage"
    if let some ty := h.type then checkLibrarySpelling name ty.qualType
    let .function _ r ps v _ _ := g.decl | throw "library builtin: function expected"
    checkLibraryType name fty (ct (.function r ps v))
  let params := n.children.filter fun c => c.kind? == some .parmVarDecl
  let body := n.children.filter fun c => c.kind? == some .compoundStmt
  for c in n.children do
    unless isAttr c || c.kind? == some .parmVarDecl || c.kind? == some .compoundStmt do
      throw s!"FunctionDecl {name}: child {c.kind} is not supported"
  for c in n.children do
    if isAttr c then
      if c.kind == .gnuInlineAttr || c.kind == .leafAttr then
        unless c.children.isEmpty do throw s!"{c.kind}: unexpected children"
      if c.kind == .gnuInlineAttr && h.inline != some true then
        throw "GNUInlineAttr: inline function expected"
      -- GNU external inline bodies need not define the external symbol. Calls through
      -- its address may use another definition; emitting this body would change them.
      if c.kind == .gnuInlineAttr && !body.isEmpty && h.storageClass != some "static" then
        throw "GNUInlineAttr: external inline definition is not supported"
      unless [Kind.c11NoReturnAttr, .builtinAttr, .noThrowAttr, .constAttr, .pureAttr,
          .formatAttr, .noInlineAttr, .alwaysInlineAttr, .unusedAttr, .usedAttr, .noReturnAttr,
          .warnUnusedResultAttr, .coldAttr, .hotAttr, .nonNullAttr,
          .restrictAttr, .allocSizeAttr, .allocAlignAttr, .returnsTwiceAttr,
          -- sanitizer instrumentation and symbol visibility: no effect on an executable's behaviour
          .noSanitizeAttr, .visibilityAttr, .gnuInlineAttr, .leafAttr].contains c.kind ||
          neutralAttr c.kind do
        throw s!"FunctionDecl {name}: attribute {c.kind} is not supported"
  let noreturn := n.children.any (·.kind? == some .c11NoReturnAttr)
  let isDef := body.size == 1
  -- parameters: the types of the declaration's type, `register` from its ParmVarDecls
  let (ret, ps, variadic) ← match fty with
    | .mk _ (.function r ps v) =>
      if params.size == ps.length then
        -- Clang's function type drops the parameters' qualifiers; their declarations keep them
        let ps' ← (ps.zip params.toList).mapM fun ((_, t, _), p) => do
          let some ph := p.header? | throw "absent parameter"
          let (q, _) ← headerType ph
          pure (q, t, ph.storageClass == some "register")
        pure (r, ps', v)
      else if params.isEmpty then pure (r, ps, v)
      else throw s!"FunctionDecl {name}: parameter count"
    | .mk _ (.functionNoParams r) =>
      -- `int f()` declares no parameters; a K&R definition's come from its ParmVarDecls
      let ps ← params.toList.mapM fun p => do
        let some ph := p.header? | throw "absent parameter"
        let (q, t) ← headerType ph
        pure (q, t, ph.storageClass == some "register")
      pure (r, ps, false)
    | _ => throw s!"FunctionDecl {name}: not a function type"
  let (sym, _) ← entitySym h name
  let old ← globalOf? sym
  let g : Global := match old with
    | some g => g
    | none => { sym, name, isFunction := true, isStatic := h.storageClass == some "static",
                firstIsDefinition := isDef, decl := .function false ret [] false false false,
                kind := .declaration }
  unless g.isFunction do throw s!"{name} redeclared as a function"
  let inline_ := g.inline_ || h.inline == some true
  let noreturn := g.noreturn || noreturn
  -- the parameters' `const` and `volatile` are not part of the function's type (STD
  -- §6.7.6.3#15): Cerberus's declarations drop them and keep `restrict`, unless the function's
  -- first declaration is its definition (then they are the definition's, qualifiers included)
  let ps := if g.firstIsDefinition then ps
    else ps.map fun (q, t, r) => ({ noQuals with restrict := q.restrict }, t, r)
  let ps ← match g.decl with
    | .function _ _ ps₀ _ _ _ => pure (if g.firstIsDefinition && old.isSome && !isDef then ps₀ else ps)
    | _ => pure ps
  let decl := Declaration.function (!g.firstIsDefinition) ret ps variadic inline_ noreturn
  setGlobal { g with
    decl, inline_, noreturn, functionSpelling := h.type.map (·.qualType),
    kind := upgrade g.kind (if isDef then .definition else .declaration) }
  if isDef then
    let translateBody : M Unit := do
      let declPs := match decl with
        | .function _ _ dps _ _ _ => dps
        | _ => []
      let mut psyms := #[]
      modify fun st => { st with localNames := {}, stackMarks := [], stack := none }
      for (p, i) in params.toList.zipIdx do
        let some ph := p.header? | throw "absent parameter"
        let (_, pt) ← headerType ph
        checkParameterBound ph pt
        checkFrameAlignment s!"parameter {ph.name.getD "(unnamed)"}" pt
        let s ← fresh (match ph.name with | some x => .id x | none => .none)
        let reg := ph.storageClass == some "register"
        modify fun st => { st with declSyms := st.declSyms.insert ph.id s,
                                   registers := if reg then st.registers.insert s.number else st.registers,
                                   localNames := match ph.name with
                                     | some x => st.localNames.insert x (.object s pt)
                                     | none => st.localNames,
                                   paramQuals := match declPs[i]? with
                                     | some (q, _, _) => st.paramQuals.insert s.number q
                                     | none => st.paramQuals }
        psyms := psyms.push s
      modify fun st => { st with labels := {}, loops := [] }
      -- Cerberus numbers a function's labels before its body
      for l in labelsOf body[0]! #[] do
        let some d := l.declId | throw "LabelStmt without a declaration"
        let s ← fresh (match l.name with | some x => .id x | none => .none)
        modify fun st => { st with labels := st.labels.insert d s }
      let marker ← freshNat
      -- the dynamic stack: the top at entry, restored on return and at the end of the body
      let (vla, alloca) := stackUses body[0]!
      if vla && alloca then throw s!"{name}: variable-length arrays and alloca in one function"
      let mut frame : Option StackFrame := none
      if vla || alloca then
        frame := some { base := ← fresh .none, ret := ret.2, vla }
      modify fun st => { st with stack := frame }
      let b ← statement body[0]!
      let b ← match frame with
        | none => pure b
        | some f =>
          let (_, top) ← ensureArena
          pure (stmt (.block [(f.base, localBinding noQuals Builtin.ulT false)]
            [stmt (.declaration [(f.base, some (Builtin.get Builtin.ulT top))]), b,
             ← stackRestore f]))
      modify fun st => { st with stack := none }
      let fd : FunctionDefinition GenTypeCategory :=
        { loc := .unknown, marker, attrs := noAttrs, params := psyms.toList, body := b }
      modify fun st => { st with functionDefinitions := st.functionDefinitions.push (sym, fd) }
    if (← get).partialBodies then
      -- Run against a snapshot: on error, parameters, labels, lifted statics, local tags,
      -- extern declarations and the symbol counter must all stay as before the attempt.
      let saved ← get
      match translateBody.run saved with
      | .ok (_, st) => set st
      | .error reason =>
        setGlobal { g with decl, inline_, noreturn }
        modify fun st => { st with skippedFunctions := st.skippedFunctions.push ⟨name, reason⟩ }
    else translateBody


def topDecl (n : Node) : M Unit := do
  let some h := n.header? | throw "absent top-level declaration"
  if h.isImplicit == some true then return
  match h.kind with
  | .typedefDecl => typedefDecl n h
  | .recordDecl => recordDecl n h
  | .enumDecl => enumDecl n h
  | .functionDecl => functionDecl n h
  | .varDecl => varDecl n h
  | .emptyDecl =>
    -- An extra file-scope semicolon declares nothing and allocates no symbols.
    unless n.children.isEmpty && n.arrayFiller.isNone do
      throw "EmptyDecl: unexpected children"
  | k => throw s!"top-level {k} is not supported"

/-! ## Zero initialisers of tentative definitions -/

partial def zeroConstant (t : Ctype) : M Constant := do
  match t with
  | .mk _ (.basic (.integer _)) => return .integer (.iconstant 0 .octal none)
  | .mk _ (.basic (.floating _)) => return .floating ("0.0", none)
  | .mk _ (.pointer _ _) => return .null
  | .mk _ (.array e (some k)) =>
    let z ← zeroConstant e
    return .array e (List.replicate k.toNat z)
  | .mk _ (.struct s) => match (← get).tagDefIdx[s.number]? with
    | some (.struct ms _) => return .struct s (← ms.mapM fun (x, (_, _, _, t)) => do
        pure (x, ← zeroConstant t))
    | _ => throw "tentative definition of an incomplete struct"
  | .mk _ (.union s) => match (← get).tagDefIdx[s.number]? with
    | some (.union ((x, (_, _, _, t)) :: _)) => return .union s x (← zeroConstant t)
    | _ => throw "tentative definition of an incomplete union"
  | _ => throw "tentative definition of an unsupported type"

def zeroType : Ctype → Except String GenType
  | .mk _ (.basic (.integer _)) => return .basic (.integer (.concrete (.signed .int)))
  | .mk _ (.basic (.floating _)) => return .basic (.floating (.realFloating .double))
  | .mk _ (.pointer _ _) => return .pointer noQuals (ct .void)
  | .mk _ (.array e n) => return .array e n
  | .mk _ (.struct s) => return .struct s
  | .mk _ (.union s) => return .union s
  | _ => throw "tentative definition of an unsupported type"

/-! ## The program -/

def finish : M TypedProgram := do
  let st ← get
  let mut objs := st.objectDefinitions
  for g in st.globals do
    if !g.isFunction && g.kind == .tentative && !g.hasObjectDefinition then
      let .object _ _ _ t := g.decl | throw "object expected"
      let z ← zeroConstant t
      objs := objs.push (g.sym, rvalue (← zeroType t) (.const z))
  let st ← get
  let declarations := st.globals.toList.map fun g => (g.sym, (Cerberus.Loc.unknown, noAttrs, g.decl))
  let ext := st.globals.toList.filter (!·.isStatic) |>.map fun g =>
    (Identifier.mk .unknown g.name, (g.sym, g.kind))
  let ext := ext.mergeSort fun a b => compare a.1.name b.1.name != .gt
  let main := st.globals.find? fun g =>
    g.name == "main" && g.isFunction && !g.isStatic && g.kind == .definition
  let sigma : Sigma GenTypeCategory := {
    declarations
    objectDefinitions := objs.toList
    functionDefinitions := st.functionDefinitions.toList
    staticAssertions := []
    tagDefinitions := st.tagDefs.toList
    externIdmap := ext
    typedefAttributes := st.typedefSyms.toList.map (·, noAttrs)
    loopAttributes := []
    cnFunctions := [], cnLemmata := [], cnPredicates := [], cnDatatypes := [], cnDeclSpecs := []
    cnIdents := [] }
  return (main.map (·.sym), sigma)

/-- Translate with optional body recovery. A recovered function has a declaration and no
function definition; errors in signatures, file-scope declarations and initializers stay fatal.
The diagnostics are returned as data so the translator remains pure. -/
def translateWith (tu : Node) (partialBodies : Bool := false) :
    Except String (Ail.TypedProgram × Array SkippedFunction) := do
  unless tu.kind? == some .translationUnitDecl do throw s!"not a translation unit: {tu.kind}"
  let (p, st) ← (do tu.children.forM topDecl; finish).run { partialBodies }
  return (p, st.skippedFunctions)

/-- Translate a translation unit to typed Ail, or say why not. -/
def translate (tu : Node) : Except String Ail.TypedProgram := do
  return (← translateWith tu).1

end Silmaril.Clang.ToAil
