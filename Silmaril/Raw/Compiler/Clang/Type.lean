module

/-! # Clang's type spellings

Clang's JSON prints the type of a declaration or an expression as a string (`qualType`), the way
its `TypePrinter` spells a type in C: `unsigned long`, `const char *restrict`, `int (*)(int, ...)`,
`struct S [3]`, `struct (unnamed at f.c:4:2)`, `size_t`. Only `TypedefDecl` has the type as a tree
of type nodes, so the translation (`Silmaril.Clang.ToAil`) reads every other type from its
spelling. This file parses a spelling into `TypeSpelling`, a C abstract declarator over named
leaves: builtin type specifiers, typedef names and tag references. Resolving the names (typedefs,
tags, Cerberus's builtin typedefs of `cerb-prelude.h`) into a `Ctype` is the translation's job.

Fail-closed: a token or a shape outside the C subset (`_Atomic(…)`, block pointers) is an
error, never a guess. Attributes that do
not change the C type (`__attribute__((noreturn))` on function types, the nullability qualifiers
`_Nonnull`, `_Nullable`, `_Null_unspecified` of Clang's builtin declarations) are dropped.

A GNU vector type is spelled with its attribute before the lane type:
`__attribute__((__vector_size__(4 * sizeof(int)))) int` is a vector of 4 `int`s
(`Leaf.vector`). Any other attribute that mentions vectors (`ext_vector_type`, …) is an error.

An array bound is a number, except where Clang folded a GNU variable-length array to a constant
array: it then prints the bound as written (`char [(sizeof(Parse) - ((int)((char *)&((Parse
*)0)->sLastToken)))]`), and the JSON has no folded value. Such a bound is parsed as a
`BoundExpr` for the translation to evaluate. The bound of a variable-length array (`int [n %
1000 + 1]`) is parsed the same way, with its identifiers as `BoundExpr.var`: the JSON of a
variable declaration has no expression for it, and the translation resolves the names.
-/

@[expose] public section

namespace Silmaril.Clang.Type

/-- Type qualifiers. -/
structure Quals where
  const : Bool := false
  restrict : Bool := false
  volatile : Bool := false
  deriving DecidableEq, Repr, Inhabited

def Quals.union (a b : Quals) : Quals :=
  ⟨a.const || b.const, a.restrict || b.restrict, a.volatile || b.volatile⟩

/-- A leaf of a type spelling. -/
inductive Leaf where
  /-- Builtin specifiers in Clang's canonical spelling: `int`, `unsigned long long`, `void`, … -/
  | builtin (words : String)
  /-- A typedef name. -/
  | typedefName (name : String)
  /-- `struct`/`union`/`enum` and the tag: a name, or Clang's `(unnamed at FILE:LINE:COL)`. -/
  | tag (keyword : String) (name : String)
  /-- A GNU vector (`vector_size`) of `lanes` lanes of the type `elem`. -/
  | vector (lanes : Nat) (elem : Leaf)
  deriving DecidableEq, Repr, Inhabited

mutual

/-- A parsed type spelling: a qualified leaf under pointer, array and function declarators. -/
inductive TypeSpelling where
  | leaf (q : Quals) (l : Leaf)
  /-- A pointer; the qualifiers are those of the pointer itself (`int *const`). -/
  | pointer (q : Quals) (t : TypeSpelling)
  | array (elem : TypeSpelling) (size : Option Nat)
  /-- An array whose bound Clang spells as an expression: a GNU variable-length array that Clang
  folded to a constant array (`char [sizeof(T) - (int)(char *)&((T *)0)->m]`). -/
  | arrayExpr (elem : TypeSpelling) (size : BoundExpr)
  /-- A function type; `params = none` is a function without a prototype (`int ()`). -/
  | function (ret : TypeSpelling) (params : Option (List TypeSpelling)) (variadic : Bool)
  deriving Repr, Inhabited

/-- An array bound spelled as an expression, in the subset that folds without objects: integer
literals, `sizeof(type)`, casts, `&`, member access through a constant pointer, unary `-` and
`+ - * / %`. -/
inductive BoundExpr where
  /-- A decimal literal and its suffix (`""`, `"U"`, `"UL"`, …). -/
  | num (n : Nat) (suffix : String)
  | sizeofType (t : TypeSpelling)
  | cast (t : TypeSpelling) (e : BoundExpr)
  | addrOf (e : BoundExpr)
  /-- `e->m` (`arrow`) or `e.m`. -/
  | member (e : BoundExpr) (arrow : Bool) (name : String)
  | neg (e : BoundExpr)
  | binary (op : Char) (a b : BoundExpr)
  /-- An identifier: the bound of a variable-length array, which no constant folds. -/
  | var (name : String)
  deriving Repr, Inhabited

end

/-! ## Tokens -/

inductive Tok where
  | word (s : String)
  | num (n : Nat)
  | punct (c : Char)
  | ellipsis
  | arrow
  /-- Clang's name of an unnamed tag, `(unnamed at …)`, parentheses included, or of an
  anonymous member's tag, qualified by the records around it: `S::(anonymous at …)`. -/
  | unnamed (s : String)
  /-- `__attribute__((__vector_size__(N * sizeof(T))))`: the lane count and `T` as spelled. -/
  | vector (lanes : Nat) (elem : String)
  deriving DecidableEq, Repr, Inhabited

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- The characters up to the parenthesis that closes an open one (depth 1), and the rest. -/
def balanced : List Char → Nat → List Char → Option (List Char × List Char)
  | [], _, _ => none
  | ')' :: cs, 1, acc => some ((')' :: acc).reverse, cs)
  | ')' :: cs, d + 1, acc => balanced cs d (')' :: acc)
  | '(' :: cs, d, acc => balanced cs (d + 1) ('(' :: acc)
  | c :: cs, d, acc => balanced cs d (c :: acc)

def startsWith (cs : List Char) (p : String) : Bool := p.toList.isPrefixOf cs

/-- The arguments of an attribute, `((…))` as `balanced` returns them, if they are Clang's
spelling of a GNU vector's size, `((__vector_size__(N * sizeof(T))))`: `N` and `T`. -/
def vectorSize? (arg : List Char) : Option (Nat × String) := do
  let p := "((__vector_size__("
  guard (startsWith arg p)
  let r := arg.drop p.length
  let ds := r.takeWhile Char.isDigit
  guard !ds.isEmpty
  let r := r.drop ds.length
  let q := " * sizeof("
  guard (startsWith r q)
  let r := r.drop q.length
  guard (r.length > 4 && startsWith (r.drop (r.length - 4)) "))))")
  return ((String.ofList ds).toNat!, String.ofList (r.take (r.length - 4)))

/-- Words that do not change the C type and are dropped. -/
def ignoredWords : List String := ["_Nonnull", "_Nullable", "_Null_unspecified"]

/-- An unnamed tag's name, `(unnamed …)` or `(anonymous …)`, and the rest. -/
def unnamedTag? (cs : List Char) : Option (List Char × List Char) :=
  match cs with
  | '(' :: rest =>
    if startsWith rest "unnamed " || startsWith rest "anonymous " then balanced rest 1 ['('] else none
  | _ => none

/-- The rest of a name qualified by `::` (`S::(anonymous at …)`, `S::(anonymous union)::…`),
which Clang prints for the type of an anonymous member: the name and what follows it. -/
partial def qualified (name : List Char) (cs : List Char) : Except String (List Char × List Char) :=
  match cs with
  | ':' :: ':' :: rest =>
    match unnamedTag? rest with
    | some (seg, rest') => qualified (name ++ [':', ':'] ++ seg) rest'
    | none =>
      let w := rest.takeWhile isWordChar
      if w.isEmpty then throw "a qualified name without a segment"
      else qualified (name ++ [':', ':'] ++ w) (rest.drop w.length)
  | _ => return (name, cs)

partial def tokenize (cs : List Char) (acc : Array Tok) : Except String (Array Tok) :=
  match cs with
  | [] => return acc
  | c :: rest =>
    if c == ' ' then tokenize rest acc
    else if c == '(' && (startsWith rest "unnamed " || startsWith rest "anonymous ") then
      match unnamedTag? cs with
      | some (inner, rest') => do
        let (n, rest'') ← qualified inner rest'
        tokenize rest'' (acc.push (.unnamed (String.ofList n)))
      | none => throw "unbalanced unnamed tag"
    else if c == '.' && startsWith rest ".." then tokenize (rest.drop 2) (acc.push .ellipsis)
    else if c == '-' && rest.head? == some '>' then tokenize rest.tail (acc.push .arrow)
    else if "*()[],&+-/%.".toList.contains c then tokenize rest (acc.push (.punct c))
    else if c.isDigit then
      let ds := cs.takeWhile Char.isDigit
      tokenize (cs.drop ds.length) (acc.push (.num (String.ofList ds).toNat!))
    else if isWordChar c then
      let w := String.ofList (cs.takeWhile isWordChar)
      let rest' := cs.drop w.length
      if w == "__attribute__" then
        -- `__attribute__((…))`: drop it
        match rest'.dropWhile (· == ' ') with
        | '(' :: r => match balanced r 1 ['('] with
          | some (arg, r') =>
            if let some (n, e) := vectorSize? arg then tokenize r' (acc.push (.vector n e))
            else if ((String.ofList arg).splitOn "vector").length > 1 then
              throw s!"vector attribute {String.ofList arg}"
            else tokenize r' acc
          | none => throw "unbalanced __attribute__"
        | _ => throw "__attribute__ without arguments"
      else if ignoredWords.contains w then tokenize rest' acc
      else if startsWith rest' "::" then do
        let (n, rest'') ← qualified w.toList rest'
        tokenize rest'' (acc.push (.unnamed (String.ofList n)))
      else tokenize rest' (acc.push (.word w))
    else throw s!"unexpected character {repr c}"

/-! ## Parser -/

abbrev P := StateT (List Tok) (Except String)

def peek : P (Option Tok) := do return (← get).head?

def advance : P Unit := modify List.tail

def expect (t : Tok) : P Unit := do
  match (← get) with
  | t' :: rest => if t == t' then set rest else throw s!"expected {repr t}, got {repr t'}"
  | [] => throw s!"expected {repr t}, got the end"

/-- Words that make up builtin type specifiers. -/
def specWords : List String :=
  ["void", "char", "short", "int", "long", "float", "double", "signed", "unsigned", "_Bool", "_Complex"]

def tagWords : List String := ["struct", "union", "enum"]

/-- Qualifier words. -/
def qualOf? : String → Option Quals
  | "const" => some { const := true }
  | "volatile" => some { volatile := true }
  | "restrict" => some { restrict := true }
  | _ => none

/-- Qualifiers, as many as follow. -/
partial def quals (q : Quals) : P Quals := do
  match ← peek with
  | some (.word w) => match qualOf? w with
    | some q' => advance; quals (q.union q')
    | none => return q
  | _ => return q

/-- The specifiers and qualifiers before the declarator: one leaf and its qualifiers. A vector
attribute among them (`vec`) makes the leaf the lane type of a vector. -/
partial def specifiers (q : Quals) (spec : List String) (leaf : Option Leaf)
    (vec : Option (Nat × String) := none) : P (Quals × Leaf) := do
  match ← peek with
  | some (.vector n e) =>
    if vec.isNone && spec.isEmpty && leaf.isNone then
      advance; specifiers q spec leaf (some (n, e))
    else throw "a misplaced vector attribute"
  | some (.word w) =>
    if let some q' := qualOf? w then advance; specifiers (q.union q') spec leaf vec
    else if specWords.contains w && leaf.isNone then advance; specifiers q (spec ++ [w]) leaf vec
    else if tagWords.contains w && spec.isEmpty && leaf.isNone then
      advance
      match ← peek with
      | some (.word n) => advance; specifiers q spec (some (.tag w n)) vec
      | some (.unnamed n) => advance; specifiers q spec (some (.tag w n)) vec
      | t => throw s!"{w} without a tag: {repr t}"
    else if spec.isEmpty && leaf.isNone && !specWords.contains w then
      advance; specifiers q spec (some (.typedefName w)) vec
    else finish q spec leaf vec
  | _ => finish q spec leaf vec
where
  finish (q : Quals) (spec : List String) (leaf : Option Leaf) (vec : Option (Nat × String)) :
      P (Quals × Leaf) := do
    let l ← match leaf, spec with
      | some l, [] => pure l
      | none, _ :: _ => pure (.builtin (" ".intercalate spec))
      | _, _ => throw "no type specifier"
    match vec with
    | none => return (q, l)
    | some (n, e) =>
      -- the lane type is spelled twice; both spellings must name the same type
      let spelled := match l with
        | .builtin w | .typedefName w => some w
        | _ => none
      unless spelled == some e do throw s!"vector of {e} spelled with lanes {repr l}"
      return (q, .vector n l)

/-- Words of a bound that are not identifiers. -/
def boundKeywords : List String :=
  ["sizeof", "alignof", "_Alignof", "__alignof", "__alignof__", "_Generic", "__extension__",
   "__builtin_offsetof", "__real__", "__imag__"] ++ specWords ++ tagWords

mutual

/-- A whole type spelling. -/
partial def typeName : P TypeSpelling := do
  let (q, l) ← specifiers {} [] none
  let d ← absDeclarator
  return d (.leaf q l)

/-- An abstract declarator, as the function it applies to the type it declares. -/
partial def absDeclarator : P (TypeSpelling → TypeSpelling) := do
  let ptrs ← pointers id
  let direct ← directDeclarator
  return fun t => direct (ptrs t)

/-- `*` with its qualifiers, repeated. -/
partial def pointers (acc : TypeSpelling → TypeSpelling) : P (TypeSpelling → TypeSpelling) := do
  match ← peek with
  | some (.punct '*') =>
    advance
    let q ← quals {}
    pointers (fun t => .pointer q (acc t))
  | _ => return acc

/-- A parenthesised declarator (`(*)`) and the array and function suffixes after it. -/
partial def directDeclarator : P (TypeSpelling → TypeSpelling) := do
  let toks ← get
  match toks with
  | .punct '(' :: .punct '*' :: _ =>
    advance
    let inner ← absDeclarator
    expect (.punct ')')
    let sufs ← suffixes
    return fun t => inner (sufs t)
  | _ => suffixes

/-- Array and function suffixes: `s₁ s₂ … sₙ` applied to `T` is `s₁ (s₂ (… (sₙ T)))`. -/
partial def suffixes : P (TypeSpelling → TypeSpelling) := do
  match ← peek with
  | some (.punct '[') =>
    advance
    let size : Option (Nat ⊕ BoundExpr) ← match ← get with
      | .num n :: .punct ']' :: _ => advance; pure (some (.inl n))
      | .punct ']' :: _ => pure none
      | _ => pure (some (.inr (← boundExpr)))
    expect (.punct ']')
    let rest ← suffixes
    return fun t => match size with
      | some (.inr e) => .arrayExpr (rest t) e
      | some (.inl n) => .array (rest t) (some n)
      | none => .array (rest t) none
  | some (.punct '(') =>
    advance
    let (params, variadic) ← parameters
    let rest ← suffixes
    return fun t => .function (rest t) params variadic
  | _ => return id

/-- The parameter list after `(`, up to and including `)`. -/
partial def parameters : P (Option (List TypeSpelling) × Bool) := do
  match (← get) with
  | .punct ')' :: rest => set rest; return (none, false)
  | .word "void" :: .punct ')' :: rest => set rest; return (some [], false)
  | _ =>
    let mut ps := #[]
    let mut variadic := false
    repeat
      if (← peek) == some .ellipsis then
        advance; variadic := true; break
      ps := ps.push (← typeName)
      if (← peek) == some (.punct ',') then advance else break
    expect (.punct ')')
    return (some ps.toList, variadic)

/-- An array bound expression: `+ -` over `* / %` over unary forms, all left-associative. -/
partial def boundExpr : P BoundExpr := do
  let mut a ← boundTerm
  repeat
    match ← peek with
    | some (.punct '+') => advance; a := .binary '+' a (← boundTerm)
    | some (.punct '-') => advance; a := .binary '-' a (← boundTerm)
    | _ => break
  return a

partial def boundTerm : P BoundExpr := do
  let mut a ← boundUnary
  repeat
    match ← peek with
    | some (.punct '*') => advance; a := .binary '*' a (← boundUnary)
    | some (.punct '/') => advance; a := .binary '/' a (← boundUnary)
    | some (.punct '%') => advance; a := .binary '%' a (← boundUnary)
    | _ => break
  return a

/-- A unary form. A parenthesis followed by a word other than `sizeof` opens a cast: a bound
names no object, and an identifier read as a type name fails to resolve. -/
partial def boundUnary : P BoundExpr := do
  match ← get with
  | .word "sizeof" :: .punct '(' :: rest =>
    set rest
    let t ← typeName
    expect (.punct ')')
    return .sizeofType t
  | .punct '&' :: rest => set rest; return .addrOf (← boundUnary)
  | .punct '-' :: rest => set rest; return .neg (← boundUnary)
  | .punct '(' :: .word w :: rest =>
    if w == "sizeof" then boundPostfix
    else
      set (.word w :: rest)
      let t ← typeName
      expect (.punct ')')
      return .cast t (← boundUnary)
  | _ => boundPostfix

/-- A primary form and the member accesses after it. -/
partial def boundPostfix : P BoundExpr := do
  let mut e ← match ← get with
    | .num n :: .word w :: rest =>
      if w.all ("uUlL".toList.contains ·) then set rest; pure (.num n w.toUpper)
      else throw s!"integer suffix {w}"
    | .num n :: rest => set rest; pure (.num n "")
    | .word w :: rest =>
      if boundKeywords.contains w then throw s!"array bound {w}" else set rest; pure (.var w)
    | .punct '(' :: rest =>
      set rest
      let e ← boundExpr
      expect (.punct ')')
      pure e
    | t => throw s!"array bound {repr t.head?} (variable-length arrays are not supported)"
  repeat
    match ← get with
    | .arrow :: .word m :: rest => set rest; e := .member e true m
    | .punct '.' :: .word m :: rest => set rest; e := .member e false m
    | _ => break
  return e

end

/-- Parse a type spelling (`qualType`). -/
def parse (s : String) : Except String TypeSpelling := do
  let toks ← tokenize s.toList #[] |>.mapError (s!"type {s}: " ++ ·)
  match typeName.run toks.toList with
  | .ok (t, []) => return t
  | .ok (_, rest) => throw s!"type {s}: unexpected {repr rest.head!}"
  | .error e => throw s!"type {s}: {e}"

end Silmaril.Clang.Type
