module

public import Silmaril.Data.Layout.Render.Defs

/-!
# C headers, a declaration subset: prototypes and typedefs

A small C header reader whose output is a value the kernel computes (`decide`), so that a
statement can say "this prototype is the one the header declares". It reads:

* **typedefs** of scalar and pointer types (`typedef unsigned int u32;`,
  `typedef unsigned char Bytef;`, `typedef Bytef *Bytef_p;`), resolved through earlier typedefs;
* **function prototypes** (`u32 gcd_u32(u32 a, u32 b);`, `int rt_failures(void);`,
  `int printf(const char *fmt, ...);`), parameters with or without names, array parameters
  adjusted to pointers (C17 6.7.6.3p7);
* the **preprocessor** lines a header needs to be read on its own: `#include "f"` of a file
  supplied with the header (`<…>` and missing files are errors), `#define NAME` and
  `#define NAME other_name` (identifier substitution; `NAME` may be used as a storage-class or
  `ZEXPORT`-style annotation that expands to nothing), `#ifndef`/`#ifdef`/`#else`/`#endif`
  on defined-ness, and `#undef`. Comments of both forms.

Everything else is **refused with a message**, not skipped: a redeclaration with a different
prototype or typedef, `#if` expressions, function-like
macros, struct/union/enum *definitions* (`struct s *` as an incomplete pointee is accepted),
bit-fields, function pointers, K&R declarations, function definitions, `static`/`inline`
functions. Qualifiers (`const`, `volatile`, `restrict`) are not part of `CTy` (they do not change
how a value is passed) and are kept beside it, by pointer level (`Header.quals?`,
`ProtoQuals`); a redeclaration must agree on them up to parameters' top-level qualifiers. Qualifiers inside a typedef
(`typedef const T *P;`) are not recorded (`CTy.typedef` carries none), so a redeclaration that
spells the same type once through such a typedef and once directly is refused: conservative. The reader is the bridge to a full C front end, not one: its
output type `Header` is what the full parser will also produce.

Types are `Silmaril.Data.Layout.CTy`; typedef names are kept (`CTy.typedef name ty`) so that
rendering gives back the spelling of the header, and the standard `<stdint.h>`/`<stddef.h>`
names (`uint32_t`, `size_t`, …) are built in. Sizes come later, from a data model; nothing here
depends on the host.
-/

@[expose] public section

namespace Silmaril.Data.Layout.Header

open Silmaril.Data.Layout

/-- A C function prototype: result, parameter types (after array-to-pointer adjustment), and
whether it ends in `...`. `f(void)` has no parameters. -/
structure CProto where
  ret : CTy
  params : List CTy
  variadic : Bool := false
  deriving DecidableEq, Repr

/-- The type qualifiers of one type as written, by level: index 0 the qualifiers among the
specifiers (of the base type), index `k` those after the `k`-th `*`; the last level qualifies
the type itself. Each level is a sublist of `["const", "volatile", "restrict"]` in that order.
An array parameter `T a[]` has one more (empty) level, for the pointer it is adjusted to. -/
abbrev Quals := List (List String)

/-- The qualifiers of a prototype's result and parameters (`CTy` has none: they do not change
how a value is passed, but they are part of the C type a header declares). -/
structure ProtoQuals where
  ret : Quals
  params : List Quals
  deriving DecidableEq, Repr

/-- The qualifiers that matter for compatibility of function types: a parameter's top-level
qualifiers do not (C17 6.7.6.3p15), so its last level is cleared. -/
def ProtoQuals.forCompat (q : ProtoQuals) : ProtoQuals :=
  { q with params := q.params.map fun l => l.dropLast ++ (if l.isEmpty then [] else [[]]) }

/-- What a header declares, in order of appearance. `quals` has, for each prototype, the
qualifiers the declaration wrote (of the first declaration). -/
structure Header where
  typedefs : List (String × CTy) := []
  protos : List (String × CProto) := []
  quals : List (String × ProtoQuals) := []
  deriving DecidableEq, Repr

/-- The prototype the header declares for `f` (the first one). -/
def Header.proto? (h : Header) (f : String) : Option CProto :=
  (h.protos.find? (·.1 == f)).map (·.2)

/-- The qualifiers the header writes in its prototype for `f` (the first one). -/
def Header.quals? (h : Header) (f : String) : Option ProtoQuals :=
  (h.quals.find? (·.1 == f)).map (·.2)

/-- The type a typedef name denotes (the first one). -/
def Header.typedef? (h : Header) (n : String) : Option CTy :=
  (h.typedefs.find? (·.1 == n)).map (·.2)

/-- The names a header declares a prototype for. -/
def Header.names (h : Header) : List String := h.protos.map (·.1)

/-- The C spelling of a prototype for `f`. -/
def CProto.render (p : CProto) (f : String) : String :=
  let ps := match p.params, p.variadic with
    | [], false => "void"
    | ps, v => ", ".intercalate (ps.map (·.declare "") ++ if v then ["..."] else [])
  p.ret.declare (f ++ "(" ++ ps ++ ")") ++ ";"

/-! ## Lexing -/

inductive Tok where
  | ident (s : String)
  | num (n : Nat)
  | punct (c : Char)
  | dots
  deriving DecidableEq, Repr

def isIdStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- The longest prefix whose characters satisfy `p`, and the rest. -/
def spanWhile (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs => if p c then let (a, b) := spanWhile p cs; (c :: a, b) else ([], c :: cs)

/-- Remove comments, keeping line structure (a block comment becomes its newlines). `mode`:
`0` code, `1` in a line comment, `2` in a block comment. -/
def strip : (mode : Nat) → List Char → Except String (List Char)
  | 2, [] => .error "unterminated block comment"
  | _, [] => .ok []
  | 0, '/' :: '/' :: cs => strip 1 cs
  | 0, '/' :: '*' :: cs => strip 2 cs
  | 0, c :: cs => (c :: ·) <$> strip 0 cs
  | 1, '\n' :: cs => ('\n' :: ·) <$> strip 0 cs
  | 1, _ :: cs => strip 1 cs
  | _, '*' :: '/' :: cs => (' ' :: ·) <$> strip 0 cs
  | _, '\n' :: cs => ('\n' :: ·) <$> strip 2 cs
  | _, _ :: cs => strip 2 cs

def stripComments (cs : List Char) : Except String (List Char) := strip 0 cs

def digits (cs : List Char) : Nat := cs.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0

/-- The tokens of one line (no preprocessor directive). Integer suffixes are dropped. -/
def lexLine : (fuel : Nat) → List Char → Except String (List Tok)
  | 0, _ => .error "lexer fuel"
  | _ + 1, [] => .ok []
  | f + 1, '.' :: '.' :: '.' :: cs => (.dots :: ·) <$> lexLine f cs
  | f + 1, c :: cs =>
    if c == ' ' || c == '\t' || c == '\r' || c == '\n' then lexLine f cs
    else if isIdStart c then
      let (w, r) := spanWhile isIdChar (c :: cs)
      (.ident (String.ofList w) :: ·) <$> lexLine f r
    else if c.isDigit then
      let (w, r) := spanWhile Char.isDigit (c :: cs)
      let r := (spanWhile (fun c => c == 'u' || c == 'U' || c == 'l' || c == 'L') r).2
      (.num (digits w) :: ·) <$> lexLine f r
    else if "(){}[];,*=".toList.contains c then (.punct c :: ·) <$> lexLine f cs
    else .error s!"unexpected character '{c}'"

/-- Split at newlines (`fuel` bounds the number of lines). -/
def lines : (fuel : Nat) → List Char → List (List Char)
  | 0, _ => []
  | _ + 1, [] => []
  | f + 1, cs => let (l, r) := spanWhile (· != '\n') cs; l :: lines f (r.drop 1)

/-! ## Preprocessing -/

/-- Preprocessor state: macros (`NAME` ↦ replacement, empty or one identifier) and the stack
of conditional branches (`true` = this branch is read). -/
structure PP where
  defs : List (String × Option String) := []
  conds : List Bool := []

def PP.active (s : PP) : Bool := s.conds.all id
def PP.defined (s : PP) (n : String) : Bool := s.defs.any (·.1 == n)

def dropWs (cs : List Char) : List Char := (spanWhile (fun c => c == ' ' || c == '\t') cs).2

/-- The word starting a directive's text, and the rest. -/
def word (cs : List Char) : String × List Char :=
  let (w, r) := spanWhile isIdChar (dropWs cs); (String.ofList w, dropWs r)

/-- Apply identifier macros to a token (one level; `#define A B` with `B` itself a macro is
refused when it is defined). -/
def PP.subst (s : PP) : Tok → List Tok
  | .ident n => match s.defs.find? (·.1 == n) with
    | some (_, none) => []
    | some (_, some m) => [.ident m]
    | none => [.ident n]
  | t => [t]

/-- Preprocess lines into tokens, with the supplied `files` for `#include "f"`; `depth`
bounds include nesting and `fuel` the number of lines read. -/
def pp (files : List (String × String)) : (fuel depth : Nat) → PP → List (List Char) →
    Except String (PP × List Tok)
  | 0, _, _, _ => .error "preprocessor fuel"
  | _ + 1, _, s, [] => .ok (s, [])
  | f + 1, depth, s, l :: ls =>
    match dropWs l with
    | '#' :: d => do
      let (s, ts) ← match directive s d with
        | .error e => .error e
        | .ok (.inl s) => pure (s, [])
        | .ok (.inr name) => match depth, files.find? (·.1 == name) with
          | 0, _ => .error "#include nesting too deep"
          | _, none => .error s!"#include \"{name}\": file not supplied"
          | n + 1, some (_, text) => do
            let cs ← stripComments text.toList
            pp files f n s (lines (cs.length + 1) cs)
      let (s, rest) ← pp files f depth s ls
      return (s, ts ++ rest)
    | l => do
      let ts ← if s.active then lexLine (l.length + 1) l else pure []
      let (s, rest) ← pp files f depth s ls
      return (s, ts.flatMap s.subst ++ rest)
where
  /-- One directive: the new state, or the name of a file to include. -/
  directive (s : PP) (d : List Char) : Except String (PP ⊕ String) :=
    let (w, r) := word d
    match w with
    | "endif" => match s.conds with
      | _ :: cs => .ok (.inl { s with conds := cs })
      | [] => .error "#endif without #if"
    | "else" => match s.conds with
      | c :: cs => .ok (.inl { s with conds := (!c) :: cs })
      | [] => .error "#else without #if"
    | "ifndef" => .ok (.inl { s with conds := (!(s.defined (word r).1)) :: s.conds })
    | "ifdef" => .ok (.inl { s with conds := s.defined (word r).1 :: s.conds })
    | "if" | "elif" => if s.active then .error "#if expressions are outside the header subset"
        else .ok (.inl { s with conds := false :: s.conds })
    | _ => if !s.active then .ok (.inl s) else match w with
      | "define" =>
        let (n, r) := spanWhile isIdChar (dropWs r)
        if r.head? == some '(' then .error s!"function-like macro {String.ofList n}"
        else
          let (m, r') := word r
          if !(dropWs r').isEmpty then
            .error s!"#define {String.ofList n}: only empty or one-identifier replacements"
          else if m != "" && s.defined m then .error s!"#define {String.ofList n} {m}: nested macro"
          else .ok (.inl { s with defs := (String.ofList n, if m == "" then none else some m) :: s.defs })
      | "undef" => let n := (word r).1; .ok (.inl { s with defs := s.defs.filter (·.1 != n) })
      | "include" => match dropWs r with
        | '"' :: q => .ok (.inr (String.ofList (spanWhile (· != '"') q).1))
        | _ => .error "#include <…>: system headers are not read; supply the declarations"
      | "pragma" => .ok (.inl s)
      | w => .error s!"#{w} is outside the header subset"

/-! ## Declarations -/

/-- The `<stdint.h>`/`<stddef.h>` names the reader knows without a typedef. -/
def builtin : String → Option CTy
  | "size_t" => some (.int .size .unsigned) | "ssize_t" => some (.int .size .signed)
  | "ptrdiff_t" => some (.int .ptrdiff .signed)
  | "intptr_t" => some (.int .intptr .signed) | "uintptr_t" => some (.int .intptr .unsigned)
  | "wchar_t" => some (.int .wchar .plain)
  | "int8_t" => some (.int (.exact 1) .signed) | "uint8_t" => some (.int (.exact 1) .unsigned)
  | "int16_t" => some (.int (.exact 2) .signed) | "uint16_t" => some (.int (.exact 2) .unsigned)
  | "int32_t" => some (.int (.exact 4) .signed) | "uint32_t" => some (.int (.exact 4) .unsigned)
  | "int64_t" => some (.int (.exact 8) .signed) | "uint64_t" => some (.int (.exact 8) .unsigned)
  | _ => none

def qualifiers : List String := ["const", "volatile", "restrict", "__restrict", "extern"]
def basicWords : List String :=
  ["void", "_Bool", "char", "short", "int", "long", "signed", "unsigned", "float", "double"]
def refused : List String :=
  ["static", "inline", "__inline", "register", "_Atomic", "__attribute__", "typeof", "auto"]

/-- The type named by basic specifier words (in any order, C17 6.7.2p2). -/
def classify (ws : List String) : Except String CTy :=
  let n (w : String) := ws.count w
  let sign : Sign := if n "unsigned" = 1 then .unsigned else if n "signed" = 1 then .signed else .plain
  let signs := n "unsigned" + n "signed"
  let only (allowed : List String) := ws.all allowed.contains
  if signs > 1 then .error "both signed and unsigned"
  else if ws = ["void"] then .ok .void
  else if ws = ["_Bool"] then .ok .bool
  else if ws = ["float"] then .ok (.float .float)
  else if ws = ["double"] then .ok (.float .double)
  else if only ["long", "double"] && n "long" = 1 && n "double" = 1 then .ok (.float .longDouble)
  else if n "char" = 1 && only ["char", "signed", "unsigned"] then .ok (.int .char sign)
  else
    let s : Sign := if sign == .unsigned then .unsigned else .signed
    if !only ["short", "int", "long", "signed", "unsigned"] || n "int" > 1 then
      .error s!"type specifiers {ws}"
    else if n "short" = 1 && n "long" = 0 then .ok (.int .short s)
    else if n "short" = 0 && n "long" = 0 && (n "int" = 1 || signs = 1) then .ok (.int .int s)
    else if n "short" = 0 && n "long" = 1 then .ok (.int .long s)
    else if n "short" = 0 && n "long" = 2 then .ok (.int .longLong s)
    else .error s!"type specifiers {ws}"

/-- A declaration's specifiers: the type they name and the remaining tokens. `struct T`,
`union T` and `enum T` name incomplete types (their definitions are refused). -/
def specifiers (h : Header) : (fuel : Nat) → List String → List Tok → Except String (CTy × List Tok)
  | 0, _, _ => .error "parser fuel"
  | f + 1, ws, ts => match ts with
    | .ident q :: r =>
      if qualifiers.contains q then specifiers h f ws r
      else if refused.contains q then .error s!"'{q}' is outside the header subset"
      else if basicWords.contains q then specifiers h f (ws ++ [q]) r
      else if q == "struct" || q == "union" || q == "enum" then
        if !ws.isEmpty then .error s!"{q} after {ws}" else
        match r with
        | .ident tag :: .punct '{' :: _ => .error s!"definition of {q} {tag} is outside the header subset"
        | .ident tag :: r =>
          let t : CTy := if q == "struct" then .struct tag else if q == "union" then .union tag
            else .enum tag none
          (fun (_, r) => (t, r)) <$> specifiers h f ["(tag)"] r
        | _ => .error s!"anonymous {q}"
      else if ws.isEmpty then
        match h.typedef? q, builtin q with
        | some t, _ => (fun (_, r) => (.typedef q t, r)) <$> specifiers h f ["(name)"] r
        | none, some t => (fun (_, r) => (.typedef q t, r)) <$> specifiers h f ["(name)"] r
        | none, none => .error s!"unknown type name '{q}'"
      else if ws == ["(tag)"] || ws == ["(name)"] then .ok (.void, ts)
      else (·, ts) <$> classify ws
    | _ =>
      if ws.isEmpty then .error "missing type specifier"
      else if ws == ["(tag)"] || ws == ["(name)"] then .ok (.void, ts)
      else (·, ts) <$> classify ws

/-- Pointer declarators `*` (with qualifiers after them). -/
def pointers : (fuel : Nat) → CTy → List Tok → CTy × List Tok
  | 0, t, ts => (t, ts)
  | f + 1, t, .punct '*' :: r => pointers f (.ptr t) r
  | f + 1, t, .ident q :: r => if qualifiers.contains q then pointers f t r else (t, .ident q :: r)
  | _, t, ts => (t, ts)

/-- The qualifier levels of a type's tokens (`Quals`): a qualifier word joins the current
level, `*` starts the next one. `__restrict` is `restrict`; `extern` is not a qualifier. -/
def qualLevels (ts : List Tok) : Quals :=
  let canon (l : List String) := ["const", "volatile", "restrict"].filter fun q =>
    l.contains q || (q == "restrict" && l.contains "__restrict")
  let rec go : List Tok → List String → Quals → Quals
    | [], cur, done => done ++ [canon cur]
    | .punct '*' :: r, cur, done => go r [] (done ++ [canon cur])
    | .ident q :: r, cur, done => go r (if qualifiers.contains q then q :: cur else cur) done
    | _ :: r, cur, done => go r cur done
  go ts [] []


def splitParams : List Tok → List (List Tok) → List Tok → List (List Tok)
  | [], acc, cur => acc ++ [cur]
  | .punct ',' :: r, acc, cur => splitParams r (acc ++ [cur]) []
  | t :: r, acc, cur => splitParams r acc (cur ++ [t])

/-- One parameter: specifiers, pointers, an optional name, optional `[n]` (adjusted to a
pointer). -/
def param (h : Header) (ts : List Tok) : Except String CTy := do
  let (t, r) ← specifiers h (ts.length + 2) [] ts
  let (t, r) := pointers (r.length + 1) t r
  let r := match r with | .ident _ :: r => r | r => r
  match r with
  | [] => if t == .void then .error "void parameter" else .ok t
  | [.punct '[', .punct ']'] | [.punct '[', .num _, .punct ']'] => .ok (.ptr t)
  | .punct '(' :: _ => .error "function-pointer parameters are outside the header subset"
  | _ => .error "parameter declarator"

/-- The qualifier levels of each parameter (as `params` reads them). -/
def paramQuals (ts : List Tok) : List Quals :=
  match ts with
  | [.ident "void"] => []
  | ts =>
    let ps := splitParams ts [] []
    let ps := match ps.getLast? with | some [.dots] => ps.dropLast | _ => ps
    ps.map fun p => if p.contains (.punct '[') then qualLevels p ++ [[]] else qualLevels p

def params (h : Header) (ts : List Tok) : Except String (List CTy × Bool) :=
  match ts with
  | [.ident "void"] => .ok ([], false)
  | [] => .error "K&R declaration f() (unspecified parameters) is outside the header subset"
  | ts =>
    let ps := splitParams ts [] []
    match ps.getLast? with
    | some [.dots] => (·, true) <$> traverse (param h) ps.dropLast
    | _ => (·, false) <$> traverse (param h) ps

/-- Add a typedef; a redefinition must name the same type (C11 6.7p3). -/
def Header.addTypedef (h : Header) (n : String) (t : CTy) : Except String Header :=
  match h.typedef? n with
  | some t' => if t' == t then .ok h else .error s!"typedef {n} redefined with a different type"
  | none => .ok { h with typedefs := h.typedefs ++ [(n, t)] }

/-- Add a prototype; a redeclaration must be the same prototype with the same qualifiers up to
parameters' top-level ones (refused otherwise, rather than keeping the first: compatible-type
rules beyond identity are not modelled). -/
def Header.addProto (h : Header) (f : String) (p : CProto) (q : ProtoQuals) : Except String Header :=
  match h.proto? f with
  | some p' =>
    if p' == p && (h.quals? f).map ProtoQuals.forCompat == some q.forCompat then .ok h
    else .error s!"{f} redeclared with a different prototype"
  | none => .ok { h with protos := h.protos ++ [(f, p)], quals := h.quals ++ [(f, q)] }

/-- One top-level declaration (the tokens before its `;`). -/
def decl (h : Header) (ts : List Tok) : Except String Header :=
  match ts with
  | .ident "typedef" :: r => do
    let (t, r) ← specifiers h (r.length + 2) [] r
    let (t, r) := pointers (r.length + 1) t r
    match r with
    | [.ident n] => h.addTypedef n t
    | [.ident n, .punct '[', .num k, .punct ']'] => h.addTypedef n (.array t k)
    | _ => .error "typedef declarator"
  | ts => do
    let (t, r) ← specifiers h (ts.length + 2) [] ts
    let (t, r) := pointers (r.length + 1) t r
    match r with
    | .ident f :: .punct '(' :: r =>
      match r.getLast? with
      | some (.punct ')') =>
        let inner := r.dropLast
        if inner.contains (.punct '(') then .error s!"{f}: nested declarators are outside the header subset"
        else
          let (ps, v) ← params h inner
          h.addProto f ⟨t, ps, v⟩ ⟨qualLevels (ts.take (ts.length - (r.length + 2))), paramQuals inner⟩
      | _ => .error s!"{f}: expected ')' at the end of the declaration"
    | [.ident n] => .error s!"object declaration '{n}' is outside the header subset"
    | _ => .error "declaration"

/-- Split tokens at `;`; tokens after the last `;` are an error. -/
def splitDecls : List Tok → List Tok → Except String (List (List Tok))
  | [], [] => .ok []
  | [], _ => .error "declaration without ';'"
  | .punct ';' :: r, cur => (cur :: ·) <$> splitDecls r []
  | .punct '{' :: _, _ => .error "'{' (a definition) is outside the header subset"
  | t :: r, cur => splitDecls r (cur ++ [t])

/-- **Read a header** `root` among the supplied `files` (name, text). -/
def read (files : List (String × String)) (root : String) : Except String Header := do
  let some (_, text) := files.find? (·.1 == root) | .error s!"{root}: file not supplied"
  let cs ← stripComments text.toList
  let (s, ts) ← pp files 100000 8 {} (lines (cs.length + 1) cs)
  unless s.conds.isEmpty do .error "unterminated #if"
  let ds ← splitDecls ts []
  ds.foldlM decl {}

end Silmaril.Data.Layout.Header

end
