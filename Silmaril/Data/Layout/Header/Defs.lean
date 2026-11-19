module

public import Silmaril.Data.Layout.Render.Defs

/-!
# C headers, a declaration subset: prototypes, typedefs and tag definitions

A small C header reader whose output is a value the kernel computes (`decide`), so that a
statement can say "this prototype is the one the header declares" and "this is the struct the
header defines". It reads:

* **typedefs** of scalar, pointer and tag types (`typedef unsigned int u32;`,
  `typedef unsigned char Bytef;`, `typedef Bytef *Bytef_p;`, `typedef struct T T;`), resolved
  through earlier typedefs;
* **function prototypes** (`u32 gcd_u32(u32 a, u32 b);`, `int rt_failures(void);`,
  `int printf(const char *fmt, ...);`), parameters with or without names, array parameters
  adjusted to pointers (C17 6.7.6.3p7);
* **struct and union definitions** with a tag (`struct T {…};`, `typedef struct T {…} T;`, and
  a definition at the head of a prototype's or member's specifiers), into `Header.decls`
  (`Header.env`, an `Env` for the layout API) in the order they are completed, a definition
  nested in a member first. Members: `,`-separated declarators with pointers, arrays of
  integer-literal size (`int a[2][3]`), bit-fields (`unsigned f : 3`, unnamed `int : 0`) of
  integer, `_Bool` and enum types, and `_Alignas(n)` (`Field.alignas`). Member types must be
  complete (a by-value struct, union or enum must be defined before);
* **enum definitions** with a tag, into `Header.enums`: enumerators with implicit (previous plus
  one, from 0) or explicit values (a decimal or hexadecimal literal, possibly negated) within
  `int`; a member of enum type has the data model's `enumRepr`;
* the **preprocessor** lines a header needs to be read on its own: `#include "f"` of a file
  supplied with the header (`<…>` and missing files are errors), `#define NAME` and
  `#define NAME other_name` (identifier substitution; `NAME` may be used as a storage-class or
  `ZEXPORT`-style annotation that expands to nothing), `#ifndef`/`#ifdef`/`#else`/`#endif`
  on defined-ness, `#undef` and `#pragma once`. Comments of both forms.

Everything else is **refused with a message**, not skipped: a redeclaration with a different
prototype or typedef, a redefinition of a tag with different members or enumerators or as
another kind (an identical redefinition is accepted, as C23 allows), a member or enumerator
declared twice, `#if` expressions, function-like macros, `#pragma` other than `once` (`pack`
changes layouts), definitions without a tag (`typedef struct {…} T;`, anonymous members,
`enum {…};`), flexible and zero-length array members, array sizes that are not literals,
`_Alignas(type)` and `_Alignas` on a bit-field, named zero-width bit-fields, bit-fields of other
types, enums with a fixed underlying type, enumerator values that are not literals or not in
`int`, definitions inside a parameter, function pointers, K&R declarations, function
definitions, object declarations, forward declarations (`struct s;`; `struct s *` as an
incomplete pointee is accepted), `static`/`inline` functions. Qualifiers (`const`, `volatile`,
`restrict`) are not part of `CTy` (they do not change how a value is passed) and are kept beside
it, by pointer level (`Header.quals?`, `ProtoQuals`), for prototypes only (members' qualifiers
are not recorded); a redeclaration must agree on them up to parameters' top-level qualifiers.
Qualifiers inside a typedef (`typedef const T *P;`) are not recorded (`CTy.typedef` carries
none), so a redeclaration that spells the same type once through such a typedef and once
directly is refused: conservative. The reader is the bridge to a full C front end, not one: its
output type `Header` is what the full parser will also produce.

Types are `Silmaril.Data.Layout.CTy`; typedef names are kept (`CTy.typedef name ty`) so that
rendering gives back the spelling of the header, and the standard `<stdint.h>`/`<stddef.h>`
names (`uint32_t`, `size_t`, …) are built in. Sizes come later, from a data model
(`layoutTy`/`tagLayout` without bit-fields, `Silmaril.Data.Layout.Bitfield` with them); nothing
here depends on the host.
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
  /-- The struct and union definitions, in the order they are completed (a nested definition
  before the one containing it). -/
  decls : Env := []
  /-- The enum definitions: tag and enumerators with their values, in order. -/
  enums : List (String × List (String × Int)) := []
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

/-- The tag definitions of the header, for layouts (`layoutTy`, `declLayout`, `bitLayout`). -/
def Header.env (h : Header) : Env := h.decls

/-- The enumerators the header defines for enum `tag`. -/
def Header.enum? (h : Header) (tag : String) : Option (List (String × Int)) :=
  (h.enums.find? (·.1 == tag)).map (·.2)

/-- Every enumerator of the header, with its value. -/
def Header.enumerators (h : Header) : List (String × Int) := h.enums.flatMap (·.2)

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

def isHex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def hexDigits (cs : List Char) : Nat :=
  cs.foldl (fun n c => 16 * n + (if c.isDigit then c.toNat - '0'.toNat
    else if 'a' ≤ c then c.toNat - 'a'.toNat + 10 else c.toNat - 'A'.toNat + 10)) 0

/-- The tokens of one line (no preprocessor directive). Integer literals are decimal or
hexadecimal (`0x…`); their suffixes are dropped. -/
def lexLine : (fuel : Nat) → List Char → Except String (List Tok)
  | 0, _ => .error "lexer fuel"
  | _ + 1, [] => .ok []
  | f + 1, '.' :: '.' :: '.' :: cs => (.dots :: ·) <$> lexLine f cs
  | f + 1, c :: cs =>
    if c == ' ' || c == '\t' || c == '\r' || c == '\n' then lexLine f cs
    else if isIdStart c then
      let (w, r) := spanWhile isIdChar (c :: cs)
      (.ident (String.ofList w) :: ·) <$> lexLine f r
    else if c == '0' && (cs.head? == some 'x' || cs.head? == some 'X') then
      let (w, r) := spanWhile isHex (cs.drop 1)
      let r := (spanWhile (fun c => c == 'u' || c == 'U' || c == 'l' || c == 'L') r).2
      if w.isEmpty then .error "hexadecimal literal without digits"
      else (.num (hexDigits w) :: ·) <$> lexLine f r
    else if c.isDigit then
      let (w, r) := spanWhile Char.isDigit (c :: cs)
      let r := (spanWhile (fun c => c == 'u' || c == 'U' || c == 'l' || c == 'L') r).2
      (.num (digits w) :: ·) <$> lexLine f r
    else if "(){}[];,*=:-".toList.contains c then (.punct c :: ·) <$> lexLine f cs
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
      | "pragma" => if (word r).1 == "once" then .ok (.inl s)
        else .error "#pragma other than `once` is outside the header subset (`pack` and others change layouts)"
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
  ["static", "inline", "__inline", "register", "_Atomic", "__attribute__", "typeof", "auto",
    "_Alignas", "alignas", "__declspec", "typedef"]

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
  | none =>
    if h.enumerators.any (·.1 == n) then .error s!"typedef {n} redeclares an enumerator"
    else .ok { h with typedefs := h.typedefs ++ [(n, t)] }

/-- Add a prototype; a redeclaration must be the same prototype with the same qualifiers up to
parameters' top-level ones (refused otherwise, rather than keeping the first: compatible-type
rules beyond identity are not modelled). -/
def Header.addProto (h : Header) (f : String) (p : CProto) (q : ProtoQuals) : Except String Header :=
  match h.proto? f with
  | some p' =>
    if p' == p && (h.quals? f).map ProtoQuals.forCompat == some q.forCompat then .ok h
    else .error s!"{f} redeclared with a different prototype"
  | none =>
    if h.enumerators.any (·.1 == f) then .error s!"{f} redeclares an enumerator"
    else .ok { h with protos := h.protos ++ [(f, p)], quals := h.quals ++ [(f, q)] }

/-! ## Tag definitions -/

/-- Whether a struct, union or enum with this tag is defined (one tag name space, C17 6.2.3). -/
def Header.tagDefined (h : Header) (tag : String) : Bool :=
  h.decls.any (·.tag == tag) || h.enums.any (·.1 == tag)

/-- A member type is complete (C17 6.7.2.1p3): an object type whose structs, unions and enums
(through typedefs and arrays) are defined, and arrays of a nonzero size. Pointers are complete
whatever they point to. -/
def Header.complete (h : Header) : CTy → Bool
  | .void => false
  | .array t n => n != 0 && h.complete t
  | .typedef _ t => h.complete t
  | .struct tag => (h.env.find? .struct tag).isSome
  | .union tag => (h.env.find? .union tag).isSome
  | .enum tag _ => (h.enum? tag).isSome
  | _ => true

/-- No string twice. -/
def dupFree : List String → Bool
  | [] => true
  | a :: as => !as.contains a && dupFree as

/-- Add a struct or union definition. A redefinition must be identical (as C23 6.7.2.3p1 allows;
C17 refuses any redefinition in one scope); a tag defined as another kind is refused. -/
def Header.addDecl (h : Header) (d : Decl) : Except String Header :=
  let kw := match d.kind with | .struct => "struct" | .union => "union"
  if !dupFree ((d.fields.map (·.name)).filter (· != "")) then
    .error s!"{kw} {d.tag}: a member declared twice"
  else match h.env.find? d.kind d.tag with
  | some d' => if d' == d then .ok h else .error s!"{kw} {d.tag} redefined with different members"
  | none =>
    if h.tagDefined d.tag then .error s!"tag {d.tag} is already defined as another kind"
    else .ok { h with decls := h.decls ++ [d] }

/-- Add an enum definition. A redefinition must be identical (as for structs); an enumerator
may not redeclare an enumerator, typedef name or function of the header. -/
def Header.addEnum (h : Header) (tag : String) (cs : List (String × Int)) : Except String Header :=
  match h.enum? tag with
  | some cs' => if cs' == cs then .ok h else .error s!"enum {tag} redefined with different enumerators"
  | none =>
    if h.tagDefined tag then .error s!"tag {tag} is already defined as another kind"
    else if !dupFree (cs.map (·.1)) then .error s!"enum {tag}: an enumerator declared twice"
    else match cs.find? (fun c => h.enumerators.any (·.1 == c.1) || (h.typedef? c.1).isSome ||
        (h.proto? c.1).isSome) with
      | some (c, _) => .error s!"enumerator {c} redeclares an identifier"
      | none => .ok { h with enums := h.enums ++ [(tag, cs)] }

/-- The largest `int` (4 bytes in every data model here). -/
def intMax : Int := 2147483647

/-- Enumerators (the items between `,`): `NAME` (the previous value plus one, from 0) or
`NAME = n` with an integer literal `n`, possibly negated; a trailing `,` is allowed. Values must
be representable as `int` (C17 6.7.2.2p2), so the enum's type is the data model's `enumRepr`. -/
def enumConsts : (next : Int) → List (List Tok) → Except String (List (String × Int))
  | _, [] => .ok []
  | _, [[]] => .ok []
  | n, it :: r => do
    let (c, v) ← match it with
      | [.ident c] => pure (c, n)
      | [.ident c, .punct '=', .num k] => pure (c, (k : Int))
      | [.ident c, .punct '=', .punct '-', .num k] => pure (c, -(k : Int))
      | _ => .error "enumerator: only NAME or NAME = integer literal is in the header subset"
    if v < -intMax - 1 || v > intMax then
      .error s!"enumerator {c}: value outside int (C17 6.7.2.2p2)"
    ((c, v) :: ·) <$> enumConsts (v + 1) r

/-- `_Alignas(n)` among a member's specifiers: the alignment (the strictest if repeated;
`_Alignas(0)` has no effect, C17 6.7.5p6) and the other tokens. `_Alignas(type)` stays, and
`specifiers` refuses it. -/
def alignasOf : List Tok → Option Nat × List Tok
  | .ident "_Alignas" :: .punct '(' :: .num n :: .punct ')' :: r =>
    let (a, r) := alignasOf r
    (if n = 0 then a else some (max n (a.getD 0)), r)
  | t :: r => let (a, r) := alignasOf r; (a, t :: r)
  | [] => (none, [])

/-- Array declarators `[n]…` with integer-literal sizes; flexible (`[]`) and zero-length
arrays are refused. -/
def arrayDims : List Tok → Except String (List Nat × List Tok)
  | .punct '[' :: .num n :: .punct ']' :: r =>
    if n = 0 then .error "zero-length arrays are outside the header subset"
    else (fun (ds, r) => (n :: ds, r)) <$> arrayDims r
  | .punct '[' :: .punct ']' :: _ => .error "flexible array members are outside the header subset"
  | .punct '[' :: _ => .error "array size: only an integer literal is in the header subset"
  | r => .ok ([], r)

/-- A type a bit-field may have: an integer, `_Bool` or enum (through typedefs). -/
def bitfieldTy (t : CTy) : Bool :=
  match t.strip with
  | .int .. | .bool | .enum .. => true
  | _ => false

/-- One member declarator of base type `t`, with the member's `_Alignas`: pointers, a name,
array sizes and a bit-field width; `: w` alone is an unnamed bit-field (name `""`). -/
def memberDecl (h : Header) (t : CTy) (al : Option Nat) (d : List Tok) : Except String Field :=
  let (t', d) := pointers (d.length + 1) t d
  match d with
  | [.punct ':', .num w] =>
    if t' != t || !bitfieldTy t then .error "bit-field: only integer, _Bool and enum types"
    else if al.isSome then .error "bit-field: _Alignas on a bit-field (C17 6.7.5p2)"
    else .ok ⟨"", t, none, some w⟩
  | .ident n :: r => do
    let (ds, r) ← arrayDims r
    let ty := ds.foldr (fun k e => CTy.array e k) t'
    if !h.complete ty then .error s!"member {n}: incomplete or void type"
    match r with
    | [] => .ok ⟨n, ty, al, none⟩
    | [.punct ':', .num w] =>
      if ty != t || !bitfieldTy t then
        .error s!"bit-field {n}: only integer, _Bool and enum types"
      else if al.isSome then .error s!"bit-field {n}: _Alignas on a bit-field (C17 6.7.5p2)"
      else if w = 0 then .error s!"bit-field {n}: a named bit-field of width 0 (C17 6.7.2.1p4)"
      else .ok ⟨n, t, none, some w⟩
    | _ => .error s!"member {n}: declarator outside the header subset"
  | .punct '(' :: _ =>
    .error "function-pointer members (parenthesized declarators) are outside the header subset"
  | _ => .error "member declarator"

/-- One member declaration (the tokens before its `;`), after the definitions it contains
(`dfn`): `_Alignas(n)`, specifiers and `,`-separated declarators. A declaration without a
declarator (an anonymous struct or union member) is refused. -/
def member (dfn : Header → List Tok → Except String (Header × List Tok × Bool)) (h : Header)
    (ts : List Tok) : Except String (Header × List Field) := do
  let (al, ts) := alignasOf ts
  let (h, ts, _) ← dfn h ts
  let (t, r) ← specifiers h (ts.length + 2) [] ts
  if r.isEmpty then
    .error "member declaration without a declarator (anonymous members are outside the header subset)"
  let fs ← traverse (memberDecl h t al) (splitParams r [] [])
  return (h, fs)

/-- The member declarations of a body, in order. -/
def members (dfn : Header → List Tok → Except String (Header × List Tok × Bool)) (h : Header) :
    List (List Tok) → Except String (Header × List Field)
  | [] => .ok (h, [])
  | m :: ms => do
    let (h, fs) ← member dfn h m
    let (h, gs) ← members dfn h ms
    return (h, fs ++ gs)

/-- The tokens before the first `{`, and the rest. -/
def beforeBrace : List Tok → List Tok × List Tok
  | [] => ([], [])
  | .punct '{' :: r => ([], .punct '{' :: r)
  | t :: r => let (a, b) := beforeBrace r; (t :: a, b)

/-- The tokens up to the `}` closing an open `{` (`depth` more are open inside), and the
tokens after it. -/
def closeBrace : (depth : Nat) → List Tok → List Tok → Except String (List Tok × List Tok)
  | _, [], _ => .error "'{' without '}'"
  | 0, .punct '}' :: r, acc => .ok (acc, r)
  | d + 1, .punct '}' :: r, acc => closeBrace d r (acc ++ [.punct '}'])
  | d, .punct '{' :: r, acc => closeBrace (d + 1) r (acc ++ [.punct '{'])
  | d, t :: r, acc => closeBrace d r (acc ++ [t])

/-- Split tokens at `;` outside braces; tokens after the last `;` are an error, and so is a
`{` after `)` (a function definition). -/
def splitDecls : (depth : Nat) → List Tok → List Tok → Except String (List (List Tok))
  | 0, [], [] => .ok []
  | 0, [], _ => .error "declaration without ';'"
  | _ + 1, [], _ => .error "'{' without '}'"
  | 0, .punct ';' :: r, cur => (cur :: ·) <$> splitDecls 0 r []
  | d, .punct '{' :: r, cur =>
    if cur.getLast? == some (.punct ')') then
      .error "function definitions are outside the header subset"
    else splitDecls (d + 1) r (cur ++ [.punct '{'])
  | 0, .punct '}' :: _, _ => .error "'}' without '{'"
  | d + 1, .punct '}' :: r, cur => splitDecls d r (cur ++ [.punct '}'])
  | d, t :: r, cur => splitDecls d r (cur ++ [t])

/-- The message for a `{` that does not open a supported definition; `pre` is what precedes it. -/
def braceError (pre : List Tok) : String :=
  match pre.reverse with
  | .ident kw :: _ =>
    if ["struct", "union", "enum"].contains kw then
      s!"anonymous {kw} definitions (without a tag) are outside the header subset"
    else if pre.contains (.punct ':') then
      "enums with a fixed underlying type are outside the header subset"
    else "'{' outside a struct, union or enum definition is outside the header subset"
  | _ => "'{' outside a struct, union or enum definition is outside the header subset"

/-- The tag definition among a declaration's specifiers, if any (`struct T {…}`,
`union T {…}`, `enum T {…}`): the header with it (and the definitions nested in its members)
added, the declaration's tokens with the body removed (`struct T`), and whether there was one.
At most one per declaration; definitions without a tag, inside a declarator (a parameter), and
enums with a fixed underlying type are refused. `fuel` bounds the nesting. -/
def defn : (fuel : Nat) → Header → List Tok → Except String (Header × List Tok × Bool)
  | 0, _, _ => .error "parser fuel"
  | f + 1, h, ts =>
    let (pre, post) := beforeBrace ts
    match post with
    | [] => .ok (h, ts, false)
    | _ :: inner =>
      if pre.contains (.punct '(') then
        .error "a definition inside a declarator is outside the header subset"
      else match pre.reverse with
      | .ident tag :: .ident kw :: _ =>
        if kw == "struct" || kw == "union" then do
          let (body, after) ← closeBrace 0 inner []
          if after.contains (.punct '{') then
            .error "two definitions in one declaration are outside the header subset"
          if body.isEmpty then .error s!"{kw} {tag} without members"
          let ms ← splitDecls 0 body []
          let (h, fs) ← members (fun h ts => defn f h ts) h ms
          let h ← h.addDecl ⟨if kw == "struct" then .struct else .union, tag, fs⟩
          return (h, pre ++ after, true)
        else if kw == "enum" then do
          let (body, after) ← closeBrace 0 inner []
          if after.contains (.punct '{') then
            .error "two definitions in one declaration are outside the header subset"
          if body.isEmpty then .error s!"enum {tag} without enumerators"
          let cs ← enumConsts 0 (splitParams body [] [])
          let h ← h.addEnum tag cs
          return (h, pre ++ after, true)
        else .error (braceError pre)
      | _ => .error (braceError pre)

/-! ## Top-level declarations -/

/-- One top-level declaration without a tag definition: a typedef or a prototype. -/
def declBody (h : Header) (ts : List Tok) : Except String Header :=
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

/-- One top-level declaration (the tokens before its `;`): its tag definition, if any, then
the typedef or prototype it declares; `struct T {…};` declares only the tag. -/
def decl (h : Header) (ts : List Tok) : Except String Header := do
  let (h, ts, defined) ← defn (ts.length + 1) h ts
  match defined, ts with
  | true, [.ident _, .ident _] => .ok h
  | _, ts => declBody h ts

/-- **Read a header** `root` among the supplied `files` (name, text). -/
def read (files : List (String × String)) (root : String) : Except String Header := do
  let some (_, text) := files.find? (·.1 == root) | .error s!"{root}: file not supplied"
  let cs ← stripComments text.toList
  let (s, ts) ← pp files 100000 8 {} (lines (cs.length + 1) cs)
  unless s.conds.isEmpty do .error "unterminated #if"
  let ds ← splitDecls 0 ts []
  ds.foldlM decl {}

end Silmaril.Data.Layout.Header

end
