module

public import Silmaril.Data.Layout.Header.Defs
public import Silmaril.Data.Layout.Render.Defs
public import Silmaril.Compiler.Clang.TotalJson.Defs
public import Silmaril.Formats.Json.Chars.Defs

/-!
# C headers from clang: a provenance-tagged normalized import

The second route from a C header to the declarations it introduces, alongside the subset
reader `Header.read`. Here the header is read by **clang**: a pinned artifact is the output of
`clang -Xclang -ast-dump=json -fsyntax-only` (a pinned clang, in a container pinned by digest,
with a recorded command) filtered to the top-level declarations of the header's own files and
projected to the keys read here (`examples/headers/recipe.sh` and its `clang/filter.py`, which
reproduce the bytes with `--check`). This module
**normalizes that tool output**; it does not assume that clang is correct. The JSON is a
pinned artifact, the decoder (`Compiler.Clang.TotalJson`) is fail-closed, and every step from
the bytes to an `Entry` is a function the kernel evaluates.

* `Imported`: the header's provenance (`Provenance`: the image, the clang version, the exact
  command with its target triple, `-std`, `-D` macros and include paths, the SHA-256 of every
  input file and of the JSON, the filter) and one `Entry` per top-level declaration, in order.
* `Entry`: the name, the kind (`DeclKind`), the source location (file and line, as clang
  prints them), whether clang made the declaration implicitly (a builtin's declaration), and
  what the import reads of it (`Body`):
  - a function (`Fn`): its `CProto` when the subset `CProto` expresses (else the reason it
    cannot, as `Got.unsupported`), variadic, the **calling convention** of its type (`CallConv`:
    the default C convention, `ms_abi`, `sysv_abi`, `regcall`, …), its **attributes** as data
    (`Attr`: noreturn, nonnull, format, deprecated, visibility, …), the symbol clang gives it
    and the **asm label** that renames it (`AsmLabelAttr`, glibc's `__REDIRECT`), its storage
    class, `inline`, and whether it is a definition;
  - a typedef and its `CTy`; a struct, union or enum, defined or only declared; a variable and
    its type;
  - anything else, kept with `Body.unsupported` and the reason. **No declaration is dropped**:
    a top-level node the strict decoder refuses becomes an entry with the decoder's message.
* `Imported.header`: the subset reader's `Header` of the import (its typedefs, and the first
  prototype of each external, explicitly declared function), the value both routes are
  compared on (`compare`).

Types are read from clang's printed types (`qualType`), with the typedef names of the import
kept (`CTy.typedef`) as the subset reader keeps them. A name the import does not declare (a
system typedef such as `size_t`) is read from clang's `desugaredQualType`. Parameters are read
from the `ParmVarDecl` children (as written, after array-to-pointer adjustment), the result and
the convention from the function type. Calling-convention attributes are part of the function
type in clang, so they are read from its spelling; `sysv_abi` on an x86-64 System V target is
the default convention (its desugared type has no attribute), and the import keeps the spelling.
-/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Import

open Silmaril.Data.Layout
open Silmaril.Formats
open Silmaril.Compiler.Clang

/-! ## The normalized header -/

/-- A value the import read, or the reason it could not. -/
inductive Got (α : Type) where
  | ok (a : α)
  | unsupported (why : String)
  deriving DecidableEq, Repr

/-- Where a declaration is written: the file as clang prints it, and the line. For a
declaration written through a macro, the place of the expansion. -/
structure SrcLoc where
  file : String
  line : Nat
  deriving DecidableEq, Repr

/-- The calling convention of a function type. -/
inductive CallConv where
  /-- The target's default C convention (no convention attribute). -/
  | c
  | msAbi
  | sysvAbi
  | regcall
  | vectorcall
  /-- Another convention attribute, by its spelling (`preserve_most`, `stdcall`, …). -/
  | other (spelling : String)
  deriving DecidableEq, Repr

/-- An attribute of a declaration, kept as data. The arguments of `format` and `nonnull` are
not in clang's JSON. -/
inductive Attr where
  /-- `__attribute__((noreturn))` (in the function type) or `_Noreturn`. -/
  | noreturn
  | nonnull
  | format
  | deprecated
  | visibility (v : String)
  | asmLabel
  | pure
  | const
  | nothrow
  | leaf
  | builtin
  | restrict
  | warnUnusedResult
  | allocSize
  | aligned
  | weak
  | alias
  | section
  | used
  | unused
  | cold
  | returnsTwice
  /-- Any other attribute: its clang node kind, or `type attribute <spelling>`. -/
  | other (kind : String)
  deriving DecidableEq, Repr

/-- The kind of a top-level declaration. -/
inductive DeclKind where
  | function
  | typedef
  | struct
  | union
  | enum
  | variable
  /-- Another declaration: its clang node kind. -/
  | other (clangKind : String)
  deriving DecidableEq, Repr

/-- What the import reads of a function declaration. -/
structure Fn where
  proto : Got CProto
  /-- The qualifiers of the result and parameters as clang prints them, if the function type
  reads. -/
  quals : Option ProtoQuals
  variadic : Bool
  cc : CallConv
  attrs : List Attr
  /-- The symbol clang gives the declaration (`mangledName`): its name, or its asm label. -/
  symbol : String
  /-- The symbol an `AsmLabelAttr` gives the declaration in place of its name. -/
  asmLabel : Option String
  /-- `extern`, `static`, or none. -/
  storage : Option String
  inline : Bool
  /-- The declaration has a body. -/
  definition : Bool
  deriving DecidableEq, Repr

/-- What the import reads of a declaration. -/
inductive Body where
  | function (f : Fn)
  | typedef (ty : Got CTy)
  /-- A struct, union or enum: a definition or only a declaration. -/
  | tag (definition : Bool)
  | variable (ty : Got CTy) (storage : Option String)
  /-- A declaration the import does not read, with the reason. -/
  | unsupported (why : String)
  deriving DecidableEq, Repr

/-- One top-level declaration. `name` is `""` for an anonymous struct, union or enum. -/
structure Entry where
  name : String
  kind : DeclKind
  loc : Option SrcLoc
  /-- Clang made the declaration itself (`isImplicit`: a library builtin's declaration). -/
  implicit : Bool
  body : Body
  deriving DecidableEq, Repr

/-- **The provenance of a pinned clang JSON AST**, as `examples/headers/recipe.sh` records it in
the artifact's `.prov` file. -/
structure Provenance where
  artifact : String := ""
  /-- The container image, by digest. -/
  image : String := ""
  /-- `clang --version`'s first line. -/
  clang : String := ""
  target : String := ""
  std : String := ""
  /-- The directory clang ran in, relative to the mounted input. -/
  cwd : String := ""
  /-- The exact clang command. -/
  command : String := ""
  defines : List String := []
  includes : List String := []
  /-- The filter command (`examples/headers/clang/filter.py`) and its SHA-256. -/
  filter : String := ""
  filterSha256 : String := ""
  /-- The release archive the inputs come from, with its SHA-256 and URL. -/
  source : Option String := none
  /-- Each input file kept by the filter, as clang names it, with its SHA-256. -/
  inputs : List (String × String) := []
  jsonSha256 : String := ""
  jsonBytes : Nat := 0
  deriving DecidableEq, Repr

/-- **A header, as clang reads it**: the provenance, and every top-level declaration. `error`
is the reason the document itself could not be read (then there are no entries). -/
structure Imported where
  provenance : Provenance
  entries : List Entry
  error : Option String := none
  deriving DecidableEq, Repr

/-! ## Clang's printed types -/

/-- Tokens of a type as clang prints it. -/
inductive TTok where
  | ident (s : String)
  | num (n : Nat)
  | punct (c : Char)
  deriving DecidableEq, Repr

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- The word read so far (reversed), as a token. -/
def flushWord : List Char → List TTok → List TTok
  | [], ts => ts
  | w, ts => match w.reverse with
    | c :: cs =>
      (if c.isDigit then .num (digits (c :: cs)) else .ident (String.ofList (c :: cs))) :: ts
    | [] => ts

/-- Tokenize a printed type; `cur` is the word being read, reversed. -/
def tlex : List Char → List Char → List TTok
  | [], cur => flushWord cur []
  | c :: cs, cur =>
    if isWordChar c then tlex cs (c :: cur)
    else flushWord cur (if c == ' ' then tlex cs [] else .punct c :: tlex cs [])

def toks (s : String) : List TTok := tlex s.toList []

/-- The type qualifiers clang prints. They are not part of `CTy` (they do not change how a value
is passed); a prototype's are kept beside it by pointer level (`qualLevelsT`, `Fn.quals`), as the
subset reader keeps them. -/
def qualWords : List String := ["const", "volatile", "restrict", "__restrict"]

/-- The type named by clang's canonical spelling of a builtin type. -/
def builtinTy : List String → Option CTy
  | ["void"] => some .void
  | ["_Bool"] => some .bool
  | ["char"] => some (.int .char .plain)
  | ["signed", "char"] => some (.int .char .signed)
  | ["unsigned", "char"] => some (.int .char .unsigned)
  | ["short"] => some (.int .short .signed)
  | ["unsigned", "short"] => some (.int .short .unsigned)
  | ["int"] => some (.int .int .signed)
  | ["unsigned", "int"] => some (.int .int .unsigned)
  | ["long"] => some (.int .long .signed)
  | ["unsigned", "long"] => some (.int .long .unsigned)
  | ["long", "long"] => some (.int .longLong .signed)
  | ["unsigned", "long", "long"] => some (.int .longLong .unsigned)
  | ["__int128"] => some (.int .int128 .signed)
  | ["unsigned", "__int128"] => some (.int .int128 .unsigned)
  | ["float"] => some (.float .float)
  | ["double"] => some (.float .double)
  | ["long", "double"] => some (.float .longDouble)
  | ["_Float128"] => some (.float .float128)
  | ["__float128"] => some (.float .float128)
  | _ => none

/-- Typedef names the import has read, each with its type or why it has none. -/
abbrev TyEnv := List (String × Got CTy)

/-- The leading words of a printed type and the rest. -/
def specWords : List TTok → List String × List TTok
  | .ident w :: ts => let (ws, r) := specWords ts; (w :: ws, r)
  | ts => ([], ts)

/-- The base type named by the specifier words (qualifiers dropped). -/
def baseTy (env : TyEnv) (ws : List String) : Except String CTy :=
  match ws.filter (!qualWords.contains ·) with
  | ["struct", t] => .ok (.struct t)
  | ["union", t] => .ok (.union t)
  | ["enum", t] => .ok (.enum t none)
  | ["_Atomic"] => .error "_Atomic types are outside CTy"
  | [n] => match builtinTy [n] with
    | some t => .ok t
    | none => match env.find? (·.1 == n) with
      | some (_, .ok t) => .ok (.typedef n t)
      | some (_, .unsupported why) => .error ("typedef " ++ n ++ ": " ++ why)
      | none => .error ("unknown type name " ++ n)
  | ws => match builtinTy ws with
    | some t => .ok t
    | none => .error ("type specifiers " ++ " ".intercalate ws)

/-- Pointer declarators (with the qualifiers after them), then array bounds. -/
def declarator : CTy → List TTok → Except String CTy
  | t, .punct '*' :: ts => declarator (.ptr t) ts
  | t, .ident q :: ts =>
    if qualWords.contains q then declarator t ts else .error ("declarator " ++ q)
  | t, ts => arrays t ts
where
  /-- `[n][m]…`, the outer bound first. -/
  arrays : CTy → List TTok → Except String CTy
  | t, [] => .ok t
  | t, .punct '[' :: .num n :: .punct ']' :: ts => (fun e => CTy.array e n) <$> arrayOf t ts
  | _, .punct '[' :: .punct ']' :: _ => .error "incomplete array type"
  | _, .punct '(' :: _ => .error "function or function-pointer type: outside CProto"
  | _, _ => .error "declarator"
  /-- The element type of the remaining bounds. -/
  arrayOf : CTy → List TTok → Except String CTy
  | t, [] => .ok t
  | t, .punct '[' :: .num n :: .punct ']' :: ts => (fun e => CTy.array e n) <$> arrayOf t ts
  | _, _ => .error "array declarator"

/-- The qualifier levels of a printed type (`Header.Quals`), by the subset reader's rule
(`Header.qualLevels`): a qualifier joins the current level, `*` starts the next one. Clang
prints a parameter declared `T a[]` as the pointer it is adjusted to. -/
def qualLevelsT (ts : List TTok) : Quals :=
  let canon (l : List String) := ["const", "volatile", "restrict"].filter fun q =>
    l.contains q || (q == "restrict" && l.contains "__restrict")
  let rec go : List TTok → List String → Quals → Quals
    | [], cur, done => done ++ [canon cur]
    | .punct '*' :: r, cur, done => go r [] (done ++ [canon cur])
    | .ident q :: r, cur, done => go r (if qualWords.contains q then q :: cur else cur) done
    | _ :: r, cur, done => go r cur done
  go ts [] []

/-- A type from its printed tokens. -/
def tyOfToks (env : TyEnv) (ts : List TTok) : Except String CTy := do
  let (ws, rest) := specWords ts
  -- `struct (unnamed at …)`, `struct (anonymous at …)`
  if ws.getLast? == some "struct" || ws.getLast? == some "union" || ws.getLast? == some "enum" then
    throw "anonymous struct, union or enum type"
  let t ← baseTy env ws
  declarator t rest

/-- The name of a type printed as one typedef name (with qualifiers). -/
def singleName (ts : List TTok) : Option String :=
  match (specWords ts).1.filter (!qualWords.contains ·), (specWords ts).2 with
  | [n], [] => if (builtinTy [n]).isSome then none else some n
  | _, _ => none

/-- **A type as clang prints it**, read with the import's typedefs. A typedef name the import
does not declare is read from the desugared spelling (keeping the name when the type is that
one name). -/
def tyOf (env : TyEnv) (q : Silmaril.Clang.QualType) : Got CTy :=
  match tyOfToks env (toks q.qualType) with
  | .ok t => .ok t
  | .error e =>
    -- a name the import read without a type keeps the import's reason
    if (singleName (toks q.qualType)).any (fun n => env.any (·.1 == n)) then .unsupported e else
    match q.desugaredQualType with
    | none => .unsupported e
    | some d => match tyOfToks [] (toks d), singleName (toks q.qualType) with
      | .ok t, some n => .ok (.typedef n t)
      | .ok t, none => .ok t
      | .error e', _ => .unsupported e'

/-! ## Function types -/

/-- `__attribute__((x))` groups at the end of reversed tokens: the spellings and the rest. -/
def typeAttrs : List TTok → List String × List TTok
  | .punct ')' :: .punct ')' :: .ident x :: .punct '(' :: .punct '(' :: .ident "__attribute__"
      :: ts =>
    let (as, r) := typeAttrs ts; (x :: as, r)
  | ts => ([], ts)

/-- Reversed tokens after a final `)`: the tokens inside its group (in order) and the reversed
tokens before its `(`. -/
def openGroup : Nat → List TTok → List TTok → Option (List TTok × List TTok)
  | _, [], _ => none
  | 0, .punct '(' :: ts, acc => some (acc, ts)
  | d + 1, .punct '(' :: ts, acc => openGroup d ts (.punct '(' :: acc)
  | d, .punct ')' :: ts, acc => openGroup (d + 1) ts (.punct ')' :: acc)
  | d, t :: ts, acc => openGroup d ts (t :: acc)

/-- Split at commas outside parentheses. -/
def splitTop : Nat → List TTok → List TTok → List (List TTok)
  | _, [], cur => [cur.reverse]
  | 0, .punct ',' :: ts, cur => cur.reverse :: splitTop 0 ts []
  | d, .punct '(' :: ts, cur => splitTop (d + 1) ts (.punct '(' :: cur)
  | d, .punct ')' :: ts, cur => splitTop (d - 1) ts (.punct ')' :: cur)
  | d, t :: ts, cur => splitTop d ts (t :: cur)

/-- A function type's parts: result tokens, parameter token lists, `...`, attribute
spellings. -/
structure FnType where
  ret : List TTok
  params : List (List TTok)
  dots : Bool
  attrs : List String

/-- Read a printed function type `R (P, …) __attribute__((a)) …`. -/
def fnType (s : String) : Except String FnType :=
  let (attrs, rest) := typeAttrs (toks s).reverse
  match rest with
  | .punct ')' :: ts => match openGroup 0 ts [] with
    | some (inside, before) =>
      let ret := before.reverse
      if ret.contains (.punct '(') then .error "the result is a function pointer: outside CProto"
      else match splitTop 0 inside [] with
        | [[]] => .error "no prototype (K&R f()): outside CProto"
        | [[.ident "void"]] => .ok ⟨ret, [], false, attrs.reverse⟩
        | ps => match ps.getLast? with
          | some [.punct '.', .punct '.', .punct '.'] =>
            .ok ⟨ret, ps.dropLast, true, attrs.reverse⟩
          | _ => .ok ⟨ret, ps, false, attrs.reverse⟩
    | none => .error "function type"
  | _ => .error "function type"

/-- The convention a type attribute names, if it is one. -/
def ccOf : String → Option CallConv
  | "ms_abi" => some .msAbi
  | "sysv_abi" => some .sysvAbi
  | "regcall" => some .regcall
  | "vectorcall" => some .vectorcall
  | s => if ["stdcall", "fastcall", "thiscall", "pascal", "preserve_most", "preserve_all",
      "swiftcall", "swiftasynccall", "aarch64_vector_pcs", "aarch64_sve_pcs", "intel_ocl_bicc",
      "pcs", "cdecl", "preserve_none", "riscv_vector_cc", "m68k_rtd"].contains s
    then some (.other s) else none

/-- The convention of a function type's attributes (the first convention attribute). -/
def convention : List String → CallConv
  | [] => .c
  | a :: as => (ccOf a).getD (convention as)

/-- The attributes of a function type that are not conventions. -/
def typeAttrList (as : List String) : List Attr :=
  as.filterMap fun a =>
    if (ccOf a).isSome then none
    else if a == "noreturn" then some .noreturn else some (.other ("type attribute " ++ a))

/-- An attribute node as data. -/
def attrOf (h : Silmaril.Clang.Header) : Option Attr :=
  match h.kind with
  | .noReturnAttr | .c11NoReturnAttr => some .noreturn
  | .nonNullAttr => some .nonnull
  | .formatAttr => some .format
  | .deprecatedAttr => some .deprecated
  | .visibilityAttr => some (.visibility (h.visibility.getD ""))
  | .asmLabelAttr => some .asmLabel
  | .pureAttr => some .pure
  | .constAttr => some .const
  | .noThrowAttr => some .nothrow
  | .leafAttr => some .leaf
  | .builtinAttr => some .builtin
  | .restrictAttr => some .restrict
  | .warnUnusedResultAttr => some .warnUnusedResult
  | .allocSizeAttr => some .allocSize
  | .alignedAttr => some .aligned
  | .weakAttr => some .weak
  | .aliasAttr => some .alias
  | .sectionAttr => some .section
  | .usedAttr => some .used
  | .unusedAttr => some .unused
  | .coldAttr => some .cold
  | .returnsTwiceAttr => some .returnsTwice
  | .allocAlignAttr | .noInlineAttr | .alwaysInlineAttr | .gnuInlineAttr
  | .hotAttr | .modeAttr | .packedAttr | .transparentUnionAttr | .constructorAttr
  | .destructorAttr | .cleanupAttr | .noSanitizeAttr | .maxFieldAlignmentAttr | .mayAliasAttr
  | .availableOnlyInDefaultEvalMethodAttr | .fallThroughAttr => some (.other h.kind.toString)
  | _ => none

/-- `traverse` into `Got`, naming the failing parameter. -/
def gotAll : Nat → List (Got CTy) → Got (List CTy)
  | _, [] => .ok []
  | i, .ok t :: gs => match gotAll (i + 1) gs with
    | .ok ts => .ok (t :: ts)
    | .unsupported w => .unsupported w
  | i, .unsupported w :: _ => .unsupported ("parameter " ++ natStr i ++ ": " ++ w)

/-! ## Declarations -/

/-- A location's file and line (the expansion of a macro location). The filter makes the
first location of every kept declaration explicit; a macro's expansion location is printed
relative to its spelling location. -/
def srcLoc : Silmaril.Clang.Loc → Option SrcLoc
  | .bare l => match l.file, l.line with
    | some f, some n => some ⟨f, n⟩
    | _, _ => none
  | .macro s e => match s.file, s.line with
    | some f, some n => some ⟨e.file.getD f, e.line.getD n⟩
    | _, _ => match e.file, e.line with
      | some f, some n => some ⟨f, n⟩
      | _, _ => none

def headerOf : Silmaril.Clang.Node → Option Silmaril.Clang.Header := Silmaril.Clang.Node.header?

/-- The typedef names a declaration's parameters are printed with that `env` does not have,
with the type of their desugared spelling (`size_t` ↦ `unsigned long`): what clang says those
names denote where it prints them. -/
def aliases (env : TyEnv) (parms : List Silmaril.Clang.Header) : TyEnv :=
  parms.foldl (fun acc p => match p.type with
    | some q => match singleName (toks q.qualType), q.desugaredQualType with
      | some n, some d =>
        if (env ++ acc).any (·.1 == n) then acc else match tyOfToks [] (toks d) with
          | .ok t => acc ++ [(n, .ok t)]
          | .error _ => acc
      | _, _ => acc
    | none => acc) []

/-- The parameter declarations of a node's children. -/
def parmsOf (kids : List Silmaril.Clang.Node) : List Silmaril.Clang.Header :=
  (kids.filterMap headerOf).filter (·.kind == .parmVarDecl)

/-- A function declaration. The result type is read with the names its parameters' types
show (`aliases`), since clang prints no desugared spelling for a function type. -/
def fnOf (env : TyEnv) (h : Silmaril.Clang.Header) (kids : List Silmaril.Clang.Node) : Fn :=
  let hs := kids.filterMap headerOf
  let parms := parmsOf kids
  let renv := env ++ aliases env parms
  let nodeAttrs := hs.filterMap attrOf
  let name := h.name.getD ""
  let symbol := h.mangledName.getD name
  let qt := (h.type.map (·.qualType)).getD ""
  let ft := fnType qt
  let tattrs := match ft with | .ok f => f.attrs | .error _ => []
  let proto : Got CProto := match ft with
    | .error e => .unsupported e
    | .ok f =>
      let ret : Got CTy := match tyOfToks renv f.ret with
        | .ok t => .ok t
        | .error e => match h.type.bind (·.desugaredQualType) with
          | some d => match fnType d with
            | .ok f' => match tyOfToks [] f'.ret with
              | .ok t => .ok t
              | .error e' => .unsupported ("result: " ++ e')
            | .error _ => .unsupported ("result: " ++ e)
          | none => .unsupported ("result: " ++ e)
      let ps : Got (List CTy) :=
        if parms.length != f.params.length then
          .unsupported "the parameter declarations do not match the function type"
        else gotAll 1 (parms.map fun p => match p.type with
          | some q => tyOf env q
          | none => .unsupported "parameter without a type")
      match ret, ps with
      | .unsupported w, _ => .unsupported w
      | _, .unsupported w => .unsupported w
      | .ok r, .ok ps => .ok ⟨r, ps, f.dots⟩
  let quals : Option ProtoQuals := match ft with
    | .error _ => none
    | .ok f => some ⟨qualLevelsT f.ret,
        parms.map fun p => qualLevelsT (toks ((p.type.map (·.qualType)).getD ""))⟩
  { proto
    quals
    variadic := h.variadic.getD false
    cc := convention tattrs
    attrs := typeAttrList tattrs ++ nodeAttrs
    symbol
    asmLabel := if nodeAttrs.contains .asmLabel then some symbol else none
    storage := h.storageClass
    inline := h.inline.getD false
    definition := hs.any (·.kind == .compoundStmt) }

/-- One decoded top-level declaration. -/
def entryOf (env : TyEnv) (n : Silmaril.Clang.Node) : Entry :=
  match n with
  | .mk h inner _ =>
    let kids := (inner.getD #[]).toList.filter (!·.isComment)
    let name := h.name.getD ""
    let loc := h.loc.bind srcLoc
    let implicit := h.isImplicit.getD false
    let mk (k : DeclKind) (b : Body) : Entry := ⟨name, k, loc, implicit, b⟩
    match h.kind with
    | .functionDecl => mk .function (.function (fnOf env h kids))
    | .typedefDecl => mk .typedef (.typedef (match h.type with
        | some q => tyOf env q
        | none => .unsupported "typedef without a type"))
    | .recordDecl => mk (if h.tagUsed == some "union" then .union else .struct)
        (.tag (h.completeDefinition.getD false))
    | .enumDecl => mk .enum (.tag (kids.any fun k => k.kind? == some .enumConstantDecl))
    | .varDecl => mk .variable (.variable (match h.type with
        | some q => tyOf env q
        | none => .unsupported "variable without a type") h.storageClass)
    | k => mk (.other k.toString)
        (.unsupported (k.toString ++ ": not a declaration the import reads"))
  | _ => ⟨"", .other "", none, false, .unsupported "not a declaration node"⟩

/-- The kind of a clang declaration kind's spelling. -/
def kindOfString : String → DeclKind
  | "FunctionDecl" => .function
  | "TypedefDecl" => .typedef
  | "VarDecl" => .variable
  | "EnumDecl" => .enum
  | "RecordDecl" => .struct
  | k => .other k

/-- A top-level node the strict decoder refuses: its kind, name and location from the raw
JSON, and the decoder's message. -/
def refusedEntry (t : TotalJson.Tree) (why : String) : Entry :=
  let fs := match TotalJson.Metadata.fields t "node" with | .ok fs => fs | .error _ => []
  let str (k : String) := ((TotalJson.Metadata.look fs k).bind TotalJson.Metadata.string?).getD ""
  let loc := match TotalJson.Metadata.look fs "loc" with
    | some l => match TotalJson.Metadata.decodeLoc l with
      | .ok l => srcLoc l
      | .error _ => none
    | none => none
  ⟨str "name", kindOfString (str "kind"), loc, false,
    .unsupported ("clang AST decoder: " ++ why)⟩

def errorText : TotalJson.Error → String
  | .syntax => "JSON syntax"
  | .bridge => "JSON outside the standard bridge"
  | .node m => m
  | .root m => m

/-- The typedefs an entry adds to the environment. -/
def Entry.env (e : Entry) : TyEnv :=
  match e.kind, e.body with
  | .typedef, .typedef t => [(e.name, t)]
  | _, _ => []

/-- The names a decoded declaration adds to the environment: its own typedef, then the
`aliases` its parameters show. -/
def nodeEnv (env : TyEnv) (e : Entry) : Silmaril.Clang.Node → TyEnv
  | .mk _ inner _ =>
    let own := e.env
    own ++ aliases (env ++ own) (parmsOf ((inner.getD #[]).toList.filter (!·.isComment)))
  | _ => e.env

/-- Import the top-level nodes in order, each with the typedefs of the earlier ones (the
first of a name is the one later names refer to). -/
def importNodes : TyEnv → List TotalJson.Tree → List Entry
  | _, [] => []
  | env, t :: ts => match TotalJson.decodeTree t with
    | .ok n => let e := entryOf env n; e :: importNodes (env ++ nodeEnv env e n) ts
    | .error err => refusedEntry t (errorText err) :: importNodes env ts

/-! ## Provenance -/

/-- Split at a character. -/
def splitAt (c : Char) : List Char → List Char → List (List Char)
  | [], cur => [cur.reverse]
  | x :: xs, cur => if x == c then cur.reverse :: splitAt c xs [] else splitAt c xs (x :: cur)

/-- `key: value` (at the first `": "`). -/
def keyValue : List Char → List Char → Option (String × String)
  | ':' :: ' ' :: v, k => some (String.ofList k.reverse, String.ofList v)
  | c :: cs, k => keyValue cs (c :: k)
  | [], _ => none

/-- The first word and the rest. -/
def firstWord (s : String) : String × String :=
  match splitAt ' ' s.toList [] with
  | w :: ws => (String.ofList w, " ".intercalate (ws.map String.ofList))
  | [] => ("", "")

/-- Add one `key: value` line of a `.prov` file. -/
def Provenance.add (p : Provenance) : String × String → Provenance
  | ("artifact", v) => { p with artifact := v }
  | ("image", v) => { p with image := v }
  | ("clang", v) => { p with clang := v }
  | ("target", v) => { p with target := v }
  | ("std", v) => { p with std := v }
  | ("cwd", v) => { p with cwd := v }
  | ("command", v) => { p with command := v }
  | ("define", v) => { p with defines := p.defines ++ [v] }
  | ("include", v) => { p with includes := p.includes ++ [v] }
  | ("filter", v) => { p with filter := v }
  | ("filter-sha256", v) => { p with filterSha256 := v }
  | ("source", v) => { p with source := some v }
  | ("input", v) => { p with inputs := p.inputs ++ [firstWord v] }
  | ("json-sha256", v) => { p with jsonSha256 := v }
  | ("json-bytes", v) => { p with jsonBytes := digits v.toList }
  | _ => p

/-- The characters of an ASCII text (`none` if it is not ASCII). -/
def asciiOf (s : String) : Option (List Char) := Json.asciiChars s.toUTF8.data.toList

/-- Read a `.prov` file (ASCII, one `key: value` per line). -/
def Provenance.parse (text : String) : Provenance :=
  match asciiOf text with
  | none => {}
  | some cs => ((splitAt '\n' cs []).filterMap (keyValue · [])).foldl Provenance.add {}

/-! ## The import -/

/-- The members of a JSON object, by name. -/
def member (ms : List (Json.Units × TotalJson.Tree)) (k : String) : Option TotalJson.Tree :=
  (ms.find? (fun p => Json.unitsString? p.1 == some k)).map (·.2)

/-- **Import a pinned clang JSON AST** (an ASCII document whose root is the
`TranslationUnitDecl`), with its provenance. Every element of the root's `inner` is one entry.
The document's byte count must be the provenance's. -/
def Imported.ofJson (prov : Provenance) (json : String) : Imported :=
  let fail (why : String) : Imported := ⟨prov, [], some why⟩
  match asciiOf json with
  | none => fail "not an ASCII document"
  | some cs =>
    if cs.length != prov.jsonBytes then fail "the byte count is not the provenance's" else
    match (Json.parseChars? .rfc8259 cs).map Json.Tree.ofAst with
    | none => fail "not an RFC 8259 JSON document"
    | some (.object ms) =>
      match (member ms "kind").bind TotalJson.Metadata.string?, member ms "inner" with
      | some "TranslationUnitDecl", some (.array ts) => ⟨prov, importNodes [] ts, none⟩
      | some "TranslationUnitDecl", none => ⟨prov, [], none⟩
      | _, _ => fail "the root is not a TranslationUnitDecl with an inner array"
    | some _ => fail "the root is not an object"

/-! ## Views -/

/-- The function entries, with what the import read of them. -/
def Imported.functions (imp : Imported) : List (Entry × Fn) :=
  imp.entries.filterMap fun e => match e.body with
    | .function f => some (e, f)
    | _ => none

/-- A function a binary may define: declared explicitly, and not `static`. -/
def Entry.external (e : Entry) (f : Fn) : Bool := !e.implicit && f.storage != some "static"

/-- Keep the first pair of each name. -/
def firstOfEach {α : Type} : List (String × α) → List String → List (String × α)
  | [], _ => []
  | (n, a) :: r, seen =>
    if seen.contains n then firstOfEach r seen else (n, a) :: firstOfEach r (n :: seen)

/-- **The subset reader's `Header` of the import**: the typedefs read (the first of each
name) and the first prototype of each external function (one `Imported.conflicts` lists if a
later declaration differs). Functions without a `CProto` are not in it (`Imported.table`
in the conformance module lists them, with the reason). -/
def Imported.header (imp : Imported) : Header where
  typedefs := firstOfEach (imp.entries.filterMap fun e => match e.kind, e.body with
    | .typedef, .typedef (.ok t) => some (e.name, t)
    | _, _ => none) []
  protos := firstOfEach (imp.functions.filterMap fun (e, f) =>
    if e.external f then match f.proto with
      | .ok p => some (e.name, p)
      | .unsupported _ => none
    else none) []
  quals := firstOfEach (imp.functions.filterMap fun (e, f) =>
    if e.external f then match f.proto, f.quals with
      | .ok _, some q => some (e.name, q)
      | _, _ => none
    else none) []

/-- The prototype the import gives `f`. -/
def Imported.proto? (imp : Imported) (f : String) : Option CProto := imp.header.proto? f

/-- The first external function entry named `f`. -/
def Imported.fn? (imp : Imported) (f : String) : Option (Entry × Fn) :=
  imp.functions.find? fun (e, x) => e.name == f && e.external x

/-- Functions declared twice with different prototypes. -/
def Imported.conflicts (imp : Imported) : List String :=
  imp.functions.filterMap fun (e, f) => match f.proto, imp.proto? e.name with
    | .ok p, some q => if e.external f && p != q then some e.name else none
    | _, _ => none

/-! ## Comparing the two routes -/

/-- **The comparison of the subset reader's header with the import**, over the reader's
functions: those with the same `CProto`, those with different ones (the reader's, then the
import's), and those the import gives no prototype. -/
structure Comparison where
  agree : List String := []
  disagree : List (String × CProto × CProto) := []
  readerOnly : List String := []
  deriving DecidableEq, Repr

def compare (H : Header) (imp : Imported) : Comparison :=
  H.protos.foldr (fun (f, p) c => match imp.proto? f with
    | some q => if p == q then { c with agree := f :: c.agree }
      else { c with disagree := (f, p, q) :: c.disagree }
    | none => { c with readerOnly := f :: c.readerOnly }) {}

/-- The comparison of a header the subset reader reads from `files` (`none` if it refuses). -/
def compareRead (files : List (String × String)) (root : String) (imp : Imported) :
    Option Comparison :=
  (read files root).toOption.map (compare · imp)

end Silmaril.Data.Layout.Header.Import

end
