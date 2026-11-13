module

public import Silmaril.Wasm.Wac.WitDir.Defs

/-!
# WIT packages in wit-parser's item order

`wit-parser` (wasm-tools 1.262.0, `ast/resolve.rs`, `populate_ast_items`) does not keep the
interfaces and worlds of a package in source order: it records, for every interface, the
interfaces and worlds of the same package that its `use` statements name (through the file's
top-level `use … as …` aliases; foreign packages are ignored, uses inside worlds are ignored),
and allocates the items in the **topological order** of `ast/toposort.rs`: Kahn's algorithm whose
ready set is a heap keyed by source position, so at each step the *first* item (in source order)
whose dependencies have all been placed comes next. The binary encoding (`component wit --wasm`)
writes the package's items in that order.

The verified elaborator and encoder (`Wit.Tool.encodeDocs`) keep source order. On a package in
which an interface uses one defined later (wit-parser's `tests/ui/use.wit`: `foo` uses `bar`,
declared after it) the two encodings differ, and wasm-tools' decoder **panics** on the
source-order one (`assertion failed: prev.is_none()`, `crates/wit-parser/src/decoding.rs:1567`):
decoding `foo`'s type registers the imported `foo:foo/bar` as a foreign interface, and the later
type export of `bar` in the same package then registers the same interface a second time. The
encoding is a valid component; the decoder assumes wit-parser's order. So the order matters for
interoperability, not only for byte equality.

* `deps`: the dependencies of a package item, as wit-parser records them;
* `topo`: Kahn's algorithm with the first ready item first;
* `sortPkg`, `sortDoc`: the package (and nested packages) in that order; top-level `use` items
  first, in source order (they are not items of the package);
* `rwPkg`, `parseFilesR`: top-level `use path as name;` items, which wit-parser keeps in the
  *file's* namespace and not in the package, are resolved file by file before the files are
  merged: every path naming the alias is replaced by the path it denotes, and the `use` item is
  dropped (the verified elaborator rejects packages with such items as an invalid WIT universe);
* `encodeTextO`: `WitDir.encodeTextX` on the resolved, sorted packages. When nothing changes
  (no alias, every package already in wit-parser's order: the common case) it **is**
  `encodeTextX` (`encodeTextO_of_unchanged` in `Thms`), so the theorems about `encodeTextX`
  apply unchanged; otherwise the same verified elaboration and encoder run on the resolved,
  reordered items.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.WitOrder

open Silmaril.Wasm.Wit

/-- The name a package item declares (`use` items declare none in the package). -/
def itemName : PackageItem → Option Name
  | .iface i => some i.name
  | .world w => some w.name
  | .use _ => none

/-- The last segment of a use path. -/
def pathName : UsePath → Name
  | .local n => n
  | .foreign _ n => n

/-- The top-level `use … as …` aliases: the name bound and the local item it denotes (`none` for
an item of a foreign package). -/
def topUses (items : List PackageItem) : List (Name × Option Name) :=
  items.filterMap fun
    | .use u => some (u.as.getD (pathName u.path), match u.path with
        | .local n => some n
        | .foreign _ _ => none)
    | _ => none

/-- The local item a `use` path inside an interface depends on, if any. -/
def depOf (tops : List (Name × Option Name)) (names : List Name) : UsePath → Option Name
  | .foreign _ _ => none
  | .local n =>
    if n ∈ names then some n
    else match tops.lookup n with
      | some (some m) => some m
      | _ => none

/-- **The dependencies of an item** (wit-parser's `order` map): the local items named by the
`use` statements of an interface; none for a world. -/
def deps (tops : List (Name × Option Name)) (names : List Name) : PackageItem → List Name
  | .iface i => i.items.filterMap fun
    | .use u => depOf tops names u.path
    | _ => none
  | _ => []

/-- An item is ready when every dependency is placed (or names nothing of the package). -/
def ready (tops : List (Name × Option Name)) (names done : List Name) (it : PackageItem) : Bool :=
  (deps tops names it).all fun d => d ∈ done || !(d ∈ names)

/-- **Kahn's algorithm, first ready item first** (`ast/toposort.rs`). A cycle (which wit-parser
rejects) leaves the remaining items in source order. -/
def topo (tops : List (Name × Option Name)) (names : List Name) :
    Nat → List Name → List PackageItem → List PackageItem
  | 0, _, rest => rest
  | f + 1, done, rest =>
    match rest.find? (ready tops names done) with
    | none => rest
    | some it => it :: topo tops names f (done ++ (itemName it).toList) (rest.erase it)

/-- A package with its items in wit-parser's order. -/
def sortPkg (p : Package) : Package :=
  let uses := p.items.filter fun it => (itemName it).isNone
  let named := p.items.filter fun it => (itemName it).isSome
  let tops := topUses p.items
  let names := named.filterMap itemName
  { p with items := uses ++ topo tops names named.length [] named }

/-- A document with every package in wit-parser's order. -/
def sortDoc (d : Document) : Document :=
  { d with main := sortPkg d.main, nested := d.nested.map sortPkg }

/-- Is every package of the document already in wit-parser's order? -/
def isSorted (d : Document) : Bool := sortDoc d == d

/-! ## Top-level `use … as …` -/

/-- Resolve a path through the file's top-level aliases. -/
def rwPath (al : List (Name × UsePath)) : UsePath → UsePath
  | .local n => (al.lookup n).getD (.local n)
  | p => p

/-- Resolve the paths of an interface body. -/
def rwIface (al : List (Name × UsePath)) (items : List IfaceItem) : List IfaceItem :=
  items.map fun
    | .use u => .use { u with path := rwPath al u.path }
    | it => it

/-- Resolve the paths of an import or export of a world. -/
def rwExtern (al : List (Name × UsePath)) (e : WorldExtern) : WorldExtern :=
  { e with ext := match e.ext with
    | .path p => .path (rwPath al p)
    | .iface n items => .iface n (rwIface al items)
    | x => x }

/-- Resolve the paths of a world body. -/
def rwWorld (al : List (Name × UsePath)) (items : List WorldItem) : List WorldItem :=
  items.map fun
    | .use u => .use { u with path := rwPath al u.path }
    | .import e => .import (rwExtern al e)
    | .export e => .export (rwExtern al e)
    | .include i => .include { i with path := rwPath al i.path }
    | it => it

/-- The top-level aliases of a file: the name bound and the path it denotes. -/
def aliases (items : List PackageItem) : List (Name × UsePath) :=
  items.filterMap fun
    | .use u => some (u.as.getD (pathName u.path), u.path)
    | _ => none

/-- **Top-level `use … as …` resolved** (wit-parser: these names live in the file's namespace,
not in the package): every path of the file naming an alias is replaced by the path the alias
denotes, and the `use` items are dropped. -/
def rwPkg (p : Package) : Package :=
  let al := aliases p.items
  { p with items := p.items.filterMap fun
    | .use _ => none
    | .iface i => some (.iface { i with items := rwIface al i.items })
    | .world w => some (.world { w with items := rwWorld al w.items }) }

/-- A file's document with its top-level aliases resolved. -/
def rwDoc (d : Document) : Document := { d with main := rwPkg d.main, nested := d.nested.map rwPkg }

/-! ## Comments as documentation -/

/-- An ASCII white-space character (Rust's `is_ascii_whitespace`). -/
def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'

/-- The rest of a block comment after its opening `/*` at nesting depth `d`: the comment's
characters (reversed onto `acc`) and the text after it. -/
def blockRest : Nat → List Char → List Char → Option (List Char × List Char)
  | d, acc, '/' :: '*' :: r => blockRest (d + 1) ('*' :: '/' :: acc) r
  | d, acc, '*' :: '/' :: r =>
    if d ≤ 1 then some ('/' :: '*' :: acc, r) else blockRest (d - 1) ('/' :: '*' :: acc) r
  | d, acc, c :: r => blockRest d (c :: acc) r
  | _, _, [] => none

/-- One comment at the start of `cs` (`//…` to the end of the line, or a nested `/* … */`): its
text and the rest. -/
def comment : List Char → Option (List Char × List Char)
  | '/' :: '/' :: r => some ('/' :: '/' :: r.takeWhile (· != '\n'), r.dropWhile (· != '\n'))
  | '/' :: '*' :: r => (blockRest 1 ['*', '/'] r).map fun p => (p.1.reverse, p.2)
  | _ => none

/-- A run of comments separated by white space only: the comments and the rest. -/
def commentRun : Nat → List Char → List (List Char) × List Char
  | 0, cs => ([], cs)
  | f + 1, cs =>
    match comment (cs.dropWhile isWs) with
    | some (c, r) => let p := commentRun f r; (c :: p.1, p.2)
    | none => ([], cs)

/-- Drop trailing white space. -/
def trimEnd (l : List Char) : List Char := (l.reverse.dropWhile isWs).reverse

/-- The doc entry of a comment (wit-parser's `Resolver::docs`): `/** … */` without its
delimiters, any other comment without its leading slashes; trailing white space trimmed. -/
def entry : List Char → List Char
  | '/' :: '*' :: '*' :: r => trimEnd (r.take (r.length - 2))
  | l => trimEnd (l.dropWhile (· == '/'))

/-- Rust's `str::lines`: split at `\n`, a final `\r` dropped, no final empty line. -/
def rustLines (l : List Char) : List (List Char) :=
  let ls := (l.splitOn '\n').map fun x => if x.getLast? == some '\r' then x.dropLast else x
  if l.getLast? == some '\n' || l.isEmpty then ls.dropLast else ls

/-- **The documentation of a run of comments**, as wit-parser computes it: the entries, dedented
by the least leading white space of the non-empty ones (as spaces), each line followed by a
newline (an empty entry is one newline), trailing newlines removed. -/
def docText (cs : List (List Char)) : List Char :=
  let es := cs.map entry
  let ws := (es.filter (· ≠ [])).map fun e => (e.takeWhile isWs).length
  let m := ws.foldl min (ws.headD 0)
  let es := es.map fun e => if e.take m == List.replicate m ' ' then e.drop m else e
  let body := es.flatMap fun e => if e.isEmpty then ['\n'] else (rustLines e).flatMap (· ++ ['\n'])
  (body.reverse.dropWhile (· == '\n')).reverse

/-- The doc text as `///` lines the verified lexer and parser read back to the same contents
(the parser strips one leading space of each line). -/
def docLinesOf (t : List Char) : List Char :=
  ((t.splitOn '\n').flatMap fun l => ['/', '/', '/', ' '] ++ l ++ ['\n'])

/-- **Comments as wit-parser reads them**: a run of comments right before an item (the previous
significant character is none, `;`, `{`, `}` or `,`, outside parentheses and angle brackets, and
the next is neither `}` nor the end) becomes `///` lines with wit-parser's documentation text
(`docText`); every other run of comments is white space. `p`, `a`: parenthesis and angle depth;
`prev`: the previous significant character; `out`: the output, reversed. -/
def docsLoop : Nat → Nat → Nat → Option Char → List Char → List Char → List Char
  | 0, _, _, _, out, cs => out.reverse ++ cs
  | f + 1, p, a, prev, out, cs =>
    match commentRun cs.length cs with
    | (c :: run, rest) =>
      let next := (rest.dropWhile isWs).head?
      let atItem := p == 0 && a == 0 && (prev.isNone || prev ∈ [some ';', some '{', some '}', some ','])
        && !(next.isNone || next == some '}')
      let emitted := if atItem then ['\n'] ++ docLinesOf (docText (c :: run)) else ['\n']
      docsLoop f p a prev (emitted.reverse ++ out) rest
    | ([], _) =>
      match cs with
      | [] => out.reverse
      | c :: r =>
        let p' := if c == '(' then p + 1 else if c == ')' then p - 1 else p
        let a' := if c == '<' then a + 1
          else if c == '>' && prev != some '-' then a - 1 else a
        let prev' := if isWs c then prev else some c
        docsLoop f p' a' prev' (c :: out) r

/-- A file's text with its comments read as wit-parser reads them. -/
def docsT (t : String) : String :=
  String.ofList (docsLoop (t.length + 1) 0 0 none [] t.toList)

/-- `WitDir.parseFiles` with each file's comments read as wit-parser reads them (`docsT`) and its
top-level aliases resolved before the merge. -/
def parseFilesR (fs : List (String × String)) : Except String Document := do
  let tss ← fs.mapM fun f => WitDir.lexX f.1 (docsT f.2)
  let h ← match WitDir.firstHeader tss with
    | some h => pure h
    | none => throw s!"no `package` header in {fs.map (·.1)}"
  let docs ← (fs.zip tss).mapM fun (f, ts) =>
    let ts' := if (WitDir.header ts).isSome then ts else h ++ ts
    match Text.Parse.document ts' with
    | some d => pure (rwDoc d)
    | none => throw s!"{f.1}: not WIT text this parser accepts"
  match docs with
  | [] => throw "a package of no files"
  | d :: ds =>
    if ds.all (·.main.name == d.main.name) then pure (WitDir.merge d ds)
    else throw s!"the files {fs.map (·.1)} declare different packages"

/-- Is the document unchanged by resolving aliases and sorting? -/
def unchanged (d₀ d : Document) : Bool := d == d₀ && isSorted d

/-- **The bytes of a package with no interface and no world** (wit-component's `encode` of an
empty package: no items, the `package-docs` and `producers` sections), written by the verified
binary encoder `Binary.encodePackage`. The elaborator refuses such a package (its name appears
in no item, so it does not survive the encoding: `Package.validB`), but `wasm-tools component wit
--wasm` writes it, and it is what a file whose items are all nested `package … { }` blocks
encodes to (only the main package is encoded). -/
def emptyBytes (P : Package) : Except String ByteArray :=
  Binary.encodePackage [] { name := Elab.pkgName P.name, docs := P.docs.contents }

/-- Does the package declare no interface and no world? -/
def isEmptyPkg (P : Package) : Bool := P.items.all fun it => (itemName it).isNone

/-- **A WIT package directory to bytes, as wit-parser resolves it**: `WitDir.encodeTextX` when
no file has a top-level alias and every package is already in wit-parser's order, else the
verified elaboration and encoder on the packages with their aliases resolved and their items
sorted; a main package with no interface and no world is `emptyBytes` (its nested packages and
dependencies are not elaborated). -/
def encodeTextO (main : List (String × String)) (deps : List (List (String × String))) :
    Except String ByteArray :=
  match WitDir.parseFiles main, deps.mapM WitDir.parseFiles, parseFilesR main,
      deps.mapM parseFilesR with
  | .ok d₀, .ok ds₀, .ok d, .ok ds =>
    if unchanged d₀ d && (ds₀.zip ds).all (fun p => unchanged p.1 p.2) then
      match WitDir.encodeTextX main deps with
      | .ok b => .ok b
      | .error e => if isEmptyPkg d.main then emptyBytes d.main else .error e
    else if isEmptyPkg d.main then emptyBytes d.main
    else Wit.Tool.encodeDocs (sortDoc d) (ds.map sortDoc) []
  | _, _, _, _ => WitDir.encodeTextX main deps

end Silmaril.Wasm.Wac.WitOrder
