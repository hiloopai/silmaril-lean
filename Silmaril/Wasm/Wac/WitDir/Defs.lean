module

public import Silmaril.Wasm.Wit.Tool.Source.Defs

/-!
# WIT packages in several files, as `wit-parser` reads a directory

`wit-parser` (`UnresolvedPackageGroup::parse_dir`, wasm-tools 1.262.0) reads a package
directory as **all** its `*.wit` files, in path order: each file is parsed on its own, at least
one has the header `package ns:name;`, every header names the same package, and the package's
items are those of all the files (the resolver then orders interfaces by their dependencies, as
for one file). A file without a header belongs to the package of the others. `deps/` holds one
package per `.wit` file and one per subdirectory (itself possibly several files).

`Wit.Tool.encodeText` reads one file per package. This module adds:

* `parseFiles`: the files of one package, each lexed by the verified lexer (`Text.lex`), a file
  without a header given the header of the first file that has one, each parsed by the verified
  parser (`Text.Parse.document`), and merged (`merge`): the items in file order, the docs of the
  first file that has package docs, the nested packages of all files;
* `dropParamDocs`: `///` lines inside parentheses (documentation of function parameters, which
  WASI's own WIT has) are dropped before parsing: `wit-parser` accepts and ignores them (a
  parameter has no docs in a package), the verified parser rejects them;
* `encodeTextX`: `Wit.Tool.encodeText` whenever the package is one file that it reads
  (`encodeTextX_of_ok`), else the files and dependencies through `parseFiles`, elaborated and
  encoded by the same verified functions (`Wit.Tool.encodeDocs`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.WitDir

open Silmaril.Wasm.Wit Silmaril.Wasm.Wit.Text

/-- Drop the doc lines at a parenthesis depth above `0` (inside parameter lists). -/
def dropParamDocs : Nat → List Tok → List Tok
  | _, [] => []
  | d, .sym '(' :: r => .sym '(' :: dropParamDocs (d + 1) r
  | d, .sym ')' :: r => .sym ')' :: dropParamDocs (d - 1) r
  | d, .doc s :: r => if d = 0 then .doc s :: dropParamDocs d r else dropParamDocs d r
  | d, t :: r => t :: dropParamDocs d r

/-- The tokens of a file. -/
def lexX (label text : String) : Except String (List Tok) :=
  match lex text.toList with
  | some ts => .ok (dropParamDocs 0 ts)
  | none => .error s!"{label}: not WIT text this lexer accepts"

/-- The tokens up to and including the first `;`, unless a `{` comes first. -/
def upToSemi : List Tok → Option (List Tok)
  | [] => none
  | .sym ';' :: _ => some [.sym ';']
  | .sym '{' :: _ => none
  | t :: r => (upToSemi r).map (t :: ·)

/-- The header `package ns:name;` of a file (after its leading doc lines), if it has one. -/
def header (ts : List Tok) : Option (List Tok) :=
  match (Parse.docs ts).2 with
  | .kw .package :: r => (upToSemi r).map (.kw .package :: ·)
  | _ => none

/-- The first header of a list of files. -/
def firstHeader : List (List Tok) → Option (List Tok)
  | [] => none
  | ts :: r => match header ts with
    | some h => some h
    | none => firstHeader r

/-- **Merge** the documents of the files of one package (all with the same package name). -/
def merge (d : Document) (ds : List Document) : Document :=
  { main := { name := d.main.name
              items := (d :: ds).flatMap (·.main.items)
              docs := ((d :: ds).find? (·.main.docs.contents.isSome)).elim {} (·.main.docs) }
    nested := (d :: ds).flatMap (·.nested) }

/-- **The package of the files `fs`** (`(path, text)`, in path order). -/
def parseFiles (fs : List (String × String)) : Except String Document := do
  let tss ← fs.mapM fun f => lexX f.1 f.2
  let h ← match firstHeader tss with
    | some h => pure h
    | none => throw s!"no `package` header in {fs.map (·.1)}"
  let docs ← (fs.zip tss).mapM fun (f, ts) =>
    let ts' := if (header ts).isSome then ts else h ++ ts
    match Parse.document ts' with
    | some d => pure d
    | none => throw s!"{f.1}: not WIT text this parser accepts"
  match docs with
  | [] => throw "a package of no files"
  | d :: ds =>
    if ds.all (·.main.name == d.main.name) then pure (merge d ds)
    else throw s!"the files {fs.map (·.1)} declare different packages"

/-- **WIT text of a package of several files, with dependencies** (each a package of one or
more files) to the bytes `wasm-tools component wit --wasm` writes: `Wit.Tool.encodeText` when
the package is one file it reads, else `parseFiles` and the same elaboration and encoder. -/
def encodeTextX (main : List (String × String)) (deps : List (List (String × String))) :
    Except String ByteArray :=
  let ext : Except String ByteArray := do
    let d ← parseFiles main
    let ds ← deps.mapM parseFiles
    Wit.Tool.encodeDocs d ds []
  match main, deps.all (·.length == 1) with
  | [m], true =>
    match Wit.Tool.encodeText m (deps.flatMap id) with
    | .ok b => .ok b
    | .error _ => ext
  | _, _ => ext

/-- On a one-file package with one-file dependencies that `Wit.Tool.encodeText` reads, the
bytes are its bytes. -/
theorem encodeTextX_of_ok {m : String × String} {deps : List (String × String)} {b : ByteArray}
    (h : Wit.Tool.encodeText m deps = .ok b) : encodeTextX [m] (deps.map ([·])) = .ok b := by
  have hd : ∀ l : List (String × String), (l.map ([·])).flatMap id = l := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih => simpa using ih
  have ha : (deps.map ([·])).all (·.length == 1) = true := by simp
  simp only [encodeTextX, ha, hd deps, h]

end Silmaril.Wasm.Wac.WitDir
