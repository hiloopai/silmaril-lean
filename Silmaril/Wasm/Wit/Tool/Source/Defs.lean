module

public import Silmaril.Wasm.Wit.Tool.Defs
public import Silmaril.Wasm.Wit.Elab.Defs
public import Silmaril.Wasm.Wit.Text.Parse.Defs
public import Silmaril.Wasm.Wit.Project.Ext.Defs
public import Silmaril.Wasm.Wit.Binary.Print.Deps.Defs
public import Silmaril.Wasm.Wit.Binary.Embed.Defs
public import Silmaril.Wasm.Component.Wat.Ids.Defs

/-!
# The core of `wasm-wit`: WIT source, worlds in core modules, `projectX`

Pure functions behind the subcommands of `wasm-wit` that read WIT text, embed
or extract a world, and project with `projectX` (`tools/wasm-wit`; theorems in
`Silmaril.Wasm.Wit.Tool.Source.Thms`).

| subcommand | function | built on |
|---|---|---|
| `encode PKG.wit --deps DIR` | `encodeText` | `Text.parse`, `Elab.elaborate` (which runs `Wit.check`), `Binary.encodePackage` |
| `check PKG.wit --deps DIR`  | `checkText`  | the same, then `Tool.check` on the bytes |
| `wit IN.wasm`               | `witAll`     | `printPackage` and the nested packages (`printPackageAll`, unverified) |
| `embed PKG.(wit\|wasm) --world W` | `embedText`, `embedBytes` | `Binary.encodeWorldType` |
| `embed … --into CORE.wasm`  | `Binary.embedPayload` | a `component-type` custom section |
| `extract CORE.wasm`         | `Binary.extractWorldType` | `Binary.decodeWorldType` |
| `project`                   | `projectBytesX`, `projectWatX` | `Project.projectX` |

A WIT source is a main document and dependency documents (one per file); their
packages form the universe given to `Elab.elaborate`, which elaborates the main
document's first package. Feature names enable `@unstable` items (wasm-tools'
`--features`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Tool

open Silmaril.Wasm.Component
open Silmaril.Wasm.Wit.Binary (Env decodePackage decodeEnv encodePackage StringEncoding)

/-! ## WIT text -/

/-- Parse one WIT document (`label` names it in the error). -/
def parseText (label text : String) : Except String Document :=
  match Text.parse text with
  | some d => .ok d
  | none => .error s!"{label}: not WIT text this parser accepts"

/-- The universe of a main document and its dependency documents. -/
def sourceUniverse (d : Document) (ds : List Document) : Universe :=
  d.packages ++ ds.flatMap Document.packages

/-- Elaborate the main package of `d` in the universe of `d` and `ds`. -/
def elabDocs (d : Document) (ds : List Document) (fs : List Name) :
    Except String (Binary.Package × Env) :=
  Elab.elaborate (sourceUniverse d ds) d.main.name fs

/-- Parse the dependency texts (`(label, text)` pairs). -/
def parseDeps (deps : List (String × String)) : Except String (List Document) :=
  deps.mapM fun (l, t) => parseText l t

/-- Parse the main text and the dependency texts. -/
def parseSource (main : String × String) (deps : List (String × String)) :
    Except String (Document × List Document) := do
  let d ← parseText main.1 main.2
  let ds ← parseDeps deps
  pure (d, ds)

/-- Parse and elaborate a WIT source. -/
def elabText (main : String × String) (deps : List (String × String)) (fs : List Name := []) :
    Except String (Binary.Package × Env) := do
  let (d, ds) ← parseSource main deps
  elabDocs d ds fs

/-- Elaborate and encode parsed documents. -/
def encodeDocs (d : Document) (ds : List Document) (fs : List Name) : Except String ByteArray := do
  let (P, env) ← elabDocs d ds fs
  encodePackage env P

/-- `wasm-wit encode PKG.wit --deps DIR`: WIT text to the bytes of
`wasm-tools component wit --wasm`. -/
def encodeText (main : String × String) (deps : List (String × String)) (fs : List Name := []) :
    Except String ByteArray := do
  let (d, ds) ← parseSource main deps
  encodeDocs d ds fs

/-- `wasm-wit check PKG.wit --deps DIR`: encode, then run the binary checks. -/
def checkText (main : String × String) (deps : List (String × String)) (fs : List Name := []) :
    Except String (ByteArray × Report) := do
  let b ← encodeText main deps fs
  pure (b, ← check b)

/-! ## WIT text of a binary with its dependencies -/

/-- `wasm-wit wit`: the main package and the nested dependency packages
(unverified printer). -/
def witAll (b : ByteArray) : Except String String := do
  let p ← decodePackage b
  let ns ← Binary.decodeForeign b p.name
  pure (Binary.printPackageAll p ns)

/-! ## Worlds embedded in core modules -/

/-- The world `n` of a package. -/
def findWorld (P : Binary.Package) (n : String) : Except String Binary.World :=
  match P.worlds.find? (·.1 == n) with
  | some (_, w) => .ok w
  | none => .error s!"no world `{n}` in the package"

/-- The `component-type` payload of world `n` of a package encoded in `env`. -/
def embedPkg (P : Binary.Package) (env : Env) (n : String) (se : StringEncoding) :
    Except String ByteArray := do
  let w ← findWorld P n
  Binary.encodeWorldType (P.env env) P.name n w se

/-- `wasm-wit embed PKG.wit --world W`: the payload of a world of a WIT source. -/
def embedText (main : String × String) (deps : List (String × String)) (fs : List Name)
    (n : String) (se : StringEncoding) : Except String ByteArray := do
  let (P, env) ← elabText main deps fs
  embedPkg P env n se

/-- `wasm-wit embed PKG.wasm --world W`: the payload of a world of a WIT binary
(in the environment the binary shows). -/
def embedBytes (b : ByteArray) (n : String) (se : StringEncoding) : Except String ByteArray := do
  let d ← decode b
  embedPkg d.pkg d.env n se

/-! ## Projection with `projectX` -/

/-- `wasm-wit project` on bytes: `Project.projectX`. -/
def projectBytesX (b : ByteArray) : Except String Project.WorldType :=
  match Binary.parse b with
  | .ok c => match Project.projectX c with
    | some w => .ok w
    | none => .error "the component is outside the domain of the projection"
  | .error _ => .error "malformed component"

/-- `wasm-wit project` on component WAT: `Project.projectX` of `Wat.readIds`
(the reader with `$identifiers`). -/
def projectWatX (t : String) : Except String Project.WorldType :=
  match Wat.readIds t with
  | some c => match Project.projectX c with
    | some w => .ok w
    | none => .error "the component is outside the domain of the projection"
  | none => .error "not component WAT this reader accepts"

end Silmaril.Wasm.Wit.Tool
