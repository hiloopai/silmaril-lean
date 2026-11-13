module

public import Silmaril.Wasm.Component.Codec.Defs
public import Silmaril.Wasm.JcoTool.WitOf.Defs
public import Silmaril.Wasm.Wit.Binary.DecodeLax.Defs
public import Silmaril.Wasm.Wac.WitDir.Defs
public import Silmaril.Wasm.JcoTool.WorldMerge.Defs
public import Silmaril.Wasm.Component.BinaryP3.Defs

/-!
# `wasm-tools component wit`: core modules, `--no-docs`, `--out-dir`, `--features`

Pieces of `WitOpts::run` (`src/bin/wasm-tools/component.rs` of wasm-tools 1.262.0) on top of
the WIT printer and encoder of `wasm-wit`:

* `witOfPayload`: the WIT of a core module's `component-type` section. Upstream decodes it with
  `metadata::decode` and prints the resolve as for a component: the package `root:root` with
  the world `root` (the world's imports and exports), then the packages the world's items come
  from, nested, **with the embedded world** in its own package (`nestedW`).
* `stripDocs`: `WitPrinter::emit_docs(false)`. The printer writes a doc comment as one line
  `///…` per doc line (`Print.doc`) and nothing else starts with `///`, so dropping those
  lines is printing without docs (`stripDocs_*` in the theorems).
* `outDirFiles`: `--out-dir DIR`: one file per package of the resolve, printed alone (no
  nested packages), the main package in `DIR`, the others in `DIR/deps`, named by the
  smallest part of `ns:name@version` that tells them apart (upstream's classification by
  name and namespace).
* `encodeTextXF`: `WitDir.encodeTextX` with the feature list of `--features`; `allFeatures`
  lists the features the sources' `@unstable(feature = …)` gates name (`--all-features`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.WitText

open Silmaril.Wasm.Wit.Binary (Package PackageName Interface World WorldFull IfaceName)
open Silmaril.Wasm.Wit.Binary.Print (PM str name indentStart indentEnd docs stability iface world)

/-! ## The WIT of a core module -/

/-- The package upstream names a core module's world after. -/
def rootRoot : PackageName := ⟨"root", "root", none⟩

/-- The WIT package (as bytes) whose world `root` of package `root:root` has the component type
`wt`. -/
def rootPackage (wt : List Silmaril.Wasm.Component.Binary.ComponentDecl) : Except String ByteArray :=
  match Silmaril.Wasm.Component.Codec.encodeMvp (.mk (Silmaril.Wasm.Wit.Binary.itemSections 0 "root"
      (Silmaril.Wasm.Wit.Binary.worldWrapper rootRoot "root" wt))) with
  | some b => .ok b
  | none => .error "a number or size exceeds 2^32"

/-- `print_package` of a nested package with its interfaces and worlds. -/
def nestedW (p : PackageName) (ifs : List (String × Interface)) (ws : List (String × World)) :
    PM Unit := do
  str "package"; str " "; name p.ns; str ":"; name p.name
  match p.version with
  | some v => name ("@" ++ v)
  | none => pure ()
  indentStart
  for (n, b) in ifs do
    docs b.docs; stability b.stability
    str "interface"; str " "; name n
    indentStart; iface p b; indentEnd
  for (n, w) in ws do
    docs w.docs; stability w.stability
    str "world"; str " "; name n
    indentStart; world p w; indentEnd
  indentEnd

/-- The nested packages, the world `w` of package `wp` added to its package (appended as a
package of its own when no interface of it is shown). -/
def withWorld (ns : List (PackageName × List (String × Interface))) (wp : PackageName)
    (w : String × World) : List (PackageName × List (String × Interface) × List (String × World)) :=
  let xs := ns.map fun (q, ifs) => (q, ifs, if q == wp then [w] else [])
  if ns.any (·.1 == wp) then xs else xs ++ [(wp, [], [w])]

/-- The text: the main package, then the nested packages separated by a blank line. -/
def printAllW (p : Package)
    (ns : List (PackageName × List (String × Interface) × List (String × World))) : String :=
  let m : PM Unit := do
    Silmaril.Wasm.Wit.Binary.Print.package p
    for ((q, ifs, ws), k) in ns.zipIdx do
      if k > 0 then Silmaril.Wasm.Wit.Binary.Print.newline; Silmaril.Wasm.Wit.Binary.Print.newline
      nestedW q ifs ws
  (m.run {}).2.out

/-- **`component wit` of a core module's `component-type` payload**. -/
def witOfPayload (pl : ByteArray) : Except String String := do
  let wf ← Silmaril.Wasm.Wit.Binary.decodeWorldFull pl
  let pb ← rootPackage wf.decls
  let p ← Silmaril.Wasm.Wit.Binary.decodePackage pb
  let ns ← Silmaril.Wasm.Wit.Binary.decodeForeign pb p.name
  pure (printAllW p (withWorld ns wf.pkg (wf.name, wf.world)))

/-- A WIT package binary with its async functions given the async form of their names
(`Binary.normSections`), encoded again: how wit-component 0.262's plain names (an async function
type under the name `f`) reach the strict decoder. `none` when the bytes do not parse or the
normalized component does not encode. -/
def laxPackageBytes (b : ByteArray) : Option ByteArray :=
  match Silmaril.Wasm.Component.Codec.decodeMvp b with
  | .ok (.mk ss) => Silmaril.Wasm.Component.Codec.encodeMvp (.mk (Silmaril.Wasm.Wit.Binary.normSections ss))
  | .error _ => none

/-- A component read by the `BinaryP3` grammar (async and threading built-ins included) as the
older syntax the projection takes, without its `canon` sections and nested components, which
the projection skips (`Project.isCode`): the sections it reads are the same in both syntaxes. -/
def withoutCanons (c : Silmaril.Wasm.Component.BinaryP3.Ast) : Silmaril.Wasm.Component.Binary.Ast :=
  .mk (c.sections.filterMap fun
    | .custom n d => some (.custom n d)
    | .coreModule b => some (.coreModule b)
    | .coreInstances xs => some (.coreInstances xs)
    | .coreTypes xs => some (.coreTypes xs)
    | .instances xs => some (.instances xs)
    | .aliases xs => some (.aliases xs)
    | .types xs => some (.types xs)
    | .start x => some (.start x)
    | .imports xs => some (.imports xs)
    | .exports xs => some (.exports xs)
    | .values xs => some (.values xs)
    | .canons _ | .component _ => none)

/-- The projection of a component that only the `BinaryP3` grammar reads (`withoutCanons`). -/
def projectP3 (b : ByteArray) : Option Silmaril.Wasm.Wit.Project.WorldType :=
  match Silmaril.Wasm.Component.Codec.decodeLax b with
  | .ok c => Silmaril.Wasm.Wit.Project.projectX (withoutCanons c)
  | .error _ => none

mutual
/-- A component read by the `BinaryP3` grammar in the older syntax wac's inference takes: the
built-ins the older syntax has (`lift`, `lower`, `resource.*`) kept, the others dropped. They
define core functions only, which the inference skips (`Wac.TypeOf.canon_` reads `lift` alone),
and no section the inference reads refers to core functions. -/
def toV0 : Silmaril.Wasm.Component.BinaryP3.Ast → Silmaril.Wasm.Component.Binary.Ast
  | .mk ss => .mk (toV0Sections ss)

def toV0Sections : List Silmaril.Wasm.Component.BinaryP3.Section →
    List Silmaril.Wasm.Component.Binary.Section
  | [] => []
  | s :: ss =>
    let rest := toV0Sections ss
    match s with
    | .custom n d => .custom n d :: rest
    | .coreModule b => .coreModule b :: rest
    | .coreInstances xs => .coreInstances xs :: rest
    | .coreTypes xs => .coreTypes xs :: rest
    | .component c => .component (toV0 c) :: rest
    | .instances xs => .instances xs :: rest
    | .aliases xs => .aliases xs :: rest
    | .types xs => .types xs :: rest
    | .canons xs => .canons (xs.filterMap fun
        | .lift f o t => some (.lift f o t)
        | .lower f o => some (.lower f o)
        | .resourceNew t => some (.resourceNew t)
        | .resourceDrop t => some (.resourceDrop t)
        | .resourceRep t => some (.resourceRep t)
        | _ => none) :: rest
    | .start x => .start x :: rest
    | .imports xs => .imports xs :: rest
    | .exports xs => .exports xs :: rest
    | .values xs => .values xs :: rest
end

/-- `JcoTool.WitOf.inferredDecls` on a component the `BinaryP3` grammar reads (`toV0`). -/
def inferredDeclsP3 (b : ByteArray) : Except String (List Silmaril.Wasm.Component.Binary.ComponentDecl) := do
  let c ← match Silmaril.Wasm.Component.Codec.decodeLax b with
    | .ok c => pure (toV0 c)
    | .error _ => throw "malformed component"
  let (pt, nom) ← Silmaril.Wasm.Wac.TypeOf.typeOf c
  if let some n := JcoTool.WitOf.sharedTypeName pt then
    throw s!"type `{n}` declared by two interfaces (wac's kinds do not say whether they are one type)"
  if let some n := JcoTool.WitOf.implementsName pt then
    throw s!"instance `{n}` names an interface of another name (WIT `implements`): not supported"
  if let some n := JcoTool.WitOf.nomClash nom then
    throw s!"two different types named `{n}` (wac's type encoder looks types up by name)"
  let m : Silmaril.Wasm.Wac.Bridge.TM Unit := do
    Silmaril.Wasm.Wac.Bridge.importDecls pt.imports
    Silmaril.Wasm.Wac.Bridge.exportDecls pt.exports
  match m.run { nom := nom } with
  | .ok ((), s) => pure s.decls
  | .error e => throw e

/-- **`component wit` of a component**: `JcoTool.WitOf.componentWit`, with the component type's
async functions given the async form of their names (`Binary.normCompDecls`, as
`decodeWorldTypeLax` reads wit-component 0.262's plain names) before the WIT decoder reads it
(the decoder rejects an async function type under a plain name). -/
def componentWit (b : ByteArray) : Except String String :=
  if JcoTool.WitOf.isWitPackage b then
    match Silmaril.Wasm.Wit.Tool.witAll b with
    | .ok t => .ok t
    | .error e => match laxPackageBytes b with
      | some b' => (Silmaril.Wasm.Wit.Tool.witAll b').mapError fun _ => e
      | none => .error e
  else do
    let wt ← match Silmaril.Wasm.Wit.Tool.projectBytesX b with
      | .ok wt => pure wt
      | .error e => match projectP3 b with
        | some wt => pure wt
        | none => match JcoTool.WitOf.inferredDecls b with
          | .ok wt => pure wt
          | .error e' => match inferredDeclsP3 b with
            | .ok wt => pure wt
            | .error e'' => throw s!"{e}; by inference: {if e' == "malformed component" then e'' else e'}"
    let pb ← JcoTool.WitOf.worldPackage (Silmaril.Wasm.Wit.Binary.normCompDecls [] wt)
    Silmaril.Wasm.Wit.Tool.witAll pb

/-- `metadata::decode` of several `component-type` sections: the worlds merged into the first
(imports and exports united by key, interface bodies united, interfaces renamed to their
canonical semver-compatible name, imports in dependency order: `JcoTool.WorldMerge`'s
`unionItems`, `canon`, `topo`), encoded and decoded again; one world is returned as it is. -/
def mergeWorlds : List WorldFull → Except String WorldFull
  | [] => throw "no component-type custom section"
  | [w] => pure w
  | wfs@(w0 :: _) => do
    let allNames := wfs.flatMap fun wf => JcoTool.WorldMerge.ifaceNames (wf.imports ++ wf.exports)
    let rn := JcoTool.WorldMerge.canon allNames
    let imps := JcoTool.WorldMerge.topo (JcoTool.WorldMerge.unionItems
      (wfs.map fun wf => wf.imports.map (JcoTool.WorldMerge.DItem.rn rn)))
    let exps := JcoTool.WorldMerge.unionItems
      (wfs.map fun wf => wf.exports.map (JcoTool.WorldMerge.DItem.rn rn))
    let env : Silmaril.Wasm.Wit.Binary.Env := (exps ++ imps).filterMap fun
      | .iface (.inl i) b => some (i, b)
      | _ => none
    let w : World := { imports := imps.map Silmaril.Wasm.Wit.Binary.DItem.toWorldItem,
                       exports := exps.map Silmaril.Wasm.Wit.Binary.DItem.toWorldItem }
    let payload ← Silmaril.Wasm.Wit.Binary.encodeWorldType env w0.pkg w0.name w w0.encoding
    Silmaril.Wasm.Wit.Binary.decodeWorldFull payload

/-- The world key of an item and its kind (`0` interface, `1` function, `2` type). -/
def itemKind : Silmaril.Wasm.Wit.Binary.DItem → String × Nat
  | .iface (.inl i) _ => (i.id, 0)
  | .iface (.inr n) _ => (n, 0)
  | .func f => (f.mangled, 1)
  | .type t => (t.name, 2)

/-- The first item of `ys` whose key is that of an item of `xs` of another kind. -/
def kindClash (xs ys : List Silmaril.Wasm.Wit.Binary.DItem) : Option String :=
  (ys.find? fun y => xs.any fun x =>
    (itemKind x).1 == (itemKind y).1 && (itemKind x).2 != (itemKind y).2).map (itemKind · |>.1)

/-- `Resolve::merge_worlds`' first check, as `component embed` runs it on a module that already
has `component-type` sections: an import (export) of the new world named like an import
(export) of an embedded one of another kind fails with upstream's message. (Its checks that a
merge changes the meaning of exports are not implemented.) -/
def mergeConflict (old : List WorldFull) (new : WorldFull) : Option String :=
  let pre := "updating metadata for section component-type\n\nCaused by:\n    0: failed to merge worlds from two documents\n    1: "
  let imps := old.flatMap (·.imports)
  let exps := old.flatMap (·.exports)
  match kindClash imps new.imports with
  | some n => some (pre ++ s!"failed to merge world import {n}\n    2: different kinds of items")
  | none => match kindClash exps new.exports with
    | some n => some (pre ++ s!"failed to merge world export {n}\n    2: different kinds of items")
    | none => exportChange (imps ++ new.imports) imps exps new.exports |>.map (pre ++ ·)

where
  /-- The interfaces an item depends on, transitively (bodies looked up in `env`). -/
  trans (env : List Silmaril.Wasm.Wit.Binary.DItem) : Nat → List IfaceName → List IfaceName → List IfaceName
    | 0, acc, _ => acc
    | _ + 1, acc, [] => acc
    | fuel + 1, acc, i :: is =>
      if acc.contains i then trans env fuel acc is
      else
        let more := match env.find? (fun x => (itemKind x).1 == i.id) with
          | some x => JcoTool.WorldMerge.depsOf x
          | none => []
        trans env fuel (acc ++ [i]) (is ++ more)
  /-- `merge_worlds`' semantic checks of added exports: an added interface export that an
  existing export uses through an import, or an added export that uses, through imports, an
  interface the world exports. -/
  exportChange (env imps exps news : List Silmaril.Wasm.Wit.Binary.DItem) : Option String :=
    let keys := exps.map (itemKind · |>.1)
    let added := news.filter fun x => !keys.contains (itemKind x).1
    added.findSome? fun x =>
      let k := (itemKind x).1
      let usedBy := exps.find? fun e =>
        imps.any (fun i => (itemKind i).1 == k) &&
          (trans env 64 [] (JcoTool.WorldMerge.depsOf e)).any (·.id == k)
      match usedBy with
      | some e => some s!"failed to add export `{k}`\n    2: export `{(itemKind e).1}` depends on `{k}` previously as an import which will change meaning if `{k}` is added as an export"
      | none =>
        match (trans env 64 [] (JcoTool.WorldMerge.depsOf x)).find? (fun i => keys.contains i.id) with
        | some i => some s!"failed to add export `{k}`\n    2: failed validating export of `{k}`\n    3: world exports `{i.id}` but it's also transitively used by an import which means that this is not valid"
        | none => none

/-- The nested packages with every embedded world added to its package (each name once). -/
def withWorlds (ns : List (PackageName × List (String × Interface))) :
    List (PackageName × String × World) →
    List (PackageName × List (String × Interface) × List (String × World))
  | [] => ns.map fun (q, ifs) => (q, ifs, [])
  | ws =>
    let pkgs := (ns.map (·.1) ++ ws.map (·.1)).eraseDups
    pkgs.map fun q =>
      ((ns.find? (·.1 == q)).map (·.2) |>.getD [],
        ws.filter (·.1 == q) |>.map (fun (_, n, w) => (n, w)) |>.foldl
          (fun acc (n, w) => if acc.any (·.1 == n) then acc else acc ++ [(n, w)]) [])
      |> fun (ifs, wss) => (q, ifs, wss)

/-- **`component wit` of a core module with its `component-type` sections**: the merged world as
`root:root/root`, then the packages, with the embedded worlds. -/
def witOfSections (pls : List ByteArray) : Except String String := do
  let wfs ← pls.mapM Silmaril.Wasm.Wit.Binary.decodeWorldFull
  let wf ← mergeWorlds wfs
  let pb ← rootPackage wf.decls
  let p ← Silmaril.Wasm.Wit.Binary.decodePackage pb
  let ns ← Silmaril.Wasm.Wit.Binary.decodeForeign pb p.name
  pure (printAllW p (withWorlds ns (wfs.map fun w => (w.pkg, w.name, w.world))))

/-! ## `--no-docs` -/

/-- Is the line a doc comment line of the printer (indentation, then `///`)? -/
def isDocLine (l : String) : Bool := l.trimAsciiStart.toString.startsWith "///"

/-- The lines of a text that are not doc comment lines. -/
def docFree (t : String) : List String := (t.splitOn "\n").filter (!isDocLine ·)

/-- **`--no-docs`**: the printed text without its doc comment lines. -/
def stripDocs (t : String) : String := "\n".intercalate (docFree t)

/-! ## `--out-dir` -/

/-- The file stem of package `p` among the packages `ps` (upstream's classification). -/
def stem (ps : List PackageName) (p : PackageName) : String :=
  let sameName := ps.filter (·.name == p.name)
  let namespaces := sameName.map (·.ns) |>.eraseDups
  let sameNs := (sameName.filter (·.ns == p.ns)).length
  if namespaces.length == 1 then
    if sameNs == 1 then p.name
    else match p.version with
      | some v => p.name ++ "@" ++ v
      | none => p.name
  else if sameNs == 1 then p.ns ++ ":" ++ p.name
  else s!"{p.ns}:{p.name}" ++ (p.version.map ("@" ++ ·)).getD ""

/-- A package of its own, from a nested package's interfaces. -/
def asPackage (q : PackageName) (ifs : List (String × Interface)) : Package :=
  { name := q, interfaces := ifs }

/-- **`--out-dir`** of a WIT package binary: `(deps?, stem, text)` per package, the dependency
packages first (in the resolve's order: dependencies before the package that uses them), then
the main package. -/
def outDirFiles (b : ByteArray) : Except String (List (Bool × String × String)) := do
  let p ← Silmaril.Wasm.Wit.Binary.decodePackage b
  let ns ← Silmaril.Wasm.Wit.Binary.decodeForeign b p.name
  let names := ns.map (·.1) ++ [p.name]
  let deps := ns.map fun (q, ifs) =>
    (true, stem names q, Silmaril.Wasm.Wit.Binary.printPackage (asPackage q ifs))
  pure (deps ++ [(false, stem names p.name, Silmaril.Wasm.Wit.Binary.printPackage p)])

/-! ## Comments as documentation -/

/-- One line with its first `//` comment written as a doc comment `///` (unchanged when it has
none, or when the comment already starts with `///`). -/
def lineDocs (l : String) : String :=
  match l.splitOn "//" with
  | a :: b :: rest =>
    if b.startsWith "/" then l else a ++ "///" ++ "//".intercalate (b :: rest)
  | _ => l

/-- **wit-parser 0.262 reads every comment before an item as its documentation**
(`parse_docs` collects every `Token::Comment`, and `docs` strips the leading slashes), so
`// x` documents the next item as `/// x` does. `wasm-wit`'s lexer reads only `///` as
documentation; this rewrites line comments `// x` as `/// x` so that it reads them as
wit-parser does (block comments are left alone). -/
def commentsAsDocs (t : String) : String := "\n".intercalate ((t.splitOn "\n").map lineDocs)

/-! ## `--features`, `--all-features` -/

/-- `WitDir.encodeTextX` with the features `fs` enabled. -/
def encodeTextXF (main : List (String × String)) (deps : List (List (String × String)))
    (fs : List String) : Except String ByteArray :=
  let ext : Except String ByteArray := do
    let d ← Wac.WitDir.parseFiles main
    let ds ← deps.mapM Wac.WitDir.parseFiles
    Wit.Tool.encodeDocs d ds fs
  match main, deps.all (·.length == 1) with
  | [m], true =>
    match Wit.Tool.encodeText m (deps.flatMap id) fs with
    | .ok b => .ok b
    | .error _ => ext
  | _, _ => ext

/-- The features named by `@unstable(feature = f)` in a text (as tokens: `@`, `unstable`, `(`,
`feature`, `=`, the name). -/
def gateFeatures (t : String) : List String :=
  let toks := (t.split (fun c => c.isWhitespace || c == '(' || c == ')' || c == '=')).toList.map
    (·.toString) |>.filter (· ≠ "")
  let rec go : List String → List String
    | "@unstable" :: "feature" :: f :: r => f :: go r
    | _ :: r => go r
    | [] => []
  go toks

/-- The features of every gate of the sources (`--all-features`), without repetition. -/
def allFeatures (main : List (String × String)) (deps : List (List (String × String))) :
    List String :=
  ((main ++ deps.flatten).flatMap fun (_, t) => gateFeatures t).eraseDups

end Silmaril.Wasm.Tools.Component.WitText
