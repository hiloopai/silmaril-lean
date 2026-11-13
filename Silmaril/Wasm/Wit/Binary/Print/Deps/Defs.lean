module

public import Silmaril.Wasm.Wit.Binary.Print.Defs
public import Silmaril.Wasm.Wit.Binary.Custom.Defs

/-!
# WIT text of a binary with its dependency packages

`wasm-tools component wit` prints the main package of a WIT binary and then, as
nested `package ns:name@version { … }` blocks, the foreign packages whose
interfaces the binary shows. This module adds the second part to
`Binary.printPackage` (wit-component 0.263.0, `src/printing.rs`, `WitPrinter::print`
with `nested`, and the package order of `src/decoding.rs`, `WitPackageDecoder::finish`).

* `itemEnvs`: the interfaces each exported item of a WIT binary shows, in binary
  order (`topViews` of `Binary.Custom`);
* `foreignPackages`: the foreign interfaces, merged per name (types in order of
  first appearance, functions from the views that have them), grouped by package
  in order of first appearance, then ordered so that a package comes after the
  packages its interfaces `use` (a depth-first visit, as `finish` does);
* `printPackageAll`: the main package (`printPackage`) followed by the nested
  packages, separated by two blank lines.

Unverified, like `printPackage`: a transcription tested differentially against
`wasm-tools component wit` (`tests/wasm-wit/differential.sh`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary

/-- The interfaces each exported item of a WIT binary's item sections shows, in
binary order (the world views first within an item, as `decodeEnv`). -/
def itemEnvs : List Section → Except String (List Env)
  | .types [.component ds] :: _ :: rest => do
    let (a, b) ← topViews ds
    let r ← itemEnvs rest
    pure ((a ++ b) :: r)
  | _ => pure []

/-- Merge a view of an interface into what is known of it: new types and
functions are appended. -/
def mergeView (b v : Interface) : Interface :=
  { b with
    types := b.types ++ v.types.filter fun t => !b.types.any (·.name == t.name)
    funcs := b.funcs ++ v.funcs.filter fun f => !b.funcs.any (·.name == f.name) }

/-- Add a view to an environment, merging with an earlier view of the same interface. -/
def addView (env : Env) (v : IfaceName × Interface) : Env :=
  if env.any (·.1 == v.1) then env.map fun e => if e.1 == v.1 then (e.1, mergeView e.2 v.2) else e
  else env ++ [v]

/-- The foreign packages of a list of views, grouped by package in order of first
appearance. -/
def groupByPackage (env : Env) : List (PackageName × List (String × Interface)) :=
  env.foldl (init := []) fun gs (i, b) =>
    if gs.any (·.1 == i.pkg) then gs.map fun g => if g.1 == i.pkg then (g.1, g.2 ++ [(i.name, b)]) else g
    else gs ++ [(i.pkg, [(i.name, b)])]

/-- The packages the interfaces of a package `use` types from. -/
def pkgDeps (p : PackageName) (ifs : List (String × Interface)) : List PackageName :=
  ifs.flatMap fun (_, b) => b.types.filterMap fun td =>
    match Print.useOf td with
    | some (j, _) => if j.pkg == p then none else some j.pkg
    | none => none

/-- Depth-first visit of package `p` (its dependencies first), with fuel. -/
def visitPkg (gs : List (PackageName × List (String × Interface))) :
    Nat → List PackageName → PackageName → List PackageName
  | 0, order, _ => order
  | f + 1, order, p =>
    if order.contains p then order
    else match gs.find? (·.1 == p) with
      | none => order
      | some (_, ifs) =>
        let order := (pkgDeps p ifs).foldl (visitPkg gs f) order
        if order.contains p then order else order ++ [p]

/-- The foreign packages a binary shows, in wit-component's order. -/
def foreignPackages (main : PackageName) (envs : List Env) :
    List (PackageName × List (String × Interface)) :=
  let env := (envs.flatten.filter (·.1.pkg != main)).foldl addView []
  let gs := groupByPackage env
  let order := gs.foldl (fun o g => visitPkg gs (gs.length + 1) o g.1) []
  order.filterMap fun p => gs.find? (·.1 == p)

namespace Print

/-- `print_package` of a nested (dependency) package. -/
def nested (p : PackageName) (ifs : List (String × Interface)) : PM Unit := do
  str "package"; str " "; name p.ns; str ":"; name p.name
  match p.version with
  | some v => name ("@" ++ v)
  | none => pure ()
  indentStart
  for (n, b) in ifs do
    docs b.docs; stability b.stability
    str "interface"; str " "; name n
    indentStart; iface p b; indentEnd
  indentEnd

/-- `WitPrinter::print`: the main package, then the nested packages. -/
def all (p : Package) (ns : List (PackageName × List (String × Interface))) : PM Unit := do
  package p
  for ((q, ifs), k) in ns.zipIdx do
    if k > 0 then newline; newline
    nested q ifs

end Print

/-- The WIT text of a package with the nested dependency packages, as `wasm-tools
component wit` prints a WIT binary (unverified). -/
def printPackageAll (p : Package) (ns : List (PackageName × List (String × Interface))) : String :=
  ((Print.all p ns).run {}).2.out

/-- The foreign packages a WIT binary shows. -/
def decodeForeign (b : ByteArray) (main : PackageName) :
    Except String (List (PackageName × List (String × Interface))) := do
  match parse b with
  | .ok (.mk ss) => pure (foreignPackages main (← itemEnvs (splitCustom ss).1))
  | .error _ => throw "malformed component"

end Silmaril.Wasm.Wit.Binary
