module

public import Silmaril.Wasm.Wac.Alias.Defs

/-!
# WAC: test cases of wac's own test suites

Documents and package registries transcribed from wac's tests (wac `5a7480c`), for the
features of the elaborator added . The expected results are checked in
`Silmaril.Wasm.Wac.WacTests.Thms`.

* `crates/wac-graph/tests/graphs/semver-highest-version-retained`: two instantiations
  wanting `foo:bar/types@0.2.1` and `foo:bar/types@0.2.0`; one merged implicit import
  under the higher name (`higherDoc`; `lowerFirstDoc` swaps the order, so the merged
  import is renamed).

Package types are written by hand from the `.wat`/`.wit` files of each test: a record
`x` is the reference `x` (records are compared by name, see `docs/projects/wasm-components.md`), a
resource is `.resource`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.WacTests

open Silmaril.Wasm.Wac Silmaril.Wasm.Wac.Syntax
open Silmaril.Wasm.Wit.Binary (Ty TyRef Owner)

/-! ## `semver-highest-version-retained` -/

/-- The record `x` of `foo:bar/types`. -/
def xRef : Ty := .ref ⟨.local, "x"⟩

/-- `foo:bar/types@0.2.1` as `test:higher` imports it: the resource `w`. -/
def typesHigh : Kind := .inst none [("w", .type (.resource "w"))]

/-- `foo:bar/types@0.2.0` as `test:lower` imports it: `x`, `y: func(x: x)`, `z`. -/
def typesLow : Kind := .inst none [("x", .type (.value xRef)),
  ("y", .func ⟨false, [("x", xRef)], none⟩), ("z", .type (.resource "z"))]

def semverEnv : PkgEnv := [
  ("test:higher", { imports := [("foo:bar/types@0.2.1", typesHigh)] }),
  ("test:lower", { imports := [("foo:bar/types@0.2.0", typesLow)] })]

/-- `let a = new test:higher { ... }; let b = new test:lower { ... };` -/
def higherDoc : Document := { pkg := ⟨"test:comp", none⟩, stmts := [
  .let "a" (.new ⟨"test:higher", none⟩ [.fill]),
  .let "b" (.new ⟨"test:lower", none⟩ [.fill])] }

/-- The same, lower version first. -/
def lowerFirstDoc : Document := { pkg := ⟨"test:comp", none⟩, stmts := [
  .let "b" (.new ⟨"test:lower", none⟩ [.fill]),
  .let "a" (.new ⟨"test:higher", none⟩ [.fill])] }

/-- An explicit import `foo:bar/types@0.2.1` beside an instantiation wanting `@0.2.0`
implicitly: wac merges the two, this elaborator rejects (documented restriction). -/
def explicitSemverDoc : Document := { pkg := ⟨"test:comp", none⟩, stmts := [
  .import { id := "t", as := some "foo:bar/types@0.2.1", ty := .iface [] },
  .let "b" (.new ⟨"test:lower", none⟩ [.fill])] }

/-! ## WIT syntax helpers -/

/-- `n: func(ps) -> r` in an interface. -/
def fnI (n : String) (ps : List (String × Wit.Ty) := []) (r : Option Wit.Ty := none) : Wit.IfaceItem :=
  .func { name := n, func := { params := ps, result := r } }

/-- A type declaration. -/
def tyI (n : String) (k : Wit.TypeDefKind) : Wit.TypeDef := { name := n, kind := k }

/-- `use path.{names}`. -/
def useOf (p : Wit.UsePath) (ns : List (String × Option String)) : Wit.Use :=
  { path := p, names := ns.map fun (n, a) => { name := n, as := a } }

/-- `import e;` / `export e;` in a world. -/
def impW (e : Wit.Extern) : Wit.WorldItem := .import { ext := e }
def expW (e : Wit.Extern) : Wit.WorldItem := .export { ext := e }

/-- `include path with { a as b, … }`. -/
def inclW (p : Wit.UsePath) (ns : List (String × String) := []) : Wit.WorldItem :=
  .include { path := p, names := ns.map fun (n, a) => { name := n, as := a } }

/-- The package `foo:bar`. -/
def fooBar : Wit.PackageName := { ns := "foo", name := "bar" }

/-- A document of type statements. -/
def declDoc (pkg : String) (ts : List TypeStmt) (targets : Option PkgPath := none) (more : List Stmt := []) :
    Document :=
  { pkg := ⟨pkg, none⟩, targets, stmts := ts.map .type ++ more }

/-! ## `resource.wac`: an alias of a resource -/

/-- `interface foo { resource x; type x2 = x;
f3: func(x: x, x2: x2, x3: borrow<x>, x4: borrow<x2>); }` -/
def resourceDoc : Document := declDoc "test:comp" [.iface { name := "foo", items := [
  .type (tyI "x" (.resource [])), .type (tyI "x2" (.alias (.named "x"))),
  fnI "f3" [("x", .named "x"), ("x2", .named "x2"), ("x3", .borrow "x"), ("x4", .borrow "x2")]] }]

/-! ## `types.wac`: `use` and `include` -/

/-- `foo:bar/i` (a record `r`) and the world `foo:bar/baz`. -/
def typesEnv : PkgEnv := [("foo:bar", { defs := [
  ("i", .type (.inst (some "foo:bar/i") [("r", .type (.value (.ref ⟨.local, "r"⟩)))])),
  ("baz", .type (.comp (some "foo:bar/baz") [("b", .func ⟨false, [], none⟩)] [("e", .func ⟨false, [], none⟩)]))] })]

/-- ```
interface i { record r { x: u32 } x: func(); }
interface i2 { use i.{r}; use i.{r as z}; }
type x = u32;
type t2 = x;
world w1 { use foo:bar/i.{r}; import a: func(); import i;
  export d: interface { x: func(); }; export i2; }
world w2 { include w1; include foo:bar/baz; resource res { constructor(); } }
``` -/
def typesDoc : Document := declDoc "test:comp" [
  .iface { name := "i", items := [.type (tyI "r" (.record [{ name := "x", ty := .u32 }])), fnI "x"] },
  .iface { name := "i2", items := [.use (useOf (.local "i") [("r", none)]), .use (useOf (.local "i") [("r", some "z")])] },
  .type (tyI "x" (.alias .u32)),
  .type (tyI "t2" (.alias (.named "x"))),
  .world { name := "w1", items := [.use (useOf (.foreign fooBar "i") [("r", none)]),
    impW (.func "a" {}), impW (.path (.local "i")),
    expW (.iface "d" [fnI "x"]), expW (.path (.local "i2"))] },
  .world { name := "w2", items := [inclW (.local "w1"), inclW (.foreign fooBar "baz"),
    .type (tyI "res" (.resource [{ kind := .ctor, func := {} }]))] }]

/-! ## `package-use-item`, `package-world-include`, `package-world-item` -/

def pkgItemsEnv : PkgEnv := [
  ("foo:bar", { defs := [
    ("baz", .type (.inst (some "foo:bar/baz") [("a", .type (.value (.prim .u32))),
      ("b", .type (.resource "b")), ("c", .type (.value (.ref ⟨.local, "c"⟩)))])),
    ("qux", .type (.inst (some "foo:bar/qux") [("x", .type (.value (.prim .string))),
      ("y", .type (.resource "y")), ("z", .type (.value (.ref ⟨.local, "z"⟩)))])),
    ("w", .type (.comp (some "foo:bar/w") [("f", .func ⟨false, [], none⟩)] []))] }),
  ("bar:baz", { defs := [("qux", .type (.inst (some "bar:baz/qux") [("g", .func ⟨false, [], none⟩)]))] })]

/-- `interface i { use foo:bar/baz.{a, b, c}; } world w { use foo:bar/qux.{x, y, z}; }` -/
def pkgUseDoc : Document := declDoc "test:comp" [
  .iface { name := "i", items := [.use (useOf (.foreign fooBar "baz") [("a", none), ("b", none), ("c", none)])] },
  .world { name := "w", items := [.use (useOf (.foreign fooBar "qux") [("x", none), ("y", none), ("z", none)])] }]

/-- `world w { include foo:bar/w; }` -/
def pkgIncludeDoc : Document := declDoc "test:comp" [.world { name := "w", items := [inclW (.foreign fooBar "w")] }]

/-- `world w { import foo:bar/baz; export bar:baz/qux; }` -/
def pkgWorldItemDoc : Document := declDoc "test:comp" [.world { name := "w", items := [
  impW (.path (.foreign fooBar "baz")), expW (.path (.foreign { ns := "bar", name := "baz" } "qux"))] }]

/-! ## Failures of `use`, `include` and world items (`fail/`) -/

/-- `duplicate-interface-export`: `interface x { x: func(); x: func(); }` -/
def dupIfaceExportDoc : Document := declDoc "test:comp" [.iface { name := "x", items := [fnI "x", fnI "x"] }]

/-- `duplicate-name-in-include`: `world w1 {} world w2 { include w1 with { a as b, a as c }; }` -/
def dupIncludeNameDoc : Document := declDoc "test:comp" [.world { name := "w1", items := [] },
  .world { name := "w2", items := [inclW (.local "w1") [("a", "b"), ("a", "c")]] }]

/-- `duplicate-use-in-interface`: `interface i { type x = u32; } interface i2 { x: func(); use i.{x}; }` -/
def dupUseIfaceDoc : Document := declDoc "foo:bar" [.iface { name := "i", items := [.type (tyI "x" (.alias .u32))] },
  .iface { name := "i2", items := [fnI "x", .use (useOf (.local "i") [("x", none)])] }]

/-- `duplicate-use-in-world`: `interface i { type x = u32; } world w { import x: func(); use i.{x}; }` -/
def dupUseWorldDoc : Document := declDoc "foo:bar" [.iface { name := "i", items := [.type (tyI "x" (.alias .u32))] },
  .world { name := "w", items := [impW (.func "x" {}), .use (useOf (.local "i") [("x", none)])] }]

/-- `duplicate-world-export`: `world w { export x: func(); export x: func(); }` -/
def dupWorldExportDoc : Document := declDoc "test:comp" [.world { name := "w", items := [expW (.func "x" {}), expW (.func "x" {})] }]

/-- `duplicate-world-import`: `world w { import x: func(); import x: func(); }` -/
def dupWorldImportDoc : Document := declDoc "test:comp" [.world { name := "w", items := [impW (.func "x" {}), impW (.func "x" {})] }]

/-- `invalid-use-alias`: `interface a { type a = u32; } interface b { type b = u32; use a.{a as b}; }` -/
def invalidUseAliasDoc : Document := declDoc "test:comp" [.iface { name := "a", items := [.type (tyI "a" (.alias .u32))] },
  .iface { name := "b", items := [.type (tyI "b" (.alias .u32)), .use (useOf (.local "a") [("a", some "b")])] }]

/-- `invalid-use`: `type x = u32; interface a { use x.{a}; }` -/
def invalidUseDoc : Document := declDoc "test:comp" [.type (tyI "x" (.alias .u32)),
  .iface { name := "a", items := [.use (useOf (.local "x") [("a", none)])] }]

/-- `invalid-world-include` (with a value type in place of wac's function type):
`type x = u32; world w { include x; }` -/
def invalidIncludeDoc : Document := declDoc "test:comp" [.type (tyI "x" (.alias .u32)),
  .world { name := "w", items := [inclW (.local "x")] }]

/-- `missing-type-in-use`: `interface a {} interface b { use a.{x}; }` -/
def missingUseTypeDoc : Document := declDoc "test:comp" [.iface { name := "a", items := [] },
  .iface { name := "b", items := [.use (useOf (.local "a") [("x", none)])] }]

/-- `missing-world-include-name`: `world w1 {} world w2 { include w1 with { a as b }; }` -/
def missingIncludeNameDoc : Document := declDoc "test:comp" [.world { name := "w1", items := [] },
  .world { name := "w2", items := [inclW (.local "w1") [("a", "b")]] }]

/-- `world-include-conflict`: `world w1 { export a: func(); } world w2 { include w1; export a: interface {}; }` -/
def includeConflictDoc : Document := declDoc "test:comp" [.world { name := "w1", items := [expW (.func "a" {})] },
  .world { name := "w2", items := [inclW (.local "w1"), expW (.iface "a" [])] }]

/-- `world-include-with-conflict`: `… include w1 with { a as x }; export x: interface {}; …` -/
def includeWithConflictDoc : Document := declDoc "test:comp" [.world { name := "w1", items := [expW (.func "a" {})] },
  .world { name := "w2", items := [inclW (.local "w1") [("a", "x")], expW (.iface "x" [])] }]

/-- `redefined-name`: `type x = u32; type x = string;` -/
def redefinedDoc : Document := declDoc "test:comp" [.type (tyI "x" (.alias .u32)), .type (tyI "x" (.alias .string))]

/-! ## Alias expansion in type checking -/

/-- A package importing `x` with `f: func(a: u32)`, and one exporting `x` with
`type t = u32; f: func(a: t)`. -/
def aliasEnv : PkgEnv := [
  ("foo:sink", { imports := [("x", .inst none [("f", .func ⟨false, [("a", .prim .u32)], none⟩)])] }),
  ("foo:src", { exports := [("x", .inst none [("t", .type (.value (.prim .u32))),
    ("f", .func ⟨false, [("a", .ref ⟨.local, "t"⟩)], none⟩)])] })]

/-- `import x: interface { type t = u32; f: func(a: t); }; let i = new foo:sink { x };` -/
def aliasDocSide : Document := { pkg := ⟨"test:comp", none⟩, stmts := [
  .import { id := "x", ty := .iface [.type (tyI "t" (.alias .u32)), fnI "f" [("a", .named "t")]] },
  .let "i" (.new ⟨"foo:sink", none⟩ [.inferred "x"])] }

/-- `let s = new foo:src {}; let i = new foo:sink { x: s.x };` -/
def aliasPkgSide : Document := { pkg := ⟨"test:comp", none⟩, stmts := [
  .let "s" (.new ⟨"foo:src", none⟩ []),
  .let "i" (.new ⟨"foo:sink", none⟩ [.named (.ident "x") (.access (.ident "s") "x")])] }

/-! ## `targets` with worlds of the document -/

/-- `func()`. -/
def fUnit : Kind := .func ⟨false, [], none⟩

/-- `targets-world/foo/bar.wat`: imports and exports `f: func()`. -/
def targetsEnv : PkgEnv := [("foo:bar", { imports := [("f", fUnit)], exports := [("f", fUnit)] })]

/-- The path `test:comp/n`. -/
def localPath (n : String) : PkgPath := ⟨"test:comp", [n], none⟩

/-- `targets-world`: ```
package test:comp targets test:comp/world;
world %world { import f: func(); export i: interface { f: func(); }; }
import f: func();
export new foo:bar { f } as i;
``` -/
def targetsWorldDoc : Document := declDoc "test:comp"
  [.world { name := "world", items := [impW (.func "f" {}), expW (.iface "i" [fnI "f"])] }]
  (some (localPath "world"))
  [.import { id := "f", ty := .func {} }, .export (.new ⟨"foo:bar", none⟩ [.inferred "f"]) (.rename "i")]

/-- `targets-empty-world`: `package test:comp targets test:comp/foo; world foo {}` -/
def targetsEmptyDoc : Document := declDoc "test:comp" [.world { name := "foo", items := [] }] (some (localPath "foo"))

/-- `target-export-mismatch`. -/
def targetExportMismatchDoc : Document := declDoc "test:comp"
  [.world { name := "world", items := [impW (.iface "foo" [fnI "foo" [("x", .u32)]]),
    expW (.iface "foo" [fnI "foo" [("x", .string)]])] }]
  (some (localPath "world"))
  [.import { id := "foo", ty := .iface [fnI "foo" [("x", .u32)]] }, .export (.ident "foo") .none]

/-- `target-extraneous-import`: `world foo { import foo: func(); } import bar: func();` -/
def targetExtraneousDoc : Document := declDoc "test:comp" [.world { name := "foo", items := [impW (.func "foo" {})] }]
  (some (localPath "foo")) [.import { id := "bar", ty := .func {} }]

/-- `target-import-mismatch-resource`. -/
def targetResourceDoc : Document := declDoc "test:comp"
  [.world { name := "foo", items := [impW (.iface "foo" [.type (tyI "x" (.resource [{ kind := .ctor, func := {} }]))])] }]
  (some (localPath "foo"))
  [.import { id := "foo2", as := some "foo", ty := .iface [.type (tyI "y" (.resource [{ kind := .ctor, func := {} }]))] }]

/-- `target-import-mismatch`: `world foo { import foo: func(); } import foo2 as foo: interface {};` -/
def targetKindDoc : Document := declDoc "test:comp" [.world { name := "foo", items := [impW (.func "foo" {})] }]
  (some (localPath "foo")) [.import { id := "foo2", as := some "foo", ty := .iface [] }]

/-- `target-import-param-name-mismatch`. -/
def targetParamNameDoc : Document := declDoc "test:comp"
  [.world { name := "foo", items := [impW (.iface "foo" [fnI "foo" [("a", .string)]])] }]
  (some (localPath "foo")) [.import { id := "foo2", as := some "foo", ty := .iface [fnI "foo" [("x", .u32)]] }]

/-- `target-import-param-type-mismatch`. -/
def targetParamTypeDoc : Document := declDoc "test:comp"
  [.world { name := "foo", items := [impW (.iface "foo" [fnI "foo" [("a", .u32)]])] }]
  (some (localPath "foo")) [.import { id := "foo2", as := some "foo", ty := .iface [fnI "foo" [("a", .string)]] }]

/-- `target-import-unexpected-method`. -/
def targetMethodDoc : Document := declDoc "test:comp"
  [.world { name := "foo", items := [impW (.iface "foo" [.type (tyI "x" (.resource [{ kind := .ctor, func := {} }]))])] }]
  (some (localPath "foo"))
  [.import { id := "foo2", as := some "foo", ty := .iface [.type (tyI "x" (.resource
    [{ kind := .ctor, func := {} }, { kind := .method "f", func := { params := [("a", .u32)] } }]))] }]

/-- `target-is-not-a-world`: `interface foo {}` -/
def targetNotWorldDoc : Document := declDoc "test:comp" [.iface { name := "foo", items := [] }] (some (localPath "foo"))

/-- `unknown-targets-path`: nothing named `foo`. -/
def unknownTargetsDoc : Document := declDoc "test:comp" [] (some (localPath "foo"))

/-- `unknown-target-path`: `targets foo:bar/baz` without the package (checked against
the empty registry). -/
def unknownTargetPkgDoc : Document := declDoc "test:comp" [] (some ⟨"foo:bar", ["baz"], none⟩)

/-- `missing-target-export`: `foo:bar/baz` exports `hello: func()`. -/
def missingExportEnv : PkgEnv :=
  [("foo:bar", { defs := [("baz", .type (.comp (some "foo:bar/baz") [] [("hello", fUnit)]))] })]

def missingExportDoc : Document := declDoc "test:comp" [] (some ⟨"foo:bar", ["baz"], none⟩)

/-! ## `targets` and the implicit imports of used interfaces -/

/-- `test:comp/indirect-dependency`. -/
def indirectI : Wit.Binary.IfaceName := ⟨{ ns := "test", name := "comp" }, "indirect-dependency"⟩

/-- `fail/targets-world-use/foo/bar.wat`: its `indirect-dependency` exports a resource
named `other-resource`. -/
def worldUseEnv : PkgEnv := [("foo:bar", { imports := [
  ("test:comp/indirect-dependency", .inst none [("other-resource", .type (.resource "other-resource"))]),
  ("my-resource", .type (.value (.ref ⟨.iface indirectI, "other-resource"⟩))),
  ("my-func", .func ⟨false, [], some (.own ⟨.iface indirectI, "other-resource"⟩)⟩)] })]

/-- `fail/targets-world-use`: ```
package test:comp targets test:comp/foo;
interface indirect-dependency { resource my-resource {} }
world foo { use indirect-dependency.{my-resource}; import my-func: func() -> my-resource; }
let i = new foo:bar { ... };
``` -/
def worldUseDoc : Document := declDoc "test:comp"
  [.iface { name := "indirect-dependency", items := [.type (tyI "my-resource" (.resource []))] },
   .world { name := "foo", items := [.use (useOf (.local "indirect-dependency") [("my-resource", none)]),
     impW (.func "my-func" { result := some (.named "my-resource") })] }]
  (some (localPath "foo")) [.let "i" (.new ⟨"foo:bar", none⟩ [.fill])]

/-- `fail/targets-interface-use/foo/bar.wat`: its `my-variant` has one case (the
document's has two); variants are compared by reference here. -/
def ifaceUseEnv : PkgEnv := [("foo:bar", { imports := [
  ("test:comp/indirect-dependency", .inst none [("my-variant", .type (.value (.ref ⟨.local, "my-variant"⟩)))]),
  ("test:comp/direct-dependency", .inst none [
    ("my-variant", .type (.value (.ref ⟨.iface indirectI, "my-variant"⟩))),
    ("fun", .func ⟨false, [], some (.ref ⟨.iface indirectI, "my-variant"⟩)⟩)])] })]

/-- `fail/targets-interface-use`: ```
package test:comp targets test:comp/foo;
interface indirect-dependency { variant my-variant { foo, bar } }
interface direct-dependency { use indirect-dependency.{my-variant}; fun: func() -> my-variant; }
world foo { import direct-dependency; }
let i = new foo:bar { ... };
``` -/
def ifaceUseDoc : Document := declDoc "test:comp"
  [.iface { name := "indirect-dependency", items := [.type (tyI "my-variant" (.variant [{ name := "foo" }, { name := "bar" }]))] },
   .iface { name := "direct-dependency", items := [.use (useOf (.local "indirect-dependency") [("my-variant", none)]),
     fnI "fun" [] (some (.named "my-variant"))] },
   .world { name := "foo", items := [impW (.path (.local "direct-dependency"))] }]
  (some (localPath "foo")) [.let "i" (.new ⟨"foo:bar", none⟩ [.fill])]

end Silmaril.Wasm.Wac.WacTests
