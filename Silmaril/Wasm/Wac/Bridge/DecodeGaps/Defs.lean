module

public import Silmaril.Wasm.Wac.Bridge.Decode.Defs

/-!
# WAC bridge: two packages outside `decodePkg`

The encoder (`Bridge.Encode`) writes every interface closed and never defines a
resource, so the `decode ∘ encode` theorems of `Bridge.DecodeNamed`,
`Bridge.DecodeItems`, `Bridge.DecodeImpl` and `Bridge.DecodeRefVal` say nothing about
two kinds of packages that wac reads from a registry. This module writes one small
binary of each kind; `Bridge.DecodeGaps.Thms` states what `decodePkg` does on them.

* `cRes`: a component that **defines a resource** (`(type (resource (rep i32)))`) and
  exports it as `r`. Its projection (`Wit.Project.projectX`, `projectI`) replaces the
  definition by the world export `(export "r" (type (sub resource)))` and the
  component's own export by `(alias outer 0 0 (type))`.
* `pkgAB`: a WIT package of two interfaces in wit-component's layout, `foo:bar/a`
  exporting a resource `t`, and `foo:bar/b` that **uses** it (`use a.{t}`) in a function
  `f : (x : borrow<t>)`. The wrapper component type of `b` imports the instance
  `foo:bar/a`, aliases its type export `t`, and refers to it from `b`'s instance type by
  `(alias outer 1 1 (type))`, re-exported as `t` (`defB`).
* `unwrapUse`: `unwrapDef` that also unwraps a wrapper with imports (the interfaces
  whose types it uses), the restated reading of such an interface.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty)

namespace DecodeGaps

/-- A component defining a resource and exporting it as `r`. -/
def cRes : Ast := .mk [.types [.resource .i32 none], .exports [⟨⟨"r", .plain0⟩, ⟨.type, 0⟩, none⟩]]

/-- Its projection: the hoisted export, then an alias to the same type index. -/
def cResWorld : Wit.Project.WorldType :=
  [.inst (.export ⟨"r", .plain0⟩ (.type .subResource)), .inst (.alias ⟨.type, .outer 0 0⟩)]

/-- The wrapper of the interface `foo:bar/a { resource t; }`. -/
def defA : DefType := .component [.inst (.type (.instance [.export ⟨"t", .plain0⟩ (.type .subResource)])),
  .inst (.export ⟨"foo:bar/a", .plain0⟩ (.instance 0))]

/-- The wrapper of the interface `foo:bar/b { use a.{t}; f: func(x: borrow<t>); }`. -/
def defB : DefType := .component [
  .inst (.type (.instance [.export ⟨"t", .plain0⟩ (.type .subResource)])),
  .import ⟨"foo:bar/a", .plain0⟩ (.instance 0),
  .inst (.alias ⟨.type, .export 0 "t"⟩),
  .inst (.type (.instance [.alias ⟨.type, .outer 1 1⟩, .export ⟨"t", .plain0⟩ (.type (.eq 0)),
    .type (.val (.borrow 1)), .type (.func ⟨[("x", .idx 2)], none, false⟩),
    .export ⟨"f", .plain0⟩ (.func 3)])),
  .inst (.export ⟨"foo:bar/b", .plain0⟩ (.instance 2))]

/-- The package of the two interfaces. -/
def pkgAB : Ast := Wit.Project.itemsPackage [("foo:bar/a", defA), ("foo:bar/b", defB)] []

/-- The items of `a`, as the decoder reads them. -/
def tA : Externs := [("t", .type (.resource "t"))]

/-- The items of `b`, as the decoder reads them: `t` is `own<t>` of a resource `t` that
`b`'s own items do not define. -/
def tB : Externs := [("t", .type (.value (.own ⟨.local, "t"⟩))),
  ("f", .func { async := false, params := [("x", .borrow ⟨.local, "t"⟩)], result := none })]

/-- What `decodePkg` returns for `pkgAB`: `a` is an interface, `b` a component type
that imports `a` and exports `b`. -/
def pkgABRead : PkgType :=
  { imports := [], exports := [],
    defs := [(defName "foo:bar/a", .type (.inst (some "foo:bar/a") tA)),
             (defName "foo:bar/b", .type (.comp (some "foo:bar/b") [("foo:bar/a", .inst (some "foo:bar/a") tA)]
               [("foo:bar/b", .inst (some "foo:bar/b") tB)]))] }

/-- `unwrapDef`, also for a wrapper whose imports are the interfaces it uses. -/
def unwrapUse : Kind → Kind
  | .comp _ _ [(id, .inst _ es)] => .inst (some id) es
  | k => unwrapDef k

end DecodeGaps

end Silmaril.Wasm.Wac.Bridge
