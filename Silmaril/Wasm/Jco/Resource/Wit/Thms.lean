module

public import Silmaril.Wasm.Jco.Resource.Wit.Defs
public import Silmaril.Wasm.Jco.Resource.Handle.Defs

/-!
# Metadata with resources from WIT: litmus

`exResWorld` is the resolved form of

```wit
world boxes {
  export box: interface {
    resource cell {
      constructor(v: u32);
      get: func() -> u32;
      take: static func(c: cell) -> u32;
    }
  }
  export add: func(a: u32, b: u32) -> u32;
}
```

(the constructor returns `own<cell>`, `get`'s `self` is `borrow<cell>`). `exResWorld_ofWorld`
(by evaluation): `MetaR.ofWorld` numbers `cell` as resource type `0` and reads the world
functions `box#[constructor]cell`, `box#[method]cell.get`, `box#[static]cell.take` and `add`
with their handle types. The destructor's export name is `box#[dtor]cell`. `exResWorld_thin`:
the thin-wrapper recognizer of `Silmaril.Wasm.Jco.Resource.Handle` accepts it. `exResWorld_ref`: an
exported interface by reference is rejected.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Res

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Wit.Binary (Ty TyRef Owner Func Interface WorldItem World TyDefKind)
open Silmaril.Wasm.Component.Binary (PrimValType)
open Silmaril.Wasm.Component (ValTy)

/-- `cell`, a local type reference. -/
def cellRef : TyRef := ⟨.local, "cell"⟩

/-- The interface `box`. -/
def boxIface : Interface where
  types := [{ name := "cell", kind := .resource }]
  funcs := [
    { name := "cell", kind := .constructor "cell", params := [("v", .prim .u32)],
      result := some (.own cellRef) },
    { name := "get", kind := .method "cell", params := [("self", .borrow cellRef)],
      result := some (.prim .u32) },
    { name := "take", kind := .static "cell", params := [("c", .own cellRef)],
      result := some (.prim .u32) }]

/-- The freestanding function `add`. -/
def addFunc : Func where
  name := "add"
  params := [("a", .prim .u32), ("b", .prim .u32)]
  result := some (.prim .u32)

/-- The world `boxes`. -/
def exResWorld : World where
  exports := [.ifaceInline "box" boxIface, .func addFunc]

theorem exResWorld_ofWorld : MetaR.ofWorld exResWorld = .ok {
    md := { world := [
      ⟨"box#[constructor]cell", [.base (.val .u32)], some (.own 0)⟩,
      ⟨"box#[method]cell.get", [.borrow 0], some (.base (.val .u32))⟩,
      ⟨"box#[static]cell.take", [.own 0], some (.base (.val .u32))⟩,
      ⟨"add", [.base (.val .u32), .base (.val .u32)], some (.base (.val .u32))⟩] },
    resources := [("box", "cell")],
    dtors := [(0, "box#[dtor]cell")] } := rfl

/-- The metadata read from `exResWorld`. -/
def exResMd : MetaR := match MetaR.ofWorld exResWorld with
  | .ok rw => rw.md
  | .error _ => default

/-- No world function is named `cabi_realloc`, so a handle-passing module for `exResWorld` gets
the thin wrapper. -/
theorem exResWorld_thin : recognizeThinR exResMd = some (thinR exResMd fuseReallocName) := rfl

theorem exResWorld_ref :
    MetaR.ofWorld { exports := [.ifaceRef ⟨⟨"ex", "pkg", none⟩, "box"⟩] } =
      .error "interfaces exported by reference are not in the fragment" := rfl

end Silmaril.Wasm.Jco.Res
