module

public import Silmaril.Wasm.Component.Reference.Defs
public import Silmaril.Wasm.Component.Semantics.Defs

/-!
# From the component IR to the reference syntax

The fragment of the component IR (`Silmaril.Wasm.Component.Comp`) that the reference soundness
results cover, and its translation to the reference component AST:

* `NumModule`: a Core 3.0 module (`Silmaril.Wasm.Module`) without imports, with its named
  numeric function exports (the IR's `CoreModule` interface);
* `Simple`: one core instance of a `NumModule`, and exports each of which is `canon lift`
  of one core export at an IR function type;
* `Simple.toComp : Comp NumModule`: the IR component
  `.mk [] [.core m []] [⟨name, ft, ⟨[.lift ft], .call k⟩⟩, …]`;
* `Simple.toRef : Core3Component`: the reference component
  `(core module m) (core instance (instantiate 0)) [(type …)* (type (func …))
  (alias core export 0 "f" (core func)) (canon lift (core func i) (type t)) (export "n" (func 2i))]*`,
  (each export adds a component function index, so the `i`-th lift is function `2i`),
  where record and variant types are emitted as `(type (record …))`/`(type (variant …))`
  definitions with generated labels `f, fx, …` and `c, cx, …`, each named by a type export
  `(export "t…" (type n))` (exported functions may only mention named types);
* `toRefVal`: the reference value types and values of IR ones.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Component (Syntax.Definition Syntax.VT Syntax.Prim Syntax.DefValType)

/-! ## Values -/

mutual
/-- The reference component value of an IR value (integers by their two's-complement or
unsigned reading, floats by their bit patterns). -/
def toRefVal : Silmaril.Wasm.Component.Val → Silmaril.Wasm.Component.Value.Val
  | .bool b => .bool b
  | .s8 x => .int .s8 x.toInt
  | .u8 x => .int .u8 x.toNat
  | .s16 x => .int .s16 x.toInt
  | .u16 x => .int .u16 x.toNat
  | .s32 x => .int .s32 x.toInt
  | .u32 x => .int .u32 x.toNat
  | .s64 x => .int .s64 x.toInt
  | .u64 x => .int .u64 x.toNat
  | .f32 b => .f32 b
  | .f64 b => .f64 b
  | .char c => .char c
  | .record vs => .record (toRefVals vs)
  | .variant i p => .variant i (toRefOpt p)

/-- `toRefVal` on lists. -/
def toRefVals : List Silmaril.Wasm.Component.Val → List Silmaril.Wasm.Component.Value.Val
  | [] => []
  | v :: vs => toRefVal v :: toRefVals vs

/-- `toRefVal` on options. -/
def toRefOpt : Option Silmaril.Wasm.Component.Val → Option Silmaril.Wasm.Component.Value.Val
  | none => none
  | some v => some (toRefVal v)
end

/-! ## Types, emitted as reference type definitions -/

/-- The reference primitive of an IR scalar type. -/
def primOf? : ValTy → Option Syntax.Prim
  | .bool => some .bool
  | .s8 => some .s8 | .u8 => some .u8 | .s16 => some .s16 | .u16 => some .u16
  | .s32 => some .s32 | .u32 => some .u32 | .s64 => some .s64 | .u64 => some .u64
  | .f32 => some .f32 | .f64 => some .f64 | .char => some .char
  | .record _ | .variant _ => none

/-- The generated name `p`, `px`, `pxx`, … of index `n` (kernel-reducible, unlike
`toString`). -/
def tag (p : String) : Nat → String
  | 0 => p
  | n + 1 => (tag p n).push 'x'

/-- Generated labels `p, px, pxx, …`. -/
def labels (p : String) {α : Type} (xs : List α) : List (String × α) :=
  xs.mapIdx fun i x => (tag p i, x)

/-- `(export "t…" (type n))` (name `tag "t" n`): names the type definition `n` (an exported
function may only mention named types); the export is the next type index. -/
def typeExport {M : Type} (n : Nat) : Syntax.Definition M :=
  .export_ { name := tag "t" n } ⟨.type, n⟩ none

mutual
/-- The reference value type of an IR type, with the type definitions it needs, from type
index `n` on (returns the next free type index). -/
def emitTy {M : Type} : ValTy → Nat → Syntax.VT × List (Syntax.Definition M) × Nat
  | .bool, n => (.prim .bool, [], n)
  | .s8, n => (.prim .s8, [], n)
  | .u8, n => (.prim .u8, [], n)
  | .s16, n => (.prim .s16, [], n)
  | .u16, n => (.prim .u16, [], n)
  | .s32, n => (.prim .s32, [], n)
  | .u32, n => (.prim .u32, [], n)
  | .s64, n => (.prim .s64, [], n)
  | .u64, n => (.prim .u64, [], n)
  | .f32, n => (.prim .f32, [], n)
  | .f64, n => (.prim .f64, [], n)
  | .char, n => (.prim .char, [], n)
  | .record ts, n =>
    let (vs, ds, n') := emitTys ts n
    (.idx (n' + 1), ds ++ [.type (.val (.record (labels "f" vs))), typeExport n'], n' + 2)
  | .variant cs, n =>
    let (os, ds, n') := emitCases cs n
    (.idx (n' + 1), ds ++ [.type (.val (.variant (labels "c" os))), typeExport n'], n' + 2)

/-- `emit` on a list of types, left to right. -/
def emitTys {M : Type} : List ValTy → Nat → List Syntax.VT × List (Syntax.Definition M) × Nat
  | [], n => ([], [], n)
  | t :: ts, n =>
    let (v, ds, n₁) := emitTy t n
    let (vs, ds', n₂) := emitTys ts n₁
    (v :: vs, ds ++ ds', n₂)

/-- `emit` on variant cases. -/
def emitCases {M : Type} : List (Option ValTy) → Nat →
    List (Option Syntax.VT) × List (Syntax.Definition M) × Nat
  | [], n => ([], [], n)
  | none :: cs, n =>
    let (os, ds, n') := emitCases cs n
    (none :: os, ds, n')
  | some t :: cs, n =>
    let (v, ds, n₁) := emitTy t n
    let (os, ds', n₂) := emitCases cs n₁
    (some v :: os, ds ++ ds', n₂)
end

/-! ## The fragment -/

/-- A Core 3.0 module without imports, with its named numeric function exports (in the
order of its function exports). -/
structure NumModule where
  /-- The module. -/
  mod : Silmaril.Wasm.Module
  /-- Its function exports with their flat types. -/
  exports : CoreIface

instance : CoreModule NumModule := ⟨fun _ => [], NumModule.exports⟩

/-- An export of a simple component: `canon lift` of core export `core` at type `ty`. -/
structure SimpleExport where
  /-- The export name. -/
  name : String
  /-- The component function type. -/
  ty : FuncTy
  /-- The index of the lifted core export. -/
  core : Nat

/-- A simple component: one core instance of an import-free module, and lifted exports. -/
structure Simple where
  /-- The core module. -/
  mod : NumModule
  /-- The exports. -/
  exports : List SimpleExport

namespace Simple

/-- The IR component of a simple component. -/
def toComp (c : Simple) : Comp NumModule :=
  .mk [] [.core c.mod []]
    (c.exports.map fun x => { name := x.name, ty := x.ty, impl := ⟨[.lift x.ty], .call x.core⟩ })

/-- The reference definitions of export number `i`, from type index `n`; returns the next
type index. -/
def exportDefs (m : NumModule) (i : Nat) (x : SimpleExport) (n : Nat) :
    List (Syntax.Definition Silmaril.Wasm.Module) × Nat :=
  let (ps, dps, n₁) := emitTys (M := Silmaril.Wasm.Module) x.ty.params n
  let (r, drs, n₂) := emitTys (M := Silmaril.Wasm.Module) x.ty.results n₁
  let core := ((m.exports[x.core]?).map (·.1)).getD ""
  (dps ++ drs ++
    [.type (.func { params := labels "a" ps, result := r.head? }),
     .alias (.coreExport 0 core .func),
     .canon (.lift i [] n₂),
     .export_ { name := x.name } ⟨.func, 2 * i⟩ none], n₂ + 1)

/-- The definitions of the exports from number `i` and type index `n` on. -/
def exportsDefs (m : NumModule) : Nat → List SimpleExport → Nat →
    List (Syntax.Definition Silmaril.Wasm.Module)
  | _, [], _ => []
  | i, x :: xs, n =>
    let (ds, n') := exportDefs m i x n
    ds ++ exportsDefs m (i + 1) xs n'

/-- The reference component of a simple component. -/
def toRef (c : Simple) : Core3Component :=
  [.coreModule c.mod.mod, .coreInstance (.instantiate 0 [])] ++
    exportsDefs c.mod 0 c.exports 0

end Simple

/-! ## Resolved types -/

section Closed

open Silmaril.Wasm.Component.Runtime (RtId)

mutual
/-- The resolved reference type of an IR type (records labelled `f, fx, …`, variants `c, cx,
…`), as instantiation of `toRef` resolves the emitted type definitions. -/
def toClosed : ValTy → Silmaril.Wasm.Component.WIT.ClosedType RtId
  | .bool => .prim .bool
  | .s8 => .prim .s8 | .u8 => .prim .u8 | .s16 => .prim .s16 | .u16 => .prim .u16
  | .s32 => .prim .s32 | .u32 => .prim .u32 | .s64 => .prim .s64 | .u64 => .prim .u64
  | .f32 => .prim .f32 | .f64 => .prim .f64 | .char => .prim .char
  | .record ts => .record (labels "f" (toClosedList ts))
  | .variant cs => .variant (labels "c" (toClosedCases cs))

/-- `toClosed` on lists. -/
def toClosedList : List ValTy → List (Silmaril.Wasm.Component.WIT.ClosedType RtId)
  | [] => []
  | t :: ts => toClosed t :: toClosedList ts

/-- `toClosed` on variant cases. -/
def toClosedCases : List (Option ValTy) → List (Option (Silmaril.Wasm.Component.WIT.ClosedType RtId))
  | [] => []
  | none :: cs => none :: toClosedCases cs
  | some t :: cs => some (toClosed t) :: toClosedCases cs
end

/-- The resolved reference function type of an IR function type (parameters `a, ax, …`, the
first result type). -/
def witFt (ft : FuncTy) : Silmaril.Wasm.Component.WIT.FuncType Empty RtId :=
  ⟨labels "a" (toClosedList ft.params), (toClosedList ft.results).head?, false⟩

end Closed

/-! ## The fragment with imports -/

/-- A Core 3.0 module with its named numeric function imports (in import order) and function
exports (in the order of its function exports). -/
structure ImpModule where
  /-- The module. -/
  mod : Silmaril.Wasm.Module
  /-- Its function imports with their flat types. -/
  imports : CoreIface
  /-- Its function exports with their flat types. -/
  exports : CoreIface

instance : CoreModule ImpModule := ⟨ImpModule.imports, ImpModule.exports⟩

/-- An import-free module as a module with (no) imports. -/
def NumModule.toImp (m : NumModule) : ImpModule := ⟨m.mod, [], m.exports⟩

/-- A simple component with imports: one core instance of `mod`, whose core import `k` is the
`canon lower` of component import `k` at the component type `imports[k].2`, and exports that
are `canon lift`s of core exports. -/
structure SimpleI where
  /-- The core module. -/
  mod : ImpModule
  /-- The component imports. -/
  imports : Iface
  /-- The exports. -/
  exports : List SimpleExport

namespace SimpleI

/-- The wiring of the core imports: core import `k` is `canon lower` of component import `k`. -/
def lowerArgs (ims : Iface) : List Impl :=
  ims.mapIdx fun k p => ⟨[.lower p.2], .call k⟩

/-- **The IR component of a simple component with imports**: the component imports are
environment functions `0, …, n - 1`, the core instance's exports follow, and export `x` is the
`canon lift` of core export `x.core`, environment function `x.core + n`. -/
def toComp (c : SimpleI) : Comp ImpModule :=
  .mk c.imports [.core c.mod (lowerArgs c.imports)]
    (c.exports.map fun x =>
      { name := x.name, ty := x.ty, impl := ⟨[.lift x.ty], .call (x.core + c.imports.length)⟩ })

/-- The reference definitions of export number `i`, from type index `n`, when the core exports
`names` are those of core instance `inst` and `base` component and core functions precede the
lifts: `alias core export` is core function `base + i`, its `canon lift` component function
`base + 2i`. Returns the next type index. -/
def exportDefsAt (names : CoreIface) (inst base i : Nat) (x : SimpleExport) (n : Nat) :
    List (Syntax.Definition Silmaril.Wasm.Module) × Nat :=
  let (ps, dps, n₁) := emitTys (M := Silmaril.Wasm.Module) x.ty.params n
  let (r, drs, n₂) := emitTys (M := Silmaril.Wasm.Module) x.ty.results n₁
  let core := ((names[x.core]?).map (·.1)).getD ""
  (dps ++ drs ++
    [.type (.func { params := labels "a" ps, result := r.head? }),
     .alias (.coreExport inst core .func),
     .canon (.lift (base + i) [] n₂),
     .export_ { name := x.name } ⟨.func, base + 2 * i⟩ none], n₂ + 1)

/-- The definitions of the exports from number `i` and type index `n` on. -/
def exportsDefsAt (names : CoreIface) (inst base : Nat) : Nat → List SimpleExport → Nat →
    List (Syntax.Definition Silmaril.Wasm.Module)
  | _, [], _ => []
  | i, x :: xs, n =>
    let (ds, n') := exportDefsAt names inst base i x n
    ds ++ exportsDefsAt names inst base (i + 1) xs n'

/-- The reference definitions of a component import, from type index `n`: the type definitions
of its function type, then `(import "name" (func (type t)))`. Returns the next type index. -/
def importDefs (p : String × FuncTy) (n : Nat) :
    List (Syntax.Definition Silmaril.Wasm.Module) × Nat :=
  let (ps, dps, n₁) := emitTys (M := Silmaril.Wasm.Module) p.2.params n
  let (r, drs, n₂) := emitTys (M := Silmaril.Wasm.Module) p.2.results n₁
  (dps ++ drs ++
    [.type (.func { params := labels "a" ps, result := r.head? }),
     .import_ { name := p.1 } (.func n₂)], n₂ + 1)

/-- The definitions of the imports from type index `n` on, and the next type index. -/
def importsDefs : Iface → Nat → List (Syntax.Definition Silmaril.Wasm.Module) × Nat
  | [], n => ([], n)
  | p :: ps, n =>
    let (ds, n') := importDefs p n
    let (ds', n'') := importsDefs ps n'
    (ds ++ ds', n'')

/-- **The reference component of a simple component with imports**: the imports (component
functions `0, …, n - 1`), the core module, `canon lower` of each import (core functions
`0, …, n - 1`), the core instance exporting them under the names of the module's imports, the
instantiation of the module with it as `"env"`, then the exports of `Simple.toRef` aliased from
that instance (core instance `1`), shifted by `n` functions. The module's imports are expected
to come from the module `"env"`. -/
def toRef (c : SimpleI) : Core3Component :=
  (importsDefs c.imports 0).1 ++ [.coreModule c.mod.mod] ++
    (c.imports.mapIdx fun k _ => .canon (.lower k [])) ++
    [.coreInstance (.exports (c.mod.imports.mapIdx fun k p => (p.1, ⟨.func, k⟩))),
     .coreInstance (.instantiate 0 [("env", 0)])] ++
    exportsDefsAt c.mod.exports 1 c.imports.length 0 c.exports (importsDefs c.imports 0).2

/-- A simple component as a simple component without imports. -/
def ofSimple (c : Simple) : SimpleI := ⟨c.mod.toImp, [], c.exports⟩

end SimpleI

end Silmaril.Wasm.Component.Reference
