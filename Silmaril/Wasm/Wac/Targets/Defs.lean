module

public import Silmaril.Wasm.Wit.Tool.Source.Defs
public import Silmaril.Wasm.Wit.Project.Infer.Defs

/-!
# WAC: targets checking by world projection

`package p targets w;` (and `wac targets COMPONENT --wit WIT`) asks that a composed
component fits the world `w`. Here the check is made on projections
(`Silmaril.Wasm.Wit.Project`):

* the component's world, at the level of names and sorts, is read off its top-level
  import and export sections (`surface`); this is total, whereas the typed projection
  `Project.projectI` is undefined on compositions that export functions aliased from
  instances they create (the function type lives inside the component type of the
  instantiated component), which is the usual shape of `wac compose` output;
* the target world is the world `w` of the WIT package, read from the projection of the
  package's binary encoding (`Project.project`, `Project.packageItems`: a world item is
  a component type wrapping the world).

`Fits c w` (a relation on the extern names and sorts of the two worlds): every import
of the component is an import of the world with the same sort, and every export of
the world is an export of the component with the same sort. `fits` decides it
(`fits_iff` in `Silmaril.Wasm.Wac.Targets.Thms`).

What this does not check, unlike `wac-types`' `validate_target` (wac 0.12.0,
`crates/wac-types/src/targets.rs`): the types behind the names (subtyping of function
and instance types), and semver-compatible name matching. It is a name-and-sort level
check; the differential test (`tests/wasm-wac/targets.sh`) compares its verdicts with
`wac targets` on cases that differ in names and sorts.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Targets

open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit

/-- The sort of an extern descriptor. -/
def sortOf : ExternDesc → String
  | .coreModule _ => "core module"
  | .func _ => "func"
  | .value _ => "value"
  | .type _ => "type"
  | .component _ => "component"
  | .instance _ => "instance"

/-- The imports of a world, with their sorts. -/
def imports (w : Project.WorldType) : List (String × String) :=
  w.filterMap fun
    | .import n d => some (n.name, sortOf d)
    | _ => none

/-- The exports of a world, with their sorts. -/
def exports (w : Project.WorldType) : List (String × String) :=
  w.filterMap fun
    | .inst (.export n d) => some (n.name, sortOf d)
    | _ => none

/-- A component with world `c` fits the world `w`: its imports are imports of `w`, and
the exports of `w` are its exports (names and sorts). Type exports of the world (`use`d
types) are not required. -/
def Fits (c w : Project.WorldType) : Prop :=
  (∀ i ∈ imports c, i ∈ imports w) ∧
  (∀ e ∈ exports w, e.2 ≠ "type" → e ∈ exports c)

/-- The decision procedure for `Fits`, with the offending names. -/
def misfits (c w : Project.WorldType) : List String :=
  ((imports c).filter (fun i => !(imports w).contains i)).map
      (fun i => s!"import `{i.1}` ({i.2}) is not an import of the target world") ++
  ((exports w).filter (fun e => e.2 != "type" && !(exports c).contains e)).map
      (fun e => s!"the target world's export `{e.1}` ({e.2}) is missing")

/-- `Fits` as a Boolean. -/
def fits (c w : Project.WorldType) : Bool := (misfits c w).isEmpty

/-- The world named `n` of a projected WIT package (a world item is a component type
that wraps the world, exported as `ns:pkg/n`). -/
def worldOfPackage (p : Project.WorldType) (n : Option String) : Except String Project.WorldType := do
  let some items := Project.packageItems 0 p | throw "not a WIT package"
  let worlds := items.filterMap fun
    | (name, .component [.inst (.type (.component w)), .inst (.export _ (.component 0))]) =>
      some (name, w)
    | _ => none
  match n, worlds with
  | none, [(_, w)] => pure w
  | none, [] => throw "the WIT package has no world"
  | none, _ => throw "the WIT package has several worlds; name one"
  | some n, ws =>
    match ws.find? (fun (m, _) => m == n || m.endsWith ("/" ++ n)) with
    | some (_, w) => pure w
    | none => throw s!"no world `{n}` in the WIT package"

/-- The world of a WIT package given as its binary encoding. -/
def targetWorld (wit : ByteArray) (n : Option String) : Except String Project.WorldType := do
  let c ← match Binary.parse wit with
    | .ok c => pure c
    | .error _ => throw "malformed WIT package"
  let some p := Project.project c | throw "the WIT package is outside the projection's domain"
  worldOfPackage p n

/-- The sort of an item. -/
def itemSortName : ItemSort → String
  | .core _ => "core module"
  | .func => "func"
  | .value => "value"
  | .type => "type"
  | .component => "component"
  | .instance => "instance"

/-- The names and sorts of a component's imports and exports, as a world of bare
declarations (`.import n d` and `.inst (.export n d)`, with placeholder indices). -/
def surface (c : Ast) : Project.WorldType :=
  c.sections.flatMap fun
    | .imports xs => xs.map fun i => .import i.name i.desc
    | .exports xs => xs.map fun e => .inst (.export e.name (match e.item.sort with
        | .func => .func 0
        | .value => .value (.eq 0)
        | .type => .type (.eq 0)
        | .component => .component 0
        | .instance => .instance 0
        | .core _ => .coreModule 0))
    | _ => []

/-- The world (names and sorts) of a component given as bytes. -/
def componentWorld (b : ByteArray) : Except String Project.WorldType :=
  match Binary.parse b with
  | .ok c => pure (surface c)
  | .error _ => throw "malformed component"

/-- `wasm-wac targets`: the offending names (empty when the component fits). -/
def check (comp wit : ByteArray) (n : Option String) : Except String (List String) := do
  let c ← componentWorld comp
  let w ← targetWorld wit n
  pure (misfits c w)

end Silmaril.Wasm.Wac.Targets
