module

public import Silmaril.Wasm.Wac.ElabSpec.Defs
public import Silmaril.Wasm.Wac.Targets.Defs
public import Silmaril.Wasm.Wac.WitKind.Defs
public import Silmaril.Wasm.Wit.Binary.Decode.Defs

/-!
# WAC: typed targets checking as world satisfaction

`package p targets w;` asks that the composed component *satisfies* the world `w`. In
wac (`validate_target`, `crates/wac-types/src/targets.rs`, wac `5a7480c`) and in the
Component Model, this is subtyping of component types: the composition, as a component
type `(imports, exports)`, is a subtype of the world's component type. `Sat c w`
states it with the WIT subtyping of `Silmaril.Wasm.Wac.Types` (`Sub` on `Kind.comp`):
every import of the composition is an import of the world, at a supertype, and every
export of the world is an export of the composition, at a subtype. Equal worlds
satisfy each other (`Sat.refl`, `Silmaril.Wasm.Wac.World.Thms`).

## The two sides

* **The target world** is a world of the WIT formalization. Its binary form (a
  `Project.WorldType`, as `Targets.worldOfPackage` reads it off the projection of the
  package) is decoded by `Wit.Binary.decWorld` and turned into kinds by
  `WitKind.ofWorld` (`targetKinds`).
* **The composition's world** cannot be read with `Project.projectI` on `wac compose`
  output: the composition exports functions aliased from instances it creates, whose
  types live in the component types of the instantiated packages. The types are
  derived from the **composition graph** instead:
  - `CGraph.typedWorld g`: the elaborator's graph, whose nodes carry kinds;
  - `profileWorld K imps c`: a component in the composition profile, given the kinds
    `K k` of its packages (component index `k`) and the kinds `imps` of its imports, by
    following the profile's index spaces (components, instances, functions, types) at
    the level of kinds. An `instantiate` of a package of kind `.comp _ is es` has the
    instance kind `.inst none es`; an alias of an export reads the instance kind's
    export table; an export takes the kind of its item.

## Relations to the untyped checks

* `TargetOk g wi we` (the elaborator's check, `checkTarget`) implies
  `Sat g.typedWorld (wi, we)`, and is equivalent to it when the names of the world's
  imports and of the composition's exports are distinct (`targetOk_iff_sat`).
* `profileWorld` refines the names-and-sorts world `Targets.surface c`: erasing the kinds
  to sorts gives exactly the imports and exports of `surface c`
  (`erase_profileWorld`). So a typed verdict implies the untyped one: `Sat` implies
  `Targets.Fits` (`fits_of_sat`), given that the target's kinds erase to the target's
  names and sorts (a property of `decWorld`/`ofWorld`, checked on examples, not proved).

What is not modelled: semver-compatible matching of names (wac matches `a:b/c@0.2.0`
against `a:b/c@0.2.1`), and type aliases (kinds are compared structurally, see
`Silmaril.Wasm.Wac.Types`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit

namespace World

/-- The sort of a kind, spelled as `Targets.sortOf` spells the sorts of descriptors. -/
def sortName : Kind → String
  | .func _ => "func"
  | .value _ => "value"
  | .resource _ => "type"
  | .type _ => "type"
  | .inst _ _ => "instance"
  | .comp _ _ _ => "component"

/-- Erase kinds to sorts. -/
def erase (es : Externs) : List (String × String) := es.map fun p => (p.1, sortName p.2)

/-- Promote every kind (wac's `ItemKind::promote`: interface types become instances,
world types components). -/
def promoteEx (es : Externs) : Externs := es.map fun p => (p.1, p.2.promote)

/-- A world as a component type: its imports and its exports. -/
abbrev WorldK := Externs × Externs

/-- **World satisfaction**: the component type `c` is a subtype of the world `w`'s
component type (interface and world types in `w` promoted). -/
def Sat (c w : WorldK) : Prop :=
  Sub (.comp none c.1 c.2) (.comp none (promoteEx w.1) (promoteEx w.2))

/-- The decision procedure for `Sat`. -/
def sat (c w : WorldK) : Bool :=
  sub (.comp none c.1 c.2) (.comp none (promoteEx w.1) (promoteEx w.2))

/-- The kinds of a target world given in binary form (decoded by the WIT
formalization; interfaces by path are looked up in `env`). -/
def targetKinds (env : Wit.Binary.Env) (w : Project.WorldType) : Except String WorldK :=
  (Wit.Binary.decWorld w).map (WitKind.ofWorld env)

/-! ## The world of a profile component, from the kinds of its packages -/

/-- The descriptor sort of an extern descriptor. -/
def descSort : ExternDesc → ItemSort
  | .coreModule _ => .core .module
  | .func _ => .func
  | .value _ => .value
  | .type _ => .type
  | .component _ => .component
  | .instance _ => .instance

/-- The kinds of the index spaces of a component, and its world so far. A type
defined in a `types` section has no kind here (`none`). -/
structure KSt where
  comps : List (Option Kind) := []
  insts : List (Option Kind) := []
  funcs : List (Option Kind) := []
  types : List (Option Kind) := []
  imports : Externs := []
  exports : Externs := []
  deriving Inhabited

namespace KSt

/-- A new item of sort `s`. -/
def push (st : KSt) (s : ItemSort) (k : Option Kind) : KSt :=
  match s with
  | .component => { st with comps := st.comps ++ [k] }
  | .instance => { st with insts := st.insts ++ [k] }
  | .func => { st with funcs := st.funcs ++ [k] }
  | .type => { st with types := st.types ++ [k] }
  | _ => st

/-- The kind of an item. -/
def get (st : KSt) (x : SortIdx) : Option Kind :=
  match x.sort with
  | .component => (st.comps[x.idx]?).join
  | .instance => (st.insts[x.idx]?).join
  | .func => (st.funcs[x.idx]?).join
  | .type => (st.types[x.idx]?).join
  | _ => none

end KSt

/-- An import: its kind is `imps`' (promoted), and must have the import's sort. -/
def kImport (imps : Externs) (st : KSt) (i : Silmaril.Wasm.Component.Binary.Import) : Except String KSt :=
  match imps.find i.name.name with
  | some k =>
    if sortName k.promote = Targets.sortOf i.desc then
      .ok { st.push (descSort i.desc) (some k.promote) with
        imports := st.imports ++ [(i.name.name, k.promote)] }
    else .error s!"import {i.name.name}: its kind has another sort"
  | none => .error s!"import {i.name.name}: no kind"

/-- An instantiation: the instance of the package's exports. -/
def kInstance (st : KSt) : InstanceExpr → Except String KSt
  | .instantiate c _ =>
    match st.comps[c]? with
    | some (some (.comp _ _ es)) => .ok (st.push .instance (some (.inst none es)))
    | _ => .error s!"instantiate: component {c} has no component kind"
  | .exports _ => .error "instance: outside the composition profile"

/-- An alias of an instance export: the kind of the export. -/
def kAlias (st : KSt) (a : Alias) : Except String KSt :=
  match a.target with
  | .export i n =>
    match st.insts[i]? with
    | some (some (.inst _ es)) =>
      match Externs.find es n with
      | some k =>
        if sortName k = Targets.itemSortName a.sort then .ok (st.push a.sort (some k))
        else .error s!"alias {n}: the export has another sort"
      | none => .error s!"alias {n}: no such export"
    | _ => .error s!"alias {n}: instance {i} has no instance kind"
  | _ => .error "alias: outside the composition profile"

/-- An export: the kind of its item. -/
def kExport (st : KSt) (e : Silmaril.Wasm.Component.Binary.Export) : Except String KSt :=
  match st.get e.item with
  | some k =>
    if sortName k = Targets.itemSortName e.item.sort then
      .ok { st.push e.item.sort (some k) with exports := st.exports ++ [(e.name.name, k)] }
    else .error s!"export {e.name.name}: its kind has another sort"
  | none => .error s!"export {e.name.name}: no kind"

/-- Fold a step over a list. -/
def foldE {α : Type} (f : KSt → α → Except String KSt) : KSt → List α → Except String KSt
  | st, [] => .ok st
  | st, a :: as => (f st a).bind fun st' => foldE f st' as

/-- One section. -/
def kSection (K : Nat → Kind) (imps : Externs) (st : KSt) : Section → Except String KSt
  | .custom _ _ => .ok st
  | .types xs => .ok { st with types := st.types ++ xs.map fun _ => none }
  | .imports xs => foldE (kImport imps) st xs
  | .component _ => .ok (st.push .component (some (K st.comps.length)))
  | .instances xs => foldE kInstance st xs
  | .aliases xs => foldE kAlias st xs
  | .exports xs => foldE kExport st xs
  | _ => .error "section outside the composition profile"

/-- **The world of a profile component** `c`, typed by the kinds `K k` of its packages
(component index `k`; an imported package takes its kind from `imps`) and the kinds
`imps` of its imports. -/
def profileWorld (K : Nat → Kind) (imps : Externs) (c : Ast) : Except String WorldK :=
  (foldE (kSection K imps) {} c.sections).map fun st => (st.imports, st.exports)

/-- **Typed targets checking** of a profile component against a world in binary form. -/
def checkTyped (K : Nat → Kind) (imps : Externs) (env : Wit.Binary.Env) (c : Ast)
    (w : Project.WorldType) : Except String Bool := do
  let cw ← profileWorld K imps c
  let tw ← targetKinds env w
  pure (sat cw tw)

end World

/-- **The world of an elaborated composition**: its imports, and its exports with the
kinds of the exported nodes. -/
def CGraph.typedWorld (g : CGraph) : World.WorldK :=
  (g.imports, g.exports.map fun p => (p.1, g.kindOf p.2))

end Silmaril.Wasm.Wac
