module

public import Silmaril.Wasm.Component.Wat.Defs

/-!
# The projection of a component to its world

A WIT world is, in binary, a component *type*: a list of `ComponentDecl`s
(`WorldType`). `project c` is the component type of the component `c`, as far as it
can be read off without type inference: the declarations of `c`'s type
definitions, imports, type aliases and exports, replayed in order.

The replay keeps the **type index space** of `c` and of the world equal item by
item (types, type imports, type aliases and type exports allocate one index in
both), and renumbers the **instance index space** (`PState.imap`): instances `c`
creates (`instantiate`, inline exports, aliases of them) have no counterpart in
the world, imported and exported instances do. Items without any effect on the
type or instance index spaces of the world (core modules and instances, `canon`,
nested components, `start`, values, custom sections) are skipped.

`project c = none` outside the domain of the replay:

* an export without a type ascription whose sort is not `type` (its type would
  need inference);
* a resource definition (component types cannot define resources; a world
  exports it as `(type (sub resource))` and later types refer to that index, a
  renumbering not done here);
* a `(value (eq i))` bound, an outer alias leaving the component (`count ≠ 0`),
  or an alias of an export of an instance the component creates.

These are the open parts of the projection (`Silmaril.Wasm.Wit.Project.Thms`).

Names are put in the WAT normal form (`normName`, `normDefType`), so the
projection does not see the spelling of attribute-free names.

`worldPackage id name w` is the binary package of one world (wit-component's
layout, `encode_world`/`worldWrapper`): a component type defining the world's
component type and exporting it as `id` (`ns:pkg/name`), exported as `name`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Project

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Wat (normName normDefType normComponentDecls)

/-- A world in binary form: the declarations of a component type. -/
abbrev WorldType := List ComponentDecl

/-- A section split into sections of one element (no other change). -/
def splitSection : Section → List Section
  | .coreInstances xs => xs.map fun x => .coreInstances [x]
  | .coreTypes xs => xs.map fun x => .coreTypes [x]
  | .instances xs => xs.map fun x => .instances [x]
  | .aliases xs => xs.map fun x => .aliases [x]
  | .types xs => xs.map fun x => .types [x]
  | .canons xs => xs.map fun x => .canons [x]
  | .imports xs => xs.map fun x => .imports [x]
  | .exports xs => xs.map fun x => .exports [x]
  | .values xs => xs.map fun x => .values [x]
  | s => [s]

/-- The state of the replay. -/
structure PState where
  /-- The world's declarations so far. -/
  decls : WorldType := []
  /-- For each instance index of the component, its index in the world. -/
  imap : List (Option Nat) := []
  /-- The number of instances of the world. -/
  wInst : Nat := 0

namespace PState

/-- Add a declaration. -/
def emit (s : PState) (d : ComponentDecl) : PState := { s with decls := s.decls ++ [d] }

/-- A new instance of the component, with or without a counterpart in the world. -/
def inst (s : PState) (inWorld : Bool) : PState :=
  if inWorld then { s with imap := s.imap ++ [some s.wInst], wInst := s.wInst + 1 }
  else { s with imap := s.imap ++ [none] }

/-- The world index of a component instance. -/
def lookup (s : PState) (i : Nat) : Option Nat := (s.imap[i]?).getD none

end PState

/-- Whether a type definition is a resource definition. -/
def isResource : DefType → Bool
  | .resource _ _ => true
  | _ => false

/-- The type of an export: its ascription, or `(type (eq i))` for a type export. -/
def exportDesc (e : Silmaril.Wasm.Component.Binary.Export) : Option ExternDesc :=
  match e.desc with
  | some d => some d
  | none => if e.item.sort = .type then some (.type (.eq e.item.idx)) else none

/-- Whether an extern descriptor is a `(value (eq i))` bound. -/
def isValueEq : ExternDesc → Bool
  | .value (.eq _) => true
  | _ => false

/-- One step of the replay, on a section of one element. -/
def step (s : PState) : Section → Option PState
  | .coreTypes [t] => some (s.emit (.inst (.coreType t)))
  | .instances [_] => some (s.inst false)
  | .aliases [a] =>
    match a.sort, a.target with
    | .type, .outer 0 _ => some (s.emit (.inst (.alias a)))
    | .core .type, .outer 0 _ => some (s.emit (.inst (.alias a)))
    | .type, .outer _ _ => none
    | .core .type, .outer _ _ => none
    | .type, .export i n => (s.lookup i).map fun j => s.emit (.inst (.alias ⟨.type, .export j n⟩))
    | .instance, .export i n =>
      (s.lookup i).map fun j => (s.emit (.inst (.alias ⟨.instance, .export j n⟩))).inst true
    | .instance, _ => some (s.inst false)
    | _, _ => some s
  | .types [t] => if isResource t then none else some (s.emit (.inst (.type (normDefType t))))
  | .imports [i] =>
    if isValueEq i.desc then none
    else
      let s' := s.emit (.import (normName i.name) i.desc)
      match i.desc with
      | .instance _ => some (s'.inst true)
      | _ => some s'
  | .exports [e] =>
    match exportDesc e with
    | none => none
    | some d =>
      if isValueEq d then none
      else
        let s' := s.emit (.inst (.export (normName e.name) d))
        if e.item.sort = ItemSort.instance then some (s'.inst true) else some s'
  | _ => some s

/-- Replay a list of sections of one element. -/
def replay : PState → List Section → Option PState
  | s, [] => some s
  | s, x :: xs => (step s x).bind fun s' => replay s' xs

/-- **The projection** of a component to its world. -/
def project (c : Ast) : Option WorldType :=
  (replay {} (c.sections.flatMap splitSection)).map (·.decls)

/-! ## Worlds as packages -/

/-- The binary package of one world `w`: a component type defining `w` and
exporting it as `id`, exported as `name` (wit-component's layout). -/
def worldPackage (id name : String) (w : WorldType) : Ast :=
  .mk [.types [.component [.inst (.type (.component w)), .inst (.export ↑id (.component 0))]],
    .exports [⟨↑name, ⟨.type, 0⟩, none⟩]]

/-- The world of a projected one-world package. -/
def worldOf : WorldType → Option WorldType
  | [.inst (.type (.component [.inst (.type (.component w)), .inst (.export _ (.component 0))])),
     .inst (.export _ (.type (.eq 0)))] => some w
  | _ => none

/-- The sections of the items of a package from the `k`-th on: item `k` is the
type `2 k`, exported under its name as the type `2 k + 1` (wit-component's
`encode` layout, interfaces as instance types and worlds as wrapped component
types). -/
def itemSecs : Nat → List (String × DefType) → List Section
  | _, [] => []
  | k, (n, d) :: rest =>
    .types [d] :: .exports [⟨↑n, ⟨.type, 2 * k⟩, none⟩] :: itemSecs (k + 1) rest

/-- The binary package of named items, followed by custom sections. -/
def itemsPackage (items : List (String × DefType)) (custom : List Section) : Ast :=
  .mk (itemSecs 0 items ++ custom)

/-- The items of a projected package, from the `k`-th on. -/
def packageItems : Nat → WorldType → Option (List (String × DefType))
  | _, [] => some []
  | k, .inst (.type d) :: .inst (.export n (.type (.eq j))) :: rest =>
    if j = 2 * k then (packageItems (k + 1) rest).map ((n.name, d) :: ·) else none
  | _, _ => none

/-- The items without effect on the projection: code and custom sections. -/
def isCode : Section → Bool
  | .custom _ _ | .coreModule _ | .coreInstances _ | .canons _ | .start _ | .component _ => true
  | _ => false

/-- Drop the code of a component: core modules and instances, `canon`, `start`,
nested components and custom sections. -/
def stripCode (c : Ast) : Ast := .mk (c.sections.filter fun s => !isCode s)

end Silmaril.Wasm.Wit.Project
