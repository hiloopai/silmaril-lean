module

public import Silmaril.Wasm.Wit.Project.Defs

/-!
# The projection, extended: resources and exports without type ascription

`projectX` extends `Silmaril.Wasm.Wit.Project.project` to two kinds of components on
which `project` is undefined:

* **resource definitions** `(type (resource …))`. A component type cannot define a
  resource; a world sees a resource the component defines only through its export,
  as `(export "r" (type (sub resource)))`. The definition is replaced by that export
  declaration (*hoisted* from the first later export of the resource's type index,
  found by looking ahead), so the type index spaces of the component and of the world
  stay aligned; the component's own export of the resource then becomes
  `(alias outer 0 t (type))` in the world (the export introduced a new index that
  is the same type). A resource that is never exported gives `none`.
* **exports without a type ascription** of functions, instances and components:
  their type is the one the component gave the item when it introduced it. The
  replay remembers it per index: `canon lift … (type t)` gives `(func (type t))`,
  an import its descriptor, an export its (given or inferred) descriptor. Items
  introduced otherwise (aliases, instantiations, nested components) have no known
  type and an unascribed export of them still gives `none`.

`projectX_of_project` (in `Silmaril.Wasm.Wit.Project.Ext.Thms`): wherever `project` is
defined, `projectX` is defined and equal to it.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Project

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Wat (normName)

/-- The state of the extended replay. -/
structure XState where
  /-- The state of the plain replay. -/
  base : PState := {}
  /-- The number of type indices of the component so far. -/
  tCount : Nat := 0
  /-- The known descriptor of each function index of the component. -/
  fdesc : List (Option ExternDesc) := []
  /-- The known descriptor of each instance index of the component. -/
  idesc : List (Option ExternDesc) := []
  /-- The known descriptor of each component index of the component. -/
  cdesc : List (Option ExternDesc) := []
  /-- Resource definitions whose export was hoisted, not yet exported. -/
  hoisted : List Nat := []

/-- Look up an optional descriptor. -/
def descAt (l : List (Option ExternDesc)) (i : Nat) : Option ExternDesc := (l[i]?).getD none

/-- The name of the first export of type index `t` in the remaining sections. -/
def resExport (t : Nat) : List Section → Option ExternName
  | [] => none
  | .exports [e] :: rest => if e.item = ⟨.type, t⟩ then some e.name else resExport t rest
  | _ :: rest => resExport t rest

/-- The descriptor an export has: its ascription, or the type its item was given. -/
def exportDescX (s : XState) (e : Export) : Option ExternDesc :=
  match exportDesc e with
  | some d => some d
  | none =>
    match e.item.sort with
    | .func => descAt s.fdesc e.item.idx
    | .instance => descAt s.idesc e.item.idx
    | .component => descAt s.cdesc e.item.idx
    | _ => none

/-- Track the indices a section of one element introduces. -/
def track (s : XState) : Section → XState
  | .types [_] => { s with tCount := s.tCount + 1 }
  | .canons [.lift _ _ t] => { s with fdesc := s.fdesc ++ [some (.func t)] }
  | .instances [_] => { s with idesc := s.idesc ++ [none] }
  | .component _ => { s with cdesc := s.cdesc ++ [none] }
  | .aliases [a] =>
    match a.sort with
    | .type => { s with tCount := s.tCount + 1 }
    | .func => { s with fdesc := s.fdesc ++ [none] }
    | .instance => { s with idesc := s.idesc ++ [none] }
    | .component => { s with cdesc := s.cdesc ++ [none] }
    | _ => s
  | .imports [i] =>
    match i.desc with
    | .type _ => { s with tCount := s.tCount + 1 }
    | .func _ => { s with fdesc := s.fdesc ++ [some i.desc] }
    | .instance _ => { s with idesc := s.idesc ++ [some i.desc] }
    | .component _ => { s with cdesc := s.cdesc ++ [some i.desc] }
    | _ => s
  | .exports [e] =>
    match e.item.sort with
    | .type => { s with tCount := s.tCount + 1 }
    | .func => { s with fdesc := s.fdesc ++ [exportDescX s e] }
    | .instance => { s with idesc := s.idesc ++ [exportDescX s e] }
    | .component => { s with cdesc := s.cdesc ++ [exportDescX s e] }
    | _ => s
  | _ => s

/-- One step of the extended replay, with the sections still to come. -/
def stepX (s : XState) (rest : List Section) : Section → Option XState
  | .types [t] =>
    if isResource t then
      (resExport s.tCount rest).map fun n =>
        { track s (.types [t]) with
          base := s.base.emit (.inst (.export (normName n) (.type .subResource)))
          hoisted := s.tCount :: s.hoisted }
    else (step s.base (.types [t])).map fun b => { track s (.types [t]) with base := b }
  | .exports [e] =>
    if e.item.sort = .type ∧ e.item.idx ∈ s.hoisted then
      some { track s (.exports [e]) with
        base := s.base.emit (.inst (.alias ⟨.type, .outer 0 e.item.idx⟩))
        hoisted := s.hoisted.erase e.item.idx }
    else
      match exportDescX s e with
      | none => none
      | some d => (step s.base (.exports [{ e with desc := some d }])).map fun b =>
          { track s (.exports [e]) with base := b }
  | x => (step s.base x).map fun b => { track s x with base := b }

/-- Replay a list of sections of one element, with look-ahead. -/
def replayX : XState → List Section → Option XState
  | s, [] => some s
  | s, x :: xs => (stepX s xs x).bind fun s' => replayX s' xs

/-- **The extended projection** of a component to its world. -/
def projectX (c : Ast) : Option WorldType :=
  (replayX {} (c.sections.flatMap splitSection)).map (·.base.decls)

end Silmaril.Wasm.Wit.Project
