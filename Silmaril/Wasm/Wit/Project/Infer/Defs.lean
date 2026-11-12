module

public import Silmaril.Wasm.Wit.Project.Ext.Defs

/-!
# The projection with type inference

`projectI` extends `Silmaril.Wasm.Wit.Project.projectX` with the type inference a
composition (a WAC-style component: instantiate, alias, export) needs. `projectX`
knows the type of an item only when the component gave it one (`canon lift`, an
import, an ascribed export); `projectI` also infers

* the type of an **aliased function** `(alias export i "f" (func))` and of an
  **aliased instance** `(alias export i "n" (instance))`, from the export table of
  instance `i`;
* the export table of an **instantiated instance** `(instantiate c …)`, from the
  component type of `c`, of an **inline instance** `(instance (export …) …)`, from the
  types of its items, of an **imported or exported instance**, from its instance type;
* the type of an exported instance created by `instantiate` or inline exports: the
  first type index of the component whose instance type has the same export table
  (`findInst`).

An **alias of an export of an instance the component creates** has no counterpart in
the world (the instance itself has none); `project` and `projectX` reject it,
`projectI` records it like the created instance (`PState.inst false`).

## Silmaril.Wasm.Component.Binary.Export tables and local type indices

A descriptor inside a component or instance type refers to that type's own type
index space. It is lifted to the enclosing component (`liftDesc`) only when the local
type is an outer alias `(alias outer 1 k (type))`, which is how a type defined in
the component is used inside an instance or component type; it then names the
component's type `k`, which the projection keeps at index `k` in the world. Every
other local type (an inline definition, an imported type, an export of a type) gives
no lifted descriptor: the world would need a new type definition, which the
index-preserving replay does not introduce. Such exports stay unknown and an
unascribed export of them still gives `none`.

What is kept of type definitions (`TInfo`): the export table of an instance type, and
of the instance a component type instantiates to. Other type indices (aliases,
imports, exports of types) have no table. Nested components (`Section.component`)
have no inferred type.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Project

open Silmaril.Wasm.Component.Binary

/-- The export table of an instance: each export's name and, if known, its descriptor
in the type index space of the component. -/
abbrev Table := List (String × Option ExternDesc)

/-- What inference keeps of a type definition. -/
inductive TInfo where
  /-- An instance type and its export table. -/
  | inst (tab : Table)
  /-- A component type and the export table of its instances. -/
  | comp (tab : Table)
  deriving Repr, DecidableEq, Inhabited

/-- Whether a declaration of a component or instance type allocates a local type index,
and if so the outer type index it aliases (`alias outer 1 k`), if any. -/
def declOuter : ComponentDecl → Option (Option Nat)
  | .import _ (.type _) => some none
  | .inst (.type _) => some none
  | .inst (.alias ⟨.type, .outer 1 k⟩) => some (some k)
  | .inst (.alias ⟨.type, _⟩) => some none
  | .inst (.export _ (.type _)) => some none
  | _ => none

/-- The local type indices of a declaration list, with the outer index each aliases. -/
def localOuter (ds : List ComponentDecl) : List (Option Nat) := ds.filterMap declOuter

/-- The outer type index of local type `j`. -/
def outerAt (lt : List (Option Nat)) (j : Nat) : Option Nat := (lt[j]?).getD none

/-- A descriptor of a component or instance type, lifted to the enclosing component. -/
def liftDesc (lt : List (Option Nat)) : ExternDesc → Option ExternDesc
  | .func j => (outerAt lt j).map .func
  | .instance j => (outerAt lt j).map .instance
  | .component j => (outerAt lt j).map .component
  | .type (.eq j) => (outerAt lt j).map fun k => .type (.eq k)
  | _ => none

/-- The export table of a declaration list. -/
def exportsTab (ds : List ComponentDecl) : Table :=
  ds.filterMap fun
    | .inst (.export n d) => some (n.name, liftDesc (localOuter ds) d)
    | _ => none

/-- What inference keeps of a type definition. -/
def tinfoOf : DefType → Option TInfo
  | .instance ds => some (.inst (exportsTab (ds.map .inst)))
  | .component ds => some (.comp (exportsTab ds))
  | _ => none

/-- The state of the replay with inference. -/
structure IState where
  /-- The state of the extended replay. -/
  x : XState := {}
  /-- What is known of each type index of the component. -/
  tinfo : List (Option TInfo) := []
  /-- The export table of each instance index of the component, if known. -/
  itab : List (Option Table) := []

/-- Look up a table entry. -/
def optAt {α : Type} (l : List (Option α)) (i : Nat) : Option α := (l[i]?).getD none

/-- The instance table of type `k`. -/
def instTabOf (s : IState) (k : Nat) : Option Table :=
  match optAt s.tinfo k with
  | some (.inst tab) => some tab
  | _ => none

/-- The instance table of the instances of the component type of component `c`. -/
def compTabOf (s : IState) (c : Nat) : Option Table :=
  match descAt s.x.cdesc c with
  | some (.component k) =>
    match optAt s.tinfo k with
    | some (.comp tab) => some tab
    | _ => none
  | _ => none

/-- The descriptor of export `n` of instance `i`, if known. -/
def aliasDesc (s : IState) (i : Nat) (n : String) : Option ExternDesc :=
  (optAt s.itab i).bind fun tab => (tab.lookup n).getD none

/-- The descriptor of an item of the component, if known. -/
def itemDesc (s : IState) (x : SortIdx) : Option ExternDesc :=
  match x.sort with
  | .func => descAt s.x.fdesc x.idx
  | .instance => descAt s.x.idesc x.idx
  | .component => descAt s.x.cdesc x.idx
  | .type => some (.type (.eq x.idx))
  | _ => none

/-- The first instance type of the component with export table `tab`. -/
def findInst (tinfo : List (Option TInfo)) (tab : Table) : Option Nat :=
  tinfo.findIdx? (· = some (.inst tab))

/-- The new entries of the type table: one per type index a section allocates
(mirroring `track`). -/
def tinfoNew : Section → List (Option TInfo)
  | .types [t] => [tinfoOf t]
  | .aliases [a] => if a.sort = .type then [none] else []
  | .imports [i] => match i.desc with
    | .type _ => [none]
    | _ => []
  | .exports [e] => if e.item.sort = .type then [none] else []
  | _ => []

/-- The table of a new instance index, if the section allocates one (mirroring `track`). -/
def itabNew (s : IState) : Section → Option (Option Table)
  | .instances [.instantiate c _] => some (compTabOf s c)
  | .instances [.exports es] => some (some (es.map fun e => (e.1.name, itemDesc s e.2)))
  | .aliases [a] =>
    if a.sort = .instance then
      some (match a.target with
        | .export i n => (aliasDesc s i n).bind fun
          | .instance k => instTabOf s k
          | _ => none
        | _ => none)
    else none
  | .imports [i] => match i.desc with
    | .instance k => some (instTabOf s k)
    | _ => none
  | .exports [e] => if e.item.sort = .instance then some (optAt s.itab e.item.idx) else none
  | _ => none

/-- Replace the last element of a list by `a` (append it to the empty list). -/
def setLast {α : Type} (l : List α) (a : α) : List α := l.dropLast ++ [a]

/-- The inferred descriptor of a created instance with export table `tab`. -/
def createdDesc (s : IState) (tab : Option Table) : Option ExternDesc :=
  tab.bind fun t => (findInst s.tinfo t).map .instance

/-- Fill in what inference knows about the item a section introduced. -/
def infer (s : IState) (sec : Section) (x : XState) : XState :=
  match sec with
  | .aliases [⟨.func, .export i n⟩] => { x with fdesc := setLast x.fdesc (aliasDesc s i n) }
  | .aliases [⟨.instance, .export i n⟩] => { x with idesc := setLast x.idesc (aliasDesc s i n) }
  | .instances [.instantiate c _] => { x with idesc := setLast x.idesc (createdDesc s (compTabOf s c)) }
  | .instances [.exports es] =>
    let tab : Table := es.map fun e => (e.1.name, itemDesc s e.2)
    { x with idesc := setLast x.idesc (createdDesc s (some tab)) }
  | _ => x

/-- Whether a section aliases an export of an instance without a world counterpart. -/
def createdAlias (s : IState) : Section → Bool
  | .aliases [⟨.instance, .export i _⟩] => (s.x.base.lookup i).isNone
  | _ => false

/-- The state after a section, from the extended replay's state `x`. -/
def finish (s : IState) (sec : Section) (x : XState) : IState :=
  ⟨infer s sec x, s.tinfo ++ tinfoNew sec, s.itab ++ (itabNew s sec).toList⟩

/-- The extended replay's step, or the record of an alias of a created instance. -/
def stepBase (s : IState) (rest : List Section) (sec : Section) : Option XState :=
  if createdAlias s sec then some { track s.x sec with base := s.x.base.inst false }
  else stepX s.x rest sec

/-- One step of the replay with inference. -/
def stepI (s : IState) (rest : List Section) (sec : Section) : Option IState :=
  (stepBase s rest sec).map (finish s sec)

/-- Replay a list of sections of one element, with look-ahead and inference. -/
def replayI : IState → List Section → Option IState
  | s, [] => some s
  | s, x :: xs => (stepI s xs x).bind fun s' => replayI s' xs

/-- **The projection with type inference** of a component to its world. -/
def projectI (c : Ast) : Option WorldType :=
  (replayI {} (c.sections.flatMap splitSection)).map (·.x.base.decls)

/-! ## A composition -/

/-- A WAC-style composition: a function type (type 0), an instance type exporting a
function of that type (type 1), a component type importing such an instance as `dep`
and exporting one as `api` (type 2); the component imports a component `c` of type 2
and an instance `dep` of type 1, instantiates `c` with `dep`, aliases its export `api`
and that instance's function `f`, and exports both without type ascriptions. -/
def composeExample : Ast :=
  .mk [.types [.func ⟨[("x", .prim .u32)], none, false⟩,
      .instance [.alias ⟨.type, .outer 1 0⟩, .export "f" (.func 0)],
      .component [.inst (.alias ⟨.type, .outer 1 1⟩), .import "dep" (.instance 0),
        .inst (.export "api" (.instance 0))]],
    .imports [⟨"c", .component 2⟩, ⟨"dep", .instance 1⟩],
    .instances [.instantiate 0 [("dep", ⟨.instance, 0⟩)]],
    .aliases [⟨.instance, .export 1 "api"⟩, ⟨.func, .export 2 "f"⟩],
    .exports [⟨"f", ⟨.func, 0⟩, none⟩, ⟨"api", ⟨.instance, 2⟩, none⟩]]

end Silmaril.Wasm.Wit.Project
