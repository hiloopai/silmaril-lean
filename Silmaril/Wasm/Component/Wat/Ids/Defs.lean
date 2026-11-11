module

public import Silmaril.Wasm.Component.Wat.Defs

/-!
# Component WAT: symbolic identifiers

Hand-written component WAT (for instance a WAC composition written as WAT) names
items with identifiers `$x` instead of numeric indices. `resolve` turns such an
S-expression into the numeric one `Wat.read` takes: binders are removed and every
reference `$x` is replaced by the index of the item it names, following the index
spaces of `Explainer.md` (component-model `8505ba7`):

* one index space per sort (core `func`, `table`, `memory`, `global`, `type`,
  `module`, `instance`; component `func`, `value`, `type`, `component`, `instance`),
  per scope; a nested component, a component type and an instance type open a scope;
* items that define an index: core modules, core instances, core types,
  `core func (canon …)`, `func (canon lift …)`, nested components, instances,
  aliases (in the space of their sort), types, imports and exports (in the space of
  their descriptor or exported item: an export introduces a new index), values and
  the results of `start`; in component and instance types: types, core types,
  aliases, imports and exports;
* the binder follows the item's keywords (`(type $t …)`, `(core func $f …)`,
  `(export $e "n" …)`), or sits in the descriptor of an import or in the sort of an
  alias (`(import "n" (func $f (type 0)))`, `(alias export $i "n" (func $f))`);
* a reference is resolved in the space its list names: `(func $f)`, `(type $t)`,
  `(instance $i)`, `(core func $f)`, `(memory $m)`, `(realloc $f)`,
  `(post-return $f)`, `(callback $f)`; under `core` items the sort keywords name core
  spaces (`(core instance (instantiate $m (with "n" (instance $i))))`), under `canon`
  component ones again; `(eq $x)` takes its parent's space; `alias export $i` is an
  instance (`alias core export $i` a core instance); `instantiate $c` a component (a
  core module under `core`); `start $f` a function; every other `$x` (value types:
  `(list $t)`, `(field "a" $t)`, `(own $r)`, `(canon resource.new $r)`, …) a type;
* `(alias outer $C $T (type))`: `$C` is the label of an enclosing component or type
  (its distance, `0` for the current scope) and `$T` a type of that scope.

Numeric indices are kept. `resolve` is the identity on S-expressions without `$`
atoms (`Silmaril.Wasm.Component.Wat.resolve_noIds`), so `readIds` extends `read`.
Not covered: identifiers inside core module types and core function types, inline
type definitions in import descriptors, binders on `start` results.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Wat

/-! ## Index spaces and scopes -/

/-- The index spaces of a scope. -/
inductive Space where
  | coreFunc | coreTable | coreMemory | coreGlobal | coreType | coreModule | coreInstance
  | func | value | type | component | instance
  deriving Repr, DecidableEq, Inhabited

/-- One scope: the names it binds, the number of items of each space, its label. -/
structure Scope where
  names : List (Space × String × Nat) := []
  counts : List (Space × Nat) := []
  label : Option String := none
  /-- A component or instance type (its exports declare, with the binder in the
  descriptor), rather than a component. -/
  isType : Bool := false
  deriving Repr, Inhabited

/-- An identifier: an atom starting with `$`. -/
def isId (a : String) : Bool := a.toList.head? = some '$'

/-- The number of items of a space. -/
def Scope.count (s : Scope) (sp : Space) : Nat :=
  ((s.counts.find? (·.1 = sp)).map (·.2)).getD 0

/-- Add an item of space `sp`, named `b` if given. -/
def Scope.add (s : Scope) (sp : Space) (b : Option String) : Scope :=
  let i := s.count sp
  { s with
    counts := (sp, i + 1) :: s.counts.filter (·.1 ≠ sp)
    names := match b with
      | some x => (sp, x, i) :: s.names
      | none => s.names }

/-- The index a name has in a space. -/
def Scope.lookup (s : Scope) (sp : Space) (x : String) : Option Nat :=
  (s.names.find? fun e => e.1 = sp ∧ e.2.1 = x).map (·.2.2)

/-- The space a sort keyword names (`core`: under a core item). -/
def spaceOf (core : Bool) : String → Option Space
  | "func" => some (if core then .coreFunc else .func)
  | "table" => some .coreTable
  | "memory" => some .coreMemory
  | "global" => some .coreGlobal
  | "type" => some (if core then .coreType else .type)
  | "module" => some .coreModule
  | "instance" => some (if core then .coreInstance else .instance)
  | "component" => some .component
  | "value" => some .value
  | "realloc" | "post-return" | "callback" | "dtor" => some .coreFunc
  | _ => none

/-- The space of a sort list `(S …)` or `(core S …)`. -/
def sortSpace : Sexp → Option Space
  | .list (.atom "core" :: .atom k :: _) => spaceOf true k
  | .list (.atom k :: _) => spaceOf false k
  | _ => none

/-- Remove a leading binder. -/
def stripId : List Sexp → List Sexp × Option String
  | .atom a :: r => if isId a then (r, some a) else (.atom a :: r, none)
  | r => (r, none)

/-- Remove the binder of a sort list `(S $x …)` or `(core S $x …)`. -/
def stripSortId : Sexp → Sexp × Option String
  | .list (.atom "core" :: .atom k :: r) =>
    ((.list (.atom "core" :: .atom k :: (stripId r).1)), (stripId r).2)
  | .list (.atom k :: r) => (.list (.atom k :: (stripId r).1), (stripId r).2)
  | s => (s, none)

/-- Strip the binder of the last element of a list. -/
def stripLast : List Sexp → List Sexp × Option String
  | [] => ([], none)
  | [s] => ([(stripSortId s).1], (stripSortId s).2)
  | s :: r => (s :: (stripLast r).1, (stripLast r).2)

/-- The descriptor or exported item of an import or export after its name and
attributes: the first list that is not an attribute. -/
def firstSort : List Sexp → Option Space
  | [] => none
  | s :: r => match R.attr s with
    | some _ => firstSort r
    | none => match sortSpace s with
      | some sp => some sp
      | none => firstSort r

/-- What an item defines: its space (if any), the item without its binder, the binder,
and the number of extra value indices (`start` results). -/
def defOf (inType : Bool) : List Sexp → Option Space × List Sexp × Option String
  | .atom "export" :: r =>
    if inType then ((r.getLast?.bind sortSpace), .atom "export" :: (stripLast r).1, (stripLast r).2)
    else (firstSort (stripId r).1, .atom "export" :: (stripId r).1, (stripId r).2)
  | .atom "component" :: r => (some .component, .atom "component" :: r, (stripId r).2)
  | .atom "core" :: .atom k :: r =>
    (spaceOf true k, .atom "core" :: .atom k :: (stripId r).1, (stripId r).2)
  | .atom "alias" :: r =>
    ((r.getLast?.bind sortSpace), .atom "alias" :: (stripLast r).1, (stripLast r).2)
  | .atom "import" :: r => ((r.getLast?.bind sortSpace), .atom "import" :: (stripLast r).1,
      (stripLast r).2)
  | .atom k :: r =>
    match spaceOf false k with
    | some sp => (some sp, .atom k :: (stripId r).1, (stripId r).2)
    | none => (none, .atom k :: r, none)
  | r => (none, r, none)

/-- The number of values a `start` item creates. -/
def startValues : List Sexp → Nat
  | .atom "start" :: r => r.countP fun
    | .list (.atom "result" :: _) => true
    | _ => false
  | _ => 0

/-! ## Resolution -/

/-- Resolve one atom in a space: an identifier is looked up in the innermost scope. -/
def rAtom (sc : List Scope) (sp : Space) (a : String) : Option Sexp :=
  if isId a then
    match sc with
    | s :: _ => (s.lookup sp a).map num
    | [] => none
  else some (.atom a)

/-- The distance of the scope labelled `a`, or the number `a`. -/
def rOuter (sc : List Scope) (a : String) : Option Nat :=
  if isId a then sc.findIdx? (·.label = some a) else num? (.atom a)

/-- The space of the direct atoms of a list `(k …)`. -/
def ctxSpace (core : Bool) (parent : Space) (k : String) : Space :=
  if k = "eq" then parent
  else if k = "instantiate" then (if core then .coreModule else .component)
  else if k = "start" then .func
  else (spaceOf core k).getD .type

mutual
/-- Resolve the references of an S-expression (`core`: under a core item; `sp`: the
space of the enclosing list). -/
def rRefs (sc : List Scope) (core : Bool) (sp : Space) : Sexp → Option Sexp
  | .atom a => rAtom sc sp a
  | .str b => some (.str b)
  | .list (.atom "alias" :: .atom "export" :: .atom i :: r) => do
    let i' ← rAtom sc .instance i
    let r' ← rRefsL sc core sp r
    pure (.list (.atom "alias" :: .atom "export" :: i' :: r'))
  | .list (.atom "alias" :: .atom "core" :: .atom "export" :: .atom i :: r) => do
    let i' ← rAtom sc .coreInstance i
    let r' ← rRefsL sc core sp r
    pure (.list (.atom "alias" :: .atom "core" :: .atom "export" :: i' :: r'))
  | .list (.atom "alias" :: .atom "outer" :: .atom c :: .atom t :: r) => do
    let c' ← if isId c then (rOuter sc c).map num else some (.atom c)
    let t' ← if isId t then (do
        let d ← rOuter sc c
        let s ← sc[d]?
        (s.lookup .type t).map num) else some (.atom t)
    let r' ← rRefsL sc core sp r
    pure (.list (.atom "alias" :: .atom "outer" :: c' :: t' :: r'))
  | .list (.atom "core" :: .atom k :: r) =>
    (rRefsL sc true (ctxSpace true sp k) r).map fun r' => .list (.atom "core" :: .atom k :: r')
  | .list (.atom "canon" :: r) =>
    (rRefsL sc false .type r).map fun r' => .list (.atom "canon" :: r')
  | .list (.atom k :: r) => (rRefsL sc core (ctxSpace core sp k) r).map fun r' => .list (.atom k :: r')
  | .list r => (rRefsL sc core sp r).map .list
/-- `rRefs` on every element. -/
def rRefsL (sc : List Scope) (core : Bool) (sp : Space) : List Sexp → Option (List Sexp)
  | [] => some []
  | s :: r => do
    let s' ← rRefs sc core sp s
    let r' ← rRefsL sc core sp r
    pure (s' :: r')
end

/-- Whether an item list is a core item. -/
def isCore : List Sexp → Bool
  | .atom "core" :: _ => true
  | _ => false

mutual
/-- Resolve an item after its binder was removed: nested components and component or
instance types open a scope labelled `b`. `n` is fuel. -/
def rItem : Nat → List Scope → Option String → List Sexp → Option Sexp
  | 0, _, _, _ => none
  | n + 1, sc, b, .atom "component" :: r =>
    (rItemsAt n ({ label := b } :: sc) (stripId r).1).map fun r' => .list (.atom "component" :: r')
  | n + 1, sc, b, [.atom "type", .list (.atom "component" :: ds)] =>
    (rItemsAt n ({ label := b, isType := true } :: sc) ds).map fun ds' =>
      .list [.atom "type", .list (.atom "component" :: ds')]
  | n + 1, sc, b, [.atom "type", .list (.atom "instance" :: ds)] =>
    (rItemsAt n ({ label := b, isType := true } :: sc) ds).map fun ds' =>
      .list [.atom "type", .list (.atom "instance" :: ds')]
  | _ + 1, sc, _, xs => rRefs sc (isCore xs) .type (.list xs)
/-- Resolve items in order, each in the scope extended by the items before it. -/
def rItemsAt : Nat → List Scope → List Sexp → Option (List Sexp)
  | 0, _, _ => none
  | _ + 1, _, [] => some []
  | n + 1, sc, .list xs :: r =>
    match sc with
    | [] => none
    | s :: outer => do
      let it' ← rItem n sc (defOf s.isType xs).2.2 (defOf s.isType xs).2.1
      let s1 := match (defOf s.isType xs).1 with
        | some sp => s.add sp (defOf s.isType xs).2.2
        | none => s
      let s2 := (List.range (startValues xs)).foldl (fun s _ => s.add .value none) s1
      let r' ← rItemsAt n (s2 :: outer) r
      pure (it' :: r')
  | n + 1, sc, s :: r => do
    let s' ← rRefs sc false .type s
    let r' ← rItemsAt n sc r
    pure (s' :: r')
end

mutual
/-- The number of nodes of an S-expression. -/
def Sexp.nodes : Sexp → Nat
  | .atom _ | .str _ => 1
  | .list xs => 1 + Sexp.nodesL xs
/-- The number of nodes of S-expressions. -/
def Sexp.nodesL : List Sexp → Nat
  | [] => 0
  | x :: xs => Sexp.nodes x + Sexp.nodesL xs
end

mutual
/-- No atom is an identifier. -/
def noIds : Sexp → Bool
  | .atom a => !isId a
  | .str _ => true
  | .list xs => noIdsL xs
/-- `noIds` of every element. -/
def noIdsL : List Sexp → Bool
  | [] => true
  | x :: xs => noIds x && noIdsL xs
end

/-- Resolve the identifiers of a component. -/
def resolve : Sexp → Option Sexp
  | .list (.atom "component" :: r) =>
    (rItemsAt (2 * Sexp.nodesL r + 2) [{ label := (stripId r).2 }] (stripId r).1).map fun r' =>
      .list (.atom "component" :: r')
  | _ => none

/-- Read a component from WAT with identifiers. -/
def readIds (s : String) : Option Binary.Ast :=
  match Sexp.read s with
  | some [x] => resolve x >>= ofSexp
  | _ => none

end Silmaril.Wasm.Component.Wat
