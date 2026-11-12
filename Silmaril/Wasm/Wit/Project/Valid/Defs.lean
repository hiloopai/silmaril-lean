module

public import Silmaril.Wasm.Wit.Project.Ext.Defs

/-!
# Validity of projected worlds: index scoping

Silmaril has no validator for the component binary AST. This module defines the part of
validation the projection is responsible for, **index scoping**: every type index and
instance index a declaration uses is bound by an earlier declaration.

* `wellScoped w` (worlds): `wCheck` walks the declarations of a component type,
  counting its type and instance indices (`WCount`), and checks every reference
  against the counts so far: the descriptors of imports and exports (`descOk`), the
  value types of type definitions (`defOk`; inside nested component and instance
  types only their outer aliases `(alias outer 1 k)` are checked, against the
  enclosing count), type aliases `(alias outer 0 k)` and export aliases of
  instances. `(value (eq i))` bounds and outer aliases of other sorts are rejected.
* `wellScopedC c` (components): `cCheck` does the same for the items of a component
  (counting types, instances, functions and components), checks the index of every
  exported item, the type of every `canon lift`, and that an export's ascription has
  the sort of the exported item (`sortOk`). Items the projection ignores (core
  modules and instances, `start`, values, custom sections, nested components) are
  not checked beyond their effect on the counts.

`projectX_wellScoped` (`Silmaril.Wasm.Wit.Project.Valid.Thms`): the projection of a
well-scoped component is a well-scoped component type.

Not checked: type equality and subtyping (a `canon lift` of a non-function type, an
ascription that does not match the item's type), names (uniqueness, kebab case),
resource and handle rules, and the inner scopes of nested types.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Project

open Silmaril.Wasm.Component.Binary

/-! ## References -/

/-- A value type refers to a bound type. -/
def valOk (t : Nat) : ValType → Bool
  | .prim _ => true
  | .idx k => decide (k < t)

/-- An optional value type refers to a bound type. -/
def optValOk (t : Nat) : Option ValType → Bool
  | none => true
  | some v => valOk t v

/-- A defined value type refers to bound types. -/
def defValOk (t : Nat) : DefValType → Bool
  | .prim _ => true
  | .record fs => fs.all fun f => valOk t f.2
  | .variant cs => cs.all fun c => optValOk t c.2
  | .list v => valOk t v
  | .tuple vs => vs.all (valOk t)
  | .flags _ => true
  | .enum _ => true
  | .option v => valOk t v
  | .result ok err => optValOk t ok && optValOk t err
  | .own k => decide (k < t)
  | .borrow k => decide (k < t)
  | .fixedList v _ => valOk t v
  | .stream v => optValOk t v
  | .future v => optValOk t v
  | .map k v => valOk t k && valOk t v

/-- A function type refers to bound types. -/
def funcOk (t : Nat) (f : FuncType) : Bool := f.params.all (fun p => valOk t p.2) && optValOk t f.result

/-- The outer aliases of a nested component or instance type refer to bound types of
the enclosing scope. -/
def nestedOk (t : Nat) (ds : List ComponentDecl) : Bool :=
  ds.all fun
    | .inst (.alias ⟨.type, .outer 1 k⟩) => decide (k < t)
    | _ => true

/-- A type definition refers to bound types. -/
def defOk (t : Nat) : DefType → Bool
  | .val d => defValOk t d
  | .func f => funcOk t f
  | .component ds => nestedOk t ds
  | .instance ds => nestedOk t (ds.map .inst)
  | .resource _ _ => true

/-- An extern descriptor refers to a bound type. -/
def descOk (t : Nat) : ExternDesc → Bool
  | .func k => decide (k < t)
  | .component k => decide (k < t)
  | .instance k => decide (k < t)
  | .type (.eq k) => decide (k < t)
  | .type .subResource => true
  | .value (.type v) => valOk t v
  | .value (.eq _) => false
  | .coreModule _ => true

/-! ## Worlds -/

/-- The type and instance counts of a component type. -/
structure WCount where
  t : Nat := 0
  i : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- The counts after a declaration with descriptor `d`. -/
def descBump (c : WCount) : ExternDesc → WCount
  | .type _ => { c with t := c.t + 1 }
  | .instance _ => { c with i := c.i + 1 }
  | _ => c

/-- One declaration of a component type, checked. -/
def wStep (c : WCount) : ComponentDecl → Option WCount
  | .import _ d => if descOk c.t d then some (descBump c d) else none
  | .inst (.export _ d) => if descOk c.t d then some (descBump c d) else none
  | .inst (.type dt) => if defOk c.t dt then some { c with t := c.t + 1 } else none
  | .inst (.coreType _) => some c
  | .inst (.alias ⟨.type, .outer 0 k⟩) => if k < c.t then some { c with t := c.t + 1 } else none
  | .inst (.alias ⟨.core .type, .outer 0 _⟩) => some c
  | .inst (.alias ⟨.type, .export j _⟩) => if j < c.i then some { c with t := c.t + 1 } else none
  | .inst (.alias ⟨.instance, .export j _⟩) =>
    if j < c.i then some { c with i := c.i + 1 } else none
  | .inst (.alias _) => none

/-- Check the declarations of a component type. -/
def wCheck : WCount → WorldType → Option WCount
  | c, [] => some c
  | c, d :: ds => (wStep c d).bind fun c' => wCheck c' ds

/-- **A well-scoped component type**: every index it uses is bound before. -/
def wellScoped (w : WorldType) : Bool := (wCheck {} w).isSome

/-! ## Components -/

/-- The type, instance, function and component counts of a component. -/
structure CCount where
  t : Nat := 0
  i : Nat := 0
  f : Nat := 0
  c : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- The count of a sort. -/
def CCount.of (k : CCount) : ItemSort → Option Nat
  | .type => some k.t
  | .instance => some k.i
  | .func => some k.f
  | .component => some k.c
  | _ => none

/-- One more item of a sort. -/
def CCount.bump (k : CCount) : ItemSort → CCount
  | .type => { k with t := k.t + 1 }
  | .instance => { k with i := k.i + 1 }
  | .func => { k with f := k.f + 1 }
  | .component => { k with c := k.c + 1 }
  | _ => k

/-- The sort of the items an extern descriptor describes. -/
def descSort : ExternDesc → ItemSort
  | .coreModule _ => .core .module
  | .func _ => .func
  | .value _ => .value
  | .type _ => .type
  | .component _ => .component
  | .instance _ => .instance

/-- An export's ascription has the sort of its item and refers to bound types. -/
def ascriptionOk (t : Nat) (e : Export) : Bool :=
  match e.desc with
  | none => true
  | some d => descOk t d && descSort d == e.item.sort

/-- An exported item is bound. -/
def itemOk (k : CCount) (x : SortIdx) : Bool :=
  match k.of x.sort with
  | some n => decide (x.idx < n)
  | none => true

/-- One item of a component (a section of one element), checked. -/
def cStep (k : CCount) : Section → Option CCount
  | .types [dt] => if defOk k.t dt then some (k.bump .type) else none
  | .coreTypes [_] => some k
  | .imports [im] => if descOk k.t im.desc then some (k.bump (descSort im.desc)) else none
  | .exports [e] =>
    if itemOk k e.item && ascriptionOk k.t e then some (k.bump e.item.sort) else none
  | .aliases [⟨.type, .outer 0 j⟩] => if j < k.t then some (k.bump .type) else none
  | .aliases [⟨.core _, _⟩] => some k
  | .aliases [⟨.type, .export j _⟩] => if j < k.i then some (k.bump .type) else none
  | .aliases [⟨.instance, .export j _⟩] => if j < k.i then some (k.bump .instance) else none
  | .aliases [⟨.func, .export j _⟩] => if j < k.i then some (k.bump .func) else none
  | .aliases [⟨.component, .export j _⟩] => if j < k.i then some (k.bump .component) else none
  | .instances [_] => some (k.bump .instance)
  | .canons [.lift _ _ ft] => if ft < k.t then some (k.bump .func) else none
  | .canons [_] => some k
  | .component _ => some (k.bump .component)
  | .custom _ _ => some k
  | .coreModule _ => some k
  | .coreInstances [_] => some k
  | .start _ => some k
  | .values [_] => some k
  | _ => none

/-- Check the items of a component, each a section of one element. -/
def cCheck : CCount → List Section → Option CCount
  | k, [] => some k
  | k, x :: xs => (cStep k x).bind fun k' => cCheck k' xs

/-- **A well-scoped component**: every index its items use is bound before, and
every export ascription has its item's sort. -/
def wellScopedC (c : Ast) : Bool := (cCheck {} (c.sections.flatMap splitSection)).isSome

end Silmaril.Wasm.Wit.Project
