module

public import Silmaril.Wasm.Wit.Binary.Model.Defs

/-!
# WAC: item kinds and WIT subtyping

The kinds of the items a WAC composition manipulates (wac `5a7480c`,
`crates/wac-types/src/component.rs`, `ItemKind` and `Type`), over the WIT types
of the WIT formalization: value types are `Wit.Binary.Ty` and function types
`Wit.Binary.Sig` (async flag, named parameters, optional result).

* `func s`, `value t`: a function, a value;
* `resource r`: a resource type (wac compares resources by name);
* `type k`: a type definition, whose definiens is the kind `k` (wac's
  `ItemKind::Type`: a value type, a function type, a resource, an interface or a
  world);
* `inst id exports`: an instance of an interface, with the interface's package path
  `id` when it has one (`foo:bar/baz`);
* `comp id imports exports`: a component, with the world's path when it has one.

Exports and imports are lists of named items; wac keeps them in an `IndexMap`, so
names are unique in every list wac builds, and lookups take the first match.

## Subtyping

`Sub a b` is wac's `SubtypeChecker::is_subtype a b` (`crates/wac-types/src/checker.rs`):
functions, values and resources are compared by equality (wac: "subtyping for
functions is done in terms of equality"); an instance is a subtype of another when it
has every export of the other, at a subtype (width and depth subtyping); a component
is a subtype of another when it has every export of the other at a subtype, and
every import of its own is an import of the other at a *supertype* (contravariance:
it may import less). Interface/world identifiers do not matter.

The checker `sub` decides it (`sub_iff`, `Wac.Types.Thms`).

**Restriction.** Value types are compared *structurally on the resolved WIT model*
(`Wit.Binary.Ty`, whose named types are references `TyRef`). wac first resolves type
aliases (`Types::resolve_value_type`) and then compares structurally. Here aliases are
expanded before comparing: in the document's declarations as they are elaborated
(`Silmaril.Wasm.Wac.WitDecl`), in the registry by `Kind.expand` (`elabDocA`,
`Silmaril.Wasm.Wac.Alias`). A reference to a record, variant, enum or flags type is
compared by its name and owner, not structurally.

## Merging implicit imports

`merge a b` is wac's `TypeAggregator::merge_item_kind` (`aggregator.rs`), which
merges the types of two implicit imports of the same name: two instances merge to
the union of their exports, where a common export must be comparable and the merge
keeps the *larger* of the two; two components merge imports (keeping the smaller) and
exports (keeping the larger); functions, values and resources merge only when equal.
Which implicit imports are merged (equal names, or semver-compatible ones, keeping the
highest version) is decided in `Silmaril.Wasm.Wac.Implicit`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Wit.Binary (Ty Sig)

/-- The kind of a WAC item. -/
inductive Kind where
  | func (s : Sig)
  | value (t : Ty)
  | resource (name : String)
  | type (k : Kind)
  | inst (id : Option String) (exports : List (String × Kind))
  | comp (id : Option String) (imports exports : List (String × Kind))
  deriving Repr, Inhabited

/-! ## Decidable equality (not derivable for the nested inductive) -/

mutual
def Kind.beq : Kind → Kind → Bool
  | .func a, .func b => decide (a = b)
  | .value a, .value b => decide (a = b)
  | .resource a, .resource b => decide (a = b)
  | .type a, .type b => Kind.beq a b
  | .inst i as, .inst j bs => decide (i = j) && Kind.beqEx as bs
  | .comp i ai ae, .comp j bi be => decide (i = j) && Kind.beqEx ai bi && Kind.beqEx ae be
  | _, _ => false
def Kind.beqEx : List (String × Kind) → List (String × Kind) → Bool
  | [], [] => true
  | (k, a) :: as, (k', b) :: bs => decide (k = k') && Kind.beq a b && Kind.beqEx as bs
  | _, _ => false
end

mutual
theorem Kind.eq_of_beq : ∀ a b : Kind, a.beq b = true → a = b
  | .func _, .func _, h | .value _, .value _, h | .resource _, .resource _, h => by
    simp [Kind.beq] at h; rw [h]
  | .type a, .type b, h => by rw [Kind.eq_of_beq a b (by simpa [Kind.beq] using h)]
  | .inst i as, .inst j bs, h => by
    simp only [Kind.beq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1, Kind.eqEx_of_beq as bs h.2]
  | .comp i ai ae, .comp j bi be, h => by
    simp only [Kind.beq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1, Kind.eqEx_of_beq ai bi h.1.2, Kind.eqEx_of_beq ae be h.2]
  | .func _, .value _, h | .func _, .resource _, h | .func _, .type _, h | .func _, .inst _ _, h | .func _, .comp _ _ _, h
  | .value _, .func _, h | .value _, .resource _, h | .value _, .type _, h | .value _, .inst _ _, h | .value _, .comp _ _ _, h
  | .resource _, .func _, h | .resource _, .value _, h | .resource _, .type _, h | .resource _, .inst _ _, h | .resource _, .comp _ _ _, h
  | .type _, .func _, h | .type _, .value _, h | .type _, .resource _, h | .type _, .inst _ _, h | .type _, .comp _ _ _, h
  | .inst _ _, .func _, h | .inst _ _, .value _, h | .inst _ _, .resource _, h | .inst _ _, .type _, h | .inst _ _, .comp _ _ _, h
  | .comp _ _ _, .func _, h | .comp _ _ _, .value _, h | .comp _ _ _, .resource _, h | .comp _ _ _, .type _, h | .comp _ _ _, .inst _ _, h =>
    by simp [Kind.beq] at h
theorem Kind.eqEx_of_beq : ∀ as bs : List (String × Kind), Kind.beqEx as bs = true → as = bs
  | [], [], _ => rfl
  | (k, a) :: as, (k', b) :: bs, h => by
    simp only [Kind.beqEx, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1, Kind.eq_of_beq a b h.1.2, Kind.eqEx_of_beq as bs h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [Kind.beqEx] at h
end

mutual
theorem Kind.beq_self : ∀ a : Kind, a.beq a = true
  | .func _ | .value _ | .resource _ => by simp [Kind.beq]
  | .type a => by simpa [Kind.beq] using Kind.beq_self a
  | .inst _ as => by simpa [Kind.beq] using Kind.beqEx_self as
  | .comp _ ai ae => by simpa [Kind.beq] using ⟨Kind.beqEx_self ai, Kind.beqEx_self ae⟩
theorem Kind.beqEx_self : ∀ as : List (String × Kind), Kind.beqEx as as = true
  | [] => rfl
  | (_, a) :: as => by simpa [Kind.beqEx] using ⟨Kind.beq_self a, Kind.beqEx_self as⟩
end

instance : DecidableEq Kind := fun a b =>
  if h : a.beq b then isTrue (Kind.eq_of_beq a b h)
  else isFalse fun e => h (e ▸ Kind.beq_self a)

/-- Named items: the exports of an instance, the imports or exports of a component. -/
abbrev Externs := List (String × Kind)

/-- The first item of a name. -/
def Externs.find (es : Externs) (n : String) : Option Kind := es.lookup n

/-- The names of a list of named items. -/
def Externs.names (es : Externs) : List String := es.map (·.1)

/-- wac's `ItemKind::promote`: an imported interface type is an instance, an imported
world type a component. -/
def Kind.promote : Kind → Kind
  | .type (.inst i es) => .inst i es
  | .type (.comp i is es) => .comp i is es
  | k => k

/-- The interface identifier of an instance. -/
def Kind.instId : Kind → Option String
  | .inst i _ => i
  | _ => none

/-- The exports of an instance (`none` for anything else). -/
def Kind.exports? : Kind → Option Externs
  | .inst _ es => some es
  | _ => none

/-! ## Subtyping as a relation -/

mutual
/-- `Sub a b`: `a` is a subtype of `b`. -/
inductive Sub : Kind → Kind → Prop
  | func (s : Sig) : Sub (.func s) (.func s)
  | value (t : Ty) : Sub (.value t) (.value t)
  | resource (r : String) : Sub (.resource r) (.resource r)
  | type {a b : Kind} : Sub a b → Sub (.type a) (.type b)
  | inst {i j : Option String} {as bs : Externs} : SubEx as bs → Sub (.inst i as) (.inst j bs)
  | comp {i j : Option String} {ai ae bi be : Externs} :
      SubEx bi ai → SubEx ae be → Sub (.comp i ai ae) (.comp j bi be)

/-- `SubEx as bs`: every item `(k, b)` of `bs` has an item `(k, a)` in `as` with
`Sub a b` (width and depth subtyping of named items). -/
inductive SubEx : Externs → Externs → Prop
  | nil (as : Externs) : SubEx as []
  | cons {as bs : Externs} {k : String} {a b : Kind} :
      (k, a) ∈ as → Sub a b → SubEx as bs → SubEx as ((k, b) :: bs)
end

/-! ## The checker -/

mutual
/-- Decide `Sub a b`. -/
def sub : Kind → Kind → Bool
  | .func s, .func s' => decide (s = s')
  | .value t, .value t' => decide (t = t')
  | .resource r, .resource r' => decide (r = r')
  | .type a, .type b => sub a b
  | .inst _ as, .inst _ bs => subEx as bs
  | .comp _ ai ae, .comp _ bi be => subEx bi ai && subEx ae be
  | _, _ => false
  termination_by a b => sizeOf a + sizeOf b

/-- Decide `SubEx as bs`. -/
def subEx (as : Externs) : Externs → Bool
  | [] => true
  | (k, b) :: bs => anyMatch as k b && subEx as bs
  termination_by bs => sizeOf as + sizeOf bs

/-- Some item `(k, a)` of `as` has `sub a b`. -/
def anyMatch : Externs → String → Kind → Bool
  | [], _, _ => false
  | (k', a) :: as, k, b => (k' == k && sub a b) || anyMatch as k b
  termination_by as _ b => sizeOf as + sizeOf b
end

/-! ## Merging (wac's `TypeAggregator`) -/

/-- Replace the item named `n`. -/
def Externs.replace (es : Externs) (n : String) (k : Kind) : Externs :=
  es.map fun p => if p.1 = n then (n, k) else p

/-- Merge the named items `ns` into `es`: a new name is appended; for a known name,
`keepNew = false` (exports) keeps the existing item when the new one is a subtype of
it and else takes the new one if the existing one is a subtype of it;
`keepNew = true` (imports) does the same with the comparisons swapped. -/
def mergeEx (contra : Bool) (es : Externs) : Externs → Option Externs
  | [] => some es
  | (n, src) :: ns =>
    match es.find n with
    | none => mergeEx contra (es ++ [(n, src)]) ns
    | some tgt =>
      let (keep, repl) := if contra then (sub tgt src, sub src tgt) else (sub src tgt, sub tgt src)
      if keep then mergeEx contra es ns
      else if repl then mergeEx contra (es.replace n src) ns
      else none

/-- Merge the kind `b` of an implicit import into the kind `a` already recorded
under the same name (wac's `merge_item_kind`). -/
def merge : Kind → Kind → Option Kind
  | .inst i es, .inst _ ns => (mergeEx false es ns).map (.inst i)
  | .comp i ei ee, .comp _ ni ne => do
    let is ← mergeEx true ei ni
    let xs ← mergeEx false ee ne
    pure (.comp i is xs)
  | .func a, .func b => if a = b then some (.func a) else none
  | .value a, .value b => if a = b then some (.value a) else none
  | .resource a, .resource b => if a = b then some (.resource a) else none
  | .type a, .type b => (merge a b).map .type
  | _, _ => none

/-- Kinds whose subtypes are themselves: functions, values, resources and type
definitions of those. Every export of a WIT interface is flat. -/
def Kind.flat : Kind → Bool
  | .func _ | .value _ | .resource _ => true
  | .type k => k.flat
  | _ => false

/-- WIT-shaped kinds: flat kinds and instances whose exports are flat (the instances of
WIT interfaces, which export only functions and types). -/
def Kind.wit : Kind → Bool
  | .inst _ es => es.all (·.2.flat)
  | k => k.flat

end Silmaril.Wasm.Wac
