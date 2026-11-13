module

public import Mathlib.Data.Fintype.Basic

@[expose] public section

/-!
# Finite named types (`FinNamed`)

The base of every finite basic object: a type with a finite list of its elements, each with a
**name**, the names pairwise distinct. A finite machine's states and labels are `FinNamed`
types. Names are the bridge to documents (JSON, TOML, the project database): a typed machine
is written out by naming its states and labels, and read back by `ofName?`.

* `FinNamed α`: `elems` (every element occurs, `complete`), `name`, distinct names
  (`nodup`);
* `FinNamed.ofName?`: the element of a name; `ofName?_name` in `Thms`;
* `FinNamed.toFintype`: the Mathlib `Fintype` of a `FinNamed` type (the standard notion of
  finiteness; `FinNamed` adds only the names and their order);
* instances for `Bool` and `Unit` here, and for `Option`, `Sum` and `Prod` in `Thms` (names
  `none`/`some(a)`, `inl(a)`/`inr(b)` and `(a,b)` with `,` and `\` escaped inside the
  components, so distinctness is a theorem for every component type);
* the command `silmaril_finite T` (in `Silmaril.Automata.Named.Derive`) derives the instance
  for an inductive type whose constructor arguments are `FinNamed`.

**Name grammar.** A nullary constructor `c` is named `c`; a constructor with arguments
`c(a₁,…,aₙ)` from the arguments' names; a structure (one constructor) `(a₁,…,aₙ)`. Distinctness
is checked by evaluation when the instance is derived (`nodup := by decide`), so it holds for
every derived instance whatever the argument types.

**Identity.** A name is local to its type. A global identity is a pair of a document
identifier (`Silmaril.Automata.Ident`) and a local name, see `Silmaril.Automata.Spec`.
-/

namespace Silmaril.Automata

/-- A finite type whose elements carry pairwise distinct names. -/
class FinNamed (α : Type) where
  /-- Every element, in a fixed order (constructor order for derived instances). -/
  elems : List α
  /-- The name of an element. -/
  name : α → String
  complete : ∀ a, a ∈ elems
  nodup : (elems.map name).Nodup

namespace FinNamed

variable {α : Type} [FinNamed α]

/-- The names, in order. -/
def names (α : Type) [FinNamed α] : List String := (elems (α := α)).map name

/-- The element of a name. -/
def ofName? (s : String) : Option α := (elems (α := α)).find? (fun a => name a == s)

/-- The Mathlib `Fintype` of a `FinNamed` type. -/
@[instance_reducible] def toFintype (α : Type) [FinNamed α] : Fintype α where
  elems := ⟨(elems (α := α) : Multiset α), List.Nodup.of_map name nodup⟩
  complete a := Multiset.mem_coe.mpr (complete a)

/-- Decidable equality through names. -/
@[instance_reducible] def decEq (α : Type) [FinNamed α] : DecidableEq α := fun a b =>
  if h : name a = name b then
    isTrue (by
      have hi := List.inj_on_of_nodup_map (nodup (α := α))
      exact hi (complete a) (complete b) h)
  else isFalse (fun e => h (e ▸ rfl))

end FinNamed

instance : FinNamed Bool where
  elems := [false, true]
  name b := if b then "true" else "false"
  complete b := by cases b <;> simp
  nodup := by decide

instance : FinNamed Unit where
  elems := [()]
  name _ := "()"
  complete _ := by simp
  nodup := by simp

/-- Escape `,` and `\` with a backslash (the components of a pair name). -/
def escChar (c : Char) : List Char := if c = ',' ∨ c = '\\' then ['\\', c] else [c]

/-- A name with `,` and `\` escaped. -/
def escapeName (s : String) : String := String.ofList (s.toList.flatMap escChar)

/-- The name of `some a`. -/
def someName (a : String) : String := "some(" ++ a ++ ")"

/-- The name of `inl a`. -/
def inlName (a : String) : String := "inl(" ++ a ++ ")"

/-- The name of `inr b`. -/
def inrName (b : String) : String := "inr(" ++ b ++ ")"

/-- The name of a pair. -/
def pairName (a b : String) : String := "(" ++ escapeName a ++ "," ++ escapeName b ++ ")"

end Silmaril.Automata
