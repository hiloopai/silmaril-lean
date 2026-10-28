module

public import Silmaril.Courses.Cambridge.L1.Syntax
public import Silmaril.Semantics.Operational.Environment
public import Mathlib.Data.Finmap

/-! # Finite partial stores for Cambridge L1

`Finmap` represents the finite partial functions from locations to integers on
p. 14. The shared `Semantics.Operational.Environment` is their partial-function view.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1

open Silmaril.Semantics

abbrev Store := Finmap (fun _ : Loc => Int)

namespace Store

def empty : Store := ∅

def lookup (s : Store) (loc : Loc) : Option Int := Finmap.lookup loc s

/-- L1 assignment updates only an already allocated location. -/
def update (s : Store) (loc : Loc) (value : Int) : Option Store :=
  if loc ∈ s then some (s.insert loc value) else none

/-- A convenient finite presentation for concrete examples. Later entries win. -/
def fromList (entries : List (Loc × Int)) : Store :=
  entries.foldl (fun s (loc, value) => s.insert loc value) empty

def toEnvironment (s : Store) : Operational.Environment Loc Int :=
  fun loc => lookup s loc

theorem supported (s : Store) :
    Operational.Environment.SupportedBy (toEnvironment s) s.keys.toList := by
  intro loc value present
  exact Finset.mem_toList.mpr
    (Finmap.mem_keys.mpr (Finmap.mem_of_lookup_eq_some present))

@[simp] theorem lookup_empty (loc : Loc) : lookup empty loc = none :=
  Finmap.lookup_empty loc

@[simp] theorem lookup_insert_same (s : Store) (loc : Loc) (value : Int) :
    lookup (s.insert loc value) loc = some value := Finmap.lookup_insert s

@[simp] theorem lookup_insert_other (s : Store) (loc other : Loc) (value : Int)
    (h : other ≠ loc) : lookup (s.insert loc value) other = lookup s other :=
  Finmap.lookup_insert_of_ne s h

theorem update_eq_some (s : Store) (loc : Loc) (value : Int) (h : loc ∈ s) :
    update s loc value = some (s.insert loc value) := by simp [update, h]

theorem update_eq_none (s : Store) (loc : Loc) (value : Int) (h : loc ∉ s) :
    update s loc value = none := by simp [update, h]

theorem toEnvironment_insert (s : Store) (loc : Loc) (value : Int) :
    toEnvironment (s.insert loc value) =
      Operational.Environment.set (toEnvironment s) loc value := by
  funext other
  by_cases h : other = loc
  · subst other
    simp [toEnvironment, Operational.Environment.set]
  · simp [toEnvironment, Operational.Environment.set, h]

end Store

end Silmaril.Courses.Cambridge.L1
