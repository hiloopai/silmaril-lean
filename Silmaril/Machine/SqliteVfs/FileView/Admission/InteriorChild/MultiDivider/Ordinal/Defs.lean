module

public import Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider

open Silmaril.Formats.Sqlite

/-- The selected child in pointer-array order. The rightmost child has
ordinal `dividers.length`. -/
def Interior.childOrdinal (page : Interior) (key : Int) : Nat :=
  page.dividers.findIdx fun divider => decide (key ≤ divider.upperKey)

/-- Fetch the child encoded at this ordinal, including the rightmost
pointer stored in the interior header. -/
def Interior.childAt? (page : Interior) (ordinal : Nat) : Option Nat :=
  match page.dividers[ordinal]? with
  | some divider => some divider.leftChild
  | none => if ordinal = page.dividers.length then some page.rightmost else none

/-- The lower endpoint is strict and the upper endpoint inclusive.
The first child has no lower endpoint and the last has no upper endpoint. -/
def Interior.ChildInterval (page : Interior) (key : Int) (ordinal : Nat) : Prop :=
  ordinal ≤ page.dividers.length ∧
    (∀ j, j + 1 = ordinal → ∀ lower, page.dividers[j]? = some lower → lower.upperKey < key) ∧
    (∀ upper, page.dividers[ordinal]? = some upper → key ≤ upper.upperKey)

end Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider
