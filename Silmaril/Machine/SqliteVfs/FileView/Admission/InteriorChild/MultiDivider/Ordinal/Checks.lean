module

import Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.Ordinal.Thms
meta import Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.Ordinal.Defs
meta import Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.Defs
meta import Silmaril.Formats.Sqlite.File.Defs

namespace Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider

open Silmaril.Formats.Sqlite

private def exampleInterior : Interior :=
  ⟨[⟨3, -7, 502, 507⟩, ⟨4, 9, 507, 512⟩], 5⟩

example : exampleInterior.childOrdinal (-9223372036854775808) = 0 := by decide
example : exampleInterior.childOrdinal (-7) = 0 := by decide
example : exampleInterior.childOrdinal (-6) = 1 := by decide
example : exampleInterior.childOrdinal 9 = 1 := by decide
example : exampleInterior.childOrdinal 9223372036854775807 = 2 := by decide

example : exampleInterior.ChildInterval (-7) 0 := exampleInterior.ordinal_interval (-7)
example : ¬ exampleInterior.ChildInterval (-7) 1 := by
  intro bounds
  exact (by decide : ¬ ((-7 : Int) < -7)) (bounds.2.1 0 rfl ⟨3, -7, 502, 507⟩ rfl)

example : exampleInterior.ChildInterval 9223372036854775807 2 :=
  exampleInterior.ordinal_interval 9223372036854775807

example : exampleInterior.childAt? 2 = some 5 := by decide
example : exampleInterior.childAt? 3 = none := by decide

private def packedView (reversePointers : Bool) : File.View :=
  let header : Array UInt8 := #[5, 0, 0, 0, 2, 1, 246, 0, 0, 0, 0, 5]
  let pointers : Array UInt8 := if reversePointers then #[1, 251, 1, 246] else #[1, 246, 1, 251]
  let cells : Array UInt8 := #[0, 0, 0, 3, 7, 0, 0, 0, 4, 9]
  File.View.ofBytes ⟨⟨header ++ pointers ++ Array.replicate 486 0 ++ cells⟩⟩

#guard (Interior.read? (packedView false) 0).map (·.childOrdinal 7) == some 0
#guard (Interior.read? (packedView true) 0).isNone

private def unorderedInterior : Interior :=
  ⟨[⟨4, 9, 507, 512⟩, ⟨3, 7, 502, 507⟩], 5⟩

example (view : File.View) (base : Nat)
    (raw : Interior.read?.readPacked? view base = some unorderedInterior) :
    Interior.read? view base = none :=
  read_rejects_unordered view base unorderedInterior raw (by decide)

#print axioms Interior.childAt_ordinal
#print axioms Interior.ordinal_interval
#print axioms Interior.ordinal_eq_iff_interval
#print axioms readable_ordinal_eq_iff_interval
#print axioms read_rejects_unordered

end Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider
