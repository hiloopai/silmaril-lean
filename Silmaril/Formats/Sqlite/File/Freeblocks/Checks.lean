module

import Silmaril.Formats.Sqlite.File.Freeblocks.Thms

namespace Silmaril.Formats.Sqlite.File.Freeblocks

open Silmaril.Formats.Sqlite
set_option maxRecDepth 2048

private def view (next length : UInt8) : File.View :=
  File.View.ofBytes ⟨⟨#[0, 0, 0, 0, 0, next, 0, length, 99, 99, 0, 0, 0, 4]⟩⟩

example : read? (view 10 4) 4 2 4 = some [⟨4, 8⟩, ⟨10, 14⟩] := by rfl
example : read? (view 10 4) 4 1 4 = none := by rfl
example : read? (view 4 4) 4 2 4 = none := by rfl
example : read? (view 10 3) 4 2 4 = none := by rfl
example : read? (view 10 32) 4 2 4 = none := by rfl

example : covers 4 14 [⟨4, 8⟩, ⟨8, 10⟩, ⟨10, 14⟩] = true := by rfl
example : covers 4 14 [⟨4, 8⟩, ⟨7, 10⟩, ⟨10, 14⟩] = false := by rfl
example : covers 4 14 [⟨4, 8⟩, ⟨9, 10⟩, ⟨10, 14⟩] = false := by rfl

#print axioms read_bounded_ordered
#print axioms cover_order
#print axioms cover_partition

end Silmaril.Formats.Sqlite.File.Freeblocks
