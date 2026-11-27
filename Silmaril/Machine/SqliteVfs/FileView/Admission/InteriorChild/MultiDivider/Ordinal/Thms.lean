module

public import Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.Ordinal.Defs
import Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.Thms
import Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.Ordinal.Interval

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider

open Silmaril.Formats.Sqlite

/-- The ordinal returns the same pointer as the landed selector. -/
theorem Interior.childAt_ordinal (page : Interior) (key : Int) :
    page.childAt? (page.childOrdinal key) = some (page.choose key) :=
  Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.Ordinal.childAt_ordinal page key

/-- The selected ordinal always satisfies its adjacent signed bounds. -/
theorem Interior.ordinal_interval (page : Interior) (key : Int) :
    page.ChildInterval key (page.childOrdinal key) :=
  Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.Ordinal.ordinal_interval page key

/-- Strict pointer-order sorting gives the converse: the unique ordinal
whose adjacent bounds contain the key is the selected ordinal. -/
theorem Interior.ordinal_eq_iff_interval (page : Interior) (key : Int) (ordinal : Nat)
    (sorted : page.dividers.Pairwise (fun left right => left.upperKey < right.upperKey)) :
    page.childOrdinal key = ordinal ↔ page.ChildInterval key ordinal :=
  Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider.Ordinal.ordinal_eq_iff_interval page key ordinal sorted

/-- The packed parser supplies the strict order required for both
directions of the exact child interval contract. -/
theorem readable_ordinal_eq_iff_interval (view : File.View) (base : Nat) (page : Interior)
    (readable : Interior.read? view base = some page) (key : Int) (ordinal : Nat) :
    page.childOrdinal key = ordinal ↔ page.ChildInterval key ordinal :=
  page.ordinal_eq_iff_interval key ordinal (decoded_signed_order view base page readable)

/-- Even if the cell layout parses, the public parser rejects non-increasing
signed divider keys. -/
theorem read_rejects_unordered (view : File.View) (base : Nat) (page : Interior)
    (raw : Interior.read?.readPacked? view base = some page)
    (unordered : ¬ page.dividers.Pairwise (fun left right => left.upperKey < right.upperKey)) :
    Interior.read? view base = none := by
  simp [Interior.read?, raw, unordered]

end Silmaril.Machine.SqliteVfs.FileView.Admission.InteriorChild.MultiDivider
