module

public import Silmaril.Formats.Parquet.Snapshot.Defs
import Silmaril.Proofs.Formats.Parquet.Snapshot.Footer

public section

namespace Silmaril.Formats.Parquet.Snapshot

variable {Failure : Type*}

/-- The checked snapshot exposes the original footer span and parsed metadata. -/
theorem check_footer {limits : Limits} {bytes : Bytes} {snapshot : Checked}
    (opened : check (Failure := Failure) limits bytes = .ok snapshot) :
    Footer.readFooter limits.footer bytes = .ok (snapshot.footer, snapshot.metadata) :=
  Proofs.Formats.Parquet.Snapshot.Footer.check_footer opened

end Silmaril.Formats.Parquet.Snapshot
