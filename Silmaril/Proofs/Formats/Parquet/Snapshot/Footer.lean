module

public import Silmaril.Formats.Parquet.Snapshot.Defs
import all Silmaril.Formats.Parquet.Snapshot.Defs

public section

namespace Silmaril.Proofs.Formats.Parquet.Snapshot.Footer

open Silmaril.Formats Parquet Snapshot

variable {Failure : Type*}

theorem check_footer {limits : Limits} {bytes : Bytes} {snapshot : Checked}
    (opened : check (Failure := Failure) limits bytes = .ok snapshot) :
    Footer.readFooter limits.footer bytes = .ok (snapshot.footer, snapshot.metadata) := by
  cases footer : Footer.readFooter limits.footer bytes with
  | error cause => simp [check, footer, Except.mapError, bind, Except.bind] at opened
  | ok pair =>
    obtain ⟨span, metadata⟩ := pair
    cases validated : Footer.validate span.start limits.maxSchemaDepth metadata with
    | error cause => simp [check, footer, validated, Except.mapError, bind, Except.bind] at opened
    | ok result =>
      cases result
      simp [check, footer, validated, Except.mapError, bind, Except.bind, pure, Except.pure] at opened
      subst snapshot
      rfl

end Silmaril.Proofs.Formats.Parquet.Snapshot.Footer
