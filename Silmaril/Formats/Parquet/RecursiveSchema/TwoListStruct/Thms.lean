module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Defs
import Silmaril.Formats.Parquet.Snapshot.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Required

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct

public section

theorem Source.bytes_exact {limits : Snapshot.Limits} {input : Bytes} (source : Source limits input) :
    source.snapshot.bytes = input :=
  Snapshot.check_bytes source.original

theorem openRequired_of_open {limits : Snapshot.Limits} {input : Bytes} {source : Source limits input}
    (original : openFile limits input = .ok source) :
    openRequired limits input =
      if source.schema.plan.element.nullable then .error .structShape else .ok source := by
  simp [openRequired, original]

theorem openRequired_exact {limits : Snapshot.Limits} {input : Bytes} {source : Source limits input}
    (accepted : openRequired limits input = .ok source) :
    openFile limits input = .ok source ∧ source.schema.plan.element.nullable = false :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.openRequired_exact accepted

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct
