module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Defs
import Silmaril.Formats.Parquet.Snapshot.Thms

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct

public section

theorem Source.bytes_exact {limits : Snapshot.Limits} {input : Bytes} (source : Source limits input) :
    source.snapshot.bytes = input :=
  Snapshot.check_bytes source.original

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct
