module

public import Silmaril.Formats.Compression.HistoryCopy.Defs
import Silmaril.Proofs.Formats.Compression.HistoryCopy.Contracts

public section

namespace Silmaril.Formats.Compression.HistoryCopy

/-- Each emitted byte comes from exactly distance bytes back in the
    history extended by the earlier bytes of this same copy. -/
theorem copy_sound {distance : Nat} (positive : 0 < distance) (count : Nat)
    (data : Array UInt8) (available : distance ≤ data.size) :
    ∃ bytes, (copy distance positive count data available).toList = data.toList ++ bytes ∧
      bytes.length = count ∧ Wire distance data.toList bytes :=
  Proofs.Formats.Compression.HistoryCopy.copy_sound positive count data available

/-- An indexed byte uses only the original history and earlier output. -/
theorem Wire.byte_at {distance : Nat} {history bytes : List UInt8} (wire : Wire distance history bytes)
    {index : Nat} (bound : index < bytes.length) :
    bytes[index]? = (history ++ bytes.take index)[history.length + index - distance]? :=
  Proofs.Formats.Compression.HistoryCopy.Wire.byte_at wire bound

end Silmaril.Formats.Compression.HistoryCopy
