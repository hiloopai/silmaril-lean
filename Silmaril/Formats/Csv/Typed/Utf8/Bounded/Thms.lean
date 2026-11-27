module

public import Silmaril.Formats.Csv.Typed.Utf8.Bounded.Defs
import Silmaril.Proofs.Formats.Csv.Typed.Utf8.Bounded

public section

namespace Silmaril.Formats.Csv.Typed.Utf8.Bounded

variable {Kind : Type*} {Value : Kind → Type*}

/-- Success is exactly complete shared decoding within the data-row cap.
Header validation, nullable cells, row order and the terminal check agree. -/
theorem decode_ok_iff (schema : Schema Kind) (codecs : (kind : Kind) → CellCodec (Value kind))
    (maxRows : Nat) (wire : Bytes) (rows : Table schema Value) :
    decode maxRows schema codecs wire = .ok rows ↔
      Typed.Utf8.decode schema codecs wire = .ok rows ∧ rows.length ≤ maxRows :=
  Silmaril.Proofs.Formats.Csv.Typed.Utf8.Bounded.decode_ok_iff schema codecs maxRows wire rows

end Silmaril.Formats.Csv.Typed.Utf8.Bounded
