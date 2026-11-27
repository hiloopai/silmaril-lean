module

public import Silmaril.Formats.Csv.Typed.Defs
import Silmaril.Proofs.Formats.Csv.Typed

/-! # Round trips for typed, nullable CSV tables -/

public section

namespace Silmaril.Formats.Csv.Typed

variable {Kind : Type*} {Value : Kind → Type*} {schema : Schema Kind}
variable {codecs : (kind : Kind) → CellCodec (Value kind)}

/-- A successful dependent traversal retains the result at each original position. -/
theorem collect_ok {E : Type*} {n : Nat} {α : Fin n → Type*}
    (f : (i : Fin n) → Except E (α i)) (values : (i : Fin n) → α i) :
    Internal.collect f = .ok values ↔ ∀ i, f i = .ok (values i) :=
  Proofs.Formats.Csv.Typed.collect_ok f values

/-- Successful lexical export and import recover the ordered typed table. -/
theorem importRows_exportRows (law : ∀ k, (codecs k).ParsePrint)
    {table : Table schema Value} {rows : Rows} (h : exportRows schema codecs table = .ok rows) :
    importRows schema codecs rows = .ok table :=
  Proofs.Formats.Csv.Typed.importRows_exportRows law h

/-- With exact text printing, successfully imported lexical rows are recovered. -/
theorem exportRows_importRows (law : ∀ k, (codecs k).PrintParse)
    {table : Table schema Value} {rows : Rows} (h : importRows schema codecs rows = .ok table) :
    exportRows schema codecs table = .ok rows :=
  Proofs.Formats.Csv.Typed.exportRows_importRows law h

/-- The marker file has one header and one marker per zero-column row. -/
theorem exportRows_zeroColumns (zero : schema.width = 0) (table : Table schema Value) :
    exportRows schema codecs table = .ok (List.replicate (table.length + 1) [[]]) :=
  Proofs.Formats.Csv.Typed.exportRows_zeroColumns zero table

/-- Successful byte export preserves the ordered nullable table on import. -/
theorem decode_encode (law : ∀ k, (codecs k).ParsePrint)
    {table : Table schema Value} {wire : Bytes} (h : encode schema codecs table = .ok wire) :
    decode schema codecs wire = .ok table :=
  Proofs.Formats.Csv.Typed.decode_encode law h

/-- Successful byte import can be re-encoded with the same ordered lexical rows. -/
theorem encode_of_decode (law : ∀ k, (codecs k).PrintParse)
    {table : Table schema Value} {input : Bytes} (h : decode schema codecs input = .ok table) :
    ∃ output, encode schema codecs table = .ok output ∧ Csv.decode output = Csv.decode input :=
  Proofs.Formats.Csv.Typed.encode_of_decode law h

end Silmaril.Formats.Csv.Typed
