module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Defs
import Silmaril.Formats.Parquet.Plain.ByteArray.File.Thms
import Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Wire

/-! Same-snapshot binding, original dictionary entries and ordered data-page slots. -/

public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback

theorem openFile_wire {limits : Limits} {input : Bytes} {name : String} {checked : Checked name}
    (opened : openFile limits input name = .ok checked) :
    Snapshot.check (Failure := Unit) limits.file.snapshot input = .ok checked.snapshot ∧
    input.length ≤ limits.file.maxFileBytes ∧ checked.snapshot.metadata.numRows.toNat ≤ limits.file.maxFileRows ∧
    checked.snapshot.metadata.schema[checked.binding.leafOrdinal]? = some checked.binding.leaf ∧
    checked.binding.leaf.name = name ∧ checked.binding.leaf.physicalType = some .byteArray ∧
    checked.binding.leaf.repetition = some FlatColumn.Layout.optional.repetition :=
  Plain.ByteArray.File.openFile_wire opened

/-- Exact PLAIN entry bytes and typed entries in the original dictionary order. -/
theorem readDictionary_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {frame : Page.Frame} {entries : Array Bytes}
    (h : readDictionary limits metadata source frame = .ok entries) : DictionaryWire limits source frame entries :=
  Proofs.Formats.Parquet.ByteArrayFallback.readDictionary_wire (profile := .rleDictionary) h

/-- The original frame selects the PLAIN or dictionary interpretation and
retains the exact definition mask, value order and declared count. -/
theorem decodeData_wire {limits : Limits} {metadata : Footer.ColumnMetadata} {source : Bytes}
    {dictionary : Option (Array Bytes)} {frame : Page.Frame} {slots : List (Option Bytes)}
    (h : decodeData limits metadata source dictionary frame = .ok slots) : PageWire limits source dictionary frame slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.decodeData_wire (profile := .rleDictionary) h

/-- A successful selected read uses its own snapshot, chunk and leading
dictionary. The result concatenates one slot list per data frame in wire order. -/
theorem readGroup_wire {name : String} {checked : Checked name} {limits : Limits}
    {index : Nat} {slots : List (Option Bytes)} (h : readGroup checked limits index = .ok slots) :
    GroupWire checked limits index slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.readGroup_wire (profile := .rleDictionary) h

/-- The original V1 header keeps its value encoding and row count. The
RLE definition tag is preserved and only the absent repetition tag changes. -/
theorem legacy_parameters_wire {header : Page.Header} {params : ScalarPage.Parameters}
    (admitted : Profile.plainDictionaryV1.parameters header = some params) :
    ∃ raw, FlatColumn.pageParameters .optional 0 header = some raw ∧
      raw.version = .v1 3 4 ∧ params = { raw with version := .v1 3 3 } :=
  Proofs.Formats.Parquet.ByteArrayFallback.legacy_parameters_wire admitted

/-- The legacy reader retains the same-snapshot wire relation for a leading
tag-2 dictionary and original V1 tag-2 or PLAIN data pages. -/
theorem readLegacyGroup_wire {name : String} {checked : Checked name} {limits : Limits}
    {index : Nat} {slots : List (Option Bytes)}
    (h : readLegacyGroup checked limits index = .ok slots) :
    GroupWireFor .plainDictionaryV1 checked limits index slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.readGroup_wire (profile := .plainDictionaryV1) h

/-- The chunk-local callbacks run in original frame order after the offsets and
advertised row count are checked. -/
theorem readFramesWith_wire {δ α ε : Type}
    {openDictionary : Page.Frame → Except (FlatColumn.PageError ε) δ}
    {decodePage : Option δ → Page.Frame → Except (FlatColumn.PageError ε) (List (Option α))}
    {metadata : Footer.ColumnMetadata} {group column rows : Nat} {name : String} {frames : List Page.Frame}
    {slots : List (Option α)}
    (h : readFramesWith openDictionary decodePage metadata group column name rows frames = .ok slots) :
    ∃ (dictionary : Option Page.Frame) (data : List Page.Frame) (entries : Option δ) (pages : List (List (Option α))),
      frames = dictionary.toList ++ data ∧
      dictionary.map (fun frame : Page.Frame => (frame.header.start : Int)) = metadata.dictionaryPageOffset ∧
      data.head?.map (fun frame : Page.Frame => (frame.header.start : Int)) = some metadata.dataPageOffset ∧
      (data.map declaredSlots).sum = rows ∧ dictionary.mapM openDictionary = .ok entries ∧
      List.Forall₂ (fun frame page => decodePage entries frame = .ok page) data pages ∧ slots = pages.flatten :=
  Proofs.Formats.Parquet.ByteArrayFallback.readFramesWith_wire h

/-- The explicit codec walk preserves the selected original frames and the
stored chunk cap before running the client decoder. -/
theorem readBoundGroupWithCodec_wire {profile : Profile} {codec : Payload.Codec} {expandedChunkCap : Nat} {snapshot : Snapshot.Checked} {name : String} {α ε : Type}
    {binding : FlatColumn.Binding snapshot ⟨name, .byteArray, .optional⟩} {limits : Limits}
    {read : Footer.ColumnMetadata → Bytes → Nat → Nat → String → Nat → List Page.Frame →
      Except (FlatColumn.Error ε) (List (Option α))}
    {index : Nat} {slots : List (Option α)} (h : readBoundGroupWithCodec codec expandedChunkCap profile binding limits read index = .ok slots) :
    ∃ group, BoundGroupWireWithCodec codec binding limits (fun metadata source rows frames output =>
      metadata.totalCompressedSize ≤ (limits.file.column.maxChunkBytes : Int) ∧
      read metadata source index binding.columnOrdinal name rows frames = .ok output) index group slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.readBoundGroupWithCodec_wire h

/-- The callback consumes the original selected frames from the bound snapshot. -/
theorem readBoundGroupWith_wire {profile : Profile} {snapshot : Snapshot.Checked} {name : String} {α ε : Type}
    {binding : FlatColumn.Binding snapshot ⟨name, .byteArray, .optional⟩} {limits : Limits}
    {read : Footer.ColumnMetadata → Bytes → Nat → Nat → String → Nat → List Page.Frame →
      Except (FlatColumn.Error ε) (List (Option α))}
    {index : Nat} {slots : List (Option α)} (h : readBoundGroupWith profile binding limits read index = .ok slots) :
    ∃ group, BoundGroupWireWith binding limits (fun metadata source rows frames output =>
      read metadata source index binding.columnOrdinal name rows frames = .ok output) index group slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.readBoundGroupWith_wire h

/-- The legacy walk can reuse a BYTE_ARRAY binding from a paired checked
snapshot, preserving its original leaf, chunk, frames and slot count. -/
theorem readBoundLegacyGroup_wire {snapshot : Snapshot.Checked} {name : String}
    {binding : FlatColumn.Binding snapshot ⟨name, .byteArray, .optional⟩}
    {limits : Limits} {index : Nat} {slots : List (Option Bytes)}
    (read : readBoundGroupFor .plainDictionaryV1 binding limits index = .ok slots) :
    ∃ group, BoundGroupWireFor .plainDictionaryV1 binding limits index group slots :=
  Proofs.Formats.Parquet.ByteArrayFallback.readBoundGroup_wire read

end Silmaril.Formats.Parquet.ByteArrayFallback
