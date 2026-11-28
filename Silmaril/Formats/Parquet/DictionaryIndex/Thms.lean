module

public import Silmaril.Formats.Parquet.DictionaryIndex.Defs
import Silmaril.Proofs.Formats.Parquet.DictionaryIndex.Correctness

/-! Exact index-stream consumption, checked selection, and ordered page slots. -/

public section

namespace Silmaril.Formats.Parquet.DictionaryIndex

/-- The first octet is the bit width. The entire suffix is a checked Hybrid stream. -/
theorem readIndices_ok_iff {limits : Hybrid.Limits} {expected : Nat} {source : Bytes}
    {indices : List Nat} :
    readIndices limits expected source = .ok indices ↔
      source.length ≤ limits.bytes ∧
      ∃ width : UInt8, ∃ runs : List UInt8,
        source.toList = width :: runs ∧ width.toNat ≤ 32 ∧
        expected < Hybrid.runLimit ∧ expected ≤ limits.values ∧
        Hybrid.Wire width.toNat expected runs indices :=
  Proofs.Formats.Parquet.DictionaryIndex.readIndices_ok_iff

/-- Each ordered index has a corresponding successful lookup in the typed dictionary. -/
theorem select_ok_iff {α : Type} {dictionary : Array α} {indices : List Nat}
    {values : List α} :
    select dictionary indices = .ok values ↔
      indices.map (fun index => dictionary[index]?) = values.map some :=
  Proofs.Formats.Parquet.DictionaryIndex.select_ok_iff

theorem select_indices_lt {α : Type} {dictionary : Array α} {indices : List Nat}
    {values : List α} (selected : select dictionary indices = .ok values)
    {index : Nat} (member : index ∈ indices) : index < dictionary.size :=
  Proofs.Formats.Parquet.DictionaryIndex.select_indices_lt selected member

theorem readValues_wire {α : Type} {limits : Hybrid.Limits} {dictionary : Array α}
    {count : Nat} {source : Bytes} {values : List α}
    (accepted : readValues limits dictionary count source = .ok values) :
    ValuesWire limits dictionary count source values :=
  Proofs.Formats.Parquet.DictionaryIndex.readValues_wire accepted

/-- Successful decoding projects back to the checked mask and the values in index order. -/
theorem decode_ok_iff {α : Type} {dictionary : Array α} {params : ScalarPage.Parameters}
    {pageLimits : ScalarPage.Limits} {indexLimits : Hybrid.Limits} {source : Bytes}
    {output : List (Option α)} :
    decode dictionary params pageLimits indexLimits source = .ok output ↔
      (params.encoding = 8 ∨ params.encoding = 2) ∧
      ∃ page indices,
        ScalarPage.prepareFor params.encoding params pageLimits source = .ok page ∧
        readIndices indexLimits (page.mask.count true) page.scalars = .ok indices ∧
        output.map Option.isSome = page.mask ∧
        indices.map (fun index => dictionary[index]?) = (output.filterMap id).map some :=
  Proofs.Formats.Parquet.DictionaryIndex.decode_ok_iff

theorem decode_counts {α : Type} {dictionary : Array α} {params : ScalarPage.Parameters}
    {pageLimits : ScalarPage.Limits} {indexLimits : Hybrid.Limits} {source : Bytes}
    {output : List (Option α)} (h : decode dictionary params pageLimits indexLimits source = .ok output) :
    output.length = params.numValues ∧
      match params.version with
      | .v1 _ _ => True
      | .v2 nulls _ _ _ _ => (output.filterMap id).length = params.numValues - nulls :=
  Proofs.Formats.Parquet.DictionaryIndex.decode_counts h

end Silmaril.Formats.Parquet.DictionaryIndex
