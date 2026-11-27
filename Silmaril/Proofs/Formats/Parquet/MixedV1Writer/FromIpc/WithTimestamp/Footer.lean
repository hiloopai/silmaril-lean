module

public import Silmaril.Formats.Parquet.MixedV1Writer.Defs
import Init.Data.List.Monadic

public section

namespace Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp

open Silmaril.Formats.Parquet
open FlatInt32Writer.Compact

/-- With uniform tags the exact pre-generalization group program is recovered. -/
theorem groupFor_legacy (physical : Int) (rows : Nat) (columns : List ColumnIndex) :
    groupFor physical rows columns = (do
      field 1 9
      listHeader 12 columns.length
      for column in columns do chunkFor physical rows column
      field 1 6
      integer .i64 (columns.map ColumnIndex.size).sum
      field 1 6
      integer .i64 rows
      octet 0) := by
  simp [groupFor, groupTyped, List.foldlM_map, Function.comp_def]

/-- The new bounded run agrees with the complete previous homogeneous footer program. -/
theorem typed_homogeneous_legacy (physical : Int) (limit : Nat) (leaves : List (Write Unit))
    (groups : List (Nat × List ColumnIndex)) :
    encodeGroupsTyped limit leaves (Internal.tagGroups physical groups) =
      ((do
        field 1 5
        integer .i32 1
        field 1 9
        listHeader 12 (leaves.length + 1)
        root leaves.length
        for writeLeaf in leaves do writeLeaf
        field 1 6
        integer .i64 (groups.map Prod.fst).sum
        field 1 9
        listHeader 12 groups.length
        for (rows, chunks) in groups do groupFor physical rows chunks
        octet 0 : Write Unit).run ⟨limit, .empty⟩).map (·.2.bytes) := by
  simp [encodeGroupsTyped, Internal.footerGroupsTyped, Internal.tagGroups, groupFor, List.foldlM_map, Function.comp_def]

@[expose] def pairLeaves (order : MixedV1Writer.Order) (ints octets : ColumnIndex) : List (Write Unit) :=
  order.columns (leaf ints) (MixedV1Writer.Compact.byteLeaf octets)

@[expose] def pairChunks (order : MixedV1Writer.Order) (group : MixedV1Writer.Compact.GroupIndex) :
    Nat × List TypedColumnIndex :=
  (group.rows, order.columns ⟨1, group.ints⟩ ⟨6, group.octets⟩)

@[simp] private theorem pairChunks_rows (order : MixedV1Writer.Order) (group : MixedV1Writer.Compact.GroupIndex) :
    (pairChunks order group).1 = group.rows := rfl

private theorem pair_group (order : MixedV1Writer.Order) (group : MixedV1Writer.Compact.GroupIndex) :
    groupTyped group.rows (pairChunks order group).2 =
      MixedV1Writer.Compact.writeGroupOrdered order group := by
  cases order <;>
    simp [groupTyped, pairChunks, MixedV1Writer.Compact.writeGroupOrdered,
      MixedV1Writer.Order.columns, MixedV1Writer.Order.arrange, Int.add_comm]

/-- Both previous primitive pair orders emit the same bounded footer bytes or error. -/
theorem typed_primitive_pair (order : MixedV1Writer.Order) (limit : Nat) (ints octets : ColumnIndex)
    (groups : List MixedV1Writer.Compact.GroupIndex) :
    encodeGroupsTyped limit (pairLeaves order ints octets) (groups.map (pairChunks order)) =
      MixedV1Writer.Compact.encodeGroupsOrdered order limit ints octets groups := by
  cases order <;>
    simp [encodeGroupsTyped, Internal.footerGroupsTyped, pairLeaves, List.foldlM_map,
      MixedV1Writer.Compact.encodeGroupsOrdered, MixedV1Writer.Compact.footerGroupsOrdered,
      MixedV1Writer.Order.columns, MixedV1Writer.Order.arrange, pair_group, Function.comp_def]

end Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp
