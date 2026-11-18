module

public import Silmaril.Formats.JsonWithBytes.Chunked.Tree.Defs
import Silmaril.Proofs.Formats.JsonWithBytes.Chunked.Tree

public section
namespace Silmaril.Formats.JsonWithBytes.Chunked.TreeValue

open Silmaril.ChunkSeq.Balanced
variable {Number : Type} [SizeOf Number]

theorem toSimple_ofSimple (value : Ordered Number) : (ofSimple value).toSimple = value :=
  Proofs.Formats.JsonWithBytes.Chunked.toSimple_ofSimple value

theorem packed_array_canonical (items : List (Canonical Number)) :
    let value := TreeValue.list (Chunks.ofList 31 (items.map Subtype.val))
    TreeValue.ofSimple value.toSimple = value :=
  Proofs.Formats.JsonWithBytes.Chunked.packed_array_canonical items

theorem packed_object_canonical (entries : List (String × Canonical Number)) :
    let value := TreeValue.map (Chunks.ofList 31 (entries.map (fun entry => (entry.1, entry.2.val))))
    TreeValue.ofSimple value.toSimple = value :=
  Proofs.Formats.JsonWithBytes.Chunked.packed_object_canonical entries

end Silmaril.Formats.JsonWithBytes.Chunked.TreeValue
