module

public import Silmaril.Formats.JsonWithBytes.Chunked.Defs
import Silmaril.Proofs.Formats.JsonWithBytes.Chunked.Tree
import Silmaril.Prelude.ChunkSeq.Balanced.Thms

public section
namespace Silmaril.Proofs.Formats.JsonWithBytes.Chunked.Lowering

open Silmaril.Formats Silmaril.Formats.JsonWithBytes Silmaril.Formats.JsonWithBytes.Chunked
open Silmaril.ChunkSeq.Balanced Canonical
variable {Number : Type} [SizeOf Number]

private theorem toSimple_scalar (value : Scalar Number) : (scalar value).toSimple = .scalar value :=
  equiv.right_inv _

theorem index_ofSimple (items : RawSyn String (Scalar Number) .arr) (index : Nat) :
    (ofSimple (.list items)).val.index? index = items.toList[index]?.map TreeValue.ofSimple := by
  change (TreeValue.ofSimple (.list items)).index? index = _
  rw [ofSimple_list, TreeValue.index?, Chunks.get?_eq]
  · rw [Chunks.toList_ofList, List.getElem?_map]
  · simp [Chunks.Canonical, Chunks.toList_ofList]

theorem entry_ofSimple (entries : RawSyn String (Scalar Number) .obj) (index : Nat) :
    (ofSimple (.map entries)).val.entry? index =
      entries.toEntries[index]?.map (fun entry => (entry.1, TreeValue.ofSimple entry.2)) := by
  change (TreeValue.ofSimple (.map entries)).entry? index = _
  rw [ofSimple_map, TreeValue.entry?, Chunks.get?_eq]
  · rw [Chunks.toList_ofList, List.getElem?_map]
  · simp [Chunks.Canonical, Chunks.toList_ofList]

theorem toSimple_ofArray (items : List (Canonical Number)) :
    (ofArray items).toSimple = .list (RawSyn.ofList (items.map toSimple)) := by
  change (TreeValue.list (Chunks.ofList 31 (items.map Subtype.val))).toSimple = _
  rw [toSimple_list, Chunks.toList_ofList, List.map_map]; rfl

theorem toSimple_ofObject (entries : List (String × Canonical Number)) :
    (ofObject entries).toSimple = .map (RawSyn.ofEntries (entries.map (fun entry => (entry.1, entry.2.toSimple)))) := by
  change (TreeValue.map (Chunks.ofList 31 (entries.map (fun entry => (entry.1, entry.2.val))))).toSimple = _
  rw [toSimple_map, Chunks.toList_ofList, List.map_map]; rfl

private theorem project_mapM {Input Raw Simple : Type} (items : List Input)
    (run : Input → Option Raw) (project : Raw → Simple) :
    (items.mapM run).map (List.map project) = items.mapM (fun item => (run item).map project) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rw [List.mapM_cons, List.mapM_cons, ← ih]
    cases run item <;> cases rest.mapM run <;> rfl

/-- Direct packing and ordered spec projection agree at every depth, including failure. -/
theorem toSimple_fromFast (depth : Nat) (value : Json.Fast.Value) :
    (fromFast? depth value).map toSimple = orderedView? depth value := by
  induction depth generalizing value with
  | zero => cases value <;> simp [fromFast?, orderedView?, toSimple_scalar]
  | succ depth ih =>
    cases value with
    | null | bool | string | number => simp [fromFast?, orderedView?, toSimple_scalar]
    | array items =>
      change ((items.toList.mapM (fromFast? depth)).map ofArray).map toSimple = _
      rw [Option.map_map]
      simp only [Function.comp_def, toSimple_ofArray]
      let finish (outputs : List Ordered) : Ordered := .list (RawSyn.ofList outputs)
      change (items.toList.mapM (fromFast? depth)).map (finish ∘ List.map toSimple) = _
      rw [← Option.map_map, project_mapM]
      simp only [ih, orderedView?]
      rfl
    | object entries cache =>
      let run (entry : String × Json.Fast.Value) : Option (String × Canonical JsonWire.Decimal) := do
        return (entry.1, ← fromFast? depth entry.2)
      let project (entry : String × Canonical JsonWire.Decimal) : String × Ordered :=
        (entry.1, entry.2.toSimple)
      change ((entries.toList.mapM run).map ofObject).map toSimple = _
      rw [Option.map_map]
      simp only [Function.comp_def, toSimple_ofObject]
      let finish (outputs : List (String × Ordered)) : Ordered := .map (RawSyn.ofEntries outputs)
      change (entries.toList.mapM run).map (finish ∘ List.map project) = _
      rw [← Option.map_map, project_mapM]
      have step (entry : String × Json.Fast.Value) : (run entry).map project =
          (do return (entry.1, ← orderedView? depth entry.2)) := by
        rw [← ih]
        dsimp only [run]
        cases fromFast? depth entry.2 <;> rfl
      simp only [step, orderedView?]
      rfl

end Silmaril.Proofs.Formats.JsonWithBytes.Chunked.Lowering
