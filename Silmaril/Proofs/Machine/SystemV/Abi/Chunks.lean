module

public import Silmaril.Machine.SystemV.Abi.Chunks.Defs

@[expose] public section
namespace Silmaril.Machine.SystemV.Abi.Chunks
open Silmaril.Machine.SystemV.Abi

private theorem forIn_advance (size : Nat) (registers : List Silmaril.X86.Reg)
    (items : List (Class × Nat)) (cursor : Cursor) :
    forIn items cursor (fun item state => ForInStep.yield <$> advance size registers state item) =
      walk size registers items cursor := by
  induction items generalizing cursor with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.forIn_cons, walk]
      cases actual : advance size registers cursor item with
      | error message => rfl
      | ok next => exact ih next

theorem chunks_eq_walk (object : Object) (registers : List Silmaril.X86.Reg) (gp fp : Nat) :
    chunks object registers gp fp = do
      let final ← walk object.size registers object.classes.zipIdx ([], gp, fp, 0)
      return final.1 := by
  unfold chunks
  rw [← forIn_advance]
  dsimp only
  apply congrArg (fun result : Except String Cursor => result.map Prod.fst)
  congr 1
  funext item cursor
  rcases cursor with ⟨result, gp, fp, offset⟩
  rcases item with ⟨cls, index⟩
  cases cls <;> simp only [advance]
  · rfl
  · cases registers[gp]? <;> rfl
  · rfl
  · split <;> rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem advance_gp {size : Nat} {cursor final : Cursor} {item : Class × Nat}
    (actual : advance size gpArguments cursor item = .ok final) :
    final.2.1 = cursor.2.1 + (if item.1 == .integer then 1 else 0) := by
  rcases cursor with ⟨result, gp, fp, offset⟩
  rcases item with ⟨cls, index⟩
  cases cls with
  | noClass => cases actual; rfl
  | integer =>
      cases selected : gpArguments[gp]? with
      | none => simp [advance, selected] at actual
      | some register =>
          simp only [advance, selected] at actual
          cases actual
          rfl
  | sse => cases actual; rfl
  | sseUp =>
      by_cases empty : fp = 0
      · simp [advance, empty] at actual
      · simp only [advance, beq_iff_eq, empty, ↓reduceIte] at actual
        cases actual
        rfl
  | x87 | x87Up | complexX87 | memory => simp [advance] at actual

private theorem advance_shift_integer {size index : Nat} {cursor final : Cursor}
    (baseGp baseFp : Nat) (capacity : baseGp + cursor.2.1 + 1 ≤ 6)
    (actual : advance size gpArguments cursor (.integer, index) = .ok final) :
    advance size gpArguments (shiftCursor baseGp baseFp cursor) (.integer, index) =
      .ok (shiftCursor baseGp baseFp final) := by
  rcases cursor with ⟨result, gp, fp, offset⟩
  change baseGp + gp + 1 ≤ 6 at capacity
  have bound : gp < gpArguments.length := by change gp < 6; omega
  have shiftedBound : baseGp + gp < gpArguments.length := by change baseGp + gp < 6; omega
  have selected : gpArguments[gp]? = some gpArguments[gp] := List.getElem?_eq_getElem bound
  have shifted : gpArguments[baseGp + gp]? = some gpArguments[baseGp + gp] :=
    List.getElem?_eq_getElem shiftedBound
  have rank : gpArguments.idxOf gpArguments[gp] = gp :=
    (by decide : gpArguments.Nodup).idxOf_getElem gp bound
  simp only [advance, selected] at actual
  cases actual
  simp [advance, shiftCursor, shifted, shiftChunk, rank, List.map_append, Nat.add_assoc]
  rfl

private theorem advance_shift_sseUp {size index : Nat} {cursor final : Cursor}
    (baseGp baseFp : Nat)
    (actual : advance size gpArguments cursor (.sseUp, index) = .ok final) :
    advance size gpArguments (shiftCursor baseGp baseFp cursor) (.sseUp, index) =
      .ok (shiftCursor baseGp baseFp final) := by
  rcases cursor with ⟨result, gp, fp, offset⟩
  by_cases empty : fp = 0
  · simp [advance, empty] at actual
  · have subtract : baseFp + fp - 1 = baseFp + (fp - 1) := by omega
    simp only [advance, beq_iff_eq, empty, ↓reduceIte] at actual
    cases actual
    simp [advance, shiftCursor, empty, shiftChunk, List.map_append, subtract]
    rfl

theorem advance_shift {size : Nat} {cursor final : Cursor} {item : Class × Nat}
    (baseGp baseFp : Nat)
    (capacity : baseGp + cursor.2.1 + (if item.1 == .integer then 1 else 0) ≤ 6)
    (actual : advance size gpArguments cursor item = .ok final) :
    advance size gpArguments (shiftCursor baseGp baseFp cursor) item =
      .ok (shiftCursor baseGp baseFp final) := by
  rcases item with ⟨cls, index⟩
  cases cls with
  | noClass => cases actual; rfl
  | integer => exact advance_shift_integer baseGp baseFp capacity actual
  | sse =>
      rcases cursor with ⟨result, gp, fp, offset⟩
      cases actual
      simp [advance, shiftCursor, shiftChunk, List.map_append, Nat.add_assoc]
      rfl
  | sseUp => exact advance_shift_sseUp baseGp baseFp actual
  | x87 | x87Up | complexX87 | memory => simp [advance] at actual

theorem demand_cons (item : Class × Nat) (rest : List (Class × Nat)) :
    demand (item :: rest) = (if item.1 == .integer then 1 else 0) + demand rest := by
  cases item
  rfl

theorem demand_eq_count (items : List (Class × Nat)) :
    demand items = (items.map Prod.fst).count .integer := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      rw [demand_cons, ih]
      simp only [List.map_cons, List.count_cons]
      exact Nat.add_comm _ _

/-- Successful relative execution rules out orphan SSEUP; the remaining
INTEGER demand supplies every actual shifted physical register lookup. -/
theorem walk_shift {size : Nat} {items : List (Class × Nat)} {cursor final : Cursor}
    (baseGp baseFp : Nat) (capacity : baseGp + cursor.2.1 + demand items ≤ 6)
    (actual : walk size gpArguments items cursor = .ok final) :
    walk size gpArguments items (shiftCursor baseGp baseFp cursor) =
      .ok (shiftCursor baseGp baseFp final) := by
  induction items generalizing cursor with
  | nil => cases actual; rfl
  | cons item rest ih =>
      cases first : advance size gpArguments cursor item with
      | error message => simp only [walk, first] at actual; cases actual
      | ok next =>
          have later : walk size gpArguments rest next = .ok final := by
            rw [walk, first] at actual
            exact actual
          have stepCapacity : baseGp + cursor.2.1 + (if item.1 == .integer then 1 else 0) ≤ 6 := by
            rw [demand_cons] at capacity
            omega
          have nextCapacity : baseGp + next.2.1 + demand rest ≤ 6 := by
            rw [advance_gp first]
            rw [demand_cons] at capacity
            omega
          have shifted := advance_shift baseGp baseFp stepCapacity first
          simp only [walk, shifted]
          exact ih nextCapacity later

/-- General equivariance of the actual production chunk loop. This covers
arbitrary class lists, holes and SSEUP chains whenever the relative execution
actually succeeds and the shifted GP bank has capacity. It does not assume the
shifted output, a value representation or a saved-memory correspondence. -/
theorem chunks_shift {object : Object} {relative : List Chunk} (gp fp : Nat)
    (capacity : gp + gpCount object ≤ 6)
    (actual : chunks object gpArguments 0 0 = .ok relative) :
    chunks object gpArguments gp fp = .ok (relative.map (shiftChunk gp fp)) := by
  rw [chunks_eq_walk] at actual
  cases source : walk object.size gpArguments object.classes.zipIdx ([], 0, 0, 0) with
  | error message => rw [source] at actual; cases actual
  | ok final =>
      rw [source] at actual
      have result : final.1 = relative := Except.ok.inj actual
      have bound : gp + (0 : Nat) + demand object.classes.zipIdx ≤ 6 := by
        simpa only [demand_eq_count, List.zipIdx_map_fst, gpCount, Nat.add_zero] using capacity
      have shifted := walk_shift gp fp bound source
      have shiftedSource : walk object.size gpArguments object.classes.zipIdx ([], gp, fp, 0) =
          .ok (shiftCursor gp fp final) := by simpa only [shiftCursor, List.map_nil, Nat.add_zero] using shifted
      rw [chunks_eq_walk, shiftedSource]
      change Except.ok ((shiftCursor gp fp final).1) = Except.ok (relative.map (shiftChunk gp fp))
      simp only [shiftCursor, result]

theorem shiftChunk_gp (gp fp index objectOffset count : Nat)
    (relative : index < gpArguments.length)
    (capacity : gp + index < gpArguments.length) :
    shiftChunk gp fp ⟨objectOffset, count, .gp gpArguments[index]⟩ =
      ⟨objectOffset, count, .gp gpArguments[gp + index]⟩ := by
  have rank := (by decide : gpArguments.Nodup).idxOf_getElem index relative
  simp only [shiftChunk, rank, List.getElem?_eq_getElem capacity, Option.getD_some]

theorem shiftChunk_vector (gp fp index byteOffset objectOffset count : Nat) :
    shiftChunk gp fp ⟨objectOffset, count, .vector index byteOffset⟩ =
      ⟨objectOffset, count, .vector (fp + index) byteOffset⟩ := rfl

end Silmaril.Machine.SystemV.Abi.Chunks
