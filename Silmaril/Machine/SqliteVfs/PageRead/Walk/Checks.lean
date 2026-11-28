module

import Silmaril.Machine.SqliteVfs.PageRead.Walk.Thms
import Silmaril.Machine.SqliteVfs.PageRead.Thms

namespace Silmaril.Machine.SqliteVfs.PageRead.Walk

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

private def handle : Handle := ⟨0⟩
private def root : Page := ⟨handle, 1, 2⟩
private def branch : Page := ⟨handle, 2, 2⟩
private def leaf : Page := ⟨handle, 3, 2⟩
private def snapshot : FileState := ⟨[2, 11, 3, 12, 0, 13], some .readOnly, 0⟩
private def cache : Cache := fun slot =>
  if slot = 0 then some .vacant
  else if slot = 9 then some (.resident root [99, 99]) else none

private def followPointer (_ : Page) (bytes : Bytes) : Option Page := do
  let byte ← bytes[0]?
  if byte = 0 then none else some ⟨handle, byte.toNat, 2⟩

private theorem route : ReadPlan snapshot root [followPointer, followPointer] [branch, leaf] :=
  .cons rfl (by unfold FullRead; decide) (.cons rfl (by unfold FullRead; decide) (.nil leaf))

example :
    let initial : Position FileState := ⟨root, fill (readOnly 6) snapshot cache 0 root⟩
    let last := walk (readOnly 6) 0 initial [followPointer, followPointer]
    last.page = leaf ∧ last.observed.cache 0 = some (.resident leaf [0, 13]) ∧
      last.observed.cache 9 = cache 9 ∧ last.observed.file = snapshot ∧
      last.observed.trace =
        [⟨root.request, .ok [2, 11]⟩, ⟨branch.request, .ok [3, 12]⟩, ⟨leaf.request, .ok [0, 13]⟩] := by
  dsimp only
  rw [walk_readOnly 6 snapshot cache 0 root _ _ rfl (by unfold FullRead; decide) route]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private def changing : Handler Nat
  | state, .read _ offset _ => (if offset = 0 then .ok [2, 11] else .ok [255], state + 1)
  | state, .openFile _ => (.error .cannotOpen, state)
  | state, .close _ => (.error .invalidHandle, state)
  | state, .write _ _ _ => (.error .invalidHandle, state)
  | state, .truncate _ _ => (.error .invalidHandle, state)
  | state, .fileSize _ => (.error .invalidHandle, state)

example :
    let initial : Position Nat := ⟨root, fill changing 0 cache 0 root⟩
    let last := walk changing 0 initial [followPointer, followPointer]
    last.page = branch ∧ last.observed.result = .error .wrongLength ∧
      last.observed.file = 2 ∧ last.observed.cache 0 = some .vacant ∧
      last.observed.cache 9 = cache 9 ∧
      last.observed.trace = [⟨root.request, .ok [2, 11]⟩, ⟨branch.request, .ok [255]⟩] ∧
      Trace.Valid changing 0 last.observed.trace last.observed.file := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact walk_trace changing 0 0 ⟨root, fill changing 0 cache 0 root⟩
    [followPointer, followPointer] (fill_trace changing 0 cache 0 root)

#print axioms walk_unselected
#print axioms advance_trace
#print axioms walk_trace
#print axioms walk_readOnly
#print axioms walk_readOnly_trace

end Silmaril.Machine.SqliteVfs.PageRead.Walk
