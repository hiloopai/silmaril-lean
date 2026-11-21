module

public import Silmaril.Formats.Dasl.Arena.Prolly.Slots.Defs
public import Silmaril.Formats.Dasl.Arena.Prolly.Index.Thms
public import Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Mark.Thms
import Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Slots

public section

namespace Silmaril.Formats.Dasl.Arena.Prolly

open Silmaril.Semantics.Arena
open Silmaril.Semantics.Prolly (Block Policy)

variable {Ref Local Name Key Payload : Type}

theorem Reader.ofSlots_refines {read : Local → Mutable.Cell (Block Ref Key Payload)} {locate : Ref → Option Local}
    {fallback target : Reader Ref Key Payload}
    (resident : ∀ ref key block, locate ref = some key → read key = some (some block) → target ref = .ok block)
    (external : ∀ ref block, locate ref = none → fallback ref = .ok block → target ref = .ok block) :
    (Reader.ofSlots read locate fallback).Refines id target :=
  Proofs.Formats.Dasl.Arena.Prolly.Slots.refines resident external

theorem Reader.ofIndexedSlots_eq (read : Nat → Mutable.Cell (Block (Handle Name) Key Payload))
    (arena : Indexed Name Key Payload) (external : Reader Name Key Payload)
    (agrees : ∀ index, (read index).join = arena.blocks[index]?) :
    Reader.ofIndexedSlots read external = arena.read external :=
  Proofs.Formats.Dasl.Arena.Prolly.Slots.indexed_eq read arena external agrees

theorem Reader.ofCollectedSlots_eq (read : Nat → Mutable.Cell (Block (Handle Name) Key Payload))
    (view : Sweep.Collected Name Key Payload) (external : Reader Name Key Payload)
    (agrees : ∀ index, (read index).join = view.slots[index]?.join) :
    Reader.ofIndexedSlots read external = view.read external :=
  Proofs.Formats.Dasl.Arena.Prolly.Slots.collected_eq read view external agrees

/-- Read preservation on every declared reachable root of a marked snapshot.
The external reader is unchanged and no reclaimed local index is recycled. -/
theorem Reader.lookup_marked [LinearOrder Key] (policy : Policy Key)
    {arena : Indexed Name Key Payload} {roots : List (Handle Name)} {view : Sweep.Collected Name Key Payload}
    (swept : Sweep.markAndSweep? arena roots = some view)
    (read : Nat → Mutable.Cell (Block (Handle Name) Key Payload)) (external : Reader Name Key Payload)
    (agrees : ∀ index, (read index).join = view.slots[index]?.join) (fuel : Nat)
    {root : Handle Name} (reachable : Sweep.Reachable arena roots root) (key : Key) :
    (Reader.ofIndexedSlots read external).lookup policy fuel root key = (arena.read external).lookup policy fuel root key := by
  rw [ofCollectedSlots_eq read view external agrees]
  exact Sweep.route_marked swept external policy.width fuel key reachable

theorem Reader.reclaimed_unreadable
    {arena : Indexed Name Key Payload} {roots : List (Handle Name)} {view : Sweep.Collected Name Key Payload}
    (swept : Sweep.markAndSweep? arena roots = some view)
    (read : Nat → Mutable.Cell (Block (Handle Name) Key Payload)) (external : Reader Name Key Payload)
    (agrees : ∀ index, (read index).join = view.slots[index]?.join) (index : Nat) (inside : index < arena.blocks.size)
    (unreachable : ¬ Sweep.Reachable arena roots (.local index)) :
    Reader.ofIndexedSlots read external (.local index) = .error (.missing (.local index)) := by
  rw [ofCollectedSlots_eq read view external agrees]
  simp [Sweep.Collected.read, (Sweep.marked_slot swept index inside).2.mpr unreachable]

end Silmaril.Formats.Dasl.Arena.Prolly
