module

public import Silmaril.Formats.Dasl.Arena.Prolly.Slots.Defs
public import Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Mark.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Slots

open Silmaril.Formats.Dasl.Arena.Prolly
open Silmaril.Semantics.Arena
open Silmaril.Semantics.Prolly (Block)

variable {Ref Local Key Payload Name : Type}

theorem refines {read : Local → Mutable.Cell (Block Ref Key Payload)} {locate : Ref → Option Local}
    {fallback target : Reader Ref Key Payload}
    (resident : ∀ ref key block, locate ref = some key → read key = some (some block) → target ref = .ok block)
    (external : ∀ ref block, locate ref = none → fallback ref = .ok block → target ref = .ok block) :
    (Reader.ofSlots read locate fallback).Refines id target := by
  intro ref block found
  have same : relabel id block = block := by
    cases block <;> simp [relabel]
  rw [same]
  cases atRef : locate ref with
  | none => exact external ref block atRef (by simpa [Reader.ofSlots, atRef] using found)
  | some key =>
    apply resident ref key block atRef
    cases atKey : read key with
    | none => simp [Reader.ofSlots, atRef, atKey] at found
    | some slot => cases slot <;> simp_all [Reader.ofSlots]

theorem indexed_eq (read : Nat → Mutable.Cell (Block (Handle Name) Key Payload)) (arena : Indexed Name Key Payload)
    (external : Reader Name Key Payload) (agrees : ∀ index, (read index).join = arena.blocks[index]?) :
    Reader.ofIndexedSlots read external = arena.read external := by
  funext ref
  cases ref with
  | «local» index =>
    cases found : read index with
    | none => simp [Reader.ofIndexedSlots, Reader.ofSlots, Indexed.read, ← agrees, found]
    | some slot => cases slot <;> simp [Reader.ofIndexedSlots, Reader.ofSlots, Indexed.read, ← agrees, found]
  | external name =>
    simp [Reader.ofIndexedSlots, Reader.ofSlots, Indexed.read]

theorem collected_eq (read : Nat → Mutable.Cell (Block (Handle Name) Key Payload)) (view : Sweep.Collected Name Key Payload)
    (external : Reader Name Key Payload) (agrees : ∀ index, (read index).join = view.slots[index]?.join) :
    Reader.ofIndexedSlots read external = view.read external := by
  funext ref
  cases ref with
  | «local» index =>
    cases found : read index with
    | none => simp [Reader.ofIndexedSlots, Reader.ofSlots, Sweep.Collected.read, ← agrees, found]
    | some slot => cases slot <;> simp [Reader.ofIndexedSlots, Reader.ofSlots, Sweep.Collected.read, ← agrees, found]
  | external name => rfl

end Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Slots
