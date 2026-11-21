module

import Silmaril.Formats.Git.Filesystem.Slots.Thms
import Silmaril.Semantics.Arena.Traits.Tagged.Thms

namespace Silmaril.Formats.Git.Filesystem.Slots.Examples

open Silmaril.Formats.Git.Arena (CasLane Oid)
open Silmaril.Formats.Dasl.Prolly (ByteKey)
open Silmaril.Semantics.Arena.Traits.Tagged

private abbrev Key (_ : Kind) := Nat
private abbrev Name (_ : Kind) := Arena.Id Cid
private def Obj : Kind → Type
  | .tree => DirBlock
  | .blob => ByteArray
  | .commit => Commit Cid Oid String

private def cid (lane : CasLane) (seed : UInt8) : Cid :=
  address (fun _ => ⟨List.replicate 32 seed, by simp⟩) lane ⟨#[]⟩

private def parent := cid .object 1
private def child := cid .object 2
private def file := cid .raw 3
private def component : ByteKey := [97]
private def entry : Entry Cid := ⟨.file .regular, file⟩
private def commit : Obj .commit := ⟨parent, [], "imported tree"⟩

private def spaces (resident : Bool) : Spaces Key Name Obj
  | .tree => fun key => if key = 0 then some ⟨none, some (.branch 1 [(component, child)])⟩ else
      if key = 1 then some ⟨none, if resident then some (.leaf [(component, entry)]) else none⟩ else none
  | .blob => fun _ => none
  | .commit => fun key => if key = 0 then some ⟨none, some commit⟩ else none

private def locateKey (name : Cid) : Option Nat :=
  if name = parent then some 0 else if name = child then some 1 else none

private def look (resident : Bool) (fuel : Nat) (path : List ByteKey) : Except ReadFault (Option (Entry Cid)) := do
  let packed := equiv (spaces resident)
  let typed : Spaces Key Name Obj := equiv.symm packed
  let some (some value) := (arena Kind.commit).read typed 0 | .error .notDirectory
  locateSlots ((arena Kind.tree).read typed) locateKey (fun _ _ => .deferred) fuel value.tree path

example : look true 2 [component] = .ok (some entry) := by
  have decoded : equiv.symm (equiv (spaces true)) = spaces true := equiv.symm_apply_apply _
  simp only [look, decoded]
  rfl

example : look false 2 [component] = .error (.deferred child) := by
  have decoded : equiv.symm (equiv (spaces false)) = spaces false := equiv.symm_apply_apply _
  simp only [look, decoded]
  rfl

example : look true 1 [component] = .error (.block (.fuel child)) := by
  have decoded : equiv.symm (equiv (spaces true)) = spaces true := equiv.symm_apply_apply _
  simp only [look, decoded]
  rfl

example : look true 2 [[96]] = .ok none := by
  have decoded : equiv.symm (equiv (spaces true)) = spaces true := equiv.symm_apply_apply _
  simp only [look, decoded]
  rfl

end Silmaril.Formats.Git.Filesystem.Slots.Examples
