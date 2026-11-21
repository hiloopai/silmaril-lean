module

import Silmaril.Formats.Git.Filesystem.Defs
import Silmaril.Semantics.Arena.Traits.Tagged.Thms

namespace Silmaril.Formats.Git.Arena.TaggedExamples

open Silmaril.Semantics.Arena
open Silmaril.Semantics.Arena.Traits.Tagged
open Silmaril.Formats.Dasl.Prolly (ByteKey)

private abbrev Key (_ : Kind) := Nat
private abbrev Name (_ : Kind) := Id Filesystem.Cid

/-- The fixture mixes the existing raw file bytes, parsed Prolly directory
block and Git commit carrier; shared numeric keys do not share identities. -/
private def Payload : Kind → Type
  | .blob => ByteArray
  | .tree => Filesystem.DirBlock
  | .commit => Commit (Key .tree) (Key .commit) Native.CommitMetadata

private def component : ByteKey := [97]
private def contents : ByteArray := ⟨#[12, 50]⟩
private def blobName := Filesystem.address (fun _ => ⟨List.replicate 32 0, by decide⟩) .raw contents
private def entry : Entry Filesystem.Cid := ⟨.file .regular, blobName⟩
private def directory : Payload .tree := .leaf [(component, entry)]
private def person : Native.Person := ⟨"Alice", "a@example.org", 1⟩
private def commit : Payload .commit := ⟨0, [1, 2], ⟨person, person, "initial\n"⟩⟩

private def spaces : Spaces Key Name Payload
  | .blob => fun key => if key = 0 then some ⟨none, some contents⟩ else none
  | .tree => fun key => if key = 0 then some ⟨none, some directory⟩ else none
  | .commit => fun key => if key = 0 then some ⟨none, some commit⟩ else if key = 1 then some ⟨none, none⟩ else none

example : read (pack spaces) .commit 0 = .ok (some (some commit)) ∧
    read (pack spaces) .commit 1 = .ok (some none) ∧ read (pack spaces) .commit 2 = .ok none := ⟨rfl, rfl, rfl⟩

example : (change .blob 0 .remove (pack spaces)).map
    (fun (_, next) => (read next .blob 0, read next .tree 0, read next .commit 0)) =
      .ok (.ok none, .ok (some (some directory)), .ok (some (some commit))) := rfl

private def malformed : Table Key Name Payload := fun _ => some ⟨.blob, ⟨none, some contents⟩⟩

example : read malformed .tree 0 = .error (.wrongKind .blob) := rfl
example : Mutable.Mutation.commit (change .tree 0 .reserve) malformed =
    (.error (.inl (.wrongKind .blob)), malformed) := rfl

end Silmaril.Formats.Git.Arena.TaggedExamples
