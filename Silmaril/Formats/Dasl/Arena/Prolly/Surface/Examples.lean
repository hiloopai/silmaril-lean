module

import Silmaril.Formats.Dasl.Arena.Prolly.Surface.Thms
public meta import Silmaril.Formats.Dasl.Arena.Prolly.Surface.Defs
public meta import Silmaril.Formats.Dasl.Prolly.Route.Defs

namespace Silmaril.Formats.Dasl.Arena.Prolly.Surface.Examples

open Silmaril.Semantics.Prolly (Policy)

private def graph : Indexed Nat Nat String := ⟨#[
  .leaf [(1, "shared")], .leaf [(2, "old")], .branch 1 [(1, .local 0), (3, .external 0)],
  .branch 1 [(1, .local 0)], .leaf [(5, "other root")]]⟩

private def policy : Policy Nat := ⟨3, by decide, fun _ _ => false⟩
private def localId (index : Nat) : Target Nat String Nat := .local ⟨24, "map", index⟩
private def missing : Reader Nat Nat String := fun name => .error (.missing name)

private def initial : Option (View Nat String graph) := do
  let view ← mount graph 24 "map"
  let left ← (view.register (localId 2)).toOption
  let right ← (left.register (localId 3)).toOption
  (right.register (localId 4)).toOption

private def compacted := initial.bind View.collect

#guard match compacted with
  | none => false
  | some view => decide (
      view.resolve (.local ⟨25, "map", 2⟩) = .error .wrongArena ∧
      view.resolve (.local ⟨24, "blob", 2⟩) = .error .wrongKind ∧
      view.resolve (localId 5) = .error .neverAllocated ∧
      view.resolve (localId 1) = .error .stale ∧
      view.lookup missing policy 2 (localId 2) 1 = .ok (some "shared") ∧
      view.lookup missing policy 2 (localId 3) 1 = .ok (some "shared") ∧
      view.lookup missing policy 2 (localId 4) 5 = .ok (some "other root") ∧
      view.lookup missing policy 2 (localId 4) 6 = .ok none ∧
      view.lookup missing policy 2 (localId 2) 3 = .error (.query (.missing (.external 0))) ∧
      view.lookup missing policy 0 (localId 2) 1 = .error (.query (.fuel (.local 2))))

#guard (do
  let view ← compacted
  let unregistered ← (view.unregister (localId 2)).toOption
  let collected ← unregistered.collect
  pure (decide (collected.resolve (localId 1) = .error .stale ∧
    collected.resolve (localId 2) = .error .stale ∧
    collected.lookup missing policy 2 (localId 3) 1 = .ok (some "shared")))) == some true

private def authority : List (Nat × ByteArray) := [(0, ⟨#[42]⟩)]

#guard (do
  let surface ← initial
  let viewed ← (⟨surface, authority⟩ : Layer Nat String (List (Nat × ByteArray)) graph).collect
  pure viewed.authority) == some authority

end Silmaril.Formats.Dasl.Arena.Prolly.Surface.Examples
