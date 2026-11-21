module

import Silmaril.Semantics.Arena.Traits.Thms

namespace Silmaril.Semantics.Arena.Traits.Examples

private def bytes (value : Nat) : ByteArray := ⟨#[value.toUInt8]⟩

private def profile : Cas.Profile Nat Nat where
  encode? value := some (bytes value)
  select? _ := some 7

private def api : CasArena (Cas.State Nat Nat Nat) Nat Nat Nat Empty := CasArena.model profile

private def empty : Cas.State Nat Nat Nat := ⟨fun _ => none, fun _ => none⟩

private def resident : Cas.State Nat Nat Nat where
  slots key := if key < 2 then some ⟨some 7, some 12⟩ else if key = 2 then some ⟨some 7, none⟩ else none
  blocks name := if name = 7 then some (bytes 12) else none

example : api.toArena.read resident 2 = some none ∧ api.toArena.read resident 3 = none := ⟨rfl, rfl⟩

example : 0 ∈ api.attachedKeys resident 7 ∧ 1 ∈ api.attachedKeys resident 7 := ⟨⟨12, rfl⟩, ⟨12, rfl⟩⟩

example : 2 ∈ api.claimKeys resident 7 ∧ 2 ∉ api.attachedKeys resident 7 := by
  refine ⟨rfl, ?_⟩
  rintro ⟨obj, observed⟩
  cases (show some (⟨some 7, none⟩ : Slot Nat Nat) = some ⟨some 7, some obj⟩ from observed)

example : ((ArenaApi.insert api.toArena 2 12).commit resident).1 = .error (.semantic .occupied) := rfl

example : (api.attach 2 7 resident) = .error (.semantic .unresident) := rfl

example : (api.get empty 7) = .ok none := rfl

example : ((api.put (bytes 12) empty).map fun (name, state) => (name, api.get state name)) =
    .ok (7, .ok (some (bytes 12))) := rfl

example : (api.put (bytes 12)).commit resident = (.ok 7, resident) := rfl

example : (api.put (bytes 13)).commit resident = (.error (.semantic (.collision 7)), resident) := rfl

example : (api.replaceAndAttach 0 13 7).commit resident =
    (.error (.semantic (.inr (.collision 7))), resident) := rfl

example : ((ArenaApi.replace api.toArena 0 13 resident).map fun (_, state) =>
    (api.keyName state 0, api.keyName state 1, api.get state 7)) = .ok (none, some 7, .ok (some (bytes 12))) := rfl

end Silmaril.Semantics.Arena.Traits.Examples
