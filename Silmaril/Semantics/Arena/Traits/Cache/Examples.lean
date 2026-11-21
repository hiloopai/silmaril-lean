module

import Silmaril.Semantics.Arena.Traits.Cache.Thms

namespace Silmaril.Semantics.Arena.Traits.Cache.Examples

private def wire : ByteArray := ⟨#[12]⟩
private def other : ByteArray := ⟨#[13]⟩
private def profile : Cas.Profile Nat Nat := ⟨fun _ => none, fun _ => some 7⟩
private def authority : Cas.State Nat Nat Nat := ⟨State.empty, fun name => if name = 7 then some wire else none⟩
private def api := CasArena.model (Key := Nat) profile
private theorem refined : api.Refines id := CasArena.model_refines profile
private def cached : CasArena (Layer (Rep := Cas.State Nat Nat Nat) Cas.State.blocks) Nat Nat Nat Empty :=
  withCache refined
private def cold := Layer.cold (bytes := Cas.State.blocks) authority
private def hot := cold.remember 7 wire rfl

example : cold.probe 7 = .unavailable () ∧ cold.get api.get 7 = .ok (some wire) := ⟨rfl, rfl⟩
example : cold.probe 8 = .unavailable () ∧ cold.get api.get 8 = .ok none := ⟨rfl, rfl⟩
example : (hot.evict 7).probe 7 = .unavailable () ∧ (hot.evict 7).get api.get 7 = .ok (some wire) := ⟨rfl, rfl⟩

example : (Layer.warm api.get refined.get_eq 7 cold).map (fun (found, next) => (found, next.probe 7)) =
    .ok (some wire, .present wire) := rfl

example : (Layer.warm api.get refined.get_eq 8 cold).map (fun (found, next) => (found, next.probe 8)) =
    .ok (none, .unavailable ()) := rfl

example : Mutable.Mutation.commit (cached.put other) hot =
    (.error (.semantic (.collision 7)), hot) := rfl

example : (cached.toArena.insert 1 99 hot).map (fun (_, next) =>
    (cached.toArena.read next 1, next.probe 7)) = .ok (some (some 99), .present wire) := rfl

private def unavailable (_ : Cas.State Nat Nat Nat) (_ : Nat) : Except Unit (Option ByteArray) := .error ()

example : hot.get unavailable 7 = .ok (some wire) ∧ (hot.evict 7).get unavailable 7 = .error () := ⟨rfl, rfl⟩

end Silmaril.Semantics.Arena.Traits.Cache.Examples
