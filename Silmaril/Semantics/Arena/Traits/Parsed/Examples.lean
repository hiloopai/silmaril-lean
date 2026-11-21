module

import Silmaril.Semantics.Arena.Traits.Parsed.Thms

namespace Silmaril.Semantics.Arena.Traits.Parsed.Examples

private def bytes (value : UInt8) : ByteArray := ⟨#[value]⟩

private def profile : Cas.Profile Nat Nat := ⟨fun val => some (bytes val.toUInt8), fun _ => some 7⟩

private def api : Traits.CasArena (Cas.State Nat Nat Nat) Nat Nat Nat Empty := Traits.CasArena.model profile

private def initial : Cas.State Nat Nat Nat :=
  ⟨fun key => if key = 0 then some ⟨none, some 12⟩ else if key = 1 then some ⟨some 7, none⟩ else none, fun _ => none⟩

private def fetched (byte : UInt8) : Source Nat Empty := fun name =>
  if name = 7 then .present (bytes byte) else .absent

example : (attach api (fetched 12) 0 7 (bytes 12) initial).map
    (fun (_, next) => (api.toArena.read next 0, api.keyName next 0, api.get next 7)) =
      .ok (some (some 12), some 7, .ok (some (bytes 12))) := rfl

example : attach api (fetched 12) 1 7 (bytes 12) initial = .error (.inl .unresident) := rfl
example : attach api (fetched 12) 2 7 (bytes 12) initial = .error (.inl .vacant) := rfl
example : attach api (fetched 13) 0 7 (bytes 13) initial = .error (.inl .encodedBytesMismatch) := rfl
example : put api (fetched 13) 7 (bytes 12) initial = .error (.inl .sourceBytesMismatch) := rfl
example : put api (fun _ => .present (bytes 12)) 8 (bytes 12) initial = .error (.inl (.nameMismatch 7)) := rfl
example : put api (fetched 12) 8 (bytes 12) initial = .error (.inl .sourceAbsent) := rfl

private def collision : Cas.State Nat Nat Nat :=
  {initial with blocks := fun name => if name = 7 then some (bytes 13) else none}

example : Mutable.Mutation.commit (attach api (fetched 12) 0 7 (bytes 12)) collision =
    (.error (.inr (.semantic (.collision 7))), collision) := rfl

private def deferredApi : Traits.CasArena (Cas.State Nat Nat Nat) Nat Nat Nat Unit :=
  { toArena := ArenaApi.ofAccess Cas.State.plain
    profile := profile
    get := fun _ _ => .error ()
    keyName := fun state => state.slots.keyName
    attachedKeys := Cas.State.attachedKeys
    put := fun _ _ => .error (.backend ())
    attach := fun _ _ _ => .error (.backend ()) }

example : Mutable.Mutation.commit (put deferredApi (Parsed.CasArena.probe deferredApi initial) 7 (bytes 12)) initial =
    (.error (.inl (.sourceUnavailable ())), initial) := rfl

end Silmaril.Semantics.Arena.Traits.Parsed.Examples
