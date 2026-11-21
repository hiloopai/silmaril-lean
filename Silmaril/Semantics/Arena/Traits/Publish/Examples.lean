module

import Silmaril.Semantics.Arena.Traits.Publish.Thms

namespace Silmaril.Semantics.Arena.Traits.Publish.Examples

private def bytes (byte : UInt8) : ByteArray := ⟨#[byte]⟩

private def profile : Cas.Profile Nat Nat :=
  ⟨fun obj => if obj = 0 then none else some (bytes obj.toUInt8), fun _ => some 7⟩

private def api : CasArena (Cas.State Nat Nat Nat) Nat Nat Nat Empty := CasArena.model profile

private def empty : Cas.State Nat Nat Nat := ⟨State.empty, fun _ => none⟩

private def reserved : Cas.State Nat Nat Nat :=
  {empty with slots := empty.slots.replaceAt 0 (some ⟨some 7, none⟩)}

private def source (name : Nat) : Parsed.Observation Unit :=
  if name = 7 then .present (bytes 12) else .absent

example : Reserve.model (Error := Empty) 0 7 empty = .ok ((), reserved) := rfl
example : api.toArena.read empty 0 = none := rfl
example : api.toArena.read reserved 0 = some none := rfl
example : api.keyName reserved 0 = some 7 := rfl
example : ¬ 0 ∈ api.attachedKeys reserved 7 := by rintro ⟨_, impossible⟩; cases impossible
example : Parsed.CasArena.probe api reserved 7 = .absent := rfl

example : run api .fulfill 0 12 7 empty = .error (.semantic .noReservation) := rfl
example : run api .fulfill 0 12 8 reserved = .error (.semantic (.wrongClaim 7)) := rfl
example : (run api .fulfill 0 12 7 reserved).map
    (fun (_, next) => (api.toArena.read next 0, api.keyName next 0, api.get next 7)) =
    .ok (some (some 12), some 7, .ok (some (bytes 12))) := rfl
example : (run api .insert 1 12 7 reserved).map (fun (_, next) => api.get next 7) =
    .ok (.ok (some (bytes 12))) := rfl
example : (run api .fulfill 0 12 7 reserved >>= fun (_, next) => run api .fulfill 0 12 7 next) =
    .error (.semantic .notReserved) := rfl
example : (run api .insert 1 12 7 reserved >>= fun (_, next) => run api .fulfill 0 12 7 next).map
    (fun (_, next) => api.get next 7) = .ok (.ok (some (bytes 12))) := rfl

example : Mutable.Mutation.commit (run api .insert 0 12 7) reserved =
    (.error (.semantic (.slot .occupied)), reserved) := rfl
example : Mutable.Mutation.commit (run api .fulfill 0 0 7) reserved =
    (.error (.semantic (.attachment .unencodable)), reserved) := rfl
example : Mutable.Mutation.commit (run api .insert 1 12 8) reserved =
    (.error (.semantic (.attachment (.mismatch 7))), reserved) := rfl

private def conflicting : Cas.State Nat Nat Nat := {reserved with blocks := fun _ => some (bytes 13)}

example : Mutable.Mutation.commit (run api .fulfill 0 12 7) conflicting =
    (.error (.semantic (.attachment (.collision 7))), conflicting) := rfl

private def gatedApi : CasArena (Cas.State Nat Nat Nat) Nat Nat Nat Unit := {api with
  toArena := ArenaApi.ofAccess Cas.State.plain
  get := fun _ _ => .error ()
  put := fun _ _ => .error (.backend ())
  attach key name := Step.ofModel (profile.attach key name)}

example : Parsed.CasArena.probe gatedApi reserved 7 = .unavailable () := rfl
example : (checked gatedApi source .fulfill 0 12 7 (bytes 12) reserved).map
    (fun (_, next) => (next.slots 0, next.blocks 7)) =
    .ok (some ⟨some 7, some 12⟩, some (bytes 12)) := rfl
example : Mutable.Mutation.commit (checked gatedApi source .fulfill 0 13 7 (bytes 12)) reserved =
    (.error (.inl .encodedBytesMismatch), reserved) := rfl
example : Mutable.Mutation.commit (checked gatedApi (fun _ => .unavailable ()) .fulfill 0 12 7 (bytes 12))
    reserved = (.error (.inl (.sourceUnavailable ())), reserved) := rfl

private def otherApi : CasArena (Cas.State Nat Nat Nat) Nat Nat Nat Unit := {gatedApi with
  profile := {profile with select? := fun _ => some 9}}

example : Mutable.Mutation.commit (checked otherApi source .fulfill 0 12 7 (bytes 12)) reserved =
    (.error (.inl (.nameMismatch 9)), reserved) := rfl

private def allocationFailure : CasArena (Cas.State Nat Nat Nat) Nat Nat Nat Unit := {gatedApi with
  toArena := {gatedApi.toArena with change := fun _ _ _ => .error (.backend ())}}

example : Mutable.Mutation.commit (run allocationFailure .insert 1 12 7) reserved =
    (.error (.backend ()), reserved) := rfl

end Silmaril.Semantics.Arena.Traits.Publish.Examples
