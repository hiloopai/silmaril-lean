module

public import Silmaril.Semantics.Arena.Traits.Tagged.Defs
public import Silmaril.Semantics.Arena.Traits.Thms
import Silmaril.Semantics.Arena.Mutable.Thms

public section

namespace Silmaril.Proofs.Semantics.Arena.Traits.Tagged

open Silmaril.Semantics.Arena
open Silmaril.Semantics.Arena.Traits
open Silmaril.Semantics.Arena.Traits.Tagged

variable {Kind : Type} {Key Name Obj : Kind → Type}

theorem pack_coherent (spaces : Spaces Key Name Obj) : Coherent (pack spaces) := by
  rintro ⟨kind, key⟩ cell atKey
  cases found : spaces kind key with
  | none => simp [pack, found] at atKey
  | some slot => simpa [pack, found] using congrArg (Option.map Sigma.fst) atKey.symm

variable [DecidableEq Kind]

theorem readSlot_pack (spaces : Spaces Key Name Obj) (kind : Kind) (key : Key kind) :
    readSlot (pack spaces) kind key = .ok (spaces kind key) := by
  cases found : spaces kind key <;> simp [readSlot, pack, found]

theorem decode_pack (spaces : Spaces Key Name Obj) : decode ⟨pack spaces, pack_coherent spaces⟩ = spaces := by
  funext kind key
  simp [decode, readSlot_pack]

theorem pack_decode (table : {table : Table Key Name Obj // Coherent table}) : pack (decode table) = table.val := by
  funext handle
  obtain ⟨kind, key⟩ := handle
  cases found : table.val ⟨kind, key⟩ with
  | none => simp [pack, decode, readSlot, found]
  | some cell =>
    obtain ⟨actual, slot⟩ := cell
    have eq : actual = kind := table.property _ _ found
    subst actual
    simp [pack, decode, readSlot, found]

variable [∀ kind, DecidableEq (Key kind)]

theorem pack_update (spaces : Spaces Key Name Obj) (kind : Kind) (key : Key kind)
    (slot : Option (Slot (Name kind) (Obj kind))) :
    pack (update spaces kind key slot) = overwrite (pack spaces) kind key slot := by
  funext handle
  obtain ⟨otherKind, other⟩ := handle
  by_cases eq : kind = otherKind
  · subst otherKind
    by_cases same : key = other <;> simp [pack, update, overwrite, State.replaceAt, same]
  · have distinct : (⟨kind, key⟩ : Handle Key) ≠ ⟨otherKind, other⟩ := fun same => eq (congrArg Sigma.fst same)
    simp [pack, update, overwrite, eq, distinct]

theorem change_pack (spaces : Spaces Key Name Obj) (kind : Kind) (key : Key kind) (operation : Mutable.Change (Obj kind)) :
    change kind key operation (pack spaces) =
      ((changeSpaces kind key operation spaces).map (fun (result, next) => (result, pack next))).mapError Sum.inr := by
  unfold change changeSpaces
  rw [readSlot_pack]
  cases applied : operation.apply (spaces kind key) with
  | error fault => simp [applied, Except.map, Except.mapError]
  | ok slot => simp [applied, pack_update, Except.map, Except.mapError]

theorem arena_refines (kind : Kind) : (arena (Key := Key) (Name := Name) (Obj := Obj) kind).Refines (· kind) := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro key operation spaces
  dsimp only [arena]
  have raw : Mutable.Access.raw.change key operation (spaces kind) =
      ((operation.apply (spaces kind key)).map ((spaces kind).replaceAt key)).map ((), ·) := by
    change ((operation.run State.step key (spaces kind)).map ((), ·)) = _
    rw [Mutable.Change.run_raw]
  rw [raw]
  cases applied : operation.apply (spaces kind key) <;> simp [Step.ofModel, changeSpaces, update, applied, Except.map,
    Except.mapError]

end Silmaril.Proofs.Semantics.Arena.Traits.Tagged
