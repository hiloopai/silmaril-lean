module

public import Silmaril.Semantics.Arena.Traits.Tagged.Defs
public import Silmaril.Semantics.Arena.Traits.Thms
import Silmaril.Proofs.Semantics.Arena.Traits.Tagged

public section

namespace Silmaril.Semantics.Arena.Traits.Tagged

variable {Kind : Type} {Key Name Obj : Kind → Type}

theorem pack_coherent (spaces : Spaces Key Name Obj) : Coherent (pack spaces) :=
  Proofs.Semantics.Arena.Traits.Tagged.pack_coherent spaces

theorem different_kind {kind other : Kind} (unequal : kind ≠ other) (key : Key kind) (query : Key other) :
    (⟨kind, key⟩ : Handle Key) ≠ ⟨other, query⟩ := fun equal => unequal (congrArg Sigma.fst equal)

variable [DecidableEq Kind]

theorem readSlot_pack (spaces : Spaces Key Name Obj) (kind : Kind) (key : Key kind) :
    readSlot (pack spaces) kind key = .ok (spaces kind key) :=
  Proofs.Semantics.Arena.Traits.Tagged.readSlot_pack spaces kind key

theorem read_pack (spaces : Spaces Key Name Obj) (kind : Kind) (key : Key kind) :
    read (pack spaces) kind key = .ok ((spaces kind key).map Slot.payload) := by
  rw [read, readSlot_pack]; rfl

/-- Separate typed tables and coherent unified tables have identical full
slot observations, including name claims, holes and reservations. -/
def equiv : Spaces Key Name Obj ≃ {table : Table Key Name Obj // Coherent table} where
  toFun spaces := ⟨pack spaces, pack_coherent spaces⟩
  invFun := decode
  left_inv := Proofs.Semantics.Arena.Traits.Tagged.decode_pack
  right_inv table := Subtype.ext (Proofs.Semantics.Arena.Traits.Tagged.pack_decode table)

variable [∀ kind, DecidableEq (Key kind)]

theorem overwrite_other_kind (table : Table Key Name Obj) {kind other : Kind}
    (unequal : kind ≠ other) (key : Key kind) (query : Key other) (slot : Option (Slot (Name kind) (Obj kind))) :
    overwrite table kind key slot ⟨other, query⟩ = table ⟨other, query⟩ := by
  simp [overwrite, different_kind unequal key query]

/-- Exact result and successor for all four ordinary edits. Starting with a
coherent table, a successful edit produces another table in the image of `pack`.
Semantic slot errors are not tagged as representation failures. -/
theorem change_pack (spaces : Spaces Key Name Obj) (kind : Kind) (key : Key kind) (operation : Mutable.Change (Obj kind)) :
    change kind key operation (pack spaces) =
      ((changeSpaces kind key operation spaces).map (fun (result, next) => (result, pack next))).mapError Sum.inr :=
  Proofs.Semantics.Arena.Traits.Tagged.change_pack spaces kind key operation

theorem arena_refines (kind : Kind) : (arena (Key := Key) (Name := Name) (Obj := Obj) kind).Refines (· kind) :=
  Proofs.Semantics.Arena.Traits.Tagged.arena_refines kind

end Silmaril.Semantics.Arena.Traits.Tagged
