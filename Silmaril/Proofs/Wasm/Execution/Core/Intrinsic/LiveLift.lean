module

public import Silmaril.Wasm.Execution.Core.Intrinsic.LiveLift.Defs

public section

namespace Silmaril.Proofs.Wasm.Execution.Core.Intrinsic

open Silmaril.Wasm Silmaril.Wasm.Execution.Core.Intrinsic

variable {kind : IntType} {locals input output : List IntType}

private theorem slot_lookup (ref : Slot locals kind) :
    Slot.lookup locals ref.toNat = some ⟨kind, ref, rfl⟩ := by
  induction ref with
  | here => rfl
  | there ref ih => simp [Slot.toNat, Slot.lookup, ih]

private theorem reify_op (op : Op locals input output) (live : op.erase ≠ .unreachable) :
    Op.reify? locals input op.erase = some ⟨output, op, rfl, live⟩ := by
  cases op with
  | nop => rfl
  | drop => rfl
  | localGet ref bound =>
    simp [Op.reify?, Op.erase, Slot.index, Idx.toNat, slot_lookup ref]
  | @intBin kind _ op => cases kind <;> rfl
  | unreachable => exact (live rfl).elim

theorem reify_erase (code : Code locals input output) (live : .unreachable ∉ code.erase) :
    Code.reify? locals input code.erase = some ⟨output, code, rfl, live⟩ := by
  induction code with
  | done => rfl
  | seq op tail ih =>
    have hOp : op.erase ≠ .unreachable := fun eq => live (List.mem_cons.mpr (.inl eq.symm))
    have hTail : .unreachable ∉ tail.erase := fun member => live (List.mem_cons.mpr (.inr member))
    simp [Code.erase, Code.reify?, reify_op op hOp, ih hTail]

private def eraseChecked (code : Code.Live locals input) : Code.CheckedRaw locals input :=
  ⟨code.2.1.erase, by rw [reify_erase code.2.1 code.2.2]; rfl⟩

private def toLive {raw : List Instr} (lifted : Code.Lifted locals input raw) : Code.Live locals input :=
  ⟨lifted.1, lifted.2.1, by rw [lifted.2.2.1]; exact lifted.2.2.2⟩

private def liftChecked (raw : Code.CheckedRaw locals input) : Code.Live locals input :=
  toLive ((Code.reify? locals input raw.1).get raw.2)

def liveEquiv (locals input : List IntType) : Code.Live locals input ≃ Code.CheckedRaw locals input where
  toFun := eraseChecked
  invFun := liftChecked
  left_inv := by
    rintro ⟨output, code, live⟩
    have checked := (eraseChecked ⟨output, code, live⟩ : Code.CheckedRaw locals input).2
    have get : (Code.reify? locals input code.erase).get checked = ⟨output, code, rfl, live⟩ :=
      Option.get_of_eq_some checked (reify_erase code live)
    change toLive ((Code.reify? locals input code.erase).get checked) = (⟨output, code, live⟩ : Code.Live locals input)
    rw [get]
    rfl
  right_inv := by
    intro raw
    apply Subtype.ext
    exact ((Code.reify? locals input raw.1).get raw.2).2.2.1

end Silmaril.Proofs.Wasm.Execution.Core.Intrinsic
