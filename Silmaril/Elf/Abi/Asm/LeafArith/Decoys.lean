module

public import Silmaril.Elf.Abi.Asm.LeafArith.Thms

/-! # Decoy bridges for the explorer's record-to-row link checker (test fixtures)

True statements that **mention** a record and a row's code without saying the row's code is the
record's function. The explorer's link checker (`tools/elf-pages`, `abiLinkSelfTest`) must
reject every link built on them; they are not results. `sat_not_clamp` is the fact that makes a
`clamp`-to-`sat_add_u32` link wrong. -/

@[expose] public section

namespace Silmaril.Elf.Abi.Asm.LeafArith.Decoys

open Silmaril.Elf.Abi.Asm.LeafArith (SameFunction)

theorem or_true : True ∨ SameFunction Silmaril.Machine.Abi.Conformance.LeafArith.satCode
    Silmaril.Elf.Asm.Example.LeafArith.clamp := .inl trivial

theorem both_refl : Silmaril.Machine.Abi.Conformance.LeafArith.satCode =
    Silmaril.Machine.Abi.Conformance.LeafArith.satCode ∧
    Silmaril.Elf.Asm.Example.LeafArith.clamp = Silmaril.Elf.Asm.Example.LeafArith.clamp := ⟨rfl, rfl⟩

/-- `sat_add_u32`'s row code is not `clamp_i32`'s record. -/
theorem sat_not_clamp : ¬ SameFunction Silmaril.Machine.Abi.Conformance.LeafArith.satCode
    Silmaril.Elf.Asm.Example.LeafArith.clamp := fun h => absurd h.1 (by decide)

end Silmaril.Elf.Abi.Asm.LeafArith.Decoys

end
