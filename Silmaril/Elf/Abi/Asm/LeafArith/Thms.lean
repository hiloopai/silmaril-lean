module

public import Silmaril.Elf.Asm.Example.LeafArith.Defs
public import Silmaril.Elf.Abi.LeafArith.Thms

/-! # Assembly records and conformance rows of `leaf-arith`: the bridge

The assembly records `Silmaril.Elf.Asm.Example.LeafArith.clamp` and `.sat` (the explorer's
Assembly tab) and the conformance rows `silmaril.elf.abi.leaf_arith.clamp_i32` and
`….sat_add_u32` are about the same function when the row's code, entered at its offset, is the
record's address and its function bytes are the record's bytes. These theorems state exactly
that (kernel computations); the explorer links a record to a row only through them.

* `clamp_record_code`, `sat_record_code`: the row's entry address (`base + off`) is the record's
  `extent.vaddr`, its extent (`len`) is the record's size, and the bytes the row calls the
  function (`(bytes.drop off).take len`) are the record's bytes. -/

@[expose] public section

namespace Silmaril.Elf.Abi.Asm.LeafArith

open Silmaril.Machine.Abi.Conformance (Code)

/-- **The row's function is the record's function**: entry address, extent and bytes. -/
def SameFunction (c : Code) (f : Silmaril.Elf.Asm.AsmFunction) : Prop :=
  c.base.toNat + c.off = f.extent.vaddr ∧ c.len = f.extent.size ∧ (c.bytes.drop c.off).take c.len = f.bytes

theorem clamp_record_code :
    SameFunction Silmaril.Machine.Abi.Conformance.LeafArith.clampCode Silmaril.Elf.Asm.Example.LeafArith.clamp :=
  ⟨by decide, rfl, rfl⟩

theorem sat_record_code :
    SameFunction Silmaril.Machine.Abi.Conformance.LeafArith.satCode Silmaril.Elf.Asm.Example.LeafArith.sat :=
  ⟨by decide, rfl, rfl⟩

end Silmaril.Elf.Abi.Asm.LeafArith

end
