module

public import Silmaril.Wasm.KernelEval.Thms
public import Silmaril.Wasm.KernelEval.Examples

@[expose] public section

/-!
# Kernel evaluation of a small Wasm subset: tests

Each test is checked by the kernel (`decide +kernel`), with no compiled code trusted. The last
ones show the intended use: evaluate on the packed memory, then transport the fact to the
reference list memory and to the reference run.
-/

namespace Silmaril.Wasm.KernelEval.Tests

open Silmaril.Wasm.KernelEval Examples Instr BinOp

/-- `sumTo 100 = 4950`, on both memories. -/
example : returns 100000 sumTo (sumToLocals 100) (NatMem.zeros 0) 4950 = true := by
  decide +kernel

example : returns 100000 sumTo (sumToLocals 10) (listZeros 0) 45 = true := by decide +kernel

/-- Insertion sort of `8, 7, …, 1` in a 64 KiB page: `mem[0] + mem[7] = 1 + 8`. -/
example : returns 100000 fillSort (fillSortLocals 8) (NatMem.zeros 65536) 9 = true := by
  decide +kernel

/-- Byte and word accesses agree: store a word, read back its bytes. -/
def bytesOfWord : List Instr :=
  [ const 0, const 0x11223344, store 0,
    const 0, load8u 0, const 1, load8u 0, const 8, bin shl, bin or,
    const 2, load8u 0, const 16, bin shl, bin or, const 3, load8u 0, const 24, bin shl, bin or,
    const 1, const 0xff, store8 1, const 0, load 0, bin xor ]

example : returns 1000 bytesOfWord [] (NatMem.zeros 8) (0x11223344 ^^^ 0x11ff3344 ^^^ 0) =
    true := by decide +kernel

example : returns 1000 bytesOfWord [] (listZeros 8) (0x11223344 ^^^ 0x11ff3344) = true := by
  decide +kernel

/-- An out-of-bounds store traps. -/
example : (run 10 (Config.init [const 65533, const 1, store 0] [] (NatMem.zeros 65536)) matches
    .trap) := by decide +kernel

/-- A branch to a missing label is stuck, not a trap. -/
example : (run 10 (Config.init [br 3] [] (NatMem.zeros 0)) matches .stuck) := by decide +kernel

/-- The paranoid mode end to end: a kernel evaluation on the packed memory proves that the
reference run, on the reference list memory of 64 KiB of zeros, returns `9`. -/
theorem fillSort8_returns :
    ∃ s ls m, run 100000 (Config.init fillSort (fillSortLocals 8)
      (⟨List.replicate 65536 0⟩ : ListMem)) = .done (9 :: s) ls m := by
  apply run_of_returns
  rw [← returns_toNatMem, zeros_eq]
  decide +kernel

end Silmaril.Wasm.KernelEval.Tests
