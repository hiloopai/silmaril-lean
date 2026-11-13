module

public import Silmaril.Wasm.KernelEval.Examples
public import Silmaril.Wasm.KernelEval.Thms
public import Silmaril.Wasm.KernelEval.MemThms
public import Silmaril.Wasm.KernelEval.CoreMemThms

@[expose] public section

/-!
# Kernel evaluation of a small Wasm subset: memory representation tests

Checked by the kernel (`decide +kernel`).
-/

open Silmaril.Wasm.KernelEval Silmaril.Wasm.KernelEval.Examples
  Silmaril.Wasm.KernelEval.Instr Silmaril.Wasm.KernelEval.BinOp

namespace Silmaril.Wasm.KernelEval.MemTests

/-- The same run on a persistent page tree (16 pages of 4 KiB) and on an overlay, transported
to the reference list memory of 64 KiB of zeros. -/
theorem fillSort8_returns_pages :
    ∃ s ls m, run 100000 (Config.init fillSort (fillSortLocals 8)
      (⟨List.replicate 65536 0⟩ : ListMem)) = .done (9 :: s) ls m := by
  apply run_of_returns
  rw [show (⟨List.replicate 65536 0⟩ : ListMem) = (PageMem.zeros 12 4).toList from
    (pageMem_zeros_toList 12 4).symm, returns_mapMem_on memSimOn_pageMem _ _ _ _ (wf_zeros 12 4)]
  decide +kernel

example : returns 100000 fillSort (fillSortLocals 8) (Overlay.ofBase (NatMem.zeros 65536)) 9 =
    true := by decide +kernel

/-- Pages of 4 bytes: a word store across a page boundary goes byte by byte. -/
example : returns 100 [const 6, const 0x11223344, store 0, const 5, load 0] []
    (PageMem.zeros 2 2) 0x22334400 = true := by decide +kernel

/-- The existing kernel evaluator's memory accesses (`fload`/`fstore` over a lazily zero
`ByteArray`) on the same program. -/
example : returns 100000 fillSort (fillSortLocals 8) (KMem.zeros 256) 9 = true := by
  decide +kernel

end Silmaril.Wasm.KernelEval.MemTests
