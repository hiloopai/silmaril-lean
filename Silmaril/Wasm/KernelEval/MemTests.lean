module

public import Silmaril.Wasm.KernelEval.Examples
public import Silmaril.Wasm.KernelEval.Thms
public import Silmaril.Wasm.KernelEval.MemThms
public import Silmaril.Wasm.KernelEval.CoreMemThms
public import Silmaril.Wasm.KernelEval.KBytesMemThms

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

/-- The same run on `Silmaril.KBytes` with path-copying stores, transported to the reference. -/
theorem fillSort8_returns_kbytes :
    ∃ s ls m, run 100000 (Config.init fillSort (fillSortLocals 8)
      (⟨List.replicate 65536 0⟩ : ListMem)) = .done (9 :: s) ls m := by
  apply run_of_returns
  rw [show (⟨List.replicate 65536 0⟩ : ListMem) = kToListMem (KPath.mk (kzeros 65536)).t from
    (kzeros_toListMem 65536).symm,
    returns_mapMem_on memSimOn_kPath _ _ _ (KPath.mk (kzeros 65536)) (wf_kzeros 65536)]
  decide +kernel

/-- A word store across a 4 KiB leaf boundary, on both `KBytes` memories. -/
example : returns 100 [const 4094, const 0x11223344, store 0, const 4093, load 0] []
    (KPath.mk (kzeros 8192)) 0x22334400 = true := by decide +kernel

example : returns 100 [const 4094, const 0x11223344, store 0, const 4093, load 0] []
    (KRope.mk (kzeros 8192)) 0x22334400 = true := by decide +kernel

/-- Rope stores on a one-leaf zero memory, transported to the reference run. -/
theorem fillSort8_returns_rope_leaf :
    ∃ s ls m, run 100000 (Config.init fillSort (fillSortLocals 8)
      (⟨List.replicate 65536 0⟩ : ListMem)) = .done (9 :: s) ls m := by
  apply run_of_returns
  rw [show (⟨List.replicate 65536 0⟩ : ListMem) = kToListMem (KRope.mk (kzero1 65536)).t from
    (kzero1_toListMem 65536).symm,
    returns_mapMem_on memSimOn_kRope _ _ _ (KRope.mk (kzero1 65536)) (wf_kzero1 65536)]
  decide +kernel

/-- An out-of-bounds rope store traps. -/
example : (run 10 (Config.init [const 65533, const 1, store 0] [] (KRope.mk (kzero1 65536)))
    matches .trap) := by decide +kernel

end Silmaril.Wasm.KernelEval.MemTests
