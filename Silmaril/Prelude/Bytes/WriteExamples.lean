module

public import Silmaril.Prelude.Bytes.Write.Thms
public import Silmaril.Prelude.Bytes.KernelExamples

/-! # Writes on kernel bytes: kernel-only examples

On the pinned `hello-gcc` (`Silmaril.Prelude.Bytes.KernelExamples.hello`, a canonical tree of
four leaves of at most 4096 bytes) and on zero memories. Each fact is proved twice where that
is instructive: once by the kernel on the concrete tree (`decide +kernel`), once from the
general theorems of `Silmaril.Prelude.Bytes.Write.Thms` with no evaluation.
-/

@[expose] public section

namespace Silmaril.KBytes.WriteExamples

open Silmaril.KBytes Silmaril.KBytes.KernelExamples

theorem hello_len_le {a : Nat} (h : a ≤ 15960) : a ≤ hello.len := by rw [hello.len_eq]; exact h

/-! ## Invariants of the canonical file tree -/

/-- Validity, leaf bound and normal leaves of the file tree (all by the kernel). -/
theorem hello_invariants : hello.wf && leafBound 4096 hello && normal hello := by decide +kernel

/-! ## A write across a leaf boundary -/

/-- Eight bytes at 4092: four in the first leaf, four in the second. -/
noncomputable def crossed : KBytes := hello.write 4092 8 0x1122334455667788

theorem crossed_read : crossed.readLE 4092 8 = some 0x1122334455667788 := by decide +kernel

/-- The same from the general theorem, with no evaluation. -/
theorem crossed_read' : crossed.readLE 4092 8 = some 0x1122334455667788 := by
  rw [crossed, readLE_write_self hello hello.wf_true _ (hello_len_le (by decide))]

/-- Truncation: a 2-byte write keeps the two low bytes. -/
theorem truncated : (hello.write 4095 2 0xABCDEF).readLE 4095 2 = some 0xCDEF := by
  decide +kernel

/-- The neighbours of the window are unchanged (disjointness theorem). -/
theorem crossed_magic : crossed.readLE 0 4 = some 0x464c457f := by
  rw [crossed, readLE_write_disjoint hello hello.wf_true _ (hello_len_le (by decide))
    (by decide)]
  exact magic

/-- The written tree keeps the leaf bound (no evaluation) and the normal leaves. -/
theorem crossed_leafBound : leafBound 4096 crossed = true := by
  rw [crossed, leafBound_write]; decide +kernel

theorem crossed_normal : normal crossed = true :=
  normal_write hello _ _ _ hello.wf_true (hello_len_le (by decide))
    (by have := hello_invariants; simp_all [Bool.and_eq_true])

/-- Path copying and the rope give the same bytes; the rope is no longer leaf-bounded. -/
theorem rope_vs_path : (hello.ropeWrite 4092 8 0x1122334455667788).readLE 4090 12 =
    crossed.readLE 4090 12 := by decide +kernel

/-! ## An ELF patch on a shared base -/

/-- Two variants of the file with different entry points (`e_entry`, 8 bytes at 24). -/
noncomputable def entryA : KBytes := hello.write 24 8 0x401000
noncomputable def entryB : KBytes := hello.write 24 8 0x402000

theorem entries : entryA.readLE 24 8 = some 0x401000 ∧ entryB.readLE 24 8 = some 0x402000 := by
  decide +kernel

/-- Outside the patched field the variants agree byte for byte (no evaluation). -/
theorem variants_agree (i : Nat) (hi : ¬(24 ≤ i ∧ i < 32)) : entryA.get? i = entryB.get? i :=
  get?_write_shared hello hello.wf_true _ _ (hello_len_le (by decide))
    (hello_len_le (by decide)) hi hi

/-- The program headers, read through a slice of a patched variant, are the file's. -/
theorem entryA_interpHeader : (entryA.slice 64 (13 * 56)).readLE 56 4 = some 3 := by
  rw [readLE_slice entryA (wf_write _ _ _ _ hello.wf_true (hello_len_le (by decide)))
    (by rw [entryA, len_write]; exact hello_len_le (by decide)), ite_eq_left (by decide), entryA,
    readLE_write_disjoint hello hello.wf_true _ (hello_len_le (by decide)) (by decide)]
  decide +kernel

/-! ## Zero memories -/

/-- One zero leaf of 64 KiB: a write crossing what would be a page boundary. -/
theorem zeros_write : ((zeros 65536).write 4094 4 0xDEADBEEF).readLE 4092 8 =
    some (0xDEADBEEF * 256 ^ 2) := by decide +kernel

/-- The canonical zero tree with 4 KiB leaves: the same reads, and a leaf bound. -/
theorem zerosCanon_write : ((zerosCanon 4096 65536).write 4094 4 0xDEADBEEF).readLE 4092 8 =
    some (0xDEADBEEF * 256 ^ 2) := by decide +kernel

theorem zeros_leafBound : leafBound 4096 (zeros 65536) = false ∧
    leafBound 4096 (zerosCanon 4096 65536) = true := by decide +kernel

end Silmaril.KBytes.WriteExamples
