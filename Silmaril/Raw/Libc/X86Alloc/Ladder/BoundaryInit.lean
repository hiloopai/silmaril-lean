module

public import Silmaril.Raw.Libc.X86Alloc.Ladder.BoundaryF9

/-! # Proofs: rung 08 (boundary tags) — the loaded data is the allocator state

The static data (`Boundary.data`) is the state for the free list `[(heap, 4096)]`: `flist`
points at the arena, the tables mark its first and last granules, and the arena is one free
block with zero links. -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Sep
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Ladder.Boundary

/-- Eight little-endian bytes of a word. -/
abbrev enc (w : Word) : List Byte := Silmaril.Machine.LittleEndian.encodeWords [w]

theorem data_eq : data = enc (wd heap) ++ (List.replicate 24 0 ++
    ((List.range 256).map (lastT [(heap, 4096)]) ++ ((List.range 256).map (firstT [(heap, 4096)]) ++
    (enc (wd 4096) ++ (enc (wd 0) ++ (enc (wd 0) ++ (List.replicate 4064 0 ++
    enc (wd 4096)))))))) := by
  decide +kernel

theorem zeros_blockAny (a k a' k' : Nat) (ha : a = a') (hk : k = k') :
    bytesPt a (List.replicate k 0) ⊢ₛ blockAny a' k' := by
  subst ha hk
  exact entails_trans (bytesPt_blockAny _ _) (entails_of_eq (by rw [List.length_replicate]))

/-- **The loaded image establishes the allocator state.** -/
theorem init : layout.Init ⊢ₛ mm := by
  unfold Layout.Init
  show bytesPt flistA data ⊢ₛ mm
  rw [data_eq]
  simp only [bytesPt, bytesAt_append, enc, Silmaril.Machine.LittleEndian.encodeWords_length,
    List.length_cons, List.length_nil, List.length_replicate, List.length_map, List.length_range,
    flistA, Nat.reduceAdd, Nat.reduceMul]
  have hg : Good (heap, 4096) := by unfold Good; decide
  refine sexists_intro [(heap, 4096)] (spure_sep_intro ⟨fun y hy => by
    rw [List.mem_singleton.1 hy]; exact hg, List.pairwise_singleton _ _⟩ ?_)
  unfold mmOf tblPt
  rw [dll, dll_nil, sep_emp, show hdOr ([] : List (Nat × Nat)) 0 = 0 from rfl,
    show hdOr [(heap, 4096)] 0 = heap from rfl]
  unfold blk
  exact sep_mono (entails_refl _) (sep_mono (zeros_blockAny _ _ _ _ (by decide) rfl)
    (sep_mono (entails_refl _) (sep_mono (entails_refl _) (sep_mono (entails_refl _)
    (sep_mono (entails_refl _) (sep_mono (entails_refl _) (sep_mono
      (zeros_blockAny _ _ _ _ (by decide) (by decide)) (entails_refl _))))))))

end Silmaril.Raw.Libc.X86Alloc.Ladder.Boundary
