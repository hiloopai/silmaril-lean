module

public import Silmaril.Libc.X86Alloc.Ladder.FirstFit.Live
public import Silmaril.Raw.Libc.X86Alloc.HdrSeg
public import Silmaril.X86.Sep.Alloc.Thms

/-! # Proofs: rung 05 (first-fit) — the loaded `.data` is the one-block free list -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitInit

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Sep
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Ladder.FirstFit

theorem init : layout.Init ⊢ₛ iface.mmS ffS0 := by
  unfold Layout.Init
  dsimp only [layout, data]
  have e2 : Silmaril.Machine.LittleEndian.encodeWords [(4080 : Word), 0] =
      Silmaril.Machine.LittleEndian.encodeWords [(4080 : Word)] ++
        Silmaril.Machine.LittleEndian.encodeWords [(0 : Word)] := by decide
  rw [e2, bytesPt, bytesAt_append, bytesAt_append, bytesAt_append, bytesAt_append]
  simp only [List.length_append, List.length_replicate,
    show (Silmaril.Machine.LittleEndian.encodeWords [(0x4030b0 : Word)]).length = 8 by decide,
    show (Silmaril.Machine.LittleEndian.encodeWords [(4080 : Word)]).length = 8 by decide]
  refine sexists_intro [⟨0x4030b0, 4080⟩] (sexists_intro (0x4030b0 : Word) ?_)
  refine spure_sep_intro (fun c hc => by simpa [ffS0] using hc) ?_
  have hWF : Block.WF ⟨0x4030b0, 4080⟩ := ⟨by decide, by decide, by decide⟩
  rw [hdrSeg_cons]
  refine entails_trans ?_ (sep_mono_right _ (sep_mono_left _ (spure_sep_intro ⟨rfl, hWF⟩
    (sexists_intro (0 : Word) (entails_refl _)))))
  dsimp only
  rw [hdrSeg_nil]
  have e1 : wordPt flAddr.toNat (0x4030b0 : Word) =
      bytesAt RW 0x4030a0 (Silmaril.Machine.LittleEndian.encodeWords [(0x4030b0 : Word)]) := by
    rw [show flAddr.toNat = 0x4030a0 by decide]; rfl
  have e3 : wordPt (0x4030b0 : Word).toNat (BitVec.ofNat 64 4080) =
      bytesAt RW (0x4030a0 + (8 + 8)) (Silmaril.Machine.LittleEndian.encodeWords [(4080 : Word)]) := by
    rw [show (0x4030b0 : Word).toNat = 0x4030a0 + (8 + 8) by decide]; rfl
  have e4 : wordPt ((0x4030b0 : Word) + 8#64).toNat 0 =
      bytesAt RW (0x4030a0 + (8 + 8) + 8) (Silmaril.Machine.LittleEndian.encodeWords [(0 : Word)]) := by
    rw [show ((0x4030b0 : Word) + 8#64).toNat = 0x4030a0 + (8 + 8) + 8 by decide]; rfl
  have hb : bytesAt RW (0x4030a0 + (8 + 8 + (8 + (Silmaril.Machine.LittleEndian.encodeWords
      [(0 : Word)]).length))) (List.replicate 4080 0) ⊢ₛ
      blockAny ((0x4030b0 : Word).toNat + 16) 4080 := by
    refine entails_trans (bytesPt_blockAny _ _) (entails_of_eq ?_)
    rw [List.length_replicate]
    congr 1
  rw [e1, e3, e4]
  refine entails_trans ?_ (sep_mono_right _ (sep_mono_left _ (sep_mono_right _ (sep_mono_right _
    (sep_mono_left _ hb)))))
  refine entails_trans ?_ (sep_mono_right _ (sep_mono_left _ (sep_mono_right _ (sep_mono_right _
    (sep_mono_right _ (show emp ⊢ₛ ⌜(0 : Word) = 0⌝ from fun _ he => ⟨he, rfl⟩))))))
  refine entails_trans (sep_mono_left _ (sep_mono_left _ (sep_mono_right _ (entails_strue _))))
    (entails_of_eq ?_)
  rw [sep_emp]
  ac_rfl

theorem initR : layout.Init ⊢ₛ ifaceR.mmS relS0 := by
  unfold Layout.Init
  dsimp only [layout, data]
  have e2 : Silmaril.Machine.LittleEndian.encodeWords [(4080 : Word), 0] =
      Silmaril.Machine.LittleEndian.encodeWords [(4080 : Word)] ++
        Silmaril.Machine.LittleEndian.encodeWords [(0 : Word)] := by decide
  rw [e2, bytesPt, bytesAt_append, bytesAt_append, bytesAt_append, bytesAt_append]
  simp only [List.length_append, List.length_replicate,
    show (Silmaril.Machine.LittleEndian.encodeWords [(0x4030b0 : Word)]).length = 8 by decide,
    show (Silmaril.Machine.LittleEndian.encodeWords [(4080 : Word)]).length = 8 by decide]
  refine sexists_intro (0x4030b0 : Word) ?_
  show _ ⊢ₛ (wordPt flAddr.toNat (0x4030b0 : Word) ∗ hdrSeg [⟨0x4030b0, 4080⟩] (0x4030b0 : Word) ∗
    strue)
  have hWF : Block.WF ⟨0x4030b0, 4080⟩ := ⟨by decide, by decide, by decide⟩
  rw [hdrSeg_cons]
  refine entails_trans ?_ (sep_mono_right _ (sep_mono_left _ (spure_sep_intro ⟨rfl, hWF⟩
    (sexists_intro (0 : Word) (entails_refl _)))))
  dsimp only
  rw [hdrSeg_nil]
  have e1 : wordPt flAddr.toNat (0x4030b0 : Word) =
      bytesAt RW 0x4030a0 (Silmaril.Machine.LittleEndian.encodeWords [(0x4030b0 : Word)]) := by
    rw [show flAddr.toNat = 0x4030a0 by decide]; rfl
  have e3 : wordPt (0x4030b0 : Word).toNat (BitVec.ofNat 64 4080) =
      bytesAt RW (0x4030a0 + (8 + 8)) (Silmaril.Machine.LittleEndian.encodeWords [(4080 : Word)]) := by
    rw [show (0x4030b0 : Word).toNat = 0x4030a0 + (8 + 8) by decide]; rfl
  have e4 : wordPt ((0x4030b0 : Word) + 8#64).toNat 0 =
      bytesAt RW (0x4030a0 + (8 + 8) + 8) (Silmaril.Machine.LittleEndian.encodeWords [(0 : Word)]) := by
    rw [show ((0x4030b0 : Word) + 8#64).toNat = 0x4030a0 + (8 + 8) + 8 by decide]; rfl
  have hb : bytesAt RW (0x4030a0 + (8 + 8 + (8 + (Silmaril.Machine.LittleEndian.encodeWords
      [(0 : Word)]).length))) (List.replicate 4080 0) ⊢ₛ
      blockAny ((0x4030b0 : Word).toNat + 16) 4080 := by
    refine entails_trans (bytesPt_blockAny _ _) (entails_of_eq ?_)
    rw [List.length_replicate]
    congr 1
  rw [e1, e3, e4]
  refine entails_trans ?_ (sep_mono_right _ (sep_mono_left _ (sep_mono_right _ (sep_mono_right _
    (sep_mono_left _ hb)))))
  refine entails_trans ?_ (sep_mono_right _ (sep_mono_left _ (sep_mono_right _ (sep_mono_right _
    (sep_mono_right _ (show emp ⊢ₛ ⌜(0 : Word) = 0⌝ from fun _ he => ⟨he, rfl⟩))))))
  refine entails_trans (sep_mono_left _ (sep_mono_left _ (sep_mono_right _ (entails_strue _))))
    (entails_of_eq ?_)
  rw [sep_emp]
  ac_rfl

end Silmaril.Raw.Libc.X86Alloc.Ladder.FirstFitInit
