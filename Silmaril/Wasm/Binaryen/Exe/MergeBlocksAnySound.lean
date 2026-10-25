module

public import Silmaril.Wasm.Binaryen.MergeBlocksAnySearch
public import Silmaril.Wasm.Binaryen.Exe.UnusedBlocksSound

@[expose] public section

/-! Soundness of searching for and splicing nested blocks. The search certificate
identifies one unchanged BCtx; validity and all observations follow from `unwrap`.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen Execution.Core Numerics

namespace MergeBlocksAnySound

open MergeBlocksAny

variable {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}

/-- The selected site is spliced in an unchanged context, so `unwrap` applies. -/
theorem mergeAt (m : BModule) (g : Nat) (hm : m.Ok) :
    (MergeBlocksAny.mergeAt m g).Ok ∧ EE H o (MergeBlocksAny.mergeAt m g) m := by
  unfold MergeBlocksAny.mergeAt
  split
  · exact ⟨hm, exportEquiv_refl _⟩
  · next body hbody =>
    split
    · exact ⟨hm, exportEquiv_refl _⟩
    · next s hs =>
      have hmem := List.mem_of_head? hs
      obtain ⟨he, hb⟩ := sites_good _ _ _ _ hmem
      exact UnusedBlocksSound.unwrap hm (he ▸ hbody) hb

end MergeBlocksAnySound

variable {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}

/-- Merging unused nested block labels preserves validity and closed-host observations. -/
theorem mergeBlocks_stageOk : StageOk o H mergeBlocksAny := by
  intro m hm
  exact UnusedBlocksSound.fold _ MergeBlocksAnySound.mergeAt _ m hm.ok

end Silmaril.Wasm.Binaryen.Exe
