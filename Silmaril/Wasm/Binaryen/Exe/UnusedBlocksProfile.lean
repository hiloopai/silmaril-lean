module

public import Silmaril.Wasm.Binaryen.Exe.UnusedBlocksSound
public import Silmaril.Wasm.Binaryen.Exe.MergeBlocksAnySound
public import Silmaril.Wasm.Binaryen.InlUnwrapProfile

@[expose] public section

/-! Exact arbitrary-profile contracts for the existing unused-label and nested
block-merging executables. The runtime search, guards and fallback are unchanged. -/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen Execution.Core Numerics

namespace UnusedBlocksProfile

open UnusedBlocksSound

variable {P : Profile} {H : Type}

/-- Splicing a checked block at a known site is a valid, equivalent module step. -/
theorem unwrap {m : BModule} {g : Nat} {K : BCtx} {bt : BlockType}
    {body : List BExpr} (hok : m.Ok)
    (hs : m.body? g = some (K.plug [.block bt body]))
    (he : UnusedBlocks.eligible body = true) :
    (m.withBody g (K.plug body)).Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H)) (m.withBody g (K.plug body)).lower m.lower := by
  have hm := withBody_self hs
  obtain ⟨hf, ha, hr⟩ := eligible_spec he
  obtain ⟨fn, hfn, -⟩ := Option.map_eq_some_iff.mp hs
  have hg := (List.getElem?_eq_some_iff.mp hfn).1
  have hok' : (m.withBody g (K.plug [.block bt body])).Ok := by rw [hm]; exact hok
  refine ⟨block_unwrap_valid hf ha hr hok', ?_⟩
  have h := block_unwrap_exportEquiv_profile (H := H) hg hok' hf ha hr P
  rwa [hm] at h

/-- Soundness of the local unused-label rewrite. -/
theorem removeAt (m : BModule) (g : Nat) (hm : m.Ok) :
    (UnusedBlocks.removeAt m g).Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H)) (UnusedBlocks.removeAt m g).lower m.lower := by
  unfold UnusedBlocks.removeAt
  split
  · next bt body hs =>
    split
    · next he => exact unwrap hm (K := .hole) hs he
    · exact ⟨hm, exportEquiv_refl _⟩
  · exact ⟨hm, exportEquiv_refl _⟩

/-- Soundness of flattening the inner member of two nested blocks. -/
theorem mergeAt (m : BModule) (g : Nat) (hm : m.Ok) :
    (UnusedBlocks.mergeAt m g).Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H)) (UnusedBlocks.mergeAt m g).lower m.lower := by
  unfold UnusedBlocks.mergeAt
  split
  · next outer bt body hs =>
    split
    · next he =>
      simpa [BCtx.plug] using
        (unwrap (P := P) hm (K := .block outer [] .hole []) hs he)
    · exact ⟨hm, exportEquiv_refl _⟩
  · exact ⟨hm, exportEquiv_refl _⟩

/-- Uniform local steps compose across the function table. -/
theorem fold (step : BModule → Nat → BModule)
    (hstep : ∀ m g, m.Ok → (step m g).Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H)) (step m g).lower m.lower)
    (gs : List Nat) (m : BModule) (hm : m.Ok) :
    (gs.foldl step m).Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H)) (gs.foldl step m).lower m.lower := by
  induction gs generalizing m with
  | nil => exact ⟨hm, exportEquiv_refl _⟩
  | cons g gs ih =>
    obtain ⟨hok, he⟩ := hstep m g hm
    obtain ⟨hok', he'⟩ := ih (step m g) hok
    exact ⟨hok', he'.1.trans (fun _ _ _ h₁ h₂ => h₁.trans h₂) he.1,
      he.2.trans (fun _ _ _ h₁ h₂ => h₂.trans h₁) he'.2⟩

end UnusedBlocksProfile

namespace MergeBlocksAnyProfile

open MergeBlocksAny

variable {P : Profile} {H : Type}

/-- The selected site is spliced in an unchanged context, so `unwrap` applies. -/
theorem mergeAt (m : BModule) (g : Nat) (hm : m.Ok) :
    (MergeBlocksAny.mergeAt m g).Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H)) (MergeBlocksAny.mergeAt m g).lower m.lower := by
  unfold MergeBlocksAny.mergeAt
  split
  · exact ⟨hm, exportEquiv_refl _⟩
  · next body hbody =>
    split
    · exact ⟨hm, exportEquiv_refl _⟩
    · next s hs =>
      have hmem := List.mem_of_head? hs
      obtain ⟨he, hb⟩ := sites_good _ _ _ _ hmem
      exact UnusedBlocksProfile.unwrap hm (he ▸ hbody) hb

end MergeBlocksAnyProfile

variable (P : Profile) {H : Type}

/-- The existing RemoveUnusedNames pass at the same arbitrary numerical profile. -/
theorem removeUnusedNames_sound_profile {m : BModule} (hm : m.Ok) :
    (removeUnusedNames m).Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H))
      (removeUnusedNames m).lower m.lower :=
  UnusedBlocksProfile.fold _ UnusedBlocksProfile.removeAt _ m hm

/-- The original whole-function nested-block pass at every numerical profile. -/
theorem mergeBlocksWhole_sound_profile {m : BModule} (hm : m.Ok) :
    (mergeBlocks m).Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H))
      (mergeBlocks m).lower m.lower :=
  UnusedBlocksProfile.fold _ UnusedBlocksProfile.mergeAt _ m hm

/-- The existing arbitrary-depth MergeBlocks pass at every numerical profile. -/
theorem mergeBlocks_sound_profile {m : BModule} (hm : m.Ok) :
    (mergeBlocksAny m).Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H))
      (mergeBlocksAny m).lower m.lower :=
  UnusedBlocksProfile.fold _ MergeBlocksAnyProfile.mergeAt _ m hm

end Silmaril.Wasm.Binaryen.Exe
