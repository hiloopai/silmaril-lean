module

public import Silmaril.Wasm.Binaryen.Pass.UnusedBlocks
public import Silmaril.Wasm.Binaryen.Exe.StageContract
public import Silmaril.Wasm.Binaryen.InlUnwrapClosed

@[expose] public section

/-! # Contracts of the initial unused-label and block-merging passes

Both contracts use the closed-host block-unwrapping simulation, including
stuck host calls. They hold for arbitrary host-state types.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen Execution.Core Numerics

namespace UnusedBlocksSound

variable {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}

/-- Restoring a function's existing body does not change the module. -/
theorem withBody_self {m : BModule} {g : Nat} {body : List BExpr}
    (h : m.body? g = some body) : m.withBody g body = m := by
  obtain ⟨fn, hfn, hb⟩ := Option.map_eq_some_iff.mp h
  rw [BModule.withBody, Unwrap.modifyAt_eq_set _ g _ hfn]
  have he : { fn with body := body } = fn := by cases fn; simp_all
  obtain ⟨hg, hget⟩ := List.getElem?_eq_some_iff.mp hfn
  rw [he, ← hget, List.set_getElem_self]

/-- The executable check supplies the simulation's three side conditions. -/
theorem eligible_spec {body : List BExpr} (h : UnusedBlocks.eligible body = true) :
    BExpr.labelsList body = [] ∧ (effectsList body).any = false ∧
      (effectsList body).branchesOut = false := by
  simpa [UnusedBlocks.eligible, Bool.and_eq_true, and_assoc] using h

/-- Splicing a checked block at a known site is a valid, equivalent module step. -/
theorem unwrap {m : BModule} {g : Nat} {K : BCtx} {bt : BlockType}
    {body : List BExpr} (hok : m.Ok)
    (hs : m.body? g = some (K.plug [.block bt body]))
    (he : UnusedBlocks.eligible body = true) :
    (m.withBody g (K.plug body)).Ok ∧ EE H o (m.withBody g (K.plug body)) m := by
  have hm := withBody_self hs
  obtain ⟨hf, ha, hr⟩ := eligible_spec he
  obtain ⟨fn, hfn, -⟩ := Option.map_eq_some_iff.mp hs
  have hg := (List.getElem?_eq_some_iff.mp hfn).1
  have hok' : (m.withBody g (K.plug [.block bt body])).Ok := by rw [hm]; exact hok
  refine ⟨block_unwrap_valid hf ha hr hok', ?_⟩
  have h := block_unwrap_exportEquiv_closed (H := H) hg hok' hf ha hr o
  rwa [hm] at h

/-- Soundness of the local unused-label rewrite. -/
theorem removeAt (m : BModule) (g : Nat) (hm : m.Ok) :
    (UnusedBlocks.removeAt m g).Ok ∧ EE H o (UnusedBlocks.removeAt m g) m := by
  unfold UnusedBlocks.removeAt
  split
  · next bt body hs =>
    split
    · next he => exact unwrap hm (K := .hole) hs he
    · exact ⟨hm, exportEquiv_refl _⟩
  · exact ⟨hm, exportEquiv_refl _⟩

/-- Soundness of flattening the inner member of two nested blocks. -/
theorem mergeAt (m : BModule) (g : Nat) (hm : m.Ok) :
    (UnusedBlocks.mergeAt m g).Ok ∧ EE H o (UnusedBlocks.mergeAt m g) m := by
  unfold UnusedBlocks.mergeAt
  split
  · next outer bt body hs =>
    split
    · next he =>
      simpa [BCtx.plug] using
        (unwrap (o := o) hm (K := .block outer [] .hole []) hs he)
    · exact ⟨hm, exportEquiv_refl _⟩
  · exact ⟨hm, exportEquiv_refl _⟩

/-- Uniform local steps compose across the function table. -/
theorem fold (step : BModule → Nat → BModule)
    (hstep : ∀ m g, m.Ok → (step m g).Ok ∧ EE H o (step m g) m)
    (gs : List Nat) (m : BModule) (hm : m.Ok) :
    (gs.foldl step m).Ok ∧ EE H o (gs.foldl step m) m := by
  induction gs generalizing m with
  | nil => exact ⟨hm, exportEquiv_refl _⟩
  | cons g gs ih =>
    obtain ⟨hok, he⟩ := hstep m g hm
    obtain ⟨hok', he'⟩ := ih (step m g) hok
    exact ⟨hok', he'.1.trans (fun _ _ _ h₁ h₂ => h₁.trans h₂) he.1,
      he.2.trans (fun _ _ _ h₁ h₂ => h₂.trans h₁) he'.2⟩

end UnusedBlocksSound

variable {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}

/-- RemoveUnusedNames preserves validity and observations under the closed host. -/
theorem removeUnusedNames_stageOk : StageOk o H removeUnusedNames := by
  intro m hm
  exact UnusedBlocksSound.fold _ (UnusedBlocksSound.removeAt) _ m hm.ok

/-- MergeBlocks preserves validity and observations under the closed host. -/
theorem mergeBlocksWhole_stageOk : StageOk o H mergeBlocks := by
  intro m hm
  exact UnusedBlocksSound.fold _ (UnusedBlocksSound.mergeAt) _ m hm.ok

end Silmaril.Wasm.Binaryen.Exe
