module

public import Silmaril.Proofs.Wasm.Game.Linking.Split.Top

/-!
# Static linking, separation: Rel4

Original module documentation:

# The three-store relation (M3 step B, #1977)

Game semantics of WebAssembly modules (tracking issue #1982), milestone M3, step (B).

`Rel4 Op₀ Oc₀ ρp Op ρc Oc σ π κ`: the provider store `π` and the consumer store `κ` both embed
into the shared store `σ` (`PartRel`), with disjoint images (globals by ownership, structs and
arrays by renamed address), and with the function and global ownership fixed once and for all
(`Op₀`, `Oc₀`).

* `Rel4.consumer_step`: a host-free step of the consumer is a host-free step of the shared world;
* `Rel4.provider_step`: a host-free step of the provider from top-level code, replayed inside the
  consumer's callout context, is a host-free step of the shared world.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Game.Linking.Split

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Numerics

variable {H : Type}

/-- The provider and consumer stores embed disjointly into the shared store. -/
structure Rel4 (Op₀ Oc₀ : Own) (ρp : Ren) (Op : Own) (ρc : Ren) (Oc : Own)
    (σ π κ : Store H) : Prop where
  rp : PartRel ρp Op π σ
  rc : PartRel ρc Oc κ σ
  fnp : Op.fn = Op₀.fn
  glp : Op.gl = Op₀.gl
  fnc : Oc.fn = Oc₀.fn
  glc : Oc.gl = Oc₀.gl
  gl : ∀ a, Op.gl a → ¬ Oc.gl a
  st : ∀ a b, Op.st a → Oc.st b → ρp.st a ≠ ρc.st b
  ar : ∀ a b, Op.ar a → Oc.ar b → ρp.ar a ≠ ρc.ar b

namespace Rel4

variable {Op₀ Oc₀ : Own} {ρp ρc : Ren} {Op Oc : Own} {σ π κ : Store H}

/-- The consumer moves the shared world. -/
theorem consumer_step {P : Profile} (hR : Rel4 Op₀ Oc₀ ρp Op ρc Oc σ π κ) {F F' : Frame}
    {X X' : List Admin} {κ' : Store H} (hf : Oc.FrameGood F) (hc : Oc.CodeGood X)
    (h : Step P noHost ⟨κ, F, X⟩ ⟨κ', F', X'⟩) :
    ∃ ρc' Oc' σ', Step P noHost ⟨σ, ρc.frame F, ρc.code X⟩ ⟨σ', ρc'.frame F', ρc'.code X'⟩ ∧
      Rel4 Op₀ Oc₀ ρp Op ρc' Oc' σ' π κ' ∧ Oc'.FrameGood F' ∧ Oc'.CodeGood X' ∧
      Grow ρc Oc ρc' Oc' σ ∧ σ.structs.length ≤ σ'.structs.length ∧
      σ.arrays.length ≤ σ'.arrays.length := by
  obtain ⟨ρc', Oc', σ', hst, hrc, hf', hc', hg, ht⟩ := step_sim h (ρ := ρc) (O := Oc) (σ := σ)
    hR.rc hf hc
  refine ⟨ρc', Oc', σ', hst, ⟨?_, hrc, hR.fnp, hR.glp, hg.fn.trans hR.fnc,
    hg.gl.trans hR.glc, ?_, ?_, ?_⟩, hf', hc', hg, ht.structs_len, ht.arrays_len⟩
  · exact hR.rp.touch ht (fun a ha => hR.gl a ha) (fun a b ha hb e => hR.st a b ha hb e.symm)
      (fun a b ha hb e => hR.ar a b ha hb e.symm)
  · intro a ha; rw [hg.gl]; exact hR.gl a ha
  · intro a b ha hb e
    rcases hg.stNew b hb with hb' | hb'
    · exact hR.st a b ha hb' (e.trans (hg.st b hb').2)
    · have := (hR.rp.st_lt ha).2
      omega
  · intro a b ha hb e
    rcases hg.arNew b hb with hb' | hb'
    · exact hR.ar a b ha hb' (e.trans (hg.ar b hb').2)
    · have := (hR.rp.ar_lt ha).2
      omega

/-- The provider moves the shared world (in the store; the code is handled by the caller). -/
theorem provider_step {P : Profile} (hR : Rel4 Op₀ Oc₀ ρp Op ρc Oc σ π κ) {F F' : Frame}
    {X X' : List Admin} {π' : Store H} (hf : Op.FrameGood F) (hc : Op.CodeGood X)
    (h : Step P noHost ⟨π, F, X⟩ ⟨π', F', X'⟩) :
    ∃ ρp' Op' σ', Step P noHost ⟨σ, ρp.frame F, ρp.code X⟩ ⟨σ', ρp'.frame F', ρp'.code X'⟩ ∧
      Rel4 Op₀ Oc₀ ρp' Op' ρc Oc σ' π' κ ∧ Op'.FrameGood F' ∧ Op'.CodeGood X' ∧
      Grow ρp Op ρp' Op' σ ∧ σ.structs.length ≤ σ'.structs.length ∧
      σ.arrays.length ≤ σ'.arrays.length := by
  obtain ⟨ρp', Op', σ', hst, hrp, hf', hc', hg, ht⟩ := step_sim h (ρ := ρp) (O := Op) (σ := σ)
    hR.rp hf hc
  refine ⟨ρp', Op', σ', hst, ⟨hrp, ?_, hg.fn.trans hR.fnp, hg.gl.trans hR.glp, hR.fnc, hR.glc,
    ?_, ?_, ?_⟩, hf', hc', hg, ht.structs_len, ht.arrays_len⟩
  · exact hR.rc.touch ht (fun a ha hb => hR.gl a hb ha) (fun a b ha hb e => hR.st b a hb ha e)
      (fun a b ha hb e => hR.ar b a hb ha e)
  · intro a ha; rw [hg.gl] at ha; exact hR.gl a ha
  · intro a b ha hb e
    rcases hg.stNew a ha with ha' | ha'
    · exact hR.st a b ha' hb ((hg.st a ha').2.symm.trans e)
    · have := (hR.rc.st_lt hb).2
      omega
  · intro a b ha hb e
    rcases hg.arNew a ha with ha' | ha'
    · exact hR.ar a b ha' hb ((hg.ar a ha').2.symm.trans e)
    · have := (hR.rc.ar_lt hb).2
      omega

end Rel4

/-- The empty frame of `$invoke` is owned by every part. -/
theorem Own.frameGood_empty (O : Own) : O.FrameGood ({} : Frame) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, fun _ h => by simp at h, fun _ h => by simp at h⟩,
    fun _ h => by simp at h⟩

@[simp] theorem Ren.frame_empty (ρ : Ren) : ρ.frame ({} : Frame) = {} := rfl

/-- A provider step from top-level code, replayed inside the consumer's callout context. -/
theorem provider_step_fill {P : Profile} {Op₀ Oc₀ : Own} {ρp ρc : Ren} {Op Oc : Own}
    {σ π κ : Store H} (hR : Rel4 Op₀ Oc₀ ρp Op ρc Oc σ π κ) {X X' : List Admin} {F' : Frame}
    {π' : Store H} (hc : Op.CodeGood X) (htop : TopOK X)
    (h : Step P noHost ⟨π, {}, X⟩ ⟨π', F', X'⟩) (E : Ctx) (G : Frame) :
    ∃ ρp' Op' σ', Step P noHost ⟨σ, G, E.fill (ρp.code X)⟩ ⟨σ', G, E.fill (ρp'.code X')⟩ ∧
      F' = {} ∧ TopOK X' ∧
      Rel4 Op₀ Oc₀ ρp' Op' ρc Oc σ' π' κ ∧ Op'.CodeGood X' ∧
      Grow ρp Op ρp' Op' σ ∧ σ.structs.length ≤ σ'.structs.length ∧
      σ.arrays.length ≤ σ'.arrays.length := by
  obtain ⟨hF, htop', -⟩ := step_reframe h htop
  simp only at hF htop'
  subst hF
  obtain ⟨ρp', Op', σ', hst, hR', -, hc', hg, hl1, hl2⟩ :=
    hR.provider_step (Op.frameGood_empty) hc h
  simp only [Ren.frame_empty] at hst
  obtain ⟨-, -, hre⟩ := step_reframe hst (ρp.topOK_code htop)
  refine ⟨ρp', Op', σ', ?_, rfl, htop', hR', hc', hg, hl1, hl2⟩
  exact E.step_fill hre G

end Silmaril.Proofs.Wasm.Game.Linking.Split
