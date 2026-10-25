module

public import Silmaril.Wasm.Binaryen.DirectizeBackSim

@[expose] public section

/-! # Directize: backward structured heads -/

namespace Silmaril.Wasm.Binaryen.DirSim.Back

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {ok : SiteOk} {mi : ModuleInst} {P : Numerics.Profile} {s t : Store H} {f : Frame}
  {args : List Val} {c₀ : Config H}

theorem head_block {bt : BlockType} {b b' : List Instr} (hb : GIL ok mi f.module b b')
    (hh : Det.Head P t f args (.plain (.block bt b')) c₀) (hSR : SR ok mi s t) :
    HRes ok mi P s f args (.plain (.block bt b)) c₀ := by
  cases hh with
  | block hbt hm =>
    exact ⟨_, tg_head (.block hbt hm), hSR, rfl,
      .cons (.label .nil (GL.append (GL.of_vals _) (GL.of_GIL hb))) (.nil _)⟩
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss

theorem head_loop {bt : BlockType} {b b' : List Instr} (hb : GIL ok mi f.module b b')
    (hh : Det.Head P t f args (.plain (.loop bt b')) c₀) (hSR : SR ok mi s t) :
    HRes ok mi P s f args (.plain (.loop bt b)) c₀ := by
  cases hh with
  | loop hbt hm =>
    exact ⟨_, tg_head (.loop hbt hm), hSR, rfl,
      .cons (.label (.cons (.loop hb) .nil) (GL.append (GL.of_vals _) (GL.of_GIL hb))) (.nil _)⟩
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss

theorem head_if {bt : BlockType} {b₁ b₁' b₂ b₂' : List Instr} (h₁ : GIL ok mi f.module b₁ b₁')
    (h₂ : GIL ok mi f.module b₂ b₂') (hh : Det.Head P t f args (.plain (.if_ bt b₁' b₂')) c₀)
    (hSR : SR ok mi s t) :
    HRes ok mi P s f args (.plain (.if_ bt b₁ b₂)) c₀ := by
  cases hh with
  | ifTrue hc =>
    exact ⟨_, tg_head (.ifTrue hc), hSR, rfl, .cons (.plain (.block h₁)) (.nil _)⟩
  | ifFalse hc =>
    exact ⟨_, tg_head (.ifFalse hc), hSR, rfl, .cons (.plain (.block h₂)) (.nil _)⟩
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss

theorem head_tryTable {bt : BlockType} {cs : List Catch} {b b' : List Instr}
    (hb : GIL ok mi f.module b b')
    (hh : Det.Head P t f args (.plain (.tryTable bt cs b')) c₀) (hSR : SR ok mi s t) :
    HRes ok mi P s f args (.plain (.tryTable bt cs b)) c₀ := by
  cases hh with
  | tryTable hbt hm =>
    exact ⟨_, tg_head (.tryTable hbt hm), hSR, rfl,
      .cons (.handler (.cons (.label .nil (GL.append (GL.of_vals _) (GL.of_GIL hb))) (.nil _)))
        (.nil _)⟩
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss



/-- Non-structured heads are identical; structured heads preserve the body relation. -/
theorem head_plain {i i' : Instr}
    (hi : GI ok mi f.module i i') (hh : Det.Head P t f args (.plain i') c₀)
    (hSR : SR ok mi s t) : HRes ok mi P s f args (.plain i) c₀ := by
  cases hi with
  | flat i =>
    by_cases hs : structuredInstr i = true
    · rcases structured_cases hs with ⟨bt, b, rfl⟩ | ⟨bt, b, rfl⟩ | ⟨bt, b₁, b₂, rfl⟩ |
        ⟨bt, cs, b, rfl⟩
      · exact head_block (GIL.refl b) hh hSR
      · exact head_loop (GIL.refl b) hh hSR
      · exact head_if (GIL.refl b₁) (GIL.refl b₂) hh hSR
      · exact head_tryTable (GIL.refl b) hh hSR
    · exact head_flat hh hSR (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h)
  | block h => exact head_block h hh hSR
  | loop h => exact head_loop h hh hSR
  | if_ h₁ h₂ => exact head_if h₁ h₂ hh hSR
  | tryTable h => exact head_tryTable h hh hSR


end Silmaril.Wasm.Binaryen.DirSim.Back
