module

public import Silmaril.Wasm.Binaryen.GlobReadBackSim

@[expose] public section

/-! # Immutable-global substitution: backward structured heads -/

namespace Silmaril.Wasm.Binaryen.GlobRead.Back

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {p : Prm} {P : Numerics.Profile} {s t : Store H} {f : Frame}
  {args : List Val} {c₀ : Config H}

theorem head_block {bt : BlockType} {b b' : List Instr} (hb : GIL p.lk p.mi f.module b b')
    (hh : Det.Head P t f args (.plain (.block bt b')) c₀) (hSR : SR p s t) :
    HRes p P s f args (.plain (.block bt b)) c₀ := by
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

theorem head_loop {bt : BlockType} {b b' : List Instr} (hb : GIL p.lk p.mi f.module b b')
    (hh : Det.Head P t f args (.plain (.loop bt b')) c₀) (hSR : SR p s t) :
    HRes p P s f args (.plain (.loop bt b)) c₀ := by
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

theorem head_if {bt : BlockType} {b₁ b₁' b₂ b₂' : List Instr} (h₁ : GIL p.lk p.mi f.module b₁ b₁')
    (h₂ : GIL p.lk p.mi f.module b₂ b₂') (hh : Det.Head P t f args (.plain (.if_ bt b₁' b₂')) c₀)
    (hSR : SR p s t) :
    HRes p P s f args (.plain (.if_ bt b₁ b₂)) c₀ := by
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
    (hb : GIL p.lk p.mi f.module b b')
    (hh : Det.Head P t f args (.plain (.tryTable bt cs b')) c₀) (hSR : SR p s t) :
    HRes p P s f args (.plain (.tryTable bt cs b)) c₀ := by
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
theorem head_plain (hok : PrmOk p) {i i' : Instr}
    (hi : GI p.lk p.mi f.module i i') (hh : Det.Head P t f args (.plain i') c₀)
    (hSR : SR p s t) : HRes p P s f args (.plain i) c₀ := by
  cases hi with
  | flat i =>
    by_cases hs : structuredInstr i = true
    · rcases structured_cases hs with ⟨bt, b, rfl⟩ | ⟨bt, b, rfl⟩ | ⟨bt, b₁, b₂, rfl⟩ |
        ⟨bt, cs, b, rfl⟩
      · exact head_block (GIL.refl b) hh hSR
      · exact head_loop (GIL.refl b) hh hSR
      · exact head_if (GIL.refl b₁) (GIL.refl b₂) hh hSR
      · exact head_tryTable (GIL.refl b) hh hSR
    · exact head_flat hok hh hSR (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h)
  | site => exact absurd hh.good.val_none (by simp [Admin.val?])
  | block h => exact head_block h hh hSR
  | loop h => exact head_loop h hh hSR
  | if_ h₁ h₂ => exact head_if h₁ h₂ hh hSR
  | tryTable h => exact head_tryTable h hh hSR

/-- Read preparation inside a label. -/
theorem prepare_label {c c' : Config H} (h : Steps P Det.noHost c c') (n : Nat)
    (cont : List Instr) :
    Steps P Det.noHost ⟨c.store, c.frame, [.label n cont c.code]⟩
      ⟨c'.store, c'.frame, [.label n cont c'.code]⟩ :=
  h.lift (fun c => (⟨c.store, c.frame, [.label n cont c.code]⟩ : Config H))
    (fun _ _ h => .ctxtLabel h)

/-- Read preparation inside a handler. -/
theorem prepare_handler {c c' : Config H} (h : Steps P Det.noHost c c') (n : Nat)
    (cs : List Catch) :
    Steps P Det.noHost ⟨c.store, c.frame, [.handler n cs c.code]⟩
      ⟨c'.store, c'.frame, [.handler n cs c'.code]⟩ :=
  h.lift (fun c => (⟨c.store, c.frame, [.handler n cs c.code]⟩ : Config H))
    (fun _ _ h => .ctxtHandler h)

/-- Read preparation inside an activation. -/
theorem prepare_frame {c c' : Config H} (h : Steps P Det.noHost c c') (n : Nat) (f : Frame) :
    Steps P Det.noHost ⟨c.store, f, [.frame n c.frame c.code]⟩
      ⟨c'.store, f, [.frame n c'.frame c'.code]⟩ :=
  h.lift (fun c => (⟨c.store, f, [.frame n c.frame c.code]⟩ : Config H))
    (fun _ _ h => .ctxtFrame h)

/-- The value prefix before a pending tail call can be prepared without touching the call. -/
theorem prepare_retCall {vs : List Val} {y : Admin} {os rest : List Admin}
    (hinv : GInv p.lk p.mi s) (h : GL p.lk p.mi f.module os (vals vs ++ y :: rest))
    (hy : y.IsReturnCallRef) :
    ∃ rest', Steps P Det.noHost ⟨s, f, os⟩ ⟨s, f, vals vs ++ y :: rest'⟩ ∧
      GL p.lk p.mi f.module rest' rest := by
  apply GL.prepare_flat hinv h
  · cases y with
    | plain i => cases i <;> simp_all [Admin.IsReturnCallRef, Admin.val?]
    | _ => simp_all [Admin.IsReturnCallRef, Admin.val?]
  · intro _ _ _ h; subst h; exact hy
  · intro _ _ _ h; subst h; exact hy
  · intro _ _ _ h; subst h; exact hy
  · exact retCall_rigid hy

end Silmaril.Wasm.Binaryen.GlobRead.Back
