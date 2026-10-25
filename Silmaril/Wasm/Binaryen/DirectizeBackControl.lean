module

public import Silmaril.Wasm.Binaryen.DirectizeBackHead

@[expose] public section

/-! # Directize: backward control heads -/

namespace Silmaril.Wasm.Binaryen.DirSim.Back

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {ok : SiteOk} {mi : ModuleInst} {P : Numerics.Profile} {s t : Store H} {f : Frame}
  {args : List Val} {c₀ : Config H}

/-- Backward matching for labels, including branch and return value prefixes. -/
theorem head_label {n : Nat} {c c' : List Instr} {b b' : List Admin}
    (IH : SimIH ok mi P H (sizeOf (Admin.label n c' b'))) (hinv : DInv ok mi s)
    (hh : Det.Head P t f args (.label n c' b') c₀) (hc : GIL ok mi f.module c c')
    (hb : GL ok mi f.module b b') (hSR : SR ok mi s t) :
    HRes ok mi P s f args (.label n c b) c₀ := by
  cases hh with
  | ctxtLabel h =>
    rename_i t' f' b₁
    obtain ⟨c₁, hp, ⟨hfr, hrel⟩, hsr⟩ := IH ⟨t, f, b'⟩ ⟨t', f', b₁⟩ ⟨s, f, b⟩
      Exec.Drv.sizeOf_label_body h ⟨rfl, hb⟩ hSR hinv
    have hm : f'.module = f.module := GlobRead.step_frame_module h
    simp only at hrel
    rw [hfr, hm] at hrel
    exact ⟨⟨c₁.store, c₁.frame, [.label n c c₁.code]⟩, tg_label hp n c, hsr, hfr,
      .cons (.label hc hrel) (.nil _)⟩
  | labelVals hb' =>
    subst hb'
    rw [GL.values_back hb]
    exact ⟨_, tg_head (.labelVals rfl), hSR, rfl, GL.refl _⟩
  | brLabelZero hb' hl hn =>
    rename_i vs' vs l rest
    have he : b' = vals (vs' ++ vs) ++ .plain (.br l) :: rest := by simpa using hb'
    rw [he] at hb
    obtain ⟨rest', hshape, _⟩ := GL.br_back hb
    have hs := tg_head (s := s) (f := f) (P := P)
      (Det.Head.brLabelZero (n := n) (cont := c) (vs' := vs') (vs := vs) (rest := rest')
        (body := b) (by simp [hshape]) hl hn)
    exact ⟨⟨s, f, vals vs ++ expression c⟩,
      (by simpa using hs),
      hSR, rfl, GL.append (GL.of_vals _) (GL.of_GIL hc)⟩
  | brLabelSucc hb' hl =>
    rename_i vs l rest
    have he : b' = vals vs ++ .plain (.br l) :: rest := by simpa using hb'
    rw [he] at hb
    obtain ⟨rest', hshape, _⟩ := GL.br_back hb
    have hs := tg_head (s := s) (f := f) (P := P)
      (Det.Head.brLabelSucc (n := n) (cont := c) (vs := vs) (rest := rest') (body := b) (by simp [hshape]) hl)
    exact ⟨⟨s, f, vals vs ++ [.plain (.br (labelPred l))]⟩,
      (by simpa using hs),
      hSR, rfl, GL.refl _⟩
  | returnCallRefLabel hb' hy =>
    rename_i vs y rest
    have he : b' = vals vs ++ y :: rest := by simpa using hb'
    rw [he] at hb
    obtain ⟨yL, rest', hshape, hyL, _⟩ := GL.ret_prefix_back hy hb
    have hs := tg_head (s := s) (f := f) (P := P)
      (Det.Head.returnCallRefLabel (k := n) (cont := c) (vs := vs) (c := yL) (rest := rest') (body := b) (by simp [hshape]) hyL)
    exact ⟨⟨s, f, vals vs ++ [yL]⟩,
      (by simpa using hs),
      hSR, rfl, GL.append (GL.of_vals vs) (.cons (.retAnn hyL hy) (.nil _))⟩
  | returnLabel hb' =>
    rename_i vs rest
    have he : b' = vals vs ++ .plain .return_ :: rest := by simpa using hb'
    rw [he] at hb
    obtain ⟨rest', hshape, _⟩ := GL.return_back hb
    have hs := tg_head (s := s) (f := f) (P := P)
      (Det.Head.returnLabel (n := n) (cont := c) (vs := vs) (rest := rest') (body := b) (by simp [hshape]))
    exact ⟨⟨s, f, vals vs ++ [.plain .return_]⟩,
      (by simpa using hs),
      hSR, rfl, GL.refl _⟩
  | throwRefLabel =>
    rw [GL.abrupt_back (r := .throw _) (by intro _ h; cases h) hb]
    exact ⟨_, tg_head .throwRefLabel, hSR, rfl, GL.refl _⟩
  | trapLabel =>
    rw [GL.abrupt_back (r := .trap) (by intro _ h; cases h) hb]
    exact ⟨_, tg_head .trapLabel, hSR, rfl, GL.refl _⟩
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



/-- Backward matching for exception handlers. -/
theorem head_handler {n : Nat} {cs : List Catch} {b b' : List Admin}
    (IH : SimIH ok mi P H (sizeOf (Admin.handler n cs b'))) (hinv : DInv ok mi s)
    (hh : Det.Head P t f args (.handler n cs b') c₀) (hb : GL ok mi f.module b b')
    (hSR : SR ok mi s t) : HRes ok mi P s f args (.handler n cs b) c₀ := by
  cases hh with
  | ctxtHandler h =>
    rename_i t' f' b₁
    obtain ⟨c₁, hp, ⟨hfr, hrel⟩, hsr⟩ := IH ⟨t, f, b'⟩ ⟨t', f', b₁⟩ ⟨s, f, b⟩
      Exec.Drv.sizeOf_handler_body h ⟨rfl, hb⟩ hSR hinv
    have hm : f'.module = f.module := GlobRead.step_frame_module h
    simp only at hrel
    rw [hfr, hm] at hrel
    exact ⟨⟨c₁.store, c₁.frame, [.handler n cs c₁.code]⟩, tg_handler hp n cs, hsr, hfr,
      .cons (.handler hrel) (.nil _)⟩
  | brHandler hb' =>
    rename_i vs l rest
    have he : b' = vals vs ++ .plain (.br l) :: rest := by simpa using hb'
    rw [he] at hb
    obtain ⟨rest', hshape, _⟩ := GL.br_back hb
    have hs := tg_head (s := s) (f := f) (P := P)
      (Det.Head.brHandler (n := n) (cs := cs) (l := l) (vs := vs) (rest := rest')
        (body := b) (by simp [hshape]))
    exact ⟨⟨s, f, vals vs ++ [.plain (.br l)]⟩,
      (by simpa using hs),
      hSR, rfl, GL.refl _⟩
  | returnCallRefHandler hb' hy =>
    rename_i vs y rest
    have he : b' = vals vs ++ y :: rest := by simpa using hb'
    rw [he] at hb
    obtain ⟨yL, rest', hshape, hyL, _⟩ := GL.ret_prefix_back hy hb
    have hs := tg_head (s := s) (f := f) (P := P)
      (Det.Head.returnCallRefHandler (k := n) (cs := cs) (vs := vs) (c := yL) (rest := rest')
        (body := b) (by simp [hshape]) hyL)
    exact ⟨⟨s, f, vals vs ++ [yL]⟩,
      (by simpa using hs),
      hSR, rfl, GL.append (GL.of_vals vs) (.cons (.retAnn hyL hy) (.nil _))⟩
  | returnHandler hb' =>
    rename_i vs rest
    have he : b' = vals vs ++ .plain .return_ :: rest := by simpa using hb'
    rw [he] at hb
    obtain ⟨rest', hshape, _⟩ := GL.return_back hb
    have hs := tg_head (s := s) (f := f) (P := P)
      (Det.Head.returnHandler (n := n) (cs := cs) (vs := vs) (rest := rest')
        (body := b) (by simp [hshape]))
    exact ⟨⟨s, f, vals vs ++ [.plain .return_]⟩,
      (by simpa using hs),
      hSR, rfl, GL.refl _⟩
  | throwRefHandlerEmpty =>
    rw [GL.abrupt_back (r := .throw _) (by intro _ h; cases h) hb]
    exact ⟨_, tg_head .throwRefHandlerEmpty, hSR, rfl, GL.refl _⟩
  | throwRefHandlerCatch he ht =>
    obtain ⟨G, hG, rfl⟩ := hSR.cases
    rw [GL.abrupt_back (r := .throw _) (by intro _ h; cases h) hb]
    exact ⟨_, tg_head (.throwRefHandlerCatch he ht), SR.mk' hG, rfl, GL.refl _⟩
  | throwRefHandlerCatchRef he ht =>
    obtain ⟨G, hG, rfl⟩ := hSR.cases
    rw [GL.abrupt_back (r := .throw _) (by intro _ h; cases h) hb]
    exact ⟨_, tg_head (.throwRefHandlerCatchRef he ht), SR.mk' hG, rfl, GL.refl _⟩
  | throwRefHandlerCatchAll =>
    rw [GL.abrupt_back (r := .throw _) (by intro _ h; cases h) hb]
    exact ⟨_, tg_head .throwRefHandlerCatchAll, hSR, rfl, GL.refl _⟩
  | throwRefHandlerCatchAllRef =>
    rw [GL.abrupt_back (r := .throw _) (by intro _ h; cases h) hb]
    exact ⟨_, tg_head .throwRefHandlerCatchAllRef, hSR, rfl, GL.refl _⟩
  | throwRefHandlerNext h =>
    obtain ⟨G, hG, rfl⟩ := hSR.cases
    rw [GL.abrupt_back (r := .throw _) (by intro _ h; cases h) hb]
    exact ⟨_, tg_head (.throwRefHandlerNext h), SR.mk' hG, rfl, GL.refl _⟩
  | handlerVals hb' =>
    subst hb'
    rw [GL.values_back hb]
    exact ⟨_, tg_head (.handlerVals rfl), hSR, rfl, GL.refl _⟩
  | trapHandler =>
    rw [GL.abrupt_back (r := .trap) (by intro _ h; cases h) hb]
    exact ⟨_, tg_head .trapHandler, hSR, rfl, GL.refl _⟩
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


end Silmaril.Wasm.Binaryen.DirSim.Back
