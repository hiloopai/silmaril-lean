module

public import Silmaril.Wasm.Binaryen.DirectizeBackControl

@[expose] public section

/-! # Directize: backward activation heads -/

namespace Silmaril.Wasm.Binaryen.DirSim.Back

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {ok : SiteOk} {mi : ModuleInst} {P : Numerics.Profile} {s t : Store H} {f : Frame}
  {args : List Val} {c₀ : Config H}

/-- Backward matching for activations; inner steps use the activation's own module. -/
theorem head_frame {k : Nat} {F : Frame} {b b' : List Admin}
    (IH : SimIH ok mi P H (sizeOf (Admin.frame k F b'))) (hinv : DInv ok mi s)
    (hh : Det.Head P t f args (.frame k F b') c₀) (hb : GL ok mi F.module b b')
    (hSR : SR ok mi s t) : HRes ok mi P s f args (.frame k F b) c₀ := by
  cases hh with
  | ctxtFrame h =>
    rename_i t' F₁ b₁
    obtain ⟨c₁, hp, ⟨hfr, hrel⟩, hsr⟩ := IH ⟨t, F, b'⟩ ⟨t', F₁, b₁⟩ ⟨s, F, b⟩
      Exec.Drv.sizeOf_frame_body h ⟨rfl, hb⟩ hSR hinv
    exact ⟨⟨c₁.store, f, [.frame k c₁.frame c₁.code]⟩, tg_frame hp k f, hsr, rfl,
      .cons (by rw [hfr] at hrel ⊢; exact .frame hrel) (.nil _)⟩
  | frameVals hb' hn =>
    subst hb'
    rw [GL.values_back hb]
    exact ⟨_, tg_head (.frameVals rfl hn), hSR, rfl, GL.refl _⟩
  | returnFrame hb' hn =>
    rename_i vs' vs rest
    have he : b' = vals (vs' ++ vs) ++ .plain .return_ :: rest := by simpa using hb'
    rw [he] at hb
    obtain ⟨rest', hshape, _⟩ := GL.return_back hb
    have hs := tg_head (s := s) (f := f) (P := P)
      (Det.Head.returnFrame (n := k) (fi := F) (vs' := vs') (vs := vs) (rest := rest')
        (body := b) (by simp [hshape]) hn)
    exact ⟨⟨s, f, vals vs⟩,
      (by simpa using hs),
      hSR, rfl, GL.refl _⟩
  | returnCallRefFrameNull hb' hy =>
    rename_i vs y rest
    have he : b' = vals (vs ++ [.ref .null]) ++ y :: rest := by
      simpa [vals, Val.toAdmin] using hb'
    rw [he] at hb
    obtain ⟨yL, rest', hshape, hyL, _⟩ := GL.ret_prefix_back hy hb
    have hs := tg_head (s := s) (f := f) (P := P)
      (Det.Head.returnCallRefFrameNull (k := k) (fi := F) (vs := vs) (c := yL) (rest := rest')
        (body := b) (by simp [hshape, vals, Val.toAdmin]) hyL)
    exact ⟨⟨s, f, [.trap]⟩,
      (by simpa using hs),
      hSR, rfl, GL.refl _⟩
  | returnCallRefFrameAddr hb' hy hf he hn =>
    rename_i vs' vs a y rest fi ps rs
    have hshape : b' = vals (vs' ++ vs ++ [.ref (.func a)]) ++ y :: rest := by
      simpa [vals, Val.toAdmin] using hb'
    rw [hshape] at hb
    obtain ⟨yL, rest', hshape, hyL, _⟩ := GL.ret_prefix_back hy hb
    have htypes : SameTypes s.funcs t.funcs := hSR.sameTypes.symm
    obtain ⟨fiL, hfL, htL⟩ := htypes.get hf
    have hs := tg_head (s := s) (f := f) (P := P)
      (Det.Head.returnCallRefFrameAddr (k := k) (fi := F) (vs' := vs') (vs := vs)
        (rest := rest') (c := yL)
        (body := b)
        (by simp [hshape, vals, Val.toAdmin]) hyL hfL (htL.symm ▸ he) hn)
    exact ⟨⟨s, f, vals vs ++ [.ref (.func a), yL.retToCallIn F.module]⟩,
      (by simpa using hs),
      hSR, rfl, GL.append (GL.of_vals vs) (.cons (.ref _ _)
        (.cons (.ann (DirSim.isCallRef_retToCallIn hyL F.module)
          (DirSim.isCallRef_retToCallIn hy F.module)) (.nil _)))⟩
  | throwRefFrame =>
    rw [GL.abrupt_back (r := .throw _) (by intro _ h; cases h) hb]
    exact ⟨_, tg_head .throwRefFrame, hSR, rfl, GL.refl _⟩
  | trapFrame =>
    rw [GL.abrupt_back (r := .trap) (by intro _ h; cases h) hb]
    exact ⟨_, tg_head .trapFrame, hSR, rfl, GL.refl _⟩
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
