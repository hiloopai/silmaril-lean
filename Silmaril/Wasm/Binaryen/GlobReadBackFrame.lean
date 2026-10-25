module

public import Silmaril.Wasm.Binaryen.GlobReadBackControl

@[expose] public section

/-! # Immutable-global substitution: backward activation heads -/

namespace Silmaril.Wasm.Binaryen.GlobRead.Back

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {p : Prm} {P : Numerics.Profile} {s t : Store H} {f : Frame}
  {args : List Val} {c₀ : Config H}

/-- Backward matching for activations; inner reads use the activation's own module. -/
theorem head_frame {k : Nat} {F : Frame} {b b' : List Admin}
    (IH : SimIH p P H (sizeOf (Admin.frame k F b'))) (hinv : GInv p.lk p.mi s)
    (hh : Det.Head P t f args (.frame k F b') c₀) (hb : GL p.lk p.mi F.module b b')
    (hSR : SR p s t) : HRes p P s f args (.frame k F b) c₀ := by
  cases hh with
  | ctxtFrame h =>
    rename_i t' F₁ b₁
    obtain ⟨c₁, hp, ⟨hfr, hrel⟩, hsr⟩ := IH ⟨t, F, b'⟩ ⟨t', F₁, b₁⟩ ⟨s, F, b⟩
      Exec.Drv.sizeOf_frame_body h ⟨rfl, hb⟩ hSR hinv
    exact ⟨⟨c₁.store, f, [.frame k c₁.frame c₁.code]⟩, tg_frame hp k f, hsr, rfl,
      .cons (by rw [hfr] at hrel ⊢; exact .frame hrel) (.nil _)⟩
  | frameVals hb' hn =>
    subst hb'
    have hp := GL.prepare_values (P := P) hinv hb
    exact ⟨_, Relation.TransGen.tail' (prepare_frame hp k f) (.frameVals hn),
      hSR, rfl, GL.refl _⟩
  | returnFrame hb' hn =>
    rename_i vs' vs rest
    have he : b' = vals (vs' ++ vs) ++ .plain .return_ :: rest := by simpa using hb'
    rw [he] at hb
    obtain ⟨rest', hp, _⟩ := GL.prepare_plain (P := P) hinv hb rfl
      ⟨rfl, fun _ h => by cases h⟩
    have hs := tg_head (s := s) (f := f) (P := P)
      (Det.Head.returnFrame (n := k) (fi := F) (vs' := vs') (vs := vs) (rest := rest')
        (body := vals (vs' ++ vs) ++ .plain .return_ :: rest') (by simp) hn)
    exact ⟨⟨s, f, vals vs⟩,
      Relation.TransGen.trans_right (prepare_frame hp k f) (by simpa using hs),
      hSR, rfl, GL.refl _⟩
  | returnCallRefFrameNull hb' hy =>
    rename_i vs y rest
    have he : b' = vals (vs ++ [.ref .null]) ++ y :: rest := by
      simpa [vals, Val.toAdmin] using hb'
    rw [he] at hb
    obtain ⟨rest', hp, _⟩ := prepare_retCall (P := P) hinv hb hy
    have hs := tg_head (s := s) (f := f) (P := P)
      (Det.Head.returnCallRefFrameNull (k := k) (fi := F) (vs := vs) (c := y) (rest := rest')
        (body := vals (vs ++ [.ref .null]) ++ y :: rest') (by simp [vals, Val.toAdmin]) hy)
    exact ⟨⟨s, f, [.trap]⟩,
      Relation.TransGen.trans_right (prepare_frame hp k f) (by simpa using hs),
      hSR, rfl, GL.refl _⟩
  | returnCallRefFrameAddr hb' hy hf he hn =>
    rename_i vs' vs a y rest fi ps rs
    have hshape : b' = vals (vs' ++ vs ++ [.ref (.func a)]) ++ y :: rest := by
      simpa [vals, Val.toAdmin] using hb'
    rw [hshape] at hb
    obtain ⟨rest', hp, _⟩ := prepare_retCall (P := P) hinv hb hy
    have htypes : SameTypes s.funcs t.funcs := by rw [hSR.ht]; exact hSR.sameTypes.symm
    obtain ⟨fiL, hfL, htL⟩ := htypes.get hf
    have hs := tg_head (s := s) (f := f) (P := P)
      (Det.Head.returnCallRefFrameAddr (k := k) (fi := F) (vs' := vs') (vs := vs)
        (rest := rest') (c := y)
        (body := vals (vs' ++ vs ++ [.ref (.func a)]) ++ y :: rest')
        (by simp [vals, Val.toAdmin]) hy hfL (htL.symm ▸ he) hn)
    exact ⟨⟨s, f, vals vs ++ [.ref (.func a), y.retToCallIn F.module]⟩,
      Relation.TransGen.trans_right (prepare_frame hp k f) (by simpa using hs),
      hSR, rfl, GL.refl _⟩
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


end Silmaril.Wasm.Binaryen.GlobRead.Back
