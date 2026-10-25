module

public import Silmaril.Wasm.Binaryen.GlobReadBackHead

@[expose] public section

/-! # Immutable-global substitution: backward control heads -/

namespace Silmaril.Wasm.Binaryen.GlobRead.Back

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {p : Prm} {P : Numerics.Profile} {s t : Store H} {f : Frame}
  {args : List Val} {c₀ : Config H}

/-- Backward matching for labels, including reads in branch/return value prefixes. -/
theorem head_label {n : Nat} {c c' : List Instr} {b b' : List Admin}
    (IH : SimIH p P H (sizeOf (Admin.label n c' b'))) (hinv : GInv p.lk p.mi s)
    (hh : Det.Head P t f args (.label n c' b') c₀) (hc : GIL p.lk p.mi f.module c c')
    (hb : GL p.lk p.mi f.module b b') (hSR : SR p s t) :
    HRes p P s f args (.label n c b) c₀ := by
  cases hh with
  | ctxtLabel h =>
    rename_i t' f' b₁
    obtain ⟨c₁, hp, ⟨hfr, hrel⟩, hsr⟩ := IH ⟨t, f, b'⟩ ⟨t', f', b₁⟩ ⟨s, f, b⟩
      Exec.Drv.sizeOf_label_body h ⟨rfl, hb⟩ hSR hinv
    have hm : f'.module = f.module := step_frame_module h
    simp only at hrel
    rw [hfr, hm] at hrel
    exact ⟨⟨c₁.store, c₁.frame, [.label n c c₁.code]⟩, tg_label hp n c, hsr, hfr,
      .cons (.label hc hrel) (.nil _)⟩
  | labelVals hb' =>
    subst hb'
    have hp := GL.prepare_values (P := P) hinv hb
    exact ⟨_, Relation.TransGen.tail' (prepare_label hp n c) .labelVals, hSR, rfl, GL.refl _⟩
  | brLabelZero hb' hl hn =>
    rename_i vs' vs l rest
    have he : b' = vals (vs' ++ vs) ++ .plain (.br l) :: rest := by simpa using hb'
    rw [he] at hb
    obtain ⟨rest', hp, _⟩ := GL.prepare_plain (P := P) hinv hb rfl
      ⟨rfl, fun _ h => by cases h⟩
    have hs := tg_head (s := s) (f := f) (P := P)
      (Det.Head.brLabelZero (n := n) (cont := c) (vs' := vs') (vs := vs) (rest := rest')
        (body := vals (vs' ++ vs) ++ .plain (.br l) :: rest') (by simp) hl hn)
    exact ⟨⟨s, f, vals vs ++ expression c⟩,
      Relation.TransGen.trans_right (prepare_label hp n c) (by simpa using hs),
      hSR, rfl, GL.append (GL.of_vals _) (GL.of_GIL hc)⟩
  | brLabelSucc hb' hl =>
    rename_i vs l rest
    have he : b' = vals vs ++ .plain (.br l) :: rest := by simpa using hb'
    rw [he] at hb
    obtain ⟨rest', hp, _⟩ := GL.prepare_plain (P := P) hinv hb rfl
      ⟨rfl, fun _ h => by cases h⟩
    have hs := tg_head (s := s) (f := f) (P := P)
      (Det.Head.brLabelSucc (n := n) (cont := c) (vs := vs) (rest := rest') (body := vals vs ++ .plain (.br l) :: rest') (by simp) hl)
    exact ⟨⟨s, f, vals vs ++ [.plain (.br (labelPred l))]⟩,
      Relation.TransGen.trans_right (prepare_label hp n c) (by simpa using hs),
      hSR, rfl, GL.refl _⟩
  | returnCallRefLabel hb' hy =>
    rename_i vs y rest
    have he : b' = vals vs ++ y :: rest := by simpa using hb'
    rw [he] at hb
    obtain ⟨rest', hp, _⟩ := prepare_retCall (P := P) hinv hb hy
    have hs := tg_head (s := s) (f := f) (P := P)
      (Det.Head.returnCallRefLabel (k := n) (cont := c) (vs := vs) (c := y) (rest := rest') (body := vals vs ++ y :: rest') (by simp) hy)
    exact ⟨⟨s, f, vals vs ++ [y]⟩,
      Relation.TransGen.trans_right (prepare_label hp n c) (by simpa using hs),
      hSR, rfl, GL.refl _⟩
  | returnLabel hb' =>
    rename_i vs rest
    have he : b' = vals vs ++ .plain .return_ :: rest := by simpa using hb'
    rw [he] at hb
    obtain ⟨rest', hp, _⟩ := GL.prepare_plain (P := P) hinv hb rfl
      ⟨rfl, fun _ h => by cases h⟩
    have hs := tg_head (s := s) (f := f) (P := P)
      (Det.Head.returnLabel (n := n) (cont := c) (vs := vs) (rest := rest') (body := vals vs ++ .plain .return_ :: rest') (by simp))
    exact ⟨⟨s, f, vals vs ++ [.plain .return_]⟩,
      Relation.TransGen.trans_right (prepare_label hp n c) (by simpa using hs),
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
    (IH : SimIH p P H (sizeOf (Admin.handler n cs b'))) (hinv : GInv p.lk p.mi s)
    (hh : Det.Head P t f args (.handler n cs b') c₀) (hb : GL p.lk p.mi f.module b b')
    (hSR : SR p s t) : HRes p P s f args (.handler n cs b) c₀ := by
  cases hh with
  | ctxtHandler h =>
    rename_i t' f' b₁
    obtain ⟨c₁, hp, ⟨hfr, hrel⟩, hsr⟩ := IH ⟨t, f, b'⟩ ⟨t', f', b₁⟩ ⟨s, f, b⟩
      Exec.Drv.sizeOf_handler_body h ⟨rfl, hb⟩ hSR hinv
    have hm : f'.module = f.module := step_frame_module h
    simp only at hrel
    rw [hfr, hm] at hrel
    exact ⟨⟨c₁.store, c₁.frame, [.handler n cs c₁.code]⟩, tg_handler hp n cs, hsr, hfr,
      .cons (.handler hrel) (.nil _)⟩
  | brHandler hb' =>
    rename_i vs l rest
    have he : b' = vals vs ++ .plain (.br l) :: rest := by simpa using hb'
    rw [he] at hb
    obtain ⟨rest', hp, _⟩ := GL.prepare_plain (P := P) hinv hb rfl
      ⟨rfl, fun _ h => by cases h⟩
    have hs := tg_head (s := s) (f := f) (P := P)
      (Det.Head.brHandler (n := n) (cs := cs) (l := l) (vs := vs) (rest := rest')
        (body := vals vs ++ .plain (.br l) :: rest') (by simp))
    exact ⟨⟨s, f, vals vs ++ [.plain (.br l)]⟩,
      Relation.TransGen.trans_right (prepare_handler hp n cs) (by simpa using hs),
      hSR, rfl, GL.refl _⟩
  | returnCallRefHandler hb' hy =>
    rename_i vs y rest
    have he : b' = vals vs ++ y :: rest := by simpa using hb'
    rw [he] at hb
    obtain ⟨rest', hp, _⟩ := prepare_retCall (P := P) hinv hb hy
    have hs := tg_head (s := s) (f := f) (P := P)
      (Det.Head.returnCallRefHandler (k := n) (cs := cs) (vs := vs) (c := y) (rest := rest')
        (body := vals vs ++ y :: rest') (by simp) hy)
    exact ⟨⟨s, f, vals vs ++ [y]⟩,
      Relation.TransGen.trans_right (prepare_handler hp n cs) (by simpa using hs),
      hSR, rfl, GL.refl _⟩
  | returnHandler hb' =>
    rename_i vs rest
    have he : b' = vals vs ++ .plain .return_ :: rest := by simpa using hb'
    rw [he] at hb
    obtain ⟨rest', hp, _⟩ := GL.prepare_plain (P := P) hinv hb rfl
      ⟨rfl, fun _ h => by cases h⟩
    have hs := tg_head (s := s) (f := f) (P := P)
      (Det.Head.returnHandler (n := n) (cs := cs) (vs := vs) (rest := rest')
        (body := vals vs ++ .plain .return_ :: rest') (by simp))
    exact ⟨⟨s, f, vals vs ++ [.plain .return_]⟩,
      Relation.TransGen.trans_right (prepare_handler hp n cs) (by simpa using hs),
      hSR, rfl, GL.refl _⟩
  | throwRefHandlerEmpty =>
    rw [GL.abrupt_back (r := .throw _) (by intro _ h; cases h) hb]
    exact ⟨_, tg_head .throwRefHandlerEmpty, hSR, rfl, GL.refl _⟩
  | throwRefHandlerCatch he ht =>
    obtain ⟨hg, rfl⟩ := hSR
    rw [GL.abrupt_back (r := .throw _) (by intro _ h; cases h) hb]
    exact ⟨_, tg_head (.throwRefHandlerCatch he ht), ⟨hg, rfl⟩, rfl, GL.refl _⟩
  | throwRefHandlerCatchRef he ht =>
    obtain ⟨hg, rfl⟩ := hSR
    rw [GL.abrupt_back (r := .throw _) (by intro _ h; cases h) hb]
    exact ⟨_, tg_head (.throwRefHandlerCatchRef he ht), ⟨hg, rfl⟩, rfl, GL.refl _⟩
  | throwRefHandlerCatchAll =>
    rw [GL.abrupt_back (r := .throw _) (by intro _ h; cases h) hb]
    exact ⟨_, tg_head .throwRefHandlerCatchAll, hSR, rfl, GL.refl _⟩
  | throwRefHandlerCatchAllRef =>
    rw [GL.abrupt_back (r := .throw _) (by intro _ h; cases h) hb]
    exact ⟨_, tg_head .throwRefHandlerCatchAllRef, hSR, rfl, GL.refl _⟩
  | throwRefHandlerNext h =>
    obtain ⟨hg, rfl⟩ := hSR
    rw [GL.abrupt_back (r := .throw _) (by intro _ h; cases h) hb]
    exact ⟨_, tg_head (.throwRefHandlerNext h), ⟨hg, rfl⟩, rfl, GL.refl _⟩
  | handlerVals hb' =>
    subst hb'
    have hp := GL.prepare_values (P := P) hinv hb
    exact ⟨_, Relation.TransGen.tail' (prepare_handler hp n cs) .handlerVals, hSR, rfl, GL.refl _⟩
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


end Silmaril.Wasm.Binaryen.GlobRead.Back
