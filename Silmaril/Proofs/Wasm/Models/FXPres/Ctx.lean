module

public import Silmaril.Proofs.Wasm.Models.FXPres.Typing

/-!
# Typed contexts of suspension

`TL.plug_inv`: if `E.plug c` is typed, then `c` is typed (at some labels, return type and stack
types), and **every** code of that type, in every extension of the store and the slot typing,
fills `E` to code of the original type. The frames of `E` have module `m₀`. This is what makes
the context captured by `suspend` a typed continuation (`ContTy`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPres

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres

variable {H : Type} {E : TyEnv H} {s : Store H} {Γ : List TypeIdx}

/-- The context `Ec` fills code typed at `(Ls', R', i', o')` to code typed at `(Ls, R, i, o)`,
in every extension. -/
def CtxTy (E : TyEnv H) (s : Store H) (Γ : List TypeIdx) (Ec : CtxV) (Ls : List (List FTy))
    (R : Option (List FTy)) (i o : List FTy) (Ls' : List (List FTy)) (R' : Option (List FTy))
    (i' o' : List FTy) : Prop :=
  ∀ (s' : Store H) (Γ' : List TypeIdx) (c : List AdminFX), StoreLe E s s' → Γ <+: Γ' →
    TL E s' Γ' Ls' R' c i' o' → TL E s' Γ' Ls R (Ec.plug c) i o

/-- The frames of `Ec` have module `m₀`. -/
def CtxFrames (E : TyEnv H) (Ec : CtxV) : Prop :=
  ∀ f : Frame, f.module = E.m₀ → (Ec.frameAt f).module = E.m₀

theorem plug_inv_seq {vs : List FVal} {Ec : CtxV} {rest c : List AdminFX}
    {Ls : List (List FTy)} {R : Option (List FTy)} {i o : List FTy}
    (ih : ∀ {i o}, TL E s Γ Ls R (Ec.plug c) i o → ∃ Ls' R' i' o',
      TL E s Γ Ls' R' c i' o' ∧ CtxFrames E Ec ∧ CtxTy E s Γ Ec Ls R i o Ls' R' i' o')
    (h : TL E s Γ Ls R ((CtxV.seq vs Ec rest).plug c) i o) :
    ∃ Ls' R' i' o', TL E s Γ Ls' R' c i' o' ∧ CtxFrames E (.seq vs Ec rest) ∧
      CtxTy E s Γ (.seq vs Ec rest) Ls R i o Ls' R' i' o' := by
  obtain ⟨m₁, m₂, hv, hm, hr⟩ := TL.split3 h
  obtain ⟨Ls', R', i', o', hc, hfr, hctx⟩ := ih hm
  refine ⟨Ls', R', i', o', hc, fun f hf => hfr f hf, ?_⟩
  intro s' Γ' c' hs hΓ hc'
  exact TL.append3 (TL.mono hs hΓ hv) (hctx s' Γ' c' hs hΓ hc') (TL.mono hs hΓ hr)

theorem plug_inv_label {n : Nat} {k : List InstrFX} {Ec : CtxV} {c : List AdminFX}
    {Ls : List (List FTy)} {R : Option (List FTy)} {i o : List FTy}
    (ih : ∀ {Ls : List (List FTy)} {i o}, TL E s Γ Ls R (Ec.plug c) i o → ∃ Ls' R' i' o',
      TL E s Γ Ls' R' c i' o' ∧ CtxFrames E Ec ∧ CtxTy E s Γ Ec Ls R i o Ls' R' i' o')
    (h : TL E s Γ Ls R ((CtxV.label n k Ec).plug c) i o) :
    ∃ Ls' R' i' o', TL E s Γ Ls' R' c i' o' ∧ CtxFrames E (.label n k Ec) ∧
      CtxTy E s Γ (.label n k Ec) Ls R i o Ls' R' i' o' := by
  cases h with
  | label hn hk hb hr =>
    cases hr
    obtain ⟨Ls', R', i', o', hc, hfr, hctx⟩ := ih hb
    refine ⟨Ls', R', i', o', hc, fun f hf => hfr f hf, ?_⟩
    intro s' Γ' c' hs hΓ hc'
    exact .label hn (TL.mono hs hΓ hk) (hctx s' Γ' c' hs hΓ hc') .nil

theorem plug_inv_frame {n : Nat} {fi : Frame} {Ec : CtxV} {c : List AdminFX}
    {Ls : List (List FTy)} {R : Option (List FTy)} {i o : List FTy}
    (ih : ∀ {Ls : List (List FTy)} {R : Option (List FTy)} {i o}, TL E s Γ Ls R (Ec.plug c) i o →
      ∃ Ls' R' i' o', TL E s Γ Ls' R' c i' o' ∧ CtxFrames E Ec ∧
        CtxTy E s Γ Ec Ls R i o Ls' R' i' o')
    (h : TL E s Γ Ls R ((CtxV.frame n fi Ec).plug c) i o) :
    ∃ Ls' R' i' o', TL E s Γ Ls' R' c i' o' ∧ CtxFrames E (.frame n fi Ec) ∧
      CtxTy E s Γ (.frame n fi Ec) Ls R i o Ls' R' i' o' := by
  cases h with
  | frame hm hn hb hr =>
    cases hr
    obtain ⟨Ls', R', i', o', hc, hfr, hctx⟩ := ih hb
    refine ⟨Ls', R', i', o', hc, fun _ _ => hfr fi hm, ?_⟩
    intro s' Γ' c' hs hΓ hc'
    exact .frame hm hn (hctx s' Γ' c' hs hΓ hc') .nil

theorem plug_inv_handler {hs : List HClause} {Ec : CtxV} {c : List AdminFX}
    {Ls : List (List FTy)} {R : Option (List FTy)} {i o : List FTy}
    (ih : ∀ {Ls : List (List FTy)} {R : Option (List FTy)} {i o}, TL E s Γ Ls R (Ec.plug c) i o →
      ∃ Ls' R' i' o', TL E s Γ Ls' R' c i' o' ∧ CtxFrames E Ec ∧
        CtxTy E s Γ Ec Ls R i o Ls' R' i' o')
    (h : TL E s Γ Ls R ((CtxV.handler hs Ec).plug c) i o) :
    ∃ Ls' R' i' o', TL E s Γ Ls' R' c i' o' ∧ CtxFrames E (.handler hs Ec) ∧
      CtxTy E s Γ (.handler hs Ec) Ls R i o Ls' R' i' o' := by
  cases h with
  | handler hh hb hr =>
    cases hr
    obtain ⟨Ls', R', i', o', hc, hfr, hctx⟩ := ih hb
    refine ⟨Ls', R', i', o', hc, fun f hf => hfr f hf, ?_⟩
    intro s' Γ' c' hst hΓ hc'
    exact .handler (fun cl hcl => hClauseOk_mono hst (hh cl hcl)) (hctx s' Γ' c' hst hΓ hc') .nil

/-- **Typed contexts.** -/
theorem TL.plug_inv {Ec : CtxV} {c : List AdminFX} {Ls : List (List FTy)}
    {R : Option (List FTy)} {i o : List FTy} (h : TL E s Γ Ls R (Ec.plug c) i o) :
    ∃ Ls' R' i' o', TL E s Γ Ls' R' c i' o' ∧ CtxFrames E Ec ∧
      CtxTy E s Γ Ec Ls R i o Ls' R' i' o' := by
  induction Ec generalizing Ls R i o with
  | hole => exact ⟨Ls, R, i, o, h, fun _ hf => hf, fun _ _ _ _ _ hc => hc⟩
  | seq vs Ec rest ih => exact plug_inv_seq ih h
  | label n k Ec ih => exact plug_inv_label ih h
  | frame n fi Ec ih => exact plug_inv_frame ih h
  | handler hs Ec ih => exact plug_inv_handler ih h

end Silmaril.Proofs.Wasm.Models.FXPres
