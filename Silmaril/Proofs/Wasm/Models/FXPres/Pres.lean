module

public import Silmaril.Proofs.Wasm.Models.FXPres.Suspend

/-!
# Preservation for `StepFXS`

**`preservation`**: under `CoreHyp`, a `StepFXS` step from a configuration whose frame has
module `m₀`, whose continuation store fits `Γ`, and whose code has type `i → o` (labels `Ls`,
return type `R`), reaches a configuration of the same kind, for a longer slot typing `Γ'` and
an extended store. The proof is by induction over the 41 rules of `StepFXS`; the contexts
(`seq`, labels, frames, handler frames) use the induction hypothesis, the Core rule uses
`CoreHyp.core`, and every other rule is one of the redex lemmas.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPres

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXResume
open Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {E : TyEnv H} {P : Profile} {host : HostSemantics H}
  {fx : H → Option FuncFX} {s s' : Store H} {Γ : List TypeIdx} {K K' : List (Option ContFX)}
  {f f' : Frame} {Ls : List (List FTy)} {R : Option (List FTy)} {i o : List FTy}

/-- The induction hypothesis at fixed `Γ`. -/
abbrev PresIH (E : TyEnv H) (s : Store H) (Γ : List TypeIdx) (es : List AdminFX)
    (s' : Store H) (K' : List (Option ContFX)) (f' : Frame) (es' : List AdminFX) : Prop :=
  ∀ {Ls : List (List FTy)} {R : Option (List FTy)} {i o : List FTy},
    TL E s Γ Ls R es i o → PresC E s Γ Ls R i o s' K' f' es'

theorem pres_seq (hyp : CoreHyp E P host fx) {vs : List FVal} {es es' rest : List AdminFX}
    (ih : PresIH E s Γ es s' K' f' es') (h : TL E s Γ Ls R (fvals vs ++ es ++ rest) i o) :
    PresC E s Γ Ls R i o s' K' f' (fvals vs ++ es' ++ rest) := by
  obtain ⟨m₁, m₂, hv, he, hr⟩ := TL.split3 h
  obtain ⟨Γ', hΓ, hext, hf', hK', he'⟩ := ih he
  have hle := CoreHyp.le hyp hext
  exact ⟨Γ', hΓ, hext, hf', hK', TL.append3 (TL.mono hle hΓ hv) he' (TL.mono hle hΓ hr)⟩

theorem pres_ctxLabel (hyp : CoreHyp E P host fx) {n : Nat} {k : List InstrFX}
    {es es' : List AdminFX} (ih : PresIH E s Γ es s' K' f' es')
    (h : TL E s Γ Ls R [.label n k es] i o) :
    PresC E s Γ Ls R i o s' K' f' [.label n k es'] := by
  cases h with
  | label hn hk hb hr =>
    cases hr
    obtain ⟨Γ', hΓ, hext, hf', hK', hb'⟩ := ih hb
    exact ⟨Γ', hΓ, hext, hf', hK', .label hn (TL.mono (CoreHyp.le hyp hext) hΓ hk) hb' .nil⟩

theorem pres_ctxFrame (hf : f.module = E.m₀) {n : Nat}
    {fi fi' : Frame} {es es' : List AdminFX}
    (ih : fi.module = E.m₀ → PresIH E s Γ es s' K' fi' es')
    (h : TL E s Γ Ls R [.frame n fi es] i o) :
    PresC E s Γ Ls R i o s' K' f [.frame n fi' es'] := by
  cases h with
  | frame hm hn hb hr =>
    cases hr
    obtain ⟨Γ', hΓ, hext, hf', hK', hb'⟩ := ih hm hb
    exact ⟨Γ', hΓ, hext, hf, hK', .frame hf' hn hb' .nil⟩

theorem pres_ctxHandler (hyp : CoreHyp E P host fx) {hs : List HClause}
    {es es' : List AdminFX} (ih : PresIH E s Γ es s' K' f' es')
    (h : TL E s Γ Ls R [.handler hs es] i o) :
    PresC E s Γ Ls R i o s' K' f' [.handler hs es'] := by
  cases h with
  | handler hh hb hr =>
    cases hr
    obtain ⟨Γ', hΓ, hext, hf', hK', hb'⟩ := ih hb
    exact ⟨Γ', hΓ, hext, hf', hK',
      .handler (fun c hc => hClauseOk_mono (CoreHyp.le hyp hext) (hh c hc)) hb' .nil⟩

theorem pres_core (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {cs cs' : List Admin} (hs : Step P (blockFX host fx) ⟨s, f, cs⟩ ⟨s', f', cs'⟩)
    (h : TL E s Γ Ls R (cs.map .core) i o) :
    PresC E s Γ Ls R i o s' K f' (cs'.map .core) := by
  obtain ⟨hext, hf', h'⟩ := hyp.core hs hf h
  exact ⟨Γ, List.prefix_refl _, hext, hf', KOk.mono hyp hK hext, h'⟩

/-- **Preservation for `StepFXS`.** -/
theorem preservation (hyp : CoreHyp E P host fx) {c c' : ConfigFX H}
    (h : StepFXS P host fx c c') :
    ∀ {Γ : List TypeIdx} {Ls : List (List FTy)} {R : Option (List FTy)} {i o : List FTy},
      c.frame.module = E.m₀ → KOk E c.store Γ c.conts → TL E c.store Γ Ls R c.code i o →
      PresC E c.store Γ Ls R i o c'.store c'.conts c'.frame c'.code := by
  induction h with
  | core hs => exact fun hf hK ht => pres_core hyp hf hK hs ht
  | seq _ _ ih => exact fun hf hK ht => pres_seq hyp (ih hf hK) ht
  | ctxLabel _ ih => exact fun hf hK ht => pres_ctxLabel hyp (ih hf hK) ht
  | ctxFrame _ ih => exact fun hf hK ht => pres_ctxFrame hf (fun hm => ih hm hK) ht
  | ctxHandler _ ih => exact fun hf hK ht => pres_ctxHandler hyp (ih hf hK) ht
  | block hbt hm => exact fun hf hK ht => pres_block hyp hf hK hbt hm ht
  | loop hbt hm => exact fun hf hK ht => pres_loop hyp hf hK hbt hm ht
  | ifTrue => exact fun hf hK ht => pres_if hyp hf hK (Or.inl rfl) ht
  | ifFalse => exact fun hf hK ht => pres_if hyp hf hK (Or.inr rfl) ht
  | labelVals => exact fun hf hK ht => pres_labelVals hyp hf hK ht
  | brLabelZero hl hn => exact fun hf hK ht => pres_brLabelZero hyp hf hK hl hn ht
  | brLabelSucc hl => exact fun hf hK ht => pres_brLabelSucc hyp hf hK hl ht
  | brHandler => exact fun _ _ ht => pres_brHandler ht
  | returnLabel => exact fun hf hK ht => pres_returnLabel hyp hf hK ht
  | returnHandler => exact fun _ _ ht => pres_returnHandler ht
  | frameVals => exact fun hf hK ht => pres_frameVals hyp hf hK ht
  | returnFrame hn => exact fun hf hK ht => pres_returnFrame hyp hf hK hn ht
  | handlerVals => exact fun hf hK ht => pres_handlerVals hyp hf hK ht
  | dropCont => exact fun hf hK ht => pres_dropCont hyp hf hK ht
  | trapSeq => exact fun hf hK _ => presC_trap hyp hf hK
  | trapLabel => exact fun hf hK _ => presC_trap hyp hf hK
  | trapFrame => exact fun hf hK _ => presC_trap hyp hf hK
  | trapHandler => exact fun hf hK _ => presC_trap hyp hf hK
  | throwSeq => exact fun hf hK ht => pres_throwSeq hyp hf hK ht
  | throwLabel => exact fun hf hK ht => pres_throwLabel hyp hf hK ht
  | throwFrame => exact fun hf hK ht => pres_throwFrame hyp hf hK ht
  | throwHandler => exact fun hf hK ht => pres_throwHandler hyp hf hK ht
  | invoke hc hfa hcode hfx hn => exact fun hf hK ht => pres_invoke hyp hf hK hc hfa hcode hfx hn ht
  | contNew hfa => exact fun hf hK ht => pres_contNew hyp hf hK hfa ht
  | contNewNull => exact fun hf hK _ => presC_trap hyp hf hK
  | contBind hk ha => exact fun hf hK ht => pres_contBind hyp hf hK hk ha ht
  | contBindNull => exact fun hf hK _ => presC_trap hyp hf hK
  | contBindUsed => exact fun hf hK _ => presC_trap hyp hf hK
  | resume hk hr ha => exact fun hf hK ht => pres_resume hyp hf hK hk hr ha ht
  | resumeNull => exact fun hf hK _ => presC_trap hyp hf hK
  | resumeUsed => exact fun hf hK _ => presC_trap hyp hf hK
  | resumeThrow hk ht hr ha => exact fun hf hK hT => pres_resumeThrow hyp hf hK hk ht hr ha hT
  | resumeThrowNull => exact fun hf hK _ => presC_trap hyp hf hK
  | suspend ht _ hc ha => exact fun hf hK hT => pres_suspend hyp hf hK ht hc ha hT
  | switch => exact fun _ _ ht => pres_switch ht

/-- **Typed configurations stay typed** under one `StepFXS` step. -/
theorem preservation_config (hyp : CoreHyp E P host fx) {c c' : ConfigFX H} {ts : List FTy}
    (h : StepFXS P host fx c c') (hc : ConfigOk E Γ c ts) :
    ∃ Γ', Γ <+: Γ' ∧ E.ext c.store c'.store ∧ ConfigOk E Γ' c' ts := by
  obtain ⟨hf, hK, ht⟩ := hc
  obtain ⟨Γ', hΓ, hext, hf', hK', ht'⟩ := preservation hyp h hf hK ht
  exact ⟨Γ', hΓ, hext, hf', hK', ht'⟩

/-- **Typed configurations stay typed** along `StepFXS` runs. -/
theorem preservation_steps (hyp : CoreHyp E P host fx) {c c' : ConfigFX H} {ts : List FTy}
    (h : StepsFXS P host fx c c') (hc : ConfigOk E Γ c ts) :
    ∃ Γ', Γ <+: Γ' ∧ E.ext c.store c'.store ∧ ConfigOk E Γ' c' ts := by
  induction h with
  | refl => exact ⟨Γ, List.prefix_refl _, hyp.ext_refl _, hc⟩
  | tail _ hstep ih =>
    obtain ⟨Γ₁, hΓ₁, hext₁, hc₁⟩ := ih
    obtain ⟨Γ₂, hΓ₂, hext₂, hc₂⟩ := preservation_config hyp hstep hc₁
    exact ⟨Γ₂, hΓ₁.trans hΓ₂, hyp.ext_trans hext₁ hext₂, hc₂⟩

end Silmaril.Proofs.Wasm.Models.FXPres
