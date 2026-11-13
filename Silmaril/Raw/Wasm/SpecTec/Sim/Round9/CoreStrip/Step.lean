module

public import Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Strip.Thms

/-!
# `ExRel` is a simulation between two hosts, related at one store (unrefined)

`exRel_step₂`: if `c → c'` with host `host₁`, `d` agrees with `c` up to export lists, and the
outcomes of `host₁` at `c.store` are matched up to export lists by outcomes of `host₂` at
`d.store` (`HostRelAt`), then `d → d'` with host `host₂`, for some `d'` that agrees with `c'` up
to export lists. This is `Round7.exRel_step` with `HostExportBlind host` replaced by the
store-local `HostRelAt host₁ host₂ c.store d.store`; only the two host-call cases change. A step
calls the host only at the store of its source, which the context rules keep. Kept unrefined:
one case per rule, as the original.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round7

variable {H : Type}

attribute [local simp] atomic_toAdmin atomic_plain atomic_ref atomic_trap atomic_constI32
  atomic_callRefType atomic_returnCallRefType allAtomic_append_iff allAtomic_cons_iff
  allAtomic_nil_iff allAtomic_vals_iff

set_option hygiene false in
/-- Start a case whose source code is atomic: put the related configuration in normal form, with
the same code. -/
macro "exrel_atomic_r9" : tactic => `(tactic| (
  intro d hd hR
  obtain ⟨F, E, js, rfl, hF, hjs⟩ := exRel_nf hd
  rw [stripAdmins_eq_atomic (by simp) hjs]))

set_option hygiene false in
/-- Start a case: put the related configuration in normal form. -/
macro "exrel_nf_r9" : tactic => `(tactic| (
  intro d hd hR
  obtain ⟨F, E, js, rfl, hF, hjs⟩ := exRel_nf hd))

/-- **`ExRel` is a simulation from `Step P host₁` to `Step P host₂`** at a pair of configurations
whose stores relate the two hosts (`HostRelAt`): a step from `c` is matched by a step from any
configuration that agrees with `c` up to export lists, to one that agrees with the successor up
to export lists. -/
theorem exRel_step₂ {P : Profile} {host₁ host₂ : HostSemantics H}
    {c c' : Config H} (h : Step P host₁ c c') :
    ∀ d, ExRel c d → HostRelAt host₁ host₂ c.store d.store →
      ∃ d', Step P host₂ d d' ∧ ExRel c' d' := by
  induction h with
  | parametric h =>
      exrel_nf_r9
      rw [stripAdmins_eq_atomic (parametricStep_atomic h) hjs]
      exact ⟨_, .parametric h, exRel_nfc hF E rfl⟩
  | numeric h =>
      exrel_nf_r9
      rw [stripAdmins_eq_atomic (numericStep_atomic h) hjs]
      exact ⟨_, .numeric h, exRel_nfc hF E rfl⟩
  | vector h =>
      exrel_nf_r9
      rw [stripAdmins_eq_atomic (vectorStep_atomic h) hjs]
      exact ⟨_, .vector h, exRel_nfc hF E rfl⟩
  | «variable» h =>
      intro d hd _
      obtain ⟨d', h', hr⟩ := exRel_fam (variableStep_atomic h)
        (fun F E _ => variableStep_setEx h F E) (variableStep_funcs h).1 hd
      exact ⟨d', .variable h', hr⟩
  | table h =>
      intro d hd _
      obtain ⟨d', h', hr⟩ := exRel_fam (tableStep_atomic h)
        (fun F E _ => tableStep_setEx h F E) (tableStep_funcs h).1 hd
      exact ⟨d', .table h', hr⟩
  | memory h =>
      intro d hd _
      obtain ⟨d', h', hr⟩ := exRel_fam (memoryStep_atomic h)
        (fun F E _ => memoryStep_setEx h F E) (memoryStep_funcs h).1 hd
      exact ⟨d', .memory h', hr⟩
  | reference h =>
      intro d hd _
      obtain ⟨d', h', hr⟩ := exRel_fam (refStep_atomic h)
        (fun F E hF => refStep_setEx h F hF E) (refStep_funcs h).1 hd
      exact ⟨d', .reference h', hr⟩
  | aggregate h =>
      intro d hd _
      obtain ⟨d', h', hr⟩ := exRel_fam (aggregateStep_atomic h)
        (fun F E _ => aggregateStep_setEx h F E) (aggregateStep_funcs h).1 hd
      exact ⟨d', .aggregate h', hr⟩
  | ctxtInstrs h hne ih =>
      exrel_nf_r9
      rw [List.append_assoc] at hjs
      obtain ⟨r', rfl, hr'⟩ := stripAdmins_eq_atomic_append _ (allAtomic_vals _) hjs
      obtain ⟨jl, jr, rfl, hl, hr⟩ := stripAdmins_eq_append hr'
      obtain ⟨⟨s₂', f₂', js'⟩, hstep, hrel⟩ := ih _ (exRel_nfc hF E hl.symm) hR
      obtain ⟨hs', hf', hc'⟩ := exRel_parts hrel
      have hne' : _ ∨ jr ≠ [] := hne.imp id (ne_nil_of_strip hr).mpr
      rw [← List.append_assoc]
      exact ⟨⟨s₂', f₂', _⟩, .ctxtInstrs hstep hne',
        exRel_mk hs' hf' (by simp only [stripAdmins_append, hc', hr])⟩
  | ctxtLabel h ih =>
      exrel_nf_r9
      obtain ⟨b, rfl, hb'⟩ := stripAdmins_eq_singleton hjs
      obtain ⟨body, rfl, hbody⟩ := stripAdmin_eq_label hb'
      obtain ⟨⟨s₂', f₂', js'⟩, hstep, hrel⟩ := ih _ (exRel_nfc hF E hbody.symm) hR
      obtain ⟨hs', hf', hc'⟩ := exRel_parts hrel
      exact ⟨⟨s₂', f₂', _⟩, .ctxtLabel hstep,
        exRel_mk hs' hf' (by simp only [stripAdmins_cons, stripAdmin, hc'])⟩
  | ctxtHandler h ih =>
      exrel_nf_r9
      obtain ⟨b, rfl, hb'⟩ := stripAdmins_eq_singleton hjs
      obtain ⟨body, rfl, hbody⟩ := stripAdmin_eq_handler hb'
      obtain ⟨⟨s₂', f₂', js'⟩, hstep, hrel⟩ := ih _ (exRel_nfc hF E hbody.symm) hR
      obtain ⟨hs', hf', hc'⟩ := exRel_parts hrel
      exact ⟨⟨s₂', f₂', _⟩, .ctxtHandler hstep,
        exRel_mk hs' hf' (by simp only [stripAdmins_cons, stripAdmin, hc'])⟩
  | ctxtFrame h ih =>
      exrel_nf_r9
      obtain ⟨b, rfl, hb'⟩ := stripAdmins_eq_singleton hjs
      obtain ⟨fi₂, body, rfl, hfi, hbody⟩ := stripAdmin_eq_frame hb'
      obtain ⟨⟨s₂', fi₂', js'⟩, hstep, hrel⟩ :=
        ih _ (exRel_mk (stripStore_withFuncs _ hF).symm hfi.symm hbody.symm) hR
      obtain ⟨hs', hf', hc'⟩ := exRel_parts hrel
      exact ⟨⟨s₂', _, _⟩, .ctxtFrame hstep,
        exRel_mk hs' (stripFrame_withEx _ E).symm
          (by simp only [stripAdmins_cons, stripAdmin, hc', hf'])⟩
  | block hbt hm =>
      exrel_atomic_r9
      exact ⟨_, .block hbt hm, exRel_nfc hF E rfl⟩
  | loop hbt hm =>
      exrel_atomic_r9
      exact ⟨_, .loop hbt hm, exRel_nfc hF E rfl⟩
  | ifTrue hc =>
      exrel_atomic_r9
      exact ⟨_, .ifTrue hc, exRel_nfc hF E rfl⟩
  | ifFalse =>
      exrel_atomic_r9
      exact ⟨_, .ifFalse, exRel_nfc hF E rfl⟩
  | labelVals =>
      exrel_nf_r9
      rw [inv_label0 (allAtomic_vals _) hjs]
      exact ⟨_, .labelVals, exRel_nfc hF E rfl⟩
  | brLabelZero hl hn =>
      exrel_nf_r9
      obtain ⟨r', rfl, -⟩ := inv_label (by simp) hjs
      exact ⟨_, .brLabelZero hl hn, exRel_nfc hF E rfl⟩
  | brLabelSucc hl =>
      exrel_nf_r9
      obtain ⟨r', rfl, -⟩ := inv_label (by simp) hjs
      exact ⟨_, .brLabelSucc hl, exRel_nfc hF E rfl⟩
  | brHandler =>
      exrel_nf_r9
      obtain ⟨r', rfl, -⟩ := inv_handler (by simp) hjs
      exact ⟨_, .brHandler, exRel_nfc hF E rfl⟩
  | brIfTrue hc =>
      exrel_atomic_r9
      exact ⟨_, .brIfTrue hc, exRel_nfc hF E rfl⟩
  | brIfFalse =>
      exrel_atomic_r9
      exact ⟨_, .brIfFalse, exRel_nfc hF E rfl⟩
  | brTableLt hi =>
      exrel_atomic_r9
      exact ⟨_, .brTableLt hi, exRel_nfc hF E rfl⟩
  | brTableGe hi =>
      exrel_atomic_r9
      exact ⟨_, .brTableGe hi, exRel_nfc hF E rfl⟩
  | brOnNullNull =>
      exrel_atomic_r9
      exact ⟨_, .brOnNullNull, exRel_nfc hF E rfl⟩
  | brOnNullAddr hv =>
      exrel_atomic_r9
      exact ⟨_, .brOnNullAddr hv, exRel_nfc hF E rfl⟩
  | brOnNonNullNull =>
      exrel_atomic_r9
      exact ⟨_, .brOnNonNullNull, exRel_nfc hF E rfl⟩
  | brOnNonNullAddr hv =>
      exrel_atomic_r9
      exact ⟨_, .brOnNonNullAddr hv, exRel_nfc hF E rfl⟩
  | brOnCastSucceed h =>
      exrel_atomic_r9
      exact ⟨_, .brOnCastSucceed ((refOk_withFuncs_iff hF).mpr h), exRel_nfc hF E rfl⟩
  | brOnCastFail h =>
      exrel_atomic_r9
      exact ⟨_, .brOnCastFail fun h' => h ((refOk_withFuncs_iff hF).mp h'), exRel_nfc hF E rfl⟩
  | brOnCastFailSucceed h =>
      exrel_atomic_r9
      exact ⟨_, .brOnCastFailSucceed ((refOk_withFuncs_iff hF).mpr h), exRel_nfc hF E rfl⟩
  | brOnCastFailFail h =>
      exrel_atomic_r9
      exact ⟨_, .brOnCastFailFail fun h' => h ((refOk_withFuncs_iff hF).mp h'),
        exRel_nfc hF E rfl⟩
  | call hx hf =>
      exrel_atomic_r9
      obtain ⟨fi₂, hfi₂, hty, -, -⟩ := stripFI_get hF hf
      exact ⟨_, .call hx hfi₂, exRel_nfc hF E (by rw [hty])⟩
  | callRefNull hc =>
      exrel_nf_r9
      rw [stripAdmins_eq_atomic (by simp [atomic_of_isCallRef hc]) hjs]
      exact ⟨_, .callRefNull hc, exRel_nfc hF E rfl⟩
  | callRefFunc hc hf he hn hcode =>
      exrel_nf_r9
      rw [stripAdmins_eq_atomic (by simp [atomic_of_isCallRef hc])
        hjs]
      obtain ⟨fi₂, hfi₂, hty, hcd, hm⟩ := stripFI_get hF hf
      refine ⟨_, .callRefFunc hc hfi₂ (hty ▸ he) hn (hcd ▸ hcode), exRel_nfc hF E ?_⟩
      simp only [stripAdmins_cons, stripAdmins_nil, stripAdmin, stripFrame_forCall hm.symm]
  | callRefHost hc hf he hn hcode hhost =>
      exrel_nf_r9
      rw [stripAdmins_eq_atomic (by simp [atomic_of_isCallRef hc])
        hjs]
      obtain ⟨fi₂, hfi₂, hty, hcd, -⟩ := stripFI_get hF hf
      obtain ⟨o, ho, heq⟩ := hR _ _ _ hhost
      cases o with
      | diverged => exact absurd heq (by simp [stripOutcome])
      | returned s₂' r₂ =>
          simp only [stripOutcome, Silmaril.Wasm.Execution.Host.Outcome.returned.injEq] at heq
          obtain ⟨hs', rfl⟩ := heq
          exact ⟨_, .callRefHost hc hfi₂ (hty ▸ he) hn (hcd ▸ hcode) ho,
            exRel_mk hs' (stripFrame_withEx _ E).symm rfl⟩
  | callRefHostDiv hc hf he hn hcode hhost =>
      exrel_nf_r9
      rw [stripAdmins_eq_atomic (by simp [atomic_of_isCallRef hc])
        hjs]
      obtain ⟨fi₂, hfi₂, hty, hcd, -⟩ := stripFI_get hF hf
      obtain ⟨o, ho, heq⟩ := hR _ _ _ hhost
      cases o with
      | diverged =>
          exact ⟨_, .callRefHostDiv hc hfi₂ (hty ▸ he) hn (hcd ▸ hcode) ho, exRel_nfc hF E rfl⟩
      | returned s₂' r₂ => exact absurd heq (by simp [stripOutcome])
  | returnCall hx hf =>
      exrel_atomic_r9
      obtain ⟨fi₂, hfi₂, hty, -, -⟩ := stripFI_get hF hf
      exact ⟨_, .returnCall hx hfi₂, exRel_nfc hF E (by rw [hty])⟩
  | returnCallRefLabel hc =>
      exrel_nf_r9
      obtain ⟨r', rfl, -⟩ :=
        inv_label (by simp [atomic_of_isReturnCallRef hc]) hjs
      exact ⟨_, .returnCallRefLabel hc, exRel_nfc hF E rfl⟩
  | returnCallRefHandler hc =>
      exrel_nf_r9
      obtain ⟨r', rfl, -⟩ :=
        inv_handler (by simp [atomic_of_isReturnCallRef hc]) hjs
      exact ⟨_, .returnCallRefHandler hc, exRel_nfc hF E rfl⟩
  | returnCallRefFrameNull hc =>
      exrel_nf_r9
      obtain ⟨fi₂, r', rfl, -, -⟩ :=
        inv_frame (by simp [atomic_of_isReturnCallRef hc]) hjs
      exact ⟨_, .returnCallRefFrameNull hc, exRel_nfc hF E rfl⟩
  | returnCallRefFrameAddr hc hf he hn =>
      exrel_nf_r9
      obtain ⟨fi₂, r', rfl, hfi, -⟩ :=
        inv_frame (by simp [atomic_of_isReturnCallRef hc]) hjs
      obtain ⟨fn₂, hfn₂, hty, -, -⟩ := stripFI_get hF hf
      refine ⟨_, .returnCallRefFrameAddr hc hfn₂ (hty ▸ he) hn, exRel_nfc hF E ?_⟩
      rw [retToCallIn_strip (stripModule_frame hfi)]
  | callIndirect =>
      exrel_atomic_r9
      exact ⟨_, .callIndirect, exRel_nfc hF E rfl⟩
  | returnCallIndirect =>
      exrel_atomic_r9
      exact ⟨_, .returnCallIndirect, exRel_nfc hF E rfl⟩
  | frameVals hn =>
      exrel_nf_r9
      obtain ⟨fi₂, rfl, -⟩ := inv_frame0 (allAtomic_vals _) hjs
      exact ⟨_, .frameVals hn, exRel_nfc hF E rfl⟩
  | returnFrame hn =>
      exrel_nf_r9
      obtain ⟨fi₂, r', rfl, -, -⟩ := inv_frame (by simp) hjs
      exact ⟨_, .returnFrame hn, exRel_nfc hF E rfl⟩
  | returnLabel =>
      exrel_nf_r9
      obtain ⟨r', rfl, -⟩ := inv_label (by simp) hjs
      exact ⟨_, .returnLabel, exRel_nfc hF E rfl⟩
  | returnHandler =>
      exrel_nf_r9
      obtain ⟨r', rfl, -⟩ := inv_handler (by simp) hjs
      exact ⟨_, .returnHandler, exRel_nfc hF E rfl⟩
  | throw ht he hn =>
      exrel_atomic_r9
      exact ⟨_, .throw ht he hn, exRel_mk (stripStore_addExn hF _) (stripFrame_withEx _ E).symm rfl⟩
  | throwRefNull =>
      exrel_atomic_r9
      exact ⟨_, .throwRefNull, exRel_nfc hF E rfl⟩
  | throwRefInstrs hne =>
      exrel_nf_r9
      obtain ⟨r', rfl, hr'⟩ := stripAdmins_eq_atomic_append _ (by simp) hjs
      exact ⟨_, .throwRefInstrs (hne.imp id (ne_nil_of_strip hr').mpr), exRel_nfc hF E rfl⟩
  | throwRefLabel =>
      exrel_nf_r9
      rw [inv_label0 (by simp) hjs]
      exact ⟨_, .throwRefLabel, exRel_nfc hF E rfl⟩
  | throwRefFrame =>
      exrel_nf_r9
      obtain ⟨fi₂, rfl, -⟩ := inv_frame0 (by simp) hjs
      exact ⟨_, .throwRefFrame, exRel_nfc hF E rfl⟩
  | throwRefHandlerEmpty =>
      exrel_nf_r9
      rw [inv_handler0 (by simp) hjs]
      exact ⟨_, .throwRefHandlerEmpty, exRel_nfc hF E rfl⟩
  | throwRefHandlerCatch he ht =>
      exrel_nf_r9
      rw [inv_handler0 (by simp) hjs]
      exact ⟨_, .throwRefHandlerCatch he ht, exRel_nfc hF E rfl⟩
  | throwRefHandlerCatchRef he ht =>
      exrel_nf_r9
      rw [inv_handler0 (by simp) hjs]
      exact ⟨_, .throwRefHandlerCatchRef he ht, exRel_nfc hF E rfl⟩
  | throwRefHandlerCatchAll =>
      exrel_nf_r9
      rw [inv_handler0 (by simp) hjs]
      exact ⟨_, .throwRefHandlerCatchAll, exRel_nfc hF E rfl⟩
  | throwRefHandlerCatchAllRef =>
      exrel_nf_r9
      rw [inv_handler0 (by simp) hjs]
      exact ⟨_, .throwRefHandlerCatchAllRef, exRel_nfc hF E rfl⟩
  | throwRefHandlerNext h =>
      exrel_nf_r9
      rw [inv_handler0 (by simp) hjs]
      exact ⟨_, .throwRefHandlerNext h, exRel_nfc hF E rfl⟩
  | tryTable hbt hm =>
      exrel_atomic_r9
      exact ⟨_, .tryTable hbt hm, exRel_nfc hF E rfl⟩
  | handlerVals =>
      exrel_nf_r9
      rw [inv_handler0 (allAtomic_vals _) hjs]
      exact ⟨_, .handlerVals, exRel_nfc hF E rfl⟩
  | trapInstrs hne =>
      exrel_nf_r9
      obtain ⟨r', rfl, hr'⟩ := stripAdmins_eq_atomic_append _ (by simp) hjs
      exact ⟨_, .trapInstrs (hne.imp id (ne_nil_of_strip hr').mpr), exRel_nfc hF E rfl⟩
  | trapLabel =>
      exrel_nf_r9
      rw [inv_label0 (by simp) hjs]
      exact ⟨_, .trapLabel, exRel_nfc hF E rfl⟩
  | trapHandler =>
      exrel_nf_r9
      rw [inv_handler0 (by simp) hjs]
      exact ⟨_, .trapHandler, exRel_nfc hF E rfl⟩
  | trapFrame =>
      exrel_nf_r9
      obtain ⟨fi₂, rfl, -⟩ := inv_frame0 (by simp) hjs
      exact ⟨_, .trapFrame, exRel_nfc hF E rfl⟩

end Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip
