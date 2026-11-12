module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeCtxAgree
public import Silmaril.Wasm.SpecTec.Sim20.StepFix.Thms

/-!
# The corrected 2.0 script forward: `pure`, `read`, `ctxt-label`, `ctxt-frame`

Every structural rule of `stepErratum20` now lifts V2-image steps in `simEnv20S B`, with all the
typing read in the original `simEnv20 B`:

* `sstepS_of_spure20`, `fwdS_pure`: a `Step_pure` derivation of the original script, between typed
  `admininstr*` sequences, is a corrected `Step` (`RelFree.spure20S_iff` moves it, `Step/pure`
  lifts it). So every forward `Step_pure` result of the Pure track (`Pure.*_iff`, at
  `simEnv20 B`) gives a corrected whole step;
* `sstepS_of_sread20`, `fwdS_read`: the same for `Step_read` (`RelFree.sread20S_iff`,
  `StepFix.sstepS_read`);
* `fwdS_label`: a corrected step of `s; f; is` lifts under `LABEL_ n {cont}`;
* `fwdS_frame`: a corrected step of `s; fi; is` to `s'; fi'; is'` lifts under `FRAME_ n {fi}` at
  any outer frame `f` (V2's `Step.ctxtFrame`, deviation 2, which the erratum adopts).

The typing hypotheses are hypotheses: subject reduction for the image is not proved.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV SPure SRead cfgV stV stateT storeT frameT nT instrsT)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S adminsTy sstepB20S_iff sstepS_pure sstepS_read
  sstepS_ctxtLabel sstepS_ctxtFrame)
open Silmaril.Wasm.SpecTec.Sim20.RelFree (spure20S_iff sread20S_iff)

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## Typing, moved -/

theorem typedV_state20S {z : Value} (h : TypedV (simEnv20 B) stateT z) :
    TypedV (simEnv20S B) stateT z := typedV_withRels20 (by decide) h

theorem typedV_admins20S {v : Value} (h : TypedV (simEnv20 B) adminsTy v) :
    TypedV (simEnv20S B) adminsTy v := typedV_withRels20 (by decide) h

theorem typedV_store20S {v : Value} (h : TypedV (simEnv20 B) storeT v) :
    TypedV (simEnv20S B) storeT v := typedV_withRels20 (by decide) h

theorem typedV_frame20S {v : Value} (h : TypedV (simEnv20 B) frameT v) :
    TypedV (simEnv20S B) frameT v := typedV_withRels20 (by decide) h

theorem typedV_n20S {v : Value} (h : TypedV (simEnv20 B) nT v) : TypedV (simEnv20S B) nT v :=
  typedV_withRels20 (by decide) h

theorem typedV_instrs20S {v : Value} (h : TypedV (simEnv20 B) instrsT v) :
    TypedV (simEnv20S B) instrsT v := typedV_withRels20 (by decide) h

/-! ## `Step/pure` and `Step/read` -/

/-- **A `Step_pure` derivation of the original script is a corrected `Step`.** -/
theorem sstepS_of_spure20 {z : Value} {is js : List Value} (hz : TypedV (simEnv20 B) stateT z)
    (his : TypedV (simEnv20 B) adminsTy (.list is)) (hjs : TypedV (simEnv20 B) adminsTy (.list js))
    (hp : SPure (simEnv20 B) is js) : SStepB (simEnv20S B) (cfgV z is) (cfgV z js) :=
  (sstepB20S_iff B).2 (sstepS_pure (typedV_state20S hz) (typedV_admins20S his)
    (typedV_admins20S hjs) ((spure20S_iff B is js).2 hp))

/-- **A `Step_read` derivation of the original script is a corrected `Step`.** -/
theorem sstepS_of_sread20 {z : Value} {is js : List Value} (hz : TypedV (simEnv20 B) stateT z)
    (his : TypedV (simEnv20 B) adminsTy (.list is)) (hjs : TypedV (simEnv20 B) adminsTy (.list js))
    (hp : SRead (simEnv20 B) (cfgV z is) js) : SStepB (simEnv20S B) (cfgV z is) (cfgV z js) :=
  (sstepB20S_iff B).2 (sstepS_read (typedV_state20S hz) (typedV_admins20S his)
    (typedV_admins20S hjs) ((sread20S_iff B _ js).2 hp))

/-- `Step/pure` forward on V2 images: a `Step_pure` derivation between the codes of two typed
configurations with the same state. -/
theorem fwdS_pure {s : Store H} {f : Frame} {is is' : List Admin}
    (hc : Typed20 (simEnv20 B) hn ⟨s, f, is⟩) (hc' : Typed20 (simEnv20 B) hn ⟨s, f, is'⟩)
    (hp : SPure (simEnv20 B) (adminsToV is) (adminsToV is')) :
    SStepB (simEnv20S B) (configV hn ⟨s, f, is⟩) (configV hn ⟨s, f, is'⟩) :=
  sstepS_of_spure20 (typedV_state_of_typed20 hc) (typedV_code_of_typed20 hc)
    (typedV_code_of_typed20 hc') hp

/-- `Step/read` forward on V2 images. -/
theorem fwdS_read {s : Store H} {f : Frame} {is is' : List Admin}
    (hc : Typed20 (simEnv20 B) hn ⟨s, f, is⟩) (hc' : Typed20 (simEnv20 B) hn ⟨s, f, is'⟩)
    (hp : SRead (simEnv20 B) (configV hn ⟨s, f, is⟩) (adminsToV is')) :
    SStepB (simEnv20S B) (configV hn ⟨s, f, is⟩) (configV hn ⟨s, f, is'⟩) :=
  sstepS_of_sread20 (typedV_state_of_typed20 hc) (typedV_code_of_typed20 hc)
    (typedV_code_of_typed20 hc') hp

/-! ## `ctxt-label` and `ctxt-frame` -/

/-- **`Step/ctxt-label` forward on V2 images**: a corrected step lifts under `LABEL_ n {cont}`. -/
theorem fwdS_label {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Silmaril.Wasm.V2.Instr}
    {is is' : List Admin} (hc : Typed20 (simEnv20 B) hn ⟨s, f, is⟩)
    (hc' : Typed20 (simEnv20 B) hn ⟨s', f', is'⟩) (hn' : TypedV (simEnv20 B) nT (.num (.natN n)))
    (hcont : TypedV (simEnv20 B) instrsT (.list (instrsToV cont)))
    (h : SStepB (simEnv20S B) (configV hn ⟨s, f, is⟩) (configV hn ⟨s', f', is'⟩)) :
    SStepB (simEnv20S B) (configV hn ⟨s, f, [.label n cont is]⟩)
      (configV hn ⟨s', f', [.label n cont is']⟩) := by
  have hs := sstepS_ctxtLabel (typedV_state20S (typedV_state_of_typed20 hc))
    (typedV_state20S (typedV_state_of_typed20 hc')) (typedV_n20S hn') (typedV_instrs20S hcont)
    (typedV_admins20S (typedV_code_of_typed20 hc)) (typedV_admins20S (typedV_code_of_typed20 hc'))
    ((sstepB20S_iff B).1 h)
  exact (sstepB20S_iff B).2 (by simpa only [configV, adminsToV, adminToV] using hs)

/-- **`Step/ctxt-frame` forward on V2 images**: a corrected step of `s; fi; is` to
`s'; fi'; is'` lifts under `FRAME_ n {fi}` at any outer frame `f`. -/
theorem fwdS_frame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (hs₁ : TypedV (simEnv20 B) storeT (storeV hn s)) (hs₂ : TypedV (simEnv20 B) storeT (storeV hn s'))
    (hf : TypedV (simEnv20 B) frameT (frameV f)) (hfi : TypedV (simEnv20 B) frameT (frameV fi))
    (hfi' : TypedV (simEnv20 B) frameT (frameV fi'))
    (hn' : TypedV (simEnv20 B) nT (.num (.natN n)))
    (his : TypedV (simEnv20 B) adminsTy (.list (adminsToV is)))
    (his' : TypedV (simEnv20 B) adminsTy (.list (adminsToV is')))
    (h : SStepB (simEnv20S B) (configV hn ⟨s, fi, is⟩) (configV hn ⟨s', fi', is'⟩)) :
    SStepB (simEnv20S B) (configV hn ⟨s, f, [.frame n fi is]⟩)
      (configV hn ⟨s', f, [.frame n fi' is']⟩) := by
  have hst := sstepS_ctxtFrame (typedV_store20S hs₁) (typedV_store20S hs₂) (typedV_frame20S hf)
    (typedV_frame20S hfi) (typedV_frame20S hfi') (typedV_n20S hn') (typedV_admins20S his)
    (typedV_admins20S his') ((sstepB20S_iff B).1 h)
  exact (sstepB20S_iff B).2 (by simpa only [configV, stateV, adminsToV, adminToV] using hst)

end Silmaril.Wasm.SpecTec.Sim20.Whole
