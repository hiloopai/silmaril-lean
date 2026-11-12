module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Lift
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Provenance

/-!
# The forward simulation, assembled

`forward`: if the families discharge `Forward` (one obligation per non-context constructor of Core's
`Step`) and the encoding satisfies `TypingFacts`, then every Core step between typed configurations
is a SpecTec step of the images. The four context rules are done here, by the lifting lemmas of
`Lift.lean`; the recursion is `Step.rec` itself, so nothing about the other constructors is
re-stated.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecStepRules (HasStepRules)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## The encoding of sequences -/

/-- `adminsToV` is `List.map adminToV`. -/
theorem adminsToV_eq_map : ∀ l : List Admin, adminsToV l = l.map adminToV
  | [] => by simp [adminsToV]
  | a :: l => by simp [adminsToV, adminsToV_eq_map l]

/-- `adminsToV` distributes over `++`. -/
theorem adminsToV_append (a b : List Admin) : adminsToV (a ++ b) = adminsToV a ++ adminsToV b := by
  simp [adminsToV_eq_map]

/-- `adminsToV` keeps the length. -/
theorem adminsToV_length (l : List Admin) : (adminsToV l).length = l.length := by
  simp [adminsToV_eq_map]

/-- A non-empty sequence has a non-empty image. -/
theorem adminsToV_ne_nil {l : List Admin} (h : l ≠ []) : adminsToV l ≠ [] := by
  intro he
  exact h (List.eq_nil_of_length_eq_zero (by rw [← adminsToV_length, he]; rfl))

/-! ## The four context rules -/

section Ctxt

variable {env : Env} {hn : H → String}

/-- `Step.ctxtInstrs`, forward. -/
theorem fwd_ctxtInstrs (T : TypingFacts env hn)
    (hr : Equiv.Validation.HasRuleAt env "Step" "%~>%" 2 Equiv.ExecStepRules.ctxtInstrsRule)
    {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (hne : vs ≠ [] ∨ rest ≠ []) (ih : FwdP env hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdP env hn ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  intro hc hc'
  have e₁ : adminsToV (vals vs ++ is ++ rest) =
      adminsToV (vals vs) ++ adminsToV is ++ adminsToV rest := by
    simp only [adminsToV_append]
  have e₂ : adminsToV (vals vs ++ is' ++ rest) =
      adminsToV (vals vs) ++ adminsToV is' ++ adminsToV rest := by
    simp only [adminsToV_append]
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  obtain ⟨hst', hcode'⟩ := (T.config _).1 hc'
  have hc₁ : TypedV env instrsT (.list (adminsToV (vals vs) ++ adminsToV is ++ adminsToV rest)) :=
    e₁ ▸ hcode
  have hc₂ : TypedV env instrsT (.list (adminsToV (vals vs) ++ adminsToV is' ++ adminsToV rest)) :=
    e₂ ▸ hcode'
  obtain ⟨hvi, hrest⟩ := (T.append _ _).1 hc₁
  obtain ⟨hv, his⟩ := (T.append _ _).1 hvi
  obtain ⟨hvi', -⟩ := (T.append _ _).1 hc₂
  obtain ⟨-, his'⟩ := (T.append _ _).1 hvi'
  have hin : Typed env hn ⟨s, f, is⟩ := (T.config _).2 ⟨hst, his⟩
  have hin' : Typed env hn ⟨s', f', is'⟩ := (T.config _).2 ⟨hst', his'⟩
  have hne' : adminsToV (vals vs) ≠ [] ∨ adminsToV rest ≠ [] := by
    rcases hne with h | h
    · exact .inl (adminsToV_ne_nil (by simpa [vals] using h))
    · exact .inr (adminsToV_ne_nil h)
  have hg := sstep_ctxtInstrs hr hst hst' (T.vals vs hv) his his' hrest hne' (ih hin hin')
  show SStep env (cfgV _ (adminsToV (vals vs ++ is ++ rest)))
    (cfgV _ (adminsToV (vals vs ++ is' ++ rest)))
  rw [e₁, e₂]
  exact hg

/-- `Step.ctxtLabel`, forward. -/
theorem fwd_ctxtLabel (T : TypingFacts env hn)
    (hr : Equiv.Validation.HasRuleAt env "Step" "%~>%" 3 Equiv.ExecStepRules.ctxtLabelRule)
    {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr} {is is' : List Admin}
    (ih : FwdP env hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdP env hn ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ := by
  intro hc hc'
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  obtain ⟨hst', hcode'⟩ := (T.config _).1 hc'
  obtain ⟨hn₀, hcont, his⟩ := T.label n cont is hcode
  obtain ⟨-, -, his'⟩ := T.label n cont is' hcode'
  have hin : Typed env hn ⟨s, f, is⟩ := (T.config _).2 ⟨hst, his⟩
  have hin' : Typed env hn ⟨s', f', is'⟩ := (T.config _).2 ⟨hst', his'⟩
  exact sstep_ctxtLabel hr hst hst' hn₀ hcont his his' (ih hin hin')

/-- `Step.ctxtHandler`, forward. -/
theorem fwd_ctxtHandler (T : TypingFacts env hn)
    (hr : Equiv.Validation.HasRuleAt env "Step" "%~>%" 4 Equiv.ExecStepRules.ctxtHandlerRule)
    {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch} {is is' : List Admin}
    (ih : FwdP env hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdP env hn ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩ := by
  intro hc hc'
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  obtain ⟨hst', hcode'⟩ := (T.config _).1 hc'
  obtain ⟨hn₀, hcs, his⟩ := T.handler n cs is hcode
  obtain ⟨-, -, his'⟩ := T.handler n cs is' hcode'
  have hin : Typed env hn ⟨s, f, is⟩ := (T.config _).2 ⟨hst, his⟩
  have hin' : Typed env hn ⟨s', f', is'⟩ := (T.config _).2 ⟨hst', his'⟩
  exact sstep_ctxtHandler hr hst hst' hn₀ hcs his his' (ih hin hin')

/-- `Step.ctxtFrame`, forward. -/
theorem fwd_ctxtFrame (T : TypingFacts env hn)
    (hr : Equiv.Validation.HasRuleAt env "Step" "%~>%" 5 Equiv.ExecStepRules.ctxtFrameRule)
    {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (ih : FwdP env hn ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
    FwdP env hn ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ := by
  intro hc hc'
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  obtain ⟨hst', hcode'⟩ := (T.config _).1 hc'
  obtain ⟨hs, hf⟩ := (T.state _ _).1 hst
  obtain ⟨hs', -⟩ := (T.state _ _).1 hst'
  obtain ⟨hn₀, hfi, his⟩ := T.frame n fi is hcode
  obtain ⟨-, hfi', his'⟩ := T.frame n fi' is' hcode'
  have hin : Typed env hn ⟨s, fi, is⟩ := (T.config _).2 ⟨(T.state _ _).2 ⟨hs, hfi⟩, his⟩
  have hin' : Typed env hn ⟨s', fi', is'⟩ := (T.config _).2 ⟨(T.state _ _).2 ⟨hs', hfi'⟩, his'⟩
  exact sstep_ctxtFrame hr hs hs' hf hfi hfi' hn₀ his his' (ih hin hin')

end Ctxt

/-! ## The assembly -/

/-- **The forward simulation, from the families' obligations.** Every Core step between typed
configurations is a SpecTec step of their images, given `Forward` (the non-context constructors),
`TypingFacts` (the encoding) and the provenance of `Step`'s rules. -/
theorem forward {env : Env} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}
    (F : Forward env hn P host) (T : TypingFacts env hn) (R : HasStepRules env)
    {c c' : Config H} (h : Step P host c c') : FwdP env hn c c' :=
  Step.rec (motive := fun c c' _ => FwdP env hn c c')
    F.parametric F.numeric F.vector F.variable_ F.table F.memory F.reference F.aggregate
    (fun _ hne ih => fwd_ctxtInstrs T R.ctxtInstrs hne ih)
    (fun _ ih => fwd_ctxtLabel T R.ctxtLabel ih) (fun _ ih => fwd_ctxtHandler T R.ctxtHandler ih)
    (fun _ ih => fwd_ctxtFrame T R.ctxtFrame ih) F.block F.loop F.ifTrue F.ifFalse F.labelVals
    F.brLabelZero F.brLabelSucc F.brHandler F.brIfTrue F.brIfFalse F.brTableLt F.brTableGe
    F.brOnNullNull F.brOnNullAddr F.brOnNonNullNull F.brOnNonNullAddr F.brOnCastSucceed
    F.brOnCastFail F.brOnCastFailSucceed F.brOnCastFailFail F.call F.callRefNull F.callRefFunc
    F.callRefHost F.callRefHostDiv F.returnCall F.returnCallRefLabel F.returnCallRefHandler
    F.returnCallRefFrameNull F.returnCallRefFrameAddr F.callIndirect F.returnCallIndirect
    F.frameVals F.returnFrame F.returnLabel F.returnHandler F.throw F.throwRefNull
    F.throwRefInstrs F.throwRefLabel F.throwRefFrame F.throwRefHandlerEmpty
    F.throwRefHandlerCatch F.throwRefHandlerCatchRef F.throwRefHandlerCatchAll
    F.throwRefHandlerCatchAllRef F.throwRefHandlerNext F.tryTable F.handlerVals F.trapInstrs
    F.trapLabel F.trapHandler F.trapFrame
    h

/-! ## A first end-to-end instance -/

/-- **Smoke test of the whole pipeline.** In every `simEnv B`, `nop` steps to nothing as a
`Step_pure` step, read declaratively, through the image `instrToV .nop` of Core's `nop`; and so
the Core step `[nop] ~> []` is a SpecTec `Step` of the images at any typed state. -/
theorem spure_nop (B : Builtins) : SPure (simEnv B) [instrToV .nop] [] :=
  dderives_of_ruleAt (hasRuleAt_simEnv B Equiv.Execution.hasStepRules_wasm30.nop) []
    QuantsOk.nil
    (evalExp_tupE_iff.2 ⟨_, evalExps_cons
      (evalExp_listE_iff.2 ⟨_, evalExps_cons
        (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)) evalExps_nil, rfl⟩)
      (evalExps_cons (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩) evalExps_nil), rfl⟩)
    (fun _ h => nomatch h)

/-- `nop` as a whole-machine step, for any state of type `state`. -/
theorem sstep_nop (B : Builtins) {z : Value} (hz : TypedV (simEnv B) stateT z)
    (h₁ : TypedV (simEnv B) instrsT (.list [instrToV .nop]))
    (h₀ : TypedV (simEnv B) instrsT (.list [])) :
    SStep (simEnv B) (cfgV z [instrToV .nop]) (cfgV z []) :=
  sstep_pure ((hasStepRules_simEnv B).pure) hz h₁ h₀ (spure_nop B)

end Silmaril.Wasm.SpecTec.Sim
