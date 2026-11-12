module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Casts.Core
public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Multi.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Multi4.Thms

/-!
# Round 6: the forward half of the cast leaf

* `fwdB_ctxtInstrs`, `fwdB_ctxtLabel`, `fwdB_ctxtHandler`, `fwdB_ctxtFrame`: `Sim.fwd_ctxt*`
  (`Assembly.lean`) for `FwdPB`, from `sstepB_ctxt*`.
* `fwdB_cast`: every Core step from a bounded cast redex is an `SStepB` step between typed
  images, by `castStep_rec`: the top-level cast steps are `castsFwdB_of` (from
  `RefOkBB`), and the four context rules are lifted.
* `calls_cast`: the successor of a cast redex keeps the typed `CALL_REF`s of its source (the cast
  results contain none), so a SpecTec witness of a typed successor is typed
  (`Round5.Multi.typed_of_configEq`).
* `castsFwd`: `Target.Casts.fwd` at the backend reading, from a `HostOk` host and `RefOkBB`.

Round 6, track casts-v: `fwdG_top`, `fwdG_cast` and `castsFwdG` are the same proofs from a
`CastsV.CastRefOk` hypothesis at `Bounded c ∧ W c`, for a predicate `W` closed under the context
rules (`Target.CtxClosedVals`) that holds at the witness; `fwdB_top`, `fwdB_cast` and `castsFwd`
are their instances at `W := True`, with unchanged statements.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Casts

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecStepRules (ctxtInstrsRule ctxtLabelRule ctxtHandlerRule ctxtFrameRule)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4 (Bounded SimRel)
open Round4Int (BI)
open Round5.Target (BoundedSel typed_of_configOk_sel)
open Round5.Multi (CodeCallsTyped AdminCallsTyped)
open Reading (FwdPB SStepB RefOkBB)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## The context rules, forward, under the new reading -/

section Ctxt

variable {env : Env}

/-- `Step.ctxtInstrs`, forward, under the new reading. -/
theorem fwdB_ctxtInstrs (T : TypingFacts env hn) (hr : HasRuleAt env "Step" "%~>%" 2 ctxtInstrsRule)
    {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (hne : vs ≠ [] ∨ rest ≠ []) (ih : FwdPB env hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdPB env hn ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ := by
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
  have hg := Reading.sstepB_ctxtInstrs hr hst hst' (T.vals vs hv) his his' hrest hne'
    (ih hin hin')
  show SStepB env (cfgV _ (adminsToV (vals vs ++ is ++ rest)))
    (cfgV _ (adminsToV (vals vs ++ is' ++ rest)))
  rw [e₁, e₂]
  exact hg

/-- `Step.ctxtLabel`, forward, under the new reading. -/
theorem fwdB_ctxtLabel (T : TypingFacts env hn) (hr : HasRuleAt env "Step" "%~>%" 3 ctxtLabelRule)
    {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr} {is is' : List Admin}
    (ih : FwdPB env hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdPB env hn ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ := by
  intro hc hc'
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  obtain ⟨hst', hcode'⟩ := (T.config _).1 hc'
  obtain ⟨hn₀, hcont, his⟩ := T.label n cont is hcode
  obtain ⟨-, -, his'⟩ := T.label n cont is' hcode'
  have hin : Typed env hn ⟨s, f, is⟩ := (T.config _).2 ⟨hst, his⟩
  have hin' : Typed env hn ⟨s', f', is'⟩ := (T.config _).2 ⟨hst', his'⟩
  exact Reading.sstepB_ctxtLabel hr hst hst' hn₀ hcont his his' (ih hin hin')

/-- `Step.ctxtHandler`, forward, under the new reading. -/
theorem fwdB_ctxtHandler (T : TypingFacts env hn)
    (hr : HasRuleAt env "Step" "%~>%" 4 ctxtHandlerRule) {s s' : Store H} {f f' : Frame}
    {n : Nat} {cs : List Catch} {is is' : List Admin}
    (ih : FwdPB env hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdPB env hn ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩ := by
  intro hc hc'
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  obtain ⟨hst', hcode'⟩ := (T.config _).1 hc'
  obtain ⟨hn₀, hcs, his⟩ := T.handler n cs is hcode
  obtain ⟨-, -, his'⟩ := T.handler n cs is' hcode'
  have hin : Typed env hn ⟨s, f, is⟩ := (T.config _).2 ⟨hst, his⟩
  have hin' : Typed env hn ⟨s', f', is'⟩ := (T.config _).2 ⟨hst', his'⟩
  exact Reading.sstepB_ctxtHandler hr hst hst' hn₀ hcs his his' (ih hin hin')

/-- `Step.ctxtFrame`, forward, under the new reading. -/
theorem fwdB_ctxtFrame (T : TypingFacts env hn) (hr : HasRuleAt env "Step" "%~>%" 5 ctxtFrameRule)
    {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (ih : FwdPB env hn ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
    FwdPB env hn ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ := by
  intro hc hc'
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  obtain ⟨hst', hcode'⟩ := (T.config _).1 hc'
  obtain ⟨hs, hf⟩ := (T.state _ _).1 hst
  obtain ⟨hs', -⟩ := (T.state _ _).1 hst'
  obtain ⟨hn₀, hfi, his⟩ := T.frame n fi is hcode
  obtain ⟨-, hfi', his'⟩ := T.frame n fi' is' hcode'
  have hin : Typed env hn ⟨s, fi, is⟩ := (T.config _).2 ⟨(T.state _ _).2 ⟨hs, hfi⟩, his⟩
  have hin' : Typed env hn ⟨s', fi', is'⟩ := (T.config _).2 ⟨(T.state _ _).2 ⟨hs', hfi'⟩, his'⟩
  exact Reading.sstepB_ctxtFrame hr hs hs' hf hfi hfi' hn₀ his his' (ih hin hin')

end Ctxt

/-! ## The forward recursion -/

/-- `Round4.Bounded` is closed under SpecTec's context decompositions. -/
theorem bounded_closed : Target.CtxClosedVals (Bounded (H := H)) where
  mid _ _ _ _ _ h := Round5.Fwd.bounded_ctxtInstrs h
  label _ _ _ _ _ h := Round5.Fwd.bounded_ctxtLabel h
  handler _ _ _ _ _ h := Round5.Fwd.bounded_ctxtHandler h
  frame _ _ _ _ _ h := Round5.Fwd.bounded_ctxtFrame h

/-- Two closed predicates have a closed conjunction. -/
theorem ctxClosedVals_and {V W : Config H → Prop} (hV : Target.CtxClosedVals V)
    (hW : Target.CtxClosedVals W) : Target.CtxClosedVals (fun c => V c ∧ W c) where
  mid s f vs b c h := ⟨hV.mid s f vs b c h.1, hW.mid s f vs b c h.2⟩
  label s f n cont body h := ⟨hV.label s f n cont body h.1, hW.label s f n cont body h.2⟩
  handler s f n cs body h := ⟨hV.handler s f n cs body h.1, hW.handler s f n cs body h.2⟩
  frame s f fi n body h := ⟨hV.frame s f fi n body h.1, hW.frame s f fi n body h.2⟩

/-- `True` is closed under SpecTec's context decompositions. -/
theorem true_closed : Target.CtxClosedVals (fun _ : Config H => True) :=
  ⟨fun _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ => trivial,
    fun _ _ _ _ _ _ => trivial⟩

/-- **The top-level cast steps, forward, under the new reading, from `CastRefOk`** at a
predicate `V` (`fwd_refTestG` & co.). -/
theorem fwdG_top {V : Config H → Prop} (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn V)
    {c c' : Config H} (h : CastTop c c') (hv : V c) : FwdPB (simEnv (BI P hn host)) hn c c' := by
  cases h with
  | testTrue h => exact (Reading.fwd_refTestG K _ _ _ _ hv).1 h
  | testFalse h => exact (Reading.fwd_refTestG K _ _ _ _ hv).2 h
  | castSucceed h => exact (Reading.fwd_refCastG K _ _ _ _ hv).1 h
  | castFail h => exact (Reading.fwd_refCastG K _ _ _ _ hv).2 h
  | brOnCastSucceed h => exact (Reading.fwd_brOnCastG K _ _ _ _ _ _ hv).1 h
  | brOnCastFail h => exact (Reading.fwd_brOnCastG K _ _ _ _ _ _ hv).2 h
  | brOnCastFailSucceed h => exact (Reading.fwd_brOnCastFailG K _ _ _ _ _ _ hv).1 h
  | brOnCastFailFail h => exact (Reading.fwd_brOnCastFailG K _ _ _ _ _ _ hv).2 h

/-- **The top-level cast steps, forward, under the new reading** (track reading's
`castsFwdB_of`). -/
theorem fwdB_top (KB : RefOkBB (simEnv (BI P hn host))) {c c' : Config H} (h : CastTop c c')
    (hb : Bounded c) : FwdPB (simEnv (BI P hn host)) hn c c' :=
  fwdG_top (Reading.castRefOk_bnd KB fun _ h => h.frame) h hb

/-- **Every Core step from a cast redex satisfying `V` is a step of the new reading** between
typed images, from `CastRefOk` at `V`, for `V` closed under the context rules. -/
theorem fwdG_cast {V : Config H → Prop} (CV : Target.CtxClosedVals V)
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn V) {c c' : Config H}
    (h : Step P host c c') (hx : castB c.code = true) :
    V c → FwdPB (simEnv (BI P hn host)) hn c c' :=
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  have R := hasStepRules_simEnv (BI P hn host)
  castStep_rec (M := fun c c' => V c → FwdPB (simEnv (BI P hn host)) hn c c')
    (fun ht hv => fwdG_top K ht hv)
    (fun {s _ f _ vs is _ rest} _ hne _ ih hv => fwdB_ctxtInstrs T R.ctxtInstrs hne
      (ih (CV.mid s f vs is rest hv)))
    (fun {s _ f _ n cont is _} _ _ ih hv =>
      fwdB_ctxtLabel T R.ctxtLabel (ih (CV.label s f n cont is hv)))
    (fun {s _ f _ n cs is _} _ _ ih hv =>
      fwdB_ctxtHandler T R.ctxtHandler (ih (CV.handler s f n cs is hv)))
    (fun {s _ f fi _ n is _} _ _ ih hv =>
      fwdB_ctxtFrame T R.ctxtFrame (ih (CV.frame s f fi n is hv)))
    h hx

/-- **Every Core step from a bounded cast redex is a step of the new reading** between typed
images, from `RefOkBB`. -/
theorem fwdB_cast (KB : RefOkBB (simEnv (BI P hn host))) {c c' : Config H}
    (h : Step P host c c') (hx : castB c.code = true) :
    Bounded c → FwdPB (simEnv (BI P hn host)) hn c c' :=
  fwdG_cast bounded_closed (Reading.castRefOk_bnd KB fun _ h => h.frame) h hx

/-! ## Typed witnesses of the successor -/

section Calls

variable {env : Env}

/-- `CodeCallsTyped` along an append. -/
theorem codeCallsTyped_append : ∀ (a b : List Admin),
    CodeCallsTyped env (a ++ b) ↔ CodeCallsTyped env a ∧ CodeCallsTyped env b
  | [], _ => by simp [CodeCallsTyped]
  | x :: a, b => by
    rw [List.cons_append, CodeCallsTyped, CodeCallsTyped, codeCallsTyped_append a b, and_assoc]

/-- The results of the cast steps have no `CALL_REF`. -/
theorem calls_top {c c' : Config H} (h : CastTop c c') : CodeCallsTyped env c'.code := by
  cases h <;> simp [CodeCallsTyped, AdminCallsTyped, Admin.IsCallRef, constI32, Val.i32,
    Val.toAdmin]

/-- **The successor of a cast redex has typed `CALL_REF`s when its source has.** -/
theorem calls_cast {c c' : Config H} (h : Step P host c c') (hx : castB c.code = true) :
    CodeCallsTyped env c.code → CodeCallsTyped env c'.code :=
  castStep_rec (M := fun c c' => CodeCallsTyped env c.code → CodeCallsTyped env c'.code)
    (fun ht _ => calls_top ht)
    (fun {_ _ _ _ vs is is' rest} _ _ _ ih hc => by
      obtain ⟨hvi, hr⟩ := (codeCallsTyped_append (vals vs ++ is) rest).1 hc
      obtain ⟨hv, hi⟩ := (codeCallsTyped_append (vals vs) is).1 hvi
      exact (codeCallsTyped_append _ rest).2 ⟨(codeCallsTyped_append _ _).2 ⟨hv, ih hi⟩, hr⟩)
    (fun _ _ ih hc => ⟨ih hc.1, trivial⟩)
    (fun _ _ ih hc => ⟨ih hc.1, trivial⟩)
    (fun _ _ ih hc => ⟨ih hc.1, trivial⟩)
    h hx

end Calls

/-- A witness of a bounded configuration is bounded (`Round5.Multi.witnessBnd`). -/
theorem bounded_witness {B : Builtins} {c d : Config H} (hb : Bounded c) (he : Bwd.ConfigEq c d)
    (ht : Typed (simEnv B) hn d) : Bounded d := by
  have hcode := Round5.Multi.witnessBnd B hn _ _ hb.code he ht
  obtain ⟨s, f, code⟩ := c
  obtain ⟨s', f', code'⟩ := d
  obtain ⟨hs, hf, -⟩ := he
  cases hs
  cases hf
  exact ⟨hb.store, hb.storeBnd, hb.frame, hcode⟩

/-- **The forward half of the cast leaf at the backend reading, from `CastRefOk`** at
`Bounded c ∧ W c`, for `W` closed under the context rules and holding at the witness. -/
theorem castsFwdG (hh : HostOk host) {W : Config H → Prop} (CW : Target.CtxClosedVals W)
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn (fun c => Bounded c ∧ W c))
    (c d c' : Config H) (ts : List CValType) (hc : ConfigOk c ts) (hb : BoundedSel c)
    (hsucc : ∀ c₁, Step P host c c₁ → BoundedSel c₁) (hd : SimRel (BI P hn host) hn c d)
    (hw : W d) (hx : Target.CastRedex d.code) (hs : Step P host c c') :
    ∃ d', SimRel (BI P hn host) hn c' d' ∧
      SStepB (simEnv (BI P hn host)) (configV hn d) (configV hn d') := by
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  have hxd : castB d.code = true := castB_of_castRedex hx
  obtain ⟨d', hsd, he'⟩ := Bwd.step_respects hs d hd.1
  have hbd : Bounded d := bounded_witness hb.1.1 hd.1 hd.2
  have hcalls : CodeCallsTyped (simEnv (BI P hn host)) d'.code :=
    calls_cast hsd hxd (Round5.Multi.codeCallsTyped_of_typedV T ((T.config d).1 hd.2).2)
  have htc' : Typed (simEnv (BI P hn host)) hn c' :=
    typed_of_configOk_sel _ hn (Step.preservation hh hc hs).1 (hsucc c' hs)
  have htd' : Typed (simEnv (BI P hn host)) hn d' := Round5.Multi.typed_of_configEq T he' htc' hcalls
  exact ⟨d', ⟨he', htd'⟩,
    fwdG_cast (ctxClosedVals_and bounded_closed CW) K hsd hxd ⟨hbd, hw⟩ hd.2 htd'⟩

/-- **The forward half of the cast leaf at the backend reading**, from a `HostOk` host and
`RefOkBB`: a Core step from a valid, `BoundedSel` configuration whose witness is a cast redex is
matched, from the witness, by a step of the new reading to a typed witness of the successor. -/
theorem castsFwd (hh : HostOk host) (KB : RefOkBB (simEnv (BI P hn host))) (c d c' : Config H)
    (ts : List CValType) (hc : ConfigOk c ts) (hb : BoundedSel c)
    (hsucc : ∀ c₁, Step P host c c₁ → BoundedSel c₁) (hd : SimRel (BI P hn host) hn c d)
    (hx : Target.CastRedex d.code) (hs : Step P host c c') :
    ∃ d', SimRel (BI P hn host) hn c' d' ∧
      SStepB (simEnv (BI P hn host)) (configV hn d) (configV hn d') :=
  castsFwdG hh true_closed (Reading.castRefOk_bnd KB fun _ h => h.1.frame) c d c' ts hc hb hsucc
    hd trivial hx hs

end Silmaril.Wasm.SpecTec.Sim.Round6.Casts
