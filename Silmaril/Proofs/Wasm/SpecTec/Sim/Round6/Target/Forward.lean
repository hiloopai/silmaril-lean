module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Target.Cast
public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Convert.Thms

/-!
# Round 6: the forward recursion up to Core's choice, away from casts

`forwardR` is `Round5.Fwd.forward5` at the concrete builtins with two changes:

* the vector steps come from `Round5.Convert.vectorFwdR_builtins`: SpecTec
  matches *a* Core vector step from the same code, the given one when Core's is unique;
* sources whose redex is a cast (`CastRedex`) are excluded, so no cast obligation, and hence no
  `Round5.Fwd.RefOkB`, is needed; every other field of `Round5.Fwd.Obl` is discharged as in
  `Round5.FwdRef.oblT` and `Round5.FwdRef.forward_validT`.

The motive is `FwdUp c c' ∨ FwdUpR c c'`: every rule but the vector one gives `FwdUp`; the
context rules carry `FwdUpR` outwards, using that a context's successor determines its hole's
(`step_ctxt*_inj`). `fwd_referenceNC` is `Round5.Fwd.fwd_reference5` with the four cast
constructors excluded by `CastRedex`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Target

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4 (Bounded)
open Round4Int (BI)
open FwdMem (FwdUp fwdUp_of_fwdP)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **A Core step `c → c'`, matched up to Core's choice**: SpecTec steps (up to call annotations)
to the image of a Core successor `c''` of `c`, which is `c'` when `c'` is the only one. -/
def FwdUpR (P : Profile) (host : HostSemantics H) (B : Builtins) (hn : H → String)
    (c c' : Config H) : Prop :=
  ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
    FwdUp (simEnv B) hn c c''

/-- An exact match is a match up to choice. -/
theorem fwdUpR_of_fwdUp {B : Builtins} {c c' : Config H} (hs : Step P host c c')
    (h : FwdUp (simEnv B) hn c c') : FwdUpR P host B hn c c' :=
  ⟨c', hs, fun _ => rfl, h⟩

/-! ## The reference steps away from casts -/

/-- **The reference steps whose redex is not a cast** (`Round5.Fwd.fwd_reference5` without its
four cast constructors). -/
theorem fwd_referenceNC {c c' : Config H} (h : RefStep c c') (hb : Bounded c)
    (hx : ¬ CastRedex c.code) : FwdP (simEnv (BI P hn host)) hn c c' := by
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  have R := Typing.rTyping_simEnv (BI P hn host)
  have F : RefsGC.RFuns (simEnv (BI P hn host)) := Prims.rFuns_builtins hn host
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Round5.Fwd.rStore_builtins hn host
  have Pr : HasRuleAt (simEnv (BI P hn host)) "Step" "%~>%" 0 Equiv.ExecStepRules.pureRule :=
    (hasStepRules_simEnv _).pure
  have Q : HasRuleAt (simEnv (BI P hn host)) "Step" "%~>%" 1 Equiv.ExecStepRules.readRule :=
    (hasStepRules_simEnv _).read
  have rr : Equiv.ExecRef.HasRefRules (envOfScript Specs.wasm30) := Equiv.ExecRef.hasRefRules_wasm30
  have rd : Equiv.ExecRead.HasReadRules (envOfScript Specs.wasm30) :=
    Equiv.ExecRead.hasReadRules_wasm30
  have pt := RefsGC.pureTable_simEnv (BI P hn host)
  have _ := hb
  cases h with
  | refNull ht =>
      exact RefsGC.fwd_of_sread T Q fun hz hc =>
        RefsGC.sread_refNull (hasRuleAt_simEnv _ rd.refNull) R hz hc
  | refFunc ha =>
      exact RefsGC.fwd_of_sread T Q fun hz hc =>
        RefsGC.sread_refFunc (hasRuleAt_simEnv _ rd.refFunc) R G ha hz hc
  | refI31 i =>
      exact RefsGC.fwd_of_spure T Pr fun _ => RefsGC.spure_refI31 (RefsGC.refRule _ rr.refI31) R F i
  | isNullTrue =>
      exact RefsGC.fwd_of_spure T Pr fun hc =>
        RefsGC.spure_isNullTrue (RefsGC.refRule _ rr.refIsNullTrue)
          (R.ref _ (RefsGC.typed_head T hc))
  | isNullFalse hr =>
      exact RefsGC.fwd_of_spure T Pr fun hc => RefsGC.spure_isNullFalse
        (RefsGC.refRule _ rr.refIsNullFalse) (RefsGC.refRule _ rr.refIsNullTrue) pt hr
        (R.ref _ (RefsGC.typed_head T hc))
  | asNonNullNull =>
      exact RefsGC.fwd_of_spure T Pr fun hc =>
        RefsGC.spure_asNonNullNull (RefsGC.refRule _ rr.refAsNonNullNull)
          (R.ref _ (RefsGC.typed_head T hc))
  | asNonNullAddr hr =>
      exact RefsGC.fwd_of_spure T Pr fun hc => RefsGC.spure_asNonNullAddr
        (RefsGC.refRule _ rr.refAsNonNullAddr) (RefsGC.refRule _ rr.refAsNonNullNull) pt hr
        (R.ref _ (RefsGC.typed_head T hc))
  | eqNull =>
      exact RefsGC.fwd_of_spure T Pr fun hc =>
        RefsGC.spure_eqNull (RefsGC.refRule _ rr.refEqNull) (R.ref _ (RefsGC.typed_head T hc))
  | eqTrue hr =>
      exact RefsGC.fwd_of_spure T Pr fun hc => RefsGC.spure_eqTrue (RefsGC.refRule _ rr.refEqTrue)
        (RefsGC.refRule _ rr.refEqNull) pt hr (R.ref _ (RefsGC.typed_head T hc))
  | eqFalse hr =>
      exact RefsGC.fwd_of_spure T Pr fun hc => RefsGC.spure_eqFalse
        (RefsGC.refRule _ rr.refEqFalse) (RefsGC.refRule _ rr.refEqNull)
        (RefsGC.refRule _ rr.refEqTrue) pt hr (R.ref _ (RefsGC.typed_head T hc))
        (R.ref _ (RefsGC.typed_head T (RefsGC.typed_tail T hc)))
  | testTrue _ => exact absurd castRedex_refTest hx
  | testFalse _ => exact absurd castRedex_refTest hx
  | castSucceed _ => exact absurd castRedex_refCast hx
  | castFail _ => exact absurd castRedex_refCast hx
  | i31GetNull sx =>
      exact RefsGC.fwd_of_spure T Pr fun _ =>
        RefsGC.spure_i31GetNull (RefsGC.refRule _ rr.i31GetNull) R sx
  | i31GetNum sx i =>
      exact RefsGC.fwd_of_spure T Pr fun _ =>
        RefsGC.spure_i31GetNum (RefsGC.refRule _ rr.i31GetNum) R F sx i
  | externConvertNull =>
      exact RefsGC.fwd_of_spure T Pr fun hc =>
        RefsGC.spure_externConvertNull (RefsGC.refRule _ rr.externConvertAnyNull)
          (R.ref _ (RefsGC.typed_head T hc))
  | externConvertAddr hr =>
      exact RefsGC.fwd_of_spure T Pr fun hc => RefsGC.spure_externConvertAddr
        (RefsGC.refRule _ rr.externConvertAnyAddr) (RefsGC.refRule _ rr.externConvertAnyNull) pt hr
        (R.ref _ (RefsGC.typed_head T hc))
  | anyConvertNull =>
      exact RefsGC.fwd_of_spure T Pr fun _ =>
        RefsGC.spure_anyConvertNull (RefsGC.refRule _ rr.anyConvertExternNull)
  | anyConvertAddr r =>
      exact RefsGC.fwd_of_spure T Pr fun hc =>
        RefsGC.spure_anyConvertAddr (RefsGC.refRule _ rr.anyConvertExternAddr)
          (R.externArg r (RefsGC.typed_head T hc))

/-! ## The vector steps, up to choice -/

/-- **The vector steps**: the bitwise operators exactly, the others up to Core's choice
(`Round5.Convert.vectorFwdR_builtins`). -/
theorem fwd_vectorR {s : Store H} {f : Frame} {is is' : List Admin} (h : VectorStep P is is')
    (hb : Bounded ⟨s, f, is⟩) :
    FwdUp (simEnv (BI P hn host)) hn ⟨s, f, is⟩ ⟨s, f, is'⟩ ∨
      FwdUpR P host (BI P hn host) hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  have hV := FwdSimdAgg.vvB_builtins (prof := P) hn host
  have h' := h
  cases h with
  | vecUnOp op a => exact .inl (fwdUp_of_fwdP (FwdSimdAgg.fwd_vecUnOp hV op a))
  | vecBinOp op a b =>
      exact .inl (fwdUp_of_fwdP (FwdSimdAgg.fwd_vecBinOp (Prims.intB_builtins hn host) hV op a b))
  | vecTernOp op a b c => exact .inl (fwdUp_of_fwdP (FwdSimdAgg.fwd_vecTernOp hV op a b c))
  | vecTestOp op a => exact .inl (fwdUp_of_fwdP (FwdSimdAgg.fwd_vecTestOp op a))
  | _ =>
      obtain ⟨is'', hs'', hu, hf⟩ := Round5.Convert.vectorFwdR_builtins (hn := hn) (host := host)
        s f _ _ h' (by simp [R4Fwd.VecArith, vconst]) hb
      refine .inr ⟨⟨s, f, is''⟩, .vector hs'', fun hU => ?_, fwdUp_of_fwdP hf⟩
      have e : is'' = _ := hu fun is₃ h₃ => by
        have := hU ⟨s, f, is₃⟩ (.vector h₃)
        simp only [Config.mk.injEq, true_and] at this
        exact this
      rw [e]

/-! ## The context rules -/

/-- `ctxt-instrs` is injective in its hole. -/
theorem step_ctxtInstrs_inj {s₁ s₂ : Store H} {f₁ f₂ : Frame} {vs : List Val}
    {k₁ k₂ rest : List Admin}
    (h : (⟨s₁, f₁, vals vs ++ k₁ ++ rest⟩ : Config H) = ⟨s₂, f₂, vals vs ++ k₂ ++ rest⟩) :
    (⟨s₁, f₁, k₁⟩ : Config H) = ⟨s₂, f₂, k₂⟩ := by
  simp only [Config.mk.injEq, List.append_cancel_right_eq, List.append_cancel_left_eq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

/-- `ctxt-instrs`, up to choice. -/
theorem fwdOr_ctxtInstrs {s s' : Store H} {f f' : Frame} {vs : List Val}
    {is is' rest : List Admin} (h : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩)
    (hne : vs ≠ [] ∨ rest ≠ [])
    (ih : FwdUp (simEnv (BI P hn host)) hn ⟨s, f, is⟩ ⟨s', f', is'⟩ ∨
      FwdUpR P host (BI P hn host) hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdUp (simEnv (BI P hn host)) hn ⟨s, f, vals vs ++ is ++ rest⟩
        ⟨s', f', vals vs ++ is' ++ rest⟩ ∨
      FwdUpR P host (BI P hn host) hn ⟨s, f, vals vs ++ is ++ rest⟩
        ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  rcases ih with ih | ⟨⟨s₂, f₂, k⟩, hst, hu, hf⟩
  · exact .inl (FwdMem.fwdUp_ctxtInstrs T hne ih)
  refine .inr ⟨⟨s₂, f₂, vals vs ++ k ++ rest⟩, .ctxtInstrs hst hne, fun hU => ?_,
    FwdMem.fwdUp_ctxtInstrs T hne hf⟩
  have e : (⟨s₂, f₂, k⟩ : Config H) = ⟨s', f', is'⟩ := hu fun ⟨a, b, k₃⟩ h₃ =>
    step_ctxtInstrs_inj (hU _ (.ctxtInstrs h₃ hne))
  simp only [Config.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  rfl

/-- `ctxt-label`, up to choice. -/
theorem fwdOr_ctxtLabel {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
    {is is' : List Admin} (h : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩)
    (ih : FwdUp (simEnv (BI P hn host)) hn ⟨s, f, is⟩ ⟨s', f', is'⟩ ∨
      FwdUpR P host (BI P hn host) hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdUp (simEnv (BI P hn host)) hn ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ ∨
      FwdUpR P host (BI P hn host) hn ⟨s, f, [.label n cont is]⟩
        ⟨s', f', [.label n cont is']⟩ := by
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  rcases ih with ih | ⟨⟨s₂, f₂, k⟩, hst, hu, hf⟩
  · exact .inl (FwdMem.fwdUp_ctxtLabel T ih)
  refine .inr ⟨⟨s₂, f₂, [.label n cont k]⟩, .ctxtLabel hst, fun hU => ?_,
    FwdMem.fwdUp_ctxtLabel T hf⟩
  have e : (⟨s₂, f₂, k⟩ : Config H) = ⟨s', f', is'⟩ := hu fun ⟨a, b, k₃⟩ h₃ => by
    have e₃ := hU _ (.ctxtLabel (n := n) (cont := cont) h₃)
    simp only [Config.mk.injEq, List.cons.injEq, Admin.label.injEq, true_and, and_true] at e₃
    obtain ⟨rfl, rfl, rfl⟩ := e₃
    rfl
  simp only [Config.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  rfl

/-- `ctxt-handler`, up to choice. -/
theorem fwdOr_ctxtHandler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch}
    {is is' : List Admin} (h : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩)
    (ih : FwdUp (simEnv (BI P hn host)) hn ⟨s, f, is⟩ ⟨s', f', is'⟩ ∨
      FwdUpR P host (BI P hn host) hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdUp (simEnv (BI P hn host)) hn ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩ ∨
      FwdUpR P host (BI P hn host) hn ⟨s, f, [.handler n cs is]⟩
        ⟨s', f', [.handler n cs is']⟩ := by
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  rcases ih with ih | ⟨⟨s₂, f₂, k⟩, hst, hu, hf⟩
  · exact .inl (FwdMem.fwdUp_ctxtHandler T ih)
  refine .inr ⟨⟨s₂, f₂, [.handler n cs k]⟩, .ctxtHandler hst, fun hU => ?_,
    FwdMem.fwdUp_ctxtHandler T hf⟩
  have e : (⟨s₂, f₂, k⟩ : Config H) = ⟨s', f', is'⟩ := hu fun ⟨a, b, k₃⟩ h₃ => by
    have e₃ := hU _ (.ctxtHandler (n := n) (cs := cs) h₃)
    simp only [Config.mk.injEq, List.cons.injEq, Admin.handler.injEq, true_and, and_true] at e₃
    obtain ⟨rfl, rfl, rfl⟩ := e₃
    rfl
  simp only [Config.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  rfl

/-- `ctxt-frame`, up to choice. -/
theorem fwdOr_ctxtFrame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (h : Step P host ⟨s, fi, is⟩ ⟨s', fi', is'⟩)
    (ih : FwdUp (simEnv (BI P hn host)) hn ⟨s, fi, is⟩ ⟨s', fi', is'⟩ ∨
      FwdUpR P host (BI P hn host) hn ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
    FwdUp (simEnv (BI P hn host)) hn ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ ∨
      FwdUpR P host (BI P hn host) hn ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ := by
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  rcases ih with ih | ⟨⟨s₂, f₂, k⟩, hst, hu, hf⟩
  · exact .inl (FwdMem.fwdUp_ctxtFrame T ih)
  refine .inr ⟨⟨s₂, f, [.frame n f₂ k]⟩, .ctxtFrame hst, fun hU => ?_,
    FwdMem.fwdUp_ctxtFrame T hf⟩
  have e : (⟨s₂, f₂, k⟩ : Config H) = ⟨s', fi', is'⟩ := hu fun ⟨a, b, k₃⟩ h₃ => by
    have e₃ := hU _ (.ctxtFrame (f := f) (n := n) h₃)
    simp only [Config.mk.injEq, List.cons.injEq, Admin.frame.injEq, true_and, and_true] at e₃
    obtain ⟨rfl, rfl, rfl⟩ := e₃
    rfl
  simp only [Config.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  rfl

/-! ## The recursion -/

/-- **The forward simulation up to Core's choice, from bounded configurations whose redex is not
a cast**, at the concrete builtins, for an injective encoding and a finite host. Nothing is
assumed: every leaf is a proved round-5 lemma. -/
theorem forwardR (hinj : Function.Injective hn) (hf : HostFinite host) {c c' : Config H}
    (h : Step P host c c') : Bounded c → ¬ CastRedex c.code →
      FwdUp (simEnv (BI P hn host)) hn c c' ∨ FwdUpR P host (BI P hn host) hn c c' :=
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  have Ty := Typing.ctrlTyping_simEnv (BI P hn host)
  have St := Typing.stateTyping_simEnv (BI P hn host)
  have X := Typing.exnTyping_simEnv' (BI P hn host)
  have TB := Round5.Int.typesB (BI P hn host)
  have hr := Round5.FwdRef2.hostRespectsT_all (BI P hn host) hinj host
  have U {c c' : Config H} (h : FwdP (simEnv (BI P hn host)) hn c c') :
      FwdUp (simEnv (BI P hn host)) hn c c' ∨ FwdUpR P host (BI P hn host) hn c c' :=
    .inl (fwdUp_of_fwdP h)
  Step.rec (motive := fun c c' _ => Bounded c → ¬ CastRedex c.code →
      FwdUp (simEnv (BI P hn host)) hn c c' ∨ FwdUpR P host (BI P hn host) hn c c')
    (fun hs _ _ => U (IntNumeric.fwd_parametric T hs))
    (fun hs _ _ => U (Round5.Fwd.fwd_numeric5 hs))
    (fun hs hb _ => fwd_vectorR hs hb)
    (fun hs _ _ => U (State.fwd_variable_ _ T St hs))
    (fun hs hb _ => U (Memory.fwd_table_bounded _ T St (ConfigOk.memTyping_simEnv _)
      (RefOk.growFuns_builtins hn host) (ConfigOk.instTyping_simEnv _) hs hb.store.tables))
    (fun hs hb _ => U (Round5.Fwd.fwd_memory5 hs hb))
    (fun hs hb hx => U (fwd_referenceNC hs hb hx))
    (fun hs hb _ => U (Round5.Fwd.fwd_aggregate5 (Round5.Fwd.aggTypesB_of TB)
      (Round5.FwdRef.newDataNumB_builtins hn host) (Round5.Fwd.initDataZeroB_builtins hn host)
      hs hb))
    (fun h hne ih hb hx => fwdOr_ctxtInstrs h hne
      (ih (Round5.Fwd.bounded_ctxtInstrs hb) (not_castRedex_mid hx)))
    (fun h ih hb hx => fwdOr_ctxtLabel h
      (ih (Round5.Fwd.bounded_ctxtLabel hb) (not_castRedex_label hx)))
    (fun h ih hb hx => fwdOr_ctxtHandler h
      (ih (Round5.Fwd.bounded_ctxtHandler hb) (not_castRedex_handler hx)))
    (fun h ih hb hx => fwdOr_ctxtFrame h
      (ih (Round5.Fwd.bounded_ctxtFrame hb) (not_castRedex_frame hx)))
    (fun h₁ h₂ hb _ => U (Round5.Fwd.fwd_block5 TB h₁ h₂ hb.frame))
    (fun h₁ h₂ hb _ => U (Round5.Fwd.fwd_loop5 TB h₁ h₂ hb.frame))
    (fun h₁ _ _ => U (fwd_ifTrue _ T Ty h₁))
    (fun _ _ => U (fwd_ifFalse _ T Ty))
    (fun _ _ => U (fwd_labelVals _ T))
    (fun h₁ h₂ _ _ => U (fwd_brLabelZero _ T Ty h₁ h₂))
    (fun h₁ _ _ => U (fwd_brLabelSucc _ T Ty h₁))
    (fun _ _ => U (fwd_brHandler _ T Ty))
    (fun h₁ _ _ => U (fwd_brIfTrue _ T Ty h₁))
    (fun _ _ => U (fwd_brIfFalse _ T Ty))
    (fun h₁ _ _ => U (fwd_brTableLt _ T Ty h₁))
    (fun h₁ _ _ => U (fwd_brTableGe _ T Ty h₁))
    (fun _ _ => U (fwd_brOnNullNull _ T Ty))
    (fun h₁ _ _ => U (fwd_brOnNullAddr _ T Ty h₁))
    (fun _ _ => U (fwd_brOnNonNullNull _ T Ty))
    (fun h₁ _ _ => U (fwd_brOnNonNullAddr _ T Ty h₁))
    (fun _ _ hx => absurd castRedex_brOnCast hx)
    (fun _ _ hx => absurd castRedex_brOnCast hx)
    (fun _ _ hx => absurd castRedex_brOnCastFail hx)
    (fun _ _ hx => absurd castRedex_brOnCastFail hx)
    (fun h₁ h₂ _ _ => U (Round5.Fwd.fwd_call5 h₁ h₂))
    (fun h₁ _ _ => U (fwd_callRefNull _ T Ty h₁))
    (fun hc hfa hex hlen hcode hb _ => U (Round5.Fwd.fwd_callRefFunc5 TB hc hfa hex hlen hcode
      (Round5.Fwd.tyBnd_funcType hb.storeBnd hfa)))
    (fun hc hfa hex hlen hcode hh hb _ => U (Round5.FwdRef.fwd_callRefHostT TB hf hr hc hfa hex
      hlen hcode hh (Round5.Fwd.tyBnd_funcType hb.storeBnd hfa)))
    (fun hc hfa hex hlen hcode hh hb _ => U (Round5.FwdRef.fwd_callRefHostDivT TB hf hr hc hfa
      hex hlen hcode hh (Round5.Fwd.tyBnd_funcType hb.storeBnd hfa)))
    (fun h₁ h₂ _ _ => U (Round5.Fwd.fwd_returnCall5 h₁ h₂))
    (fun h₁ _ _ => U (fwd_returnCallRefLabel _ T Ty h₁))
    (fun h₁ _ _ => U (fwd_returnCallRefHandler _ T Ty h₁))
    (fun h₁ _ _ => U (fwd_returnCallRefFrameNull _ T Ty h₁))
    (fun hc hfn hex hlen hb _ => .inl (Round5.Fwd.fwdUp_returnCallRefFrameAddr5 TB hc hfn hex hlen
      (Round5.Fwd.tyBnd_funcType hb.storeBnd hfn)))
    (fun _ _ => U (fwd_callIndirect _ T Ty))
    (fun _ _ => U (fwd_returnCallIndirect _ T Ty))
    (fun h₁ _ _ => U (fwd_frameVals _ T h₁))
    (fun h₁ _ _ => U (fwd_returnFrame _ T Ty h₁))
    (fun _ _ => U (fwd_returnLabel _ T))
    (fun _ _ => U (fwd_returnHandler _ T))
    (fun htag hex hlen hb _ => U (Round5.Fwd.fwd_throw5 TB htag hex hlen hb.storeBnd))
    (fun _ _ => U (Exn.fwd_throwRefNull _ T))
    (fun h₁ _ _ => U (Exn.fwd_throwRefInstrs _ T X h₁))
    (fun _ _ => U (Exn.fwd_throwRefLabel _ T X))
    (fun _ _ => U (Exn.fwd_throwRefFrame _ T X))
    (fun _ _ => U (Exn.fwd_throwRefHandlerEmpty _ T X))
    (fun he ht _ _ => U (Round5.Fwd.fwd_throwRefHandlerCatch5 he ht))
    (fun he ht _ _ => U (Round5.Fwd.fwd_throwRefHandlerCatchRef5 he ht))
    (fun _ _ => U (Exn.fwd_throwRefHandlerCatchAll _ T X))
    (fun _ _ => U (Exn.fwd_throwRefHandlerCatchAllRef _ T X))
    (fun hnm _ _ => U (Round5.Fwd.fwd_throwRefHandlerNext5 hnm))
    (fun h₁ h₂ hb _ => U (Round5.Fwd.fwd_tryTable5 TB h₁ h₂ hb.frame))
    (fun _ _ => U (Exn.fwd_handlerVals _ T))
    (fun h₁ _ _ => U (fwd_trapInstrs _ T h₁))
    (fun _ _ => U (fwd_trapLabel _ T))
    (fun _ _ => U (fwd_trapHandler _ T))
    (fun _ _ => U (fwd_trapFrame _ T))
    h

/-- **`forwardR`, as a match up to choice.** -/
theorem forwardR' (hinj : Function.Injective hn) (hf : HostFinite host) {c c' : Config H}
    (h : Step P host c c') (hb : Bounded c) (hx : ¬ CastRedex c.code) :
    FwdUpR P host (BI P hn host) hn c c' :=
  (forwardR hinj hf h hb hx).elim (fwdUpR_of_fwdUp h) id

end Silmaril.Wasm.SpecTec.Sim.Round6.Target
