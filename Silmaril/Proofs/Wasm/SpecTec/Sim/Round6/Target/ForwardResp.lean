module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Target.Forward
public import Silmaril.Wasm.SpecTec.Sim.Round5.Multi.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int2.Thms

/-!
# Round 6: the forward recursion up to choice, from every SpecTec witness

`fwdRespOr` is `Round5.Multi.fwdResp_of_step_host` (the forward simulation from
**every** typed SpecTec witness `d ≈ c`, `FwdResp`) with `forwardR` for `Round5.Fwd.forward5`:
the rules whose left-hand side is `deep` (no `CALL_REF`) go through `forwardR` at the source
itself (`respOr_deep`), which handles the vector rules up to Core's choice and excludes cast
redexes; the other base cases are track multi's, unchanged; the context rules carry the choice
outwards (`respOr_ctxt*`, as `fwdOr_ctxt*`). No `Round5.Fwd.Obl` is needed.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Target

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4 (Bounded)
open Round4Int (BI)
open FwdMem (FwdUp fwdUp_of_fwdP)
open Round5.Multi (FwdResp resp_deep resp_prefix resp_labelPrefix resp_handlerPrefix
  resp_framePrefix resp_call resp_callDiv)
open _root_.Silmaril.Wasm.SpecTec.Sim.Bwd (ConfigEq CodeEq codeDeep codeDeep_app codeDeep_vals
  deep_vals_app codeDeep_one codeDeep_two isReturnCallRef_deep)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **A Core step `c → c'`, matched up to Core's choice from every witness**: `FwdResp` to a
Core successor `c''` of `c`, which is `c'` when `c'` is the only one. -/
def FwdRespR (P : Profile) (host : HostSemantics H) (B : Builtins) (hn : H → String)
    (c c' : Config H) : Prop :=
  ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
    FwdResp (simEnv B) hn c c''

/-- A step whose left-hand side has no `CALL_REF`: the witness is the source. -/
theorem respOr_deep {B : Builtins} {c c' : Config H} (hp : codeDeep c.code = true)
    (h : FwdUp (simEnv B) hn c c' ∨ FwdUpR P host B hn c c') :
    FwdResp (simEnv B) hn c c' ∨ FwdRespR P host B hn c c' :=
  h.imp (resp_deep hp) fun ⟨c'', hs, hu, hf⟩ => ⟨c'', hs, hu, resp_deep hp hf⟩

/-- `ctxt-instrs`, from every witness, up to choice. -/
theorem respOr_ctxtInstrs {s s' : Store H} {f f' : Frame} {vs : List Val}
    {is is' rest : List Admin} (h : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩)
    (hne : vs ≠ [] ∨ rest ≠ [])
    (ih : FwdResp (simEnv (BI P hn host)) hn ⟨s, f, is⟩ ⟨s', f', is'⟩ ∨
      FwdRespR P host (BI P hn host) hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdResp (simEnv (BI P hn host)) hn ⟨s, f, vals vs ++ is ++ rest⟩
        ⟨s', f', vals vs ++ is' ++ rest⟩ ∨
      FwdRespR P host (BI P hn host) hn ⟨s, f, vals vs ++ is ++ rest⟩
        ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  rcases ih with ih | ⟨⟨s₂, f₂, k⟩, hst, hu, hf⟩
  · exact .inl (Round5.Multi.resp_ctxtInstrs T hne ih)
  refine .inr ⟨⟨s₂, f₂, vals vs ++ k ++ rest⟩, .ctxtInstrs hst hne, fun hU => ?_,
    Round5.Multi.resp_ctxtInstrs T hne hf⟩
  have e : (⟨s₂, f₂, k⟩ : Config H) = ⟨s', f', is'⟩ := hu fun ⟨a, b, k₃⟩ h₃ =>
    step_ctxtInstrs_inj (hU _ (.ctxtInstrs h₃ hne))
  simp only [Config.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  rfl

/-- `ctxt-label`, from every witness, up to choice. -/
theorem respOr_ctxtLabel {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
    {is is' : List Admin} (h : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩)
    (ih : FwdResp (simEnv (BI P hn host)) hn ⟨s, f, is⟩ ⟨s', f', is'⟩ ∨
      FwdRespR P host (BI P hn host) hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdResp (simEnv (BI P hn host)) hn ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ ∨
      FwdRespR P host (BI P hn host) hn ⟨s, f, [.label n cont is]⟩
        ⟨s', f', [.label n cont is']⟩ := by
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  rcases ih with ih | ⟨⟨s₂, f₂, k⟩, hst, hu, hf⟩
  · exact .inl (Round5.Multi.resp_ctxtLabel T ih)
  refine .inr ⟨⟨s₂, f₂, [.label n cont k]⟩, .ctxtLabel hst, fun hU => ?_,
    Round5.Multi.resp_ctxtLabel T hf⟩
  have e : (⟨s₂, f₂, k⟩ : Config H) = ⟨s', f', is'⟩ := hu fun ⟨a, b, k₃⟩ h₃ => by
    have e₃ := hU _ (.ctxtLabel (n := n) (cont := cont) h₃)
    simp only [Config.mk.injEq, List.cons.injEq, Admin.label.injEq, true_and, and_true] at e₃
    obtain ⟨rfl, rfl, rfl⟩ := e₃
    rfl
  simp only [Config.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  rfl

/-- `ctxt-handler`, from every witness, up to choice. -/
theorem respOr_ctxtHandler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch}
    {is is' : List Admin} (h : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩)
    (ih : FwdResp (simEnv (BI P hn host)) hn ⟨s, f, is⟩ ⟨s', f', is'⟩ ∨
      FwdRespR P host (BI P hn host) hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdResp (simEnv (BI P hn host)) hn ⟨s, f, [.handler n cs is]⟩
        ⟨s', f', [.handler n cs is']⟩ ∨
      FwdRespR P host (BI P hn host) hn ⟨s, f, [.handler n cs is]⟩
        ⟨s', f', [.handler n cs is']⟩ := by
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  rcases ih with ih | ⟨⟨s₂, f₂, k⟩, hst, hu, hf⟩
  · exact .inl (Round5.Multi.resp_ctxtHandler T ih)
  refine .inr ⟨⟨s₂, f₂, [.handler n cs k]⟩, .ctxtHandler hst, fun hU => ?_,
    Round5.Multi.resp_ctxtHandler T hf⟩
  have e : (⟨s₂, f₂, k⟩ : Config H) = ⟨s', f', is'⟩ := hu fun ⟨a, b, k₃⟩ h₃ => by
    have e₃ := hU _ (.ctxtHandler (n := n) (cs := cs) h₃)
    simp only [Config.mk.injEq, List.cons.injEq, Admin.handler.injEq, true_and, and_true] at e₃
    obtain ⟨rfl, rfl, rfl⟩ := e₃
    rfl
  simp only [Config.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  rfl

/-- `ctxt-frame`, from every witness, up to choice. -/
theorem respOr_ctxtFrame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (h : Step P host ⟨s, fi, is⟩ ⟨s', fi', is'⟩)
    (ih : FwdResp (simEnv (BI P hn host)) hn ⟨s, fi, is⟩ ⟨s', fi', is'⟩ ∨
      FwdRespR P host (BI P hn host) hn ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
    FwdResp (simEnv (BI P hn host)) hn ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ ∨
      FwdRespR P host (BI P hn host) hn ⟨s, f, [.frame n fi is]⟩
        ⟨s', f, [.frame n fi' is']⟩ := by
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  rcases ih with ih | ⟨⟨s₂, f₂, k⟩, hst, hu, hf⟩
  · exact .inl (Round5.Multi.resp_ctxtFrame T ih)
  refine .inr ⟨⟨s₂, f, [.frame n f₂ k]⟩, .ctxtFrame hst, fun hU => ?_,
    Round5.Multi.resp_ctxtFrame T hf⟩
  have e : (⟨s₂, f₂, k⟩ : Config H) = ⟨s', fi', is'⟩ := hu fun ⟨a, b, k₃⟩ h₃ => by
    have e₃ := hU _ (.ctxtFrame (f := f) (n := n) h₃)
    simp only [Config.mk.injEq, List.cons.injEq, Admin.frame.injEq, true_and, and_true] at e₃
    obtain ⟨rfl, rfl, rfl⟩ := e₃
    rfl
  simp only [Config.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  rfl

/-- **The forward simulation up to Core's choice from every typed witness**, from bounded
configurations whose redex is not a cast, at the concrete builtins, for an injective encoding
and a finite host. No open leaf. -/
theorem fwdRespOr (hinj : Function.Injective hn) (hf : HostFinite host) {c c' : Config H}
    (h : Step P host c c') : Bounded c → ¬ CastRedex c.code →
      FwdResp (simEnv (BI P hn host)) hn c c' ∨ FwdRespR P host (BI P hn host) hn c c' :=
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  have Ty := Typing.ctrlTyping_simEnv (BI P hn host)
  have X := Typing.exnTyping_simEnv' (BI P hn host)
  have TB := Round5.Int.typesB (BI P hn host)
  have HC := Round5.Int2.hostCallsFwdT hf
    (Round5.FwdRef2.hostRespectsT_all (BI P hn host) hinj host)
  have U {c c' : Config H} (hp : codeDeep c.code = true) (hs : Step P host c c')
      (hb : Bounded c) (hx : ¬ CastRedex c.code) :
      FwdResp (simEnv (BI P hn host)) hn c c' ∨ FwdRespR P host (BI P hn host) hn c c' :=
    respOr_deep hp (forwardR hinj hf hs hb hx)
  have V {c c' : Config H} (h : FwdP (simEnv (BI P hn host)) hn c c') :
      FwdUp (simEnv (BI P hn host)) hn c c' := fwdUp_of_fwdP h
  Step.rec (motive := fun c c' _ => Bounded c → ¬ CastRedex c.code →
      FwdResp (simEnv (BI P hn host)) hn c c' ∨ FwdRespR P host (BI P hn host) hn c c')
    (fun hs => U (Bwd.parametric_deep hs) (.parametric hs))
    (fun hs => U (Bwd.numeric_deep hs) (.numeric hs))
    (fun hs => U (Bwd.vector_deep hs) (.vector hs))
    (fun hs => U (Bwd.variable_deep hs) (.variable hs))
    (fun hs => U (Bwd.table_deep hs) (.table hs))
    (fun hs => U (Bwd.memory_deep hs) (.memory hs))
    (fun hs => U (Bwd.reference_deep hs) (.reference hs))
    (fun hs => U (Bwd.aggregate_deep hs) (.aggregate hs))
    (fun h hne ih hb hx => respOr_ctxtInstrs h hne
      (ih (Round5.Fwd.bounded_ctxtInstrs hb) (not_castRedex_mid hx)))
    (fun h ih hb hx => respOr_ctxtLabel h
      (ih (Round5.Fwd.bounded_ctxtLabel hb) (not_castRedex_label hx)))
    (fun h ih hb hx => respOr_ctxtHandler h
      (ih (Round5.Fwd.bounded_ctxtHandler hb) (not_castRedex_handler hx)))
    (fun h ih hb hx => respOr_ctxtFrame h
      (ih (Round5.Fwd.bounded_ctxtFrame hb) (not_castRedex_frame hx)))
    (fun h₁ h₂ => U (deep_vals_app _ rfl) (.block h₁ h₂))
    (fun h₁ h₂ => U (deep_vals_app _ rfl) (.loop h₁ h₂))
    (fun h₁ => U rfl (.ifTrue h₁))
    (U rfl .ifFalse)
    (U (Bwd.codeDeep_label1 (codeDeep_vals _)) .labelVals)
    (fun h₁ h₂ _ _ => .inl (resp_labelPrefix (codeDeep_app (deep_vals_app _ (codeDeep_vals _)) rfl)
      fun _ => V (fwd_brLabelZero _ T Ty h₁ h₂)))
    (fun h₁ _ _ => .inl (resp_labelPrefix (deep_vals_app _ rfl) fun _ =>
      V (fwd_brLabelSucc _ T Ty h₁)))
    (fun _ _ => .inl (resp_handlerPrefix (deep_vals_app _ rfl) fun _ => V (fwd_brHandler _ T Ty)))
    (fun h₁ => U rfl (.brIfTrue h₁))
    (U rfl .brIfFalse)
    (fun h₁ => U rfl (.brTableLt h₁))
    (fun h₁ => U rfl (.brTableGe h₁))
    (U rfl .brOnNullNull)
    (fun h₁ => U (codeDeep_two (Bwd.deep_toAdmin _) rfl) (.brOnNullAddr h₁))
    (U rfl .brOnNonNullNull)
    (fun h₁ => U (codeDeep_two (Bwd.deep_toAdmin _) rfl) (.brOnNonNullAddr h₁))
    (fun h₁ => U rfl (.brOnCastSucceed h₁))
    (fun h₁ => U rfl (.brOnCastFail h₁))
    (fun h₁ => U rfl (.brOnCastFailSucceed h₁))
    (fun h₁ => U rfl (.brOnCastFailFail h₁))
    (fun h₁ h₂ => U rfl (.call h₁ h₂))
    (fun h₁ _ _ => .inl (resp_call (q := []) rfl rfl h₁ fun _ h => V (fwd_callRefNull _ T Ty h)))
    (fun h₁ h₂ h₃ h₄ h₅ hb _ => .inl (resp_call (codeDeep_vals _) rfl h₁ fun _ h =>
      V (Round5.Fwd.fwd_callRefFunc5 TB h h₂ h₃ h₄ h₅ (Round5.Fwd.tyBnd_funcType hb.storeBnd h₂))))
    (fun h₁ h₂ h₃ h₄ h₅ h₆ hb _ => .inl (resp_call (codeDeep_vals _) rfl h₁ fun _ h =>
      V (HC.1 h h₂ h₃ h₄ h₅ h₆ (Round5.Fwd.tyBnd_funcType hb.storeBnd h₂))))
    (fun h₁ h₂ h₃ h₄ h₅ h₆ hb _ => .inl (resp_callDiv (codeDeep_vals _) rfl h₁ fun _ h =>
      HC.2 h h₂ h₃ h₄ h₅ h₆ (Round5.Fwd.tyBnd_funcType hb.storeBnd h₂)))
    (fun h₁ h₂ => U rfl (.returnCall h₁ h₂))
    (fun h₁ _ _ => .inl (resp_labelPrefix (deep_vals_app _ (codeDeep_one (isReturnCallRef_deep h₁)))
      fun _ => V (fwd_returnCallRefLabel _ T Ty h₁)))
    (fun h₁ _ _ => .inl (resp_handlerPrefix
      (deep_vals_app _ (codeDeep_one (isReturnCallRef_deep h₁)))
      fun _ => V (fwd_returnCallRefHandler _ T Ty h₁)))
    (fun h₁ _ _ => .inl (resp_framePrefix
      (deep_vals_app _ (codeDeep_two rfl (isReturnCallRef_deep h₁)))
      fun _ => V (fwd_returnCallRefFrameNull _ T Ty h₁)))
    (fun h₁ h₂ h₃ h₄ hb _ => .inl (resp_framePrefix
      (codeDeep_app (deep_vals_app _ (codeDeep_vals _))
      (codeDeep_two rfl (isReturnCallRef_deep h₁))) fun _ =>
        Round5.Fwd.fwdUp_returnCallRefFrameAddr5 TB h₁ h₂ h₃ h₄
          (Round5.Fwd.tyBnd_funcType hb.storeBnd h₂)))
    (U rfl .callIndirect)
    (U rfl .returnCallIndirect)
    (fun h₁ => U (Bwd.codeDeep_frame1 (codeDeep_vals _)) (.frameVals h₁))
    (fun h₁ _ _ => .inl (resp_framePrefix (codeDeep_app (deep_vals_app _ (codeDeep_vals _)) rfl)
      fun _ => V (fwd_returnFrame _ T Ty h₁)))
    (fun _ _ => .inl (resp_labelPrefix (deep_vals_app _ rfl) fun _ => V (fwd_returnLabel _ T)))
    (fun _ _ => .inl (resp_handlerPrefix (deep_vals_app _ rfl) fun _ => V (fwd_returnHandler _ T)))
    (fun h₁ h₂ h₃ => U (deep_vals_app _ rfl) (.throw h₁ h₂ h₃))
    (U rfl .throwRefNull)
    (fun h₁ _ _ => .inl (resp_prefix (deep_vals_app _ rfl)
      fun _ h => V (Exn.fwd_throwRefInstrs _ T X (h₁.imp id h))))
    (U rfl .throwRefLabel)
    (U rfl .throwRefFrame)
    (U rfl .throwRefHandlerEmpty)
    (fun h₁ h₂ => U rfl (.throwRefHandlerCatch h₁ h₂))
    (fun h₁ h₂ => U rfl (.throwRefHandlerCatchRef h₁ h₂))
    (U rfl .throwRefHandlerCatchAll)
    (U rfl .throwRefHandlerCatchAllRef)
    (fun h₁ => U rfl (.throwRefHandlerNext h₁))
    (fun h₁ h₂ => U (deep_vals_app _ rfl) (.tryTable h₁ h₂))
    (U (Bwd.codeDeep_handler1 (codeDeep_vals _)) .handlerVals)
    (fun h₁ _ _ => .inl (resp_prefix (deep_vals_app _ rfl)
      fun _ h => V (fwd_trapInstrs _ T (h₁.imp id h))))
    (U rfl .trapLabel)
    (U rfl .trapHandler)
    (U rfl .trapFrame)

    h

/-- **`fwdRespOr`, as a match up to choice.** -/
theorem fwdRespR_of (hinj : Function.Injective hn) (hf : HostFinite host) {c c' : Config H}
    (h : Step P host c c') (hb : Bounded c) (hx : ¬ CastRedex c.code) :
    FwdRespR P host (BI P hn host) hn c c' :=
  (fwdRespOr hinj hf h hb hx).elim (fun hr => ⟨c', h, fun _ => rfl, hr⟩) id

end Silmaril.Wasm.SpecTec.Sim.Round6.Target
