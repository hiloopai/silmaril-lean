module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Multi.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int.Thms

/-!
# Round 5: SpecTec respects `ConfigEq` along a Core step

`fwdResp_of_step`: for the concrete `B`, from track fwd's obligations `Obl`, every Core step
`c → c'` from a bounded `c` is matched from the image of **every** typed witness `d ≈ c`: SpecTec
steps to the image of a typed `e ≈ c'`. This is the SpecTec half of "both semantics respect the
equivalence" (Core's half is `Bwd.step_respects`).

The proof is by induction on `Step`, with the case split of `Bwd.step_respects`:

* rules whose left-hand side is `deep` (no `CALL_REF` at any depth): the witness is `c` itself,
  and `forward5` applies (`resp_deep`);
* rules with an arbitrary tail (`br*`, `return*`, `trap-instrs`, `throw_ref-instrs`): the
  witness has a different tail, and the forward lemma, which is stated for every tail, applies
  to it (`resp_prefix`, `resp_labelPrefix`, …);
* the call rules: the witness has a different `CALL_REF`, and the forward lemmas accept any
  (`resp_call`; the divergent host call stutters, `resp_callDiv`);
* the four context rules recurse, carrying the witness's untouched parts (`resp_ctxt*`).

No bound on the witness is needed: the rules that use one use the store's (`StoreBnd`), which
the witness shares with `c`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Multi

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4 (Bounded)
open Round4Int (BI)
open FwdMem (FwdUp fwdUp_of_fwdP)
open _root_.Silmaril.Wasm.SpecTec.Sim.Bwd (ConfigEq CodeEq codeDeep codeDeep_app codeDeep_vals
  deep_vals_app codeDeep_one codeDeep_two isReturnCallRef_deep)

variable {H : Type}

/-! ## The generic cases -/

section Generic

variable {env : Env} {hn : H → String}

/-- A step whose left-hand side has no `CALL_REF`: the witness is the source. -/
theorem resp_deep {c c' : Config H} (hp : codeDeep c.code = true) (h : FwdUp env hn c c') :
    FwdResp env hn c c' := fun d hd htd htc' => by
  obtain rfl := Bwd.cfgEq_deep hp hd
  exact h htd htc'

/-- A step that drops an arbitrary tail after a `deep` prefix. -/
theorem resp_prefix {s : Store H} {f : Frame} {p r : List Admin} {c' : Config H}
    (hp : codeDeep p = true)
    (h : ∀ r', (r ≠ [] → r' ≠ []) → FwdUp env hn ⟨s, f, p ++ r'⟩ c') :
    FwdResp env hn ⟨s, f, p ++ r⟩ c' := fun d hd htd htc' => by
  obtain ⟨r', rfl, hr⟩ := Bwd.cfgEq_prefix hp hd
  have hne : r ≠ [] → r' ≠ [] := fun h₁ h₂ =>
    h₁ (List.eq_nil_of_length_eq_zero (by rw [hr.length_eq, h₂]; rfl))
  exact h r' hne htd htc'

/-- A step out of a label whose body is a `deep` prefix and an arbitrary tail. -/
theorem resp_labelPrefix {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {p r : List Admin} {c' : Config H} (hp : codeDeep p = true)
    (h : ∀ r', FwdUp env hn ⟨s, f, [.label n cont (p ++ r')]⟩ c') :
    FwdResp env hn ⟨s, f, [.label n cont (p ++ r)]⟩ c' := fun d hd htd htc' => by
  obtain ⟨r', rfl⟩ := Bwd.cfgEq_labelPrefix hp hd
  exact h r' htd htc'

/-- A step out of a handler whose body is a `deep` prefix and an arbitrary tail. -/
theorem resp_handlerPrefix {s : Store H} {f : Frame} {n : Nat} {cs : List Catch}
    {p r : List Admin} {c' : Config H} (hp : codeDeep p = true)
    (h : ∀ r', FwdUp env hn ⟨s, f, [.handler n cs (p ++ r')]⟩ c') :
    FwdResp env hn ⟨s, f, [.handler n cs (p ++ r)]⟩ c' := fun d hd htd htc' => by
  obtain ⟨r', rfl⟩ := Bwd.cfgEq_handlerPrefix hp hd
  exact h r' htd htc'

/-- A step out of a frame whose body is a `deep` prefix and an arbitrary tail. -/
theorem resp_framePrefix {s : Store H} {f : Frame} {n : Nat} {fi : Frame}
    {p r : List Admin} {c' : Config H} (hp : codeDeep p = true)
    (h : ∀ r', FwdUp env hn ⟨s, f, [.frame n fi (p ++ r')]⟩ c') :
    FwdResp env hn ⟨s, f, [.frame n fi (p ++ r)]⟩ c' := fun d hd htd htc' => by
  obtain ⟨r', rfl⟩ := Bwd.cfgEq_framePrefix hp hd
  exact h r' htd htc'

/-- A call rule: the witness's `CALL_REF` may carry any annotation. -/
theorem resp_call {s : Store H} {f : Frame} {q : List Admin} {x c : Admin} {c' : Config H}
    (hq : codeDeep q = true) (hx : Bwd.deep x = true) (hc : c.IsCallRef)
    (h : ∀ c₂ : Admin, c₂.IsCallRef → FwdUp env hn ⟨s, f, q ++ [x, c₂]⟩ c') :
    FwdResp env hn ⟨s, f, q ++ [x, c]⟩ c' := fun d hd htd htc' => by
  obtain ⟨c₂, hc₂, rfl⟩ := Bwd.cfgEq_call2 hq hx hc hd
  exact h c₂ hc₂ htd htc'

/-- The divergent host call stutters, from the witness too. -/
theorem resp_callDiv {s : Store H} {f : Frame} {q : List Admin} {x c : Admin}
    (hq : codeDeep q = true) (hx : Bwd.deep x = true) (hc : c.IsCallRef)
    (h : ∀ c₂ : Admin, c₂.IsCallRef →
      FwdP env hn ⟨s, f, q ++ [x, c₂]⟩ ⟨s, f, q ++ [x, c₂]⟩) :
    FwdResp env hn ⟨s, f, q ++ [x, c]⟩ ⟨s, f, q ++ [x, c]⟩ := fun d hd htd _ => by
  obtain ⟨c₂, hc₂, rfl⟩ := Bwd.cfgEq_call2 hq hx hc hd
  exact ⟨_, hd, htd, h c₂ hc₂ htd htd⟩

end Generic

/-! ## The context rules -/

section Ctxt

variable {B : Builtins} {hn : H → String} (T : TypingFacts (simEnv B) hn)
include T

/-- `Step.ctxtInstrs`: the witness keeps its own tail. -/
theorem resp_ctxtInstrs {s s' : Store H} {f f' : Frame} {vs : List Val}
    {is is' rest : List Admin} (hne : vs ≠ [] ∨ rest ≠ [])
    (ih : FwdResp (simEnv B) hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdResp (simEnv B) hn ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  intro d hd htd htc'
  have hd' : ConfigEq ⟨s, f, vals vs ++ (is ++ rest)⟩ d := by
    rw [← List.append_assoc]
    exact hd
  obtain ⟨r', rfl, hr⟩ := Bwd.cfgEq_prefix (codeDeep_vals vs) hd'
  obtain ⟨j₁, j₂, rfl, h₁, h₂⟩ := Bwd.codeEq_append_left hr
  obtain ⟨hst, hcode⟩ := (T.config _).1 htd
  obtain ⟨hst', hcode'⟩ := (T.config _).1 htc'
  have hcd : TypedV (simEnv B) instrsT
      (.list (adminsToV (vals vs) ++ (adminsToV j₁ ++ adminsToV j₂))) := by
    simpa only [adminsToV_append] using hcode
  obtain ⟨-, hj⟩ := typedV_list_append.1 hcd
  obtain ⟨hj₁, hj₂⟩ := typedV_list_append.1 hj
  have hcc : TypedV (simEnv B) instrsT
      (.list (adminsToV (vals vs) ++ (adminsToV is' ++ adminsToV rest))) := by
    simpa only [adminsToV_append, List.append_assoc] using hcode'
  obtain ⟨hv', hc'⟩ := typedV_list_append.1 hcc
  obtain ⟨his', -⟩ := typedV_list_append.1 hc'
  obtain ⟨⟨s₂, f₂, K⟩, ⟨hs, hf, hK⟩, hte, hstep⟩ :=
    ih ⟨s, f, j₁⟩ ⟨rfl, rfl, h₁⟩ ((T.config _).2 ⟨hst, hj₁⟩) ((T.config _).2 ⟨hst', his'⟩)
  obtain rfl : s' = s₂ := hs
  obtain rfl : f' = f₂ := hf
  have hK' := ((T.config _).1 hte).2
  have hne' : vs ≠ [] ∨ j₂ ≠ [] := hne.imp id fun h₃ h₄ =>
    h₃ (List.eq_nil_of_length_eq_zero (by rw [h₂.length_eq, h₄]; rfl))
  have hte' : Typed (simEnv B) hn ⟨s', f', vals vs ++ K ++ j₂⟩ :=
    (T.config _).2 ⟨hst', by
      simpa only [adminsToV_append, List.append_assoc] using
        typedV_list_append.2 ⟨hv', typedV_list_append.2 ⟨hK', hj₂⟩⟩⟩
  have htd' : Typed (simEnv B) hn ⟨s, f, vals vs ++ j₁ ++ j₂⟩ := by
    rw [List.append_assoc]
    exact htd
  refine ⟨⟨s', f', vals vs ++ K ++ j₂⟩, ⟨rfl, rfl, ((CodeEq.refl _).append hK).append h₂⟩, hte',
    ?_⟩
  have key := fwd_ctxtInstrs T (hasStepRules_simEnv B).ctxtInstrs hne' (fun _ _ => hstep) htd' hte'
  simpa only [List.append_assoc] using key

/-- `Step.ctxtLabel`. -/
theorem resp_ctxtLabel {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
    {is is' : List Admin} (ih : FwdResp (simEnv B) hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdResp (simEnv B) hn ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ := by
  intro d hd htd htc'
  obtain ⟨js, rfl, hj⟩ := Bwd.cfgEq_label hd
  obtain ⟨hst, hcode⟩ := (T.config _).1 htd
  obtain ⟨hst', hcode'⟩ := (T.config _).1 htc'
  obtain ⟨-, -, hjs⟩ := T.label n cont js hcode
  obtain ⟨hn₀, hcont, his'⟩ := T.label n cont is' hcode'
  obtain ⟨⟨s₂, f₂, K⟩, ⟨hs, hf, hK⟩, hte, hstep⟩ :=
    ih ⟨s, f, js⟩ ⟨rfl, rfl, hj⟩ ((T.config _).2 ⟨hst, hjs⟩) ((T.config _).2 ⟨hst', his'⟩)
  obtain rfl : s' = s₂ := hs
  obtain rfl : f' = f₂ := hf
  have hte' : Typed (simEnv B) hn ⟨s', f', [.label n cont K]⟩ :=
    (T.config _).2 ⟨hst', FwdMem.typedV_label hn₀ hcont ((T.config _).1 hte).2⟩
  exact ⟨⟨s', f', [.label n cont K]⟩, ⟨rfl, rfl, .cons (.label hK) .nil⟩, hte',
    fwd_ctxtLabel T (hasStepRules_simEnv B).ctxtLabel (fun _ _ => hstep) htd hte'⟩

/-- `Step.ctxtHandler`. -/
theorem resp_ctxtHandler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch}
    {is is' : List Admin} (ih : FwdResp (simEnv B) hn ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    FwdResp (simEnv B) hn ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩ := by
  intro d hd htd htc'
  obtain ⟨js, rfl, hj⟩ := Bwd.cfgEq_handler hd
  obtain ⟨hst, hcode⟩ := (T.config _).1 htd
  obtain ⟨hst', hcode'⟩ := (T.config _).1 htc'
  obtain ⟨-, -, hjs⟩ := T.handler n cs js hcode
  obtain ⟨hn₀, hcs, his'⟩ := T.handler n cs is' hcode'
  obtain ⟨⟨s₂, f₂, K⟩, ⟨hs, hf, hK⟩, hte, hstep⟩ :=
    ih ⟨s, f, js⟩ ⟨rfl, rfl, hj⟩ ((T.config _).2 ⟨hst, hjs⟩) ((T.config _).2 ⟨hst', his'⟩)
  obtain rfl : s' = s₂ := hs
  obtain rfl : f' = f₂ := hf
  have hte' : Typed (simEnv B) hn ⟨s', f', [.handler n cs K]⟩ :=
    (T.config _).2 ⟨hst', FwdMem.typedV_handler hn₀ hcs ((T.config _).1 hte).2⟩
  exact ⟨⟨s', f', [.handler n cs K]⟩, ⟨rfl, rfl, .cons (.handler hK) .nil⟩, hte',
    fwd_ctxtHandler T (hasStepRules_simEnv B).ctxtHandler (fun _ _ => hstep) htd hte'⟩

/-- `Step.ctxtFrame`. -/
theorem resp_ctxtFrame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (ih : FwdResp (simEnv B) hn ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
    FwdResp (simEnv B) hn ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ := by
  intro d hd htd htc'
  obtain ⟨js, rfl, hj⟩ := Bwd.cfgEq_frame hd
  obtain ⟨hst, hcode⟩ := (T.config _).1 htd
  obtain ⟨hst', hcode'⟩ := (T.config _).1 htc'
  obtain ⟨hs₀, -⟩ := (T.state _ _).1 hst
  obtain ⟨hs₀', -⟩ := (T.state _ _).1 hst'
  obtain ⟨-, hfi, hjs⟩ := T.frame n fi js hcode
  obtain ⟨hn₀, hfi', his'⟩ := T.frame n fi' is' hcode'
  obtain ⟨⟨s₂, f₂, K⟩, ⟨hs, hf, hK⟩, hte, hstep⟩ :=
    ih ⟨s, fi, js⟩ ⟨rfl, rfl, hj⟩ ((T.config _).2 ⟨(T.state _ _).2 ⟨hs₀, hfi⟩, hjs⟩)
      ((T.config _).2 ⟨(T.state _ _).2 ⟨hs₀', hfi'⟩, his'⟩)
  obtain rfl : s' = s₂ := hs
  obtain rfl : fi' = f₂ := hf
  have hte' : Typed (simEnv B) hn ⟨s', f, [.frame n fi' K]⟩ :=
    (T.config _).2 ⟨hst', FwdMem.typedV_frame hn₀ hfi' ((T.config _).1 hte).2⟩
  exact ⟨⟨s', f, [.frame n fi' K]⟩, ⟨rfl, rfl, .cons (.frame hK) .nil⟩, hte',
    fwd_ctxtFrame T (hasStepRules_simEnv B).ctxtFrame (fun _ _ => hstep) htd hte'⟩

end Ctxt

/-! ## Every Core step -/

variable {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **SpecTec respects `ConfigEq` along every Core step from a bounded source**, for the
concrete `B`, from `TypesB` and `Obl` and the two host `call_ref` rules forward
(`HostCallsFwd`, for any `CALL_REF` and a bounded callee type). -/
theorem fwdResp_of_step_host (TB : Fwd.TypesB (simEnv (BI P hn host)))
    (HC : HostCallsFwd (BI P hn host) hn host) (O : Fwd.Obl (BI P hn host) hn P host)
    {c c' : Config H} (h : Step P host c c') :
    Bounded c → FwdResp (simEnv (BI P hn host)) hn c c' :=
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  have Ty := Typing.ctrlTyping_simEnv (BI P hn host)
  have X := Typing.exnTyping_simEnv' (BI P hn host)
  have U {c c' : Config H} (hp : codeDeep c.code = true) (hs : Step P host c c')
      (hb : Bounded c) : FwdResp (simEnv (BI P hn host)) hn c c' :=
    resp_deep hp (Fwd.forward5 O hs hb)
  have V {c c' : Config H} (h : FwdP (simEnv (BI P hn host)) hn c c') :
      FwdUp (simEnv (BI P hn host)) hn c c' := fwdUp_of_fwdP h
  Step.rec (motive := fun c c' _ => Bounded c → FwdResp (simEnv (BI P hn host)) hn c c')
    (fun hs => U (Bwd.parametric_deep hs) (.parametric hs))
    (fun hs => U (Bwd.numeric_deep hs) (.numeric hs))
    (fun hs => U (Bwd.vector_deep hs) (.vector hs))
    (fun hs => U (Bwd.variable_deep hs) (.variable hs))
    (fun hs => U (Bwd.table_deep hs) (.table hs))
    (fun hs => U (Bwd.memory_deep hs) (.memory hs))
    (fun hs => U (Bwd.reference_deep hs) (.reference hs))
    (fun hs => U (Bwd.aggregate_deep hs) (.aggregate hs))
    (fun _ hne ih hb => resp_ctxtInstrs T hne (ih (Fwd.bounded_ctxtInstrs hb)))
    (fun _ ih hb => resp_ctxtLabel T (ih (Fwd.bounded_ctxtLabel hb)))
    (fun _ ih hb => resp_ctxtHandler T (ih (Fwd.bounded_ctxtHandler hb)))
    (fun _ ih hb => resp_ctxtFrame T (ih (Fwd.bounded_ctxtFrame hb)))
    (fun h₁ h₂ => U (deep_vals_app _ rfl) (.block h₁ h₂))
    (fun h₁ h₂ => U (deep_vals_app _ rfl) (.loop h₁ h₂))
    (fun h₁ => U rfl (.ifTrue h₁))
    (U rfl .ifFalse)
    (U (Bwd.codeDeep_label1 (codeDeep_vals _)) .labelVals)
    (fun h₁ h₂ _ => resp_labelPrefix (codeDeep_app (deep_vals_app _ (codeDeep_vals _)) rfl)
      fun _ => V (fwd_brLabelZero _ T Ty h₁ h₂))
    (fun h₁ _ => resp_labelPrefix (deep_vals_app _ rfl) fun _ => V (fwd_brLabelSucc _ T Ty h₁))
    (fun _ => resp_handlerPrefix (deep_vals_app _ rfl) fun _ => V (fwd_brHandler _ T Ty))
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
    (fun h₁ _ => resp_call (q := []) rfl rfl h₁ fun _ h => V (fwd_callRefNull _ T Ty h))
    (fun h₁ h₂ h₃ h₄ h₅ hb => resp_call (codeDeep_vals _) rfl h₁ fun _ h =>
      V (Fwd.fwd_callRefFunc5 TB h h₂ h₃ h₄ h₅ (Fwd.tyBnd_funcType hb.storeBnd h₂)))
    (fun h₁ h₂ h₃ h₄ h₅ h₆ hb => resp_call (codeDeep_vals _) rfl h₁ fun _ h =>
      V (HC.1 h h₂ h₃ h₄ h₅ h₆ (Fwd.tyBnd_funcType hb.storeBnd h₂)))
    (fun h₁ h₂ h₃ h₄ h₅ h₆ hb => resp_callDiv (codeDeep_vals _) rfl h₁ fun _ h =>
      HC.2 h h₂ h₃ h₄ h₅ h₆ (Fwd.tyBnd_funcType hb.storeBnd h₂))
    (fun h₁ h₂ => U rfl (.returnCall h₁ h₂))
    (fun h₁ _ => resp_labelPrefix (deep_vals_app _ (codeDeep_one (isReturnCallRef_deep h₁)))
      fun _ => V (fwd_returnCallRefLabel _ T Ty h₁))
    (fun h₁ _ => resp_handlerPrefix (deep_vals_app _ (codeDeep_one (isReturnCallRef_deep h₁)))
      fun _ => V (fwd_returnCallRefHandler _ T Ty h₁))
    (fun h₁ _ => resp_framePrefix (deep_vals_app _ (codeDeep_two rfl (isReturnCallRef_deep h₁)))
      fun _ => V (fwd_returnCallRefFrameNull _ T Ty h₁))
    (fun h₁ h₂ h₃ h₄ hb => resp_framePrefix (codeDeep_app (deep_vals_app _ (codeDeep_vals _))
      (codeDeep_two rfl (isReturnCallRef_deep h₁))) fun _ =>
        Fwd.fwdUp_returnCallRefFrameAddr5 TB h₁ h₂ h₃ h₄ (Fwd.tyBnd_funcType hb.storeBnd h₂))
    (U rfl .callIndirect)
    (U rfl .returnCallIndirect)
    (fun h₁ => U (Bwd.codeDeep_frame1 (codeDeep_vals _)) (.frameVals h₁))
    (fun h₁ _ => resp_framePrefix (codeDeep_app (deep_vals_app _ (codeDeep_vals _)) rfl)
      fun _ => V (fwd_returnFrame _ T Ty h₁))
    (fun _ => resp_labelPrefix (deep_vals_app _ rfl) fun _ => V (fwd_returnLabel _ T))
    (fun _ => resp_handlerPrefix (deep_vals_app _ rfl) fun _ => V (fwd_returnHandler _ T))
    (fun h₁ h₂ h₃ => U (deep_vals_app _ rfl) (.throw h₁ h₂ h₃))
    (U rfl .throwRefNull)
    (fun h₁ _ => resp_prefix (deep_vals_app _ rfl)
      fun _ h => V (Exn.fwd_throwRefInstrs _ T X (h₁.imp id h)))
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
    (fun h₁ _ => resp_prefix (deep_vals_app _ rfl)
      fun _ h => V (fwd_trapInstrs _ T (h₁.imp id h)))
    (U rfl .trapLabel)
    (U rfl .trapHandler)
    (U rfl .trapFrame)
    h

/-- **SpecTec respects `ConfigEq` along every Core step from a bounded source**, for the
concrete `B`, from `TypesB` and `Obl` and a finite host respecting the encoding. -/
theorem fwdResp_of_step (TB : Fwd.TypesB (simEnv (BI P hn host))) (hfin : HostFinite host)
    (hr : Prims.HostRespects hn host) (O : Fwd.Obl (BI P hn host) hn P host) {c c' : Config H}
    (h : Step P host c c') : Bounded c → FwdResp (simEnv (BI P hn host)) hn c c' :=
  fwdResp_of_step_host TB
    ⟨fun hc hfa hex hlen hcode hh hd => Fwd.fwd_callRefHost5 TB hfin hr hc hfa hex hlen hcode hh hd,
      fun hc hfa hex hlen hcode hh hd =>
        Fwd.fwd_callRefHostDiv5 TB hfin hr hc hfa hex hlen hcode hh hd⟩ O h

end Silmaril.Wasm.SpecTec.Sim.Round5.Multi
