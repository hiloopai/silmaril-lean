module

public import Silmaril.Proofs.Wasm.Logic.V1.BigStep.Compose
public import Silmaril.Wasm.V1.Execution.Properties

/-!
# Every big-step derivation is a finite reduction

One half of the equivalence of Theorem 1 of Watt et al.: a big-step derivation
is realised by the small-step reduction of `Silmaril.Wasm.V1.Execution.Step`.
Branch and return results leave behind an unreachable code tail, which the
enclosing `label` or `frame` discards; the statement quantifies it existentially.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1 Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

variable {H : Type*} {host : HostSemantics H}

/-- Reductions in front of a realising reduction are absorbed. -/
private theorem Outcome.Reaches.head' {o : Outcome H} {c c' : Config H}
    (h : Steps host c c') (hr : o.Reaches host c') : o.Reaches host c := by
  obtain ⟨st, fr, r⟩ := o
  cases r with
  | normal ws => exact h.trans hr
  | br l ws => obtain ⟨tail, ht⟩ := hr; exact ⟨tail, h.trans ht⟩
  | ret ws => obtain ⟨tail, ht⟩ := hr; exact ⟨tail, h.trans ht⟩
  | trap => exact h.trans hr

/-- Equal code is reached in zero steps. -/
private theorem stepsOfEq {s : Store H} {f : Frame} {a b : List Admin} (h : a = b) :
    Steps host ⟨s, f, a⟩ ⟨s, f, b⟩ := h ▸ Relation.ReflTransGen.refl

/-- A single step inside an evaluation context. -/
private theorem stepCtx {s s' : Store H} {f f' : Frame} {before after : List Admin}
    (h : Step host ⟨s, f, before⟩ ⟨s', f', after⟩) (vs : List Value) (tail : List Admin) :
    Steps host ⟨s, f, values vs ++ before ++ tail⟩ ⟨s', f', values vs ++ after ++ tail⟩ :=
  (h.context vs tail).steps

/-- A single pure step inside an evaluation context. -/
private theorem pureSteps (s : Store H) (f : Frame) {before after : List Admin}
    (h : PureStep before after) (vs : List Value) (tail : List Admin) :
    Steps host ⟨s, f, values vs ++ before ++ tail⟩ ⟨s, f, values vs ++ after ++ tail⟩ :=
  stepCtx (Step.pure s f h) vs tail

private theorem plainSteps {s s' : Store H} {f f' : Frame} {args rets : List Value} {i : Silmaril.Wasm.V1.Instr}
    (h : Plain s f args i s' f' rets) :
    Steps host ⟨s, f, values args ++ [.source i]⟩ ⟨s', f', values rets⟩ := Plain.toStep h

private theorem plainTrapSteps {s : Store H} {f : Frame} {args : List Value} {i : Silmaril.Wasm.V1.Instr}
    (h : PlainTrap s f args i) :
    Steps host ⟨s, f, values args ++ [.source i]⟩ ⟨s, f, [.trap]⟩ := PlainTrap.toStep h

theorem BigStep.toSteps {s : Store H} {f : Frame} {vs : List Value} {es : List Admin}
    {o : Outcome H} (h : BigStep host s f vs es o) :
    o.Reaches host ⟨s, f, values vs ++ es⟩ := by
  induction h with
  | nil =>
    show Steps host _ _
    rw [List.append_nil]
  | @plain _ _ _ _ _ _ _ vs es _ step _ ih =>
    refine Outcome.Reaches.head' ?_ ih
    simpa [values] using Steps.context (plainSteps (host := host) step) vs es
  | @plainTrap _ _ _ _ vs es step =>
    show Steps host _ _
    refine Relation.ReflTransGen.trans ?_ (Steps.trapCollapse _ _ vs es)
    simpa [values] using Steps.context (plainTrapSteps (host := host) step) vs es
  | trap s f vs es =>
    show Steps host _ _
    simpa [values] using Steps.trapCollapse (host := host) s f vs es
  | @block s f vs bt body es _ _ ih =>
    refine Outcome.Reaches.head' ?_ ih
    simpa [values] using pureSteps (host := host) s f (PureStep.block bt body) vs es
  | @loop s f vs bt body es _ _ ih =>
    refine Outcome.Reaches.head' ?_ ih
    simpa [values] using pureSteps (host := host) s f (PureStep.loop bt body) vs es
  | @ifZero s f vs bt left right es _ _ ih =>
    refine Outcome.Reaches.head' ?_ ih
    simpa [values] using pureSteps (host := host) s f (PureStep.ifZero bt left right) vs es
  | @ifNonzero s f vs bt left right es _ c nonzero _ ih =>
    refine Outcome.Reaches.head' ?_ ih
    simpa [values] using
      pureSteps (host := host) s f (PureStep.ifNonzero bt left right c nonzero) vs es
  | @br _ _ _ _ es => exact ⟨es, stepsOfEq (by simp)⟩
  | @brIfZero s f vs l es _ _ ih =>
    refine Outcome.Reaches.head' ?_ ih
    simpa [values] using pureSteps (host := host) s f (PureStep.brIfZero l) vs es
  | @brIfNonzero s f vs l es _ c nonzero _ ih =>
    refine Outcome.Reaches.head' ?_ ih
    simpa [values] using pureSteps (host := host) s f (PureStep.brIfNonzero l c nonzero) vs es
  | @brTable s f vs ls dflt es _ c _ ih =>
    refine Outcome.Reaches.head' ?_ ih
    simpa [values] using pureSteps (host := host) s f (PureStep.brTable ls dflt c) vs es
  | @return_ _ _ _ es => exact ⟨es, stepsOfEq (by simp)⟩
  | @call s f vs i a es _ found _ ih =>
    refine Outcome.Reaches.head' ?_ ih
    simpa [values] using stepCtx (Step.call (host := host) s f i a found) vs es
  | @callIndirect s f vs i c table a fn ft es _ tableFound typeFound element found typeMatch _ ih =>
    refine Outcome.Reaches.head' ?_ ih
    simpa [values] using
      stepCtx (Step.callIndirect (host := host) s f i c table a fn ft tableFound typeFound
        element found typeMatch) vs es
  | @callIndirectBounds s f vs i c table es tableFound outOfBounds =>
    show Steps host _ _
    refine Relation.ReflTransGen.trans ?_ (Steps.trapCollapse _ _ vs es)
    simpa [values] using
      stepCtx (Step.callIndirectBounds (host := host) s f i c table tableFound outOfBounds) vs es
  | @callIndirectNull s f vs i c table es tableFound null =>
    show Steps host _ _
    refine Relation.ReflTransGen.trans ?_ (Steps.trapCollapse _ _ vs es)
    simpa [values] using
      stepCtx (Step.callIndirectNull (host := host) s f i c table tableFound null) vs es
  | @callIndirectType s f vs i c table a fn ft es tableFound typeFound element found typeMismatch =>
    show Steps host _ _
    refine Relation.ReflTransGen.trans ?_ (Steps.trapCollapse _ _ vs es)
    simpa [values] using
      stepCtx (Step.callIndirectType (host := host) s f i c table a fn ft tableFound typeFound
        element found typeMismatch) vs es
  | @invokeWasm s f vs args a ft md fn es _ found arity resultArity _ ih =>
    refine Outcome.Reaches.head' ?_ ih
    simpa [values] using
      stepCtx (Step.invokeWasm (host := host) s f a ft md fn args found arity resultArity) vs es
  | @invokeHost s s' f vs args a ft fn r es _ found arity behavior _ ih =>
    refine Outcome.Reaches.head' ?_ ih
    simpa [values] using
      stepCtx (Step.invokeHost (host := host) s s' f a ft fn args r found arity behavior) vs es
  | @labelNormal s s' f f' vs ws n cont body es _ _ _ ih₁ ih₂ =>
    refine Outcome.Reaches.head' ?_ ih₂
    have h1 : Steps host ⟨s, f, body⟩ ⟨s', f', values ws⟩ := ih₁
    have step1 : Steps host ⟨s, f, values vs ++ [.label n cont body] ++ es⟩
        ⟨s', f', values vs ++ [.label n cont (values ws)] ++ es⟩ :=
      Steps.context (Steps.label h1 n cont) vs es
    have step2 := pureSteps (host := host) s' f' (PureStep.labelDone n cont ws) vs es
    simpa [values] using step1.trans step2
  | @labelBrZero s s' f f' vs extra ws n cont body es l o _ target arity _ ih₁ ih₂ =>
    show o.Reaches host ⟨s, f, values vs ++ .label n cont body :: es⟩
    refine Outcome.Reaches.head' ?_ ih₂
    obtain ⟨tail, ht⟩ := ih₁
    obtain rfl : l = (⟨0⟩ : LabelIdx) := Idx.toNat_injective (by rw [target]; rfl)
    have ht' : Steps host ⟨s, f, body⟩
        ⟨s', f', values extra ++ values ws ++ [.source (.br ⟨0⟩)] ++ tail⟩ := by
      simpa [values] using ht
    have step1 : Steps host ⟨s, f, values vs ++ [.label n cont body] ++ es⟩
        ⟨s', f', values vs ++
          [.label n cont (values extra ++ values ws ++ [.source (.br ⟨0⟩)] ++ tail)] ++ es⟩ :=
      Steps.context (Steps.label ht' n cont) vs es
    have step2 :=
      pureSteps (host := host) s' f' (PureStep.labelBranch n cont extra ws tail arity) vs es
    simpa [values] using step1.trans step2
  | @labelBrSucc s s' f f' vs ws n cont body es l _ outer ih =>
    show ∃ tail, Steps host ⟨s, f, values vs ++ .label n cont body :: es⟩
      ⟨s', f', values (vs ++ ws) ++ [.source (.br (lowerLabel l))] ++ tail⟩
    obtain ⟨tail, ht⟩ := ih
    refine ⟨es, ?_⟩
    have ht' : Steps host ⟨s, f, body⟩ ⟨s', f', values ws ++ [.source (.br l)] ++ tail⟩ := ht
    have step1 : Steps host ⟨s, f, values vs ++ [.label n cont body] ++ es⟩
        ⟨s', f', values vs ++ [.label n cont (values ws ++ [.source (.br l)] ++ tail)] ++ es⟩ :=
      Steps.context (Steps.label ht' n cont) vs es
    have step2 :=
      pureSteps (host := host) s' f' (PureStep.labelBranchOuter n cont ws tail l outer) vs es
    simpa [values] using step1.trans step2
  | @labelRet s s' f f' vs ws n cont body es _ ih =>
    show ∃ tail, Steps host ⟨s, f, values vs ++ .label n cont body :: es⟩
      ⟨s', f', values (vs ++ ws) ++ [.source .return_] ++ tail⟩
    obtain ⟨tail, ht⟩ := ih
    refine ⟨es, ?_⟩
    have ht' : Steps host ⟨s, f, body⟩ ⟨s', f', values ws ++ [.source .return_] ++ tail⟩ := ht
    have step1 : Steps host ⟨s, f, values vs ++ [.label n cont body] ++ es⟩
        ⟨s', f', values vs ++ [.label n cont (values ws ++ [.source .return_] ++ tail)] ++ es⟩ :=
      Steps.context (Steps.label ht' n cont) vs es
    have step2 := pureSteps (host := host) s' f' (PureStep.labelReturn n cont ws tail) vs es
    simpa [values] using step1.trans step2
  | @labelTrap s s' f f' vs n cont body es _ ih =>
    show Steps host _ _
    have ht : Steps host ⟨s, f, body⟩ ⟨s', f', [.trap]⟩ := ih
    have step1 : Steps host ⟨s, f, values vs ++ [.label n cont body] ++ es⟩
        ⟨s', f', values vs ++ [.label n cont [.trap]] ++ es⟩ :=
      Steps.context (Steps.label ht n cont) vs es
    have step2 := pureSteps (host := host) s' f' (PureStep.labelTrap n cont) vs es
    refine Relation.ReflTransGen.trans ?_ (Steps.trapCollapse _ _ vs es)
    simpa [values] using step1.trans step2
  | @frameNormal s s' f fr fr' vs ws n body es _ _ arity _ ih₁ ih₂ =>
    refine Outcome.Reaches.head' ?_ ih₂
    have h1 : Steps host ⟨s, fr, body⟩ ⟨s', fr', values ws⟩ := ih₁
    have step1 : Steps host ⟨s, f, values vs ++ [.frame n fr body] ++ es⟩
        ⟨s', f, values vs ++ [.frame n fr' (values ws)] ++ es⟩ :=
      Steps.context (Steps.frame h1 n f) vs es
    have step2 := pureSteps (host := host) s' f (PureStep.frameDone n fr' ws arity) vs es
    simpa [values] using step1.trans step2
  | @frameRet s s' f fr fr' vs extra ws n body es o _ arity _ ih₁ ih₂ =>
    show o.Reaches host ⟨s, f, values vs ++ .frame n fr body :: es⟩
    refine Outcome.Reaches.head' ?_ ih₂
    obtain ⟨tail, ht⟩ := ih₁
    have ht' : Steps host ⟨s, fr, body⟩
        ⟨s', fr', values extra ++ values ws ++ [.source .return_] ++ tail⟩ := by
      simpa [values] using ht
    have step1 : Steps host ⟨s, f, values vs ++ [.frame n fr body] ++ es⟩
        ⟨s', f, values vs ++
          [.frame n fr' (values extra ++ values ws ++ [.source .return_] ++ tail)] ++ es⟩ :=
      Steps.context (Steps.frame ht' n f) vs es
    have step2 :=
      pureSteps (host := host) s' f (PureStep.frameReturn n fr' extra ws tail arity) vs es
    simpa [values] using step1.trans step2
  | @frameTrap s s' f fr fr' vs n body es _ ih =>
    show Steps host _ _
    have ht : Steps host ⟨s, fr, body⟩ ⟨s', fr', [.trap]⟩ := ih
    have step1 : Steps host ⟨s, f, values vs ++ [.frame n fr body] ++ es⟩
        ⟨s', f, values vs ++ [.frame n fr' [.trap]] ++ es⟩ :=
      Steps.context (Steps.frame ht n f) vs es
    have step2 := pureSteps (host := host) s' f (PureStep.frameTrap n fr') vs es
    refine Relation.ReflTransGen.trans ?_ (Steps.trapCollapse _ _ vs es)
    simpa [values] using step1.trans step2

theorem BigStep.toSteps_normal {s s' : Store H} {f f' : Frame} {vs ws : List Value}
    {es : List Admin} (h : BigStep host s f vs es ⟨s', f', .normal ws⟩) :
    Steps host ⟨s, f, values vs ++ es⟩ ⟨s', f', values ws⟩ := h.toSteps

theorem BigStep.toSteps_trap {s s' : Store H} {f f' : Frame} {vs : List Value}
    {es : List Admin} (h : BigStep host s f vs es ⟨s', f', .trap⟩) :
    Steps host ⟨s, f, values vs ++ es⟩ ⟨s', f', [.trap]⟩ := h.toSteps

end Silmaril.Wasm.Logic.V1
