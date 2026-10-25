module

public import Silmaril.Wasm.Binaryen.MergeBackControl
public import Silmaril.Wasm.Binaryen.MergeBackAggregate

@[expose] public section

/-! # Exact backward simulation for closed-host module merging

Every actual target step can be reproduced from a related, scoped source while
retaining the relation to that exact target successor. Numeric profile choices
are matched directly, so no numerical determinism or invocation typing is needed.
-/

namespace Silmaril.Wasm.Binaryen.MergeUntyped

open Execution.Core Numerics Validation
open Silmaril.Wasm.Link.GC Silmaril.Wasm.Link.GC.AdminRelation

variable {H : Type} {P : Profile}

private theorem throwing_control (mode : Mode) (left right : ModuleInst) (a : Nat) :
    Control mode left right (throwing a) (throwing a) := .ref (.throwRef .nil)

/-- Reproduce the particular target successor, preserving matching stores,
frames and administrative code. The host relation remains empty, since an
arbitrary host could inspect the different stored function bodies. -/
theorem back_matching {target target' : Config H}
    (step : Step P Simulation.noHost target target') :
    BackwardStep P Simulation.noHost target target' := by
  induction step
  case parametric h => exact BackwardStep.parametric h
  case numeric h => exact BackwardStep.numeric h
  case vector h => exact BackwardStep.vector h
  case «variable» h => exact BackwardStep.variable h
  case table h => exact BackwardStep.table h
  case memory h => exact BackwardStep.memory h
  case reference h => exact BackwardStep.reference h
  case aggregate h => exact BackwardStep.aggregate h
  case ctxtInstrs step nonempty ih => exact BackwardStep.instrs step nonempty ih
  case ctxtLabel step ih => exact BackwardStep.label ih
  case ctxtHandler step ih => exact BackwardStep.handler step ih
  case ctxtFrame step ih => exact BackwardStep.frame ih
  case callRefHost _ _ _ _ _ impossible => exact impossible.elim
  case callRefHostDiv _ _ _ _ _ impossible => exact impossible.elim
  case throw s f x vs ta ti ts tag signature arity =>
    rintro mode ⟨s₀, f₀, X⟩ matching _
    obtain ⟨i, rfl, rewrite⟩ := matching.code.vals_plain_right rfl
    cases mode with
    | same =>
      obtain rfl := frames_same matching.frames
      change i = _ at rewrite
      subst rewrite
      have tags : s₀.tags = s.tags := matching.stores.tags
      have tag₀ : s₀.tag? f₀ x = some (ta, ti) := by
        simpa only [Store.tag?, tags] using tag
      have sourceStep := Step.throw (P := P) (host := Simulation.noHost) tag₀ signature arity
      have exns : s₀.exns = s.exns := matching.stores.exns
      rw [exns] at sourceStep
      exact ⟨_, sourceStep, matching.stores.addExn _, .same _, throwing_control _ _ _ _⟩
    | relocated r => exact (inv_none rewrite (fun h => h) (by simp [instruction?])).elim
  case throwRefNull =>
    rintro mode ⟨s₀, f₀, X⟩ matching _
    obtain ⟨rest, rfl, tail⟩ := matching.code.ref_right
    obtain ⟨rest₀, rfl, tail₀⟩ := tail.throwRef_right
    obtain rfl := tail₀.nil_right
    exact ⟨_, .throwRefNull, matching.stores, matching.frames, .trap .nil⟩
  case throwRefInstrs s f vs a rest nonempty =>
    rintro mode ⟨s₀, f₀, X⟩ matching _
    have control := matching.code
    rw [List.append_assoc] at control
    obtain ⟨R, rfl, hR⟩ := control.vals_right
    obtain ⟨R', rfl, hR'⟩ := hR.ref_right
    obtain ⟨rest₀, rfl, tail⟩ := hR'.throwRef_right
    have nonempty₀ : vs ≠ [] ∨ rest₀ ≠ [] := by
      rcases nonempty with h | h
      · exact .inl h
      · right
        intro empty
        subst empty
        exact h tail.nil_left
    refine ⟨⟨s₀, f₀, throwing a⟩, ?_, matching.stores, matching.frames,
      throwing_control _ _ _ _⟩
    simpa only [throwing, List.append_assoc, List.cons_append, List.nil_append] using
      (Step.throwRefInstrs nonempty₀ : Step P Simulation.noHost
        ⟨s₀, f₀, vals vs ++ throwing a ++ rest₀⟩ ⟨s₀, f₀, throwing a⟩)
  case throwRefLabel =>
    rintro mode ⟨s₀, f₀, X⟩ matching _
    obtain ⟨cont₀, body₀, rest, rfl, _, body, tail⟩ := matching.code.label_right
    obtain rfl := tail.nil_right
    obtain ⟨R, rfl, hR⟩ := body.ref_right
    obtain ⟨R', rfl, hR'⟩ := hR.throwRef_right
    obtain rfl := hR'.nil_right
    exact ⟨_, .throwRefLabel, matching.stores, matching.frames, throwing_control _ _ _ _⟩
  case throwRefFrame =>
    rintro mode ⟨s₀, f₀, X⟩ matching _
    obtain ⟨innerMode, fi₀, body₀, rest, rfl, _, body, tail⟩ := matching.code.frame_right
    obtain rfl := tail.nil_right
    obtain ⟨R, rfl, hR⟩ := body.ref_right
    obtain ⟨R', rfl, hR'⟩ := hR.throwRef_right
    obtain rfl := hR'.nil_right
    exact ⟨_, .throwRefFrame, matching.stores, matching.frames, throwing_control _ _ _ _⟩
  case throwRefHandlerEmpty =>
    rintro mode ⟨s₀, f₀, X⟩ matching _
    obtain ⟨body₀, rest, rfl, _, _, body, tail⟩ := matching.code.handler_right
    obtain rfl := tail.nil_right
    obtain ⟨R, rfl, hR⟩ := body.ref_right
    obtain ⟨R', rfl, hR'⟩ := hR.throwRef_right
    obtain rfl := hR'.nil_right
    exact ⟨_, .throwRefHandlerEmpty, matching.stores, matching.frames, throwing_control _ _ _ _⟩
  case throwRefHandlerCatch s f n x l cs a e exception tag =>
    rintro mode ⟨s₀, f₀, X⟩ matching _
    obtain ⟨body₀, rest, rfl, rfl, _, body, tail⟩ := matching.code.handler_right
    obtain rfl := tail.nil_right
    obtain rfl := frames_same matching.frames
    obtain ⟨R, rfl, hR⟩ := body.ref_right
    obtain ⟨R', rfl, hR'⟩ := hR.throwRef_right
    obtain rfl := hR'.nil_right
    have exception₀ : s₀.exns[a]? = some e := by rwa [matching.stores.exns]
    exact ⟨_, .throwRefHandlerCatch exception₀ tag, matching.stores,
      .same _, Control.same _ _⟩
  case throwRefHandlerCatchRef s f n x l cs a e exception tag =>
    rintro mode ⟨s₀, f₀, X⟩ matching _
    obtain ⟨body₀, rest, rfl, rfl, _, body, tail⟩ := matching.code.handler_right
    obtain rfl := tail.nil_right
    obtain rfl := frames_same matching.frames
    obtain ⟨R, rfl, hR⟩ := body.ref_right
    obtain ⟨R', rfl, hR'⟩ := hR.throwRef_right
    obtain rfl := hR'.nil_right
    have exception₀ : s₀.exns[a]? = some e := by rwa [matching.stores.exns]
    exact ⟨_, .throwRefHandlerCatchRef exception₀ tag, matching.stores,
      .same _, Control.same _ _⟩
  case throwRefHandlerCatchAll =>
    rintro mode ⟨s₀, f₀, X⟩ matching _
    obtain ⟨body₀, rest, rfl, rfl, modules, body, tail⟩ := matching.code.handler_right
    obtain rfl := tail.nil_right
    obtain rfl := frames_same matching.frames
    obtain ⟨R, rfl, hR⟩ := body.ref_right
    obtain ⟨R', rfl, hR'⟩ := hR.throwRef_right
    obtain rfl := hR'.nil_right
    exact ⟨_, .throwRefHandlerCatchAll, matching.stores, .same _, Control.same _ _⟩
  case throwRefHandlerCatchAllRef =>
    rintro mode ⟨s₀, f₀, X⟩ matching _
    obtain ⟨body₀, rest, rfl, rfl, modules, body, tail⟩ := matching.code.handler_right
    obtain rfl := tail.nil_right
    obtain rfl := frames_same matching.frames
    obtain ⟨R, rfl, hR⟩ := body.ref_right
    obtain ⟨R', rfl, hR'⟩ := hR.throwRef_right
    obtain rfl := hR'.nil_right
    exact ⟨_, .throwRefHandlerCatchAllRef, matching.stores, .same _, Control.same _ _⟩
  case throwRefHandlerNext s f n c cs a unmatched =>
    rintro mode ⟨s₀, f₀, X⟩ matching _
    obtain ⟨body₀, rest, rfl, rfl, _, body, tail⟩ := matching.code.handler_right
    obtain rfl := tail.nil_right
    obtain rfl := frames_same matching.frames
    obtain ⟨R, rfl, hR⟩ := body.ref_right
    obtain ⟨R', rfl, hR'⟩ := hR.throwRef_right
    obtain rfl := hR'.nil_right
    have unmatched₀ : ¬ CatchMatches s₀ f₀ a c := by
      rwa [catchMatches_iff matching.stores.exns]
    exact ⟨_, .throwRefHandlerNext unmatched₀, matching.stores, .same _, Control.same _ _⟩
  case tryTable s f bt cs body vs ps rs lookup arity =>
    rintro mode ⟨s₀, f₀, X⟩ matching _
    obtain ⟨i, rfl, rewrite⟩ := matching.code.vals_plain_right rfl
    cases mode with
    | same =>
      obtain rfl := frames_same matching.frames
      change i = _ at rewrite
      subst rewrite
      exact ⟨_, .tryTable lookup arity, matching.stores, .same _, Control.same _ _⟩
    | relocated r => exact (inv_none rewrite (fun h => h) (by simp [instruction?])).elim
  case handlerVals =>
    rintro mode ⟨s₀, f₀, X⟩ matching _
    obtain ⟨body₀, rest, rfl, _, _, body, tail⟩ := matching.code.handler_right
    obtain rfl := tail.nil_right
    obtain rfl := body.vals_right_exact
    exact ⟨_, .handlerVals, matching.stores, matching.frames, Control.values _ _ _ _⟩
  case block lookup arity => exact BackwardStep.block lookup arity
  case loop lookup arity => exact BackwardStep.loop lookup arity
  case ifTrue condition => exact BackwardStep.ifTrue condition
  case ifFalse => exact BackwardStep.ifFalse
  case labelVals => exact BackwardStep.labelVals
  case brLabelZero zero arity => exact BackwardStep.brLabelZero zero arity
  case brLabelSucc positive => exact BackwardStep.brLabelSucc positive
  case brHandler => exact BackwardStep.brHandler
  case brIfTrue condition => exact BackwardStep.brIfTrue condition
  case brIfFalse => exact BackwardStep.brIfFalse
  case brTableLt lookup => exact BackwardStep.brTableLt lookup
  case brTableGe bound => exact BackwardStep.brTableGe bound
  case brOnNullNull => exact BackwardStep.brOnNullNull
  case brOnNullAddr nonnull => exact BackwardStep.brOnNullAddr nonnull
  case brOnNonNullNull => exact BackwardStep.brOnNonNullNull
  case brOnNonNullAddr nonnull => exact BackwardStep.brOnNonNullAddr nonnull
  case brOnCastSucceed valid => exact BackwardStep.brOnCastSucceed valid
  case brOnCastFail invalid => exact BackwardStep.brOnCastFail invalid
  case brOnCastFailSucceed valid => exact BackwardStep.brOnCastFailSucceed valid
  case brOnCastFailFail invalid => exact BackwardStep.brOnCastFailFail invalid
  case call lookup definition => exact BackwardStep.call lookup definition
  case returnCall lookup definition => exact BackwardStep.returnCall lookup definition
  case callRefNull call => exact BackwardStep.callRefNull call
  case callRefFunc call definition signature arity wasm =>
    exact BackwardStep.callRefFunc call definition signature arity wasm
  case returnCallRefLabel call => exact BackwardStep.returnCallRefLabel call
  case returnCallRefHandler call => exact BackwardStep.returnCallRefHandler call
  case returnCallRefFrameNull call => exact BackwardStep.returnCallRefFrameNull call
  case returnCallRefFrameAddr call definition signature arity =>
    exact BackwardStep.returnCallRefFrameAddr call definition signature arity
  case callIndirect => exact BackwardStep.callIndirect
  case returnCallIndirect => exact BackwardStep.returnCallIndirect
  case frameVals arity => exact BackwardStep.frameVals arity
  case returnFrame arity => exact BackwardStep.returnFrame arity
  case returnLabel => exact BackwardStep.returnLabel
  case returnHandler => exact BackwardStep.returnHandler
  case trapInstrs nonempty => exact BackwardStep.trapInstrs nonempty
  case trapLabel => exact BackwardStep.trapLabel
  case trapHandler => exact BackwardStep.trapHandler
  case trapFrame => exact BackwardStep.trapFrame

end Silmaril.Wasm.Binaryen.MergeUntyped
