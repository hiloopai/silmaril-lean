module

public import Silmaril.Wasm.Link.ContextSimulation
public import Silmaril.Wasm.Link.LeafControlSimulation
public import Silmaril.Wasm.Link.StructuralSimulation
public import Silmaril.Wasm.Link.AmbientSimulation
public import Silmaril.Wasm.Execution.Core.Soundness
public import Silmaril.Wasm.Execution.Core.Properties

/-! # Whole core executions across actual linked stores

Each source reduction has a matching target reduction. Source configuration
typing supplies scoped annotations and stored bodies throughout a run. The
host relation is empty: arbitrary host code could inspect the different stored
bodies and would need a separate relational host contract.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.WholeSimulation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open AdminRelation Simulation

variable {H : Type} {P : Profile}

theorem step {source sourceFinal : Config H} (sourceStep : Step P noHost source sourceFinal) :
    ∀ {mode : Mode} {target : Config H}, Matching mode source target →
      AdminScope.Admins source.frame.module.types.length source.code →
      FunctionScopes source.store →
      ∃ targetFinal, Step P noHost target targetFinal ∧ Matching mode sourceFinal targetFinal := by
  induction sourceStep
  all_goals intro mode target matching scope functions
  case parametric h => exact LeafControlSimulation.parametric h matching
  case numeric h => exact LeafControlSimulation.numeric h matching
  case vector h => exact LeafControlSimulation.vector h matching
  case «variable» h => exact LeafControlSimulation.variable h matching
  case table h => exact AmbientSimulation.table h matching
  case memory h => exact AmbientSimulation.memory h matching
  case reference h => exact LeafControlSimulation.reference h matching scope
  case aggregate h => exact LeafControlSimulation.aggregate_step h matching
  case ctxtInstrs sourceStep nonempty ih =>
    exact ContextSimulation.instrs sourceStep nonempty matching scope
      (fun paired boundScope => ih paired boundScope functions)
  case ctxtLabel sourceStep ih =>
    exact ContextSimulation.label sourceStep matching scope
      (fun paired boundScope => ih paired boundScope functions)
  case ctxtHandler sourceStep ih =>
    exact ContextSimulation.handler sourceStep matching scope
      (fun paired boundScope => ih paired boundScope functions)
  case ctxtFrame sourceStep ih =>
    exact ContextSimulation.frame sourceStep matching scope
      (fun paired boundScope => ih paired boundScope functions)
  case callRefHost _ _ _ _ _ impossible => exact False.elim impossible
  case callRefHostDiv _ _ _ _ _ impossible => exact False.elim impossible
  case block hbt hm =>
    exact StructuralSimulation.step (.block hbt hm) (.block hbt hm) matching scope functions
  case loop hbt hm =>
    exact StructuralSimulation.step (.loop hbt hm) (.loop hbt hm) matching scope functions
  case ifTrue hc =>
    exact StructuralSimulation.step (.ifTrue hc) (.ifTrue hc) matching scope functions
  case ifFalse =>
    exact StructuralSimulation.step (.ifFalse) (.ifFalse) matching scope functions
  case labelVals =>
    exact StructuralSimulation.step (.labelVals) (.labelVals) matching scope functions
  case brLabelZero hl hn =>
    exact StructuralSimulation.step (.brLabelZero hl hn) (.brLabelZero hl hn) matching scope functions
  case brLabelSucc hl =>
    exact StructuralSimulation.step (.brLabelSucc hl) (.brLabelSucc hl) matching scope functions
  case brHandler =>
    exact StructuralSimulation.step (.brHandler) (.brHandler) matching scope functions
  case brIfTrue hc =>
    exact StructuralSimulation.step (.brIfTrue hc) (.brIfTrue hc) matching scope functions
  case brIfFalse =>
    exact StructuralSimulation.step (.brIfFalse) (.brIfFalse) matching scope functions
  case brTableLt hi =>
    exact StructuralSimulation.step (.brTableLt hi) (.brTableLt hi) matching scope functions
  case brTableGe hi =>
    exact StructuralSimulation.step (.brTableGe hi) (.brTableGe hi) matching scope functions
  case brOnNullNull =>
    exact StructuralSimulation.step (.brOnNullNull) (.brOnNullNull) matching scope functions
  case brOnNullAddr hv =>
    exact StructuralSimulation.step (.brOnNullAddr hv) (.brOnNullAddr hv) matching scope functions
  case brOnNonNullNull =>
    exact StructuralSimulation.step (.brOnNonNullNull) (.brOnNonNullNull) matching scope functions
  case brOnNonNullAddr hv =>
    exact StructuralSimulation.step (.brOnNonNullAddr hv) (.brOnNonNullAddr hv) matching scope functions
  case brOnCastSucceed h =>
    exact StructuralSimulation.step (.brOnCastSucceed h) (.brOnCastSucceed h) matching scope functions
  case brOnCastFail h =>
    exact StructuralSimulation.step (.brOnCastFail h) (.brOnCastFail h) matching scope functions
  case brOnCastFailSucceed h =>
    exact StructuralSimulation.step (.brOnCastFailSucceed h) (.brOnCastFailSucceed h) matching scope functions
  case brOnCastFailFail h =>
    exact StructuralSimulation.step (.brOnCastFailFail h) (.brOnCastFailFail h) matching scope functions
  case call hx hf =>
    exact StructuralSimulation.step (.call hx hf) (.call hx hf) matching scope functions
  case callRefNull hc =>
    exact StructuralSimulation.step (.callRefNull hc) (.callRefNull hc) matching scope functions
  case callRefFunc hc hf he hn hcode =>
    exact StructuralSimulation.step (.callRefFunc hc hf he hn hcode) (.callRefFunc hc hf he hn hcode) matching scope functions
  case returnCall hx hf =>
    exact StructuralSimulation.step (.returnCall hx hf) (.returnCall hx hf) matching scope functions
  case returnCallRefLabel hc =>
    exact StructuralSimulation.step (.returnCallRefLabel hc) (.returnCallRefLabel hc) matching scope functions
  case returnCallRefHandler hc =>
    exact StructuralSimulation.step (.returnCallRefHandler hc) (.returnCallRefHandler hc) matching scope functions
  case returnCallRefFrameNull hc =>
    exact StructuralSimulation.step (.returnCallRefFrameNull hc) (.returnCallRefFrameNull hc) matching scope functions
  case returnCallRefFrameAddr hc hf he hn =>
    exact StructuralSimulation.step (.returnCallRefFrameAddr hc hf he hn) (.returnCallRefFrameAddr hc hf he hn) matching scope functions
  case callIndirect =>
    exact StructuralSimulation.step (.callIndirect) (.callIndirect) matching scope functions
  case returnCallIndirect =>
    exact StructuralSimulation.step (.returnCallIndirect) (.returnCallIndirect) matching scope functions
  case frameVals hn =>
    exact StructuralSimulation.step (.frameVals hn) (.frameVals hn) matching scope functions
  case returnFrame hn =>
    exact StructuralSimulation.step (.returnFrame hn) (.returnFrame hn) matching scope functions
  case returnLabel =>
    exact StructuralSimulation.step (.returnLabel) (.returnLabel) matching scope functions
  case returnHandler =>
    exact StructuralSimulation.step (.returnHandler) (.returnHandler) matching scope functions
  case trapInstrs hne =>
    exact StructuralSimulation.step (.trapInstrs hne) (.trapInstrs hne) matching scope functions
  case trapLabel =>
    exact StructuralSimulation.step (.trapLabel) (.trapLabel) matching scope functions
  case trapHandler =>
    exact StructuralSimulation.step (.trapHandler) (.trapHandler) matching scope functions
  case trapFrame =>
    exact StructuralSimulation.step (.trapFrame) (.trapFrame) matching scope functions
  case throw ht he hn =>
    exact AmbientSimulation.step (.throw ht he hn) (.throw ht he hn) matching
  case throwRefNull =>
    exact AmbientSimulation.step (.throwRefNull) (.throwRefNull) matching
  case throwRefInstrs hne =>
    exact AmbientSimulation.step (.throwRefInstrs hne) (.throwRefInstrs hne) matching
  case throwRefLabel =>
    exact AmbientSimulation.step (.throwRefLabel) (.throwRefLabel) matching
  case throwRefFrame =>
    exact AmbientSimulation.step (.throwRefFrame) (.throwRefFrame) matching
  case throwRefHandlerEmpty =>
    exact AmbientSimulation.step (.throwRefHandlerEmpty) (.throwRefHandlerEmpty) matching
  case throwRefHandlerCatch he ht =>
    exact AmbientSimulation.step (.throwRefHandlerCatch he ht) (.throwRefHandlerCatch he ht) matching
  case throwRefHandlerCatchRef he ht =>
    exact AmbientSimulation.step (.throwRefHandlerCatchRef he ht) (.throwRefHandlerCatchRef he ht) matching
  case throwRefHandlerCatchAll =>
    exact AmbientSimulation.step (.throwRefHandlerCatchAll) (.throwRefHandlerCatchAll) matching
  case throwRefHandlerCatchAllRef =>
    exact AmbientSimulation.step (.throwRefHandlerCatchAllRef) (.throwRefHandlerCatchAllRef) matching
  case throwRefHandlerNext h =>
    exact AmbientSimulation.step (.throwRefHandlerNext h) (.throwRefHandlerNext h) matching
  case tryTable hbt hm =>
    exact AmbientSimulation.step (.tryTable hbt hm) (.tryTable hbt hm) matching
  case handlerVals =>
    exact AmbientSimulation.step (.handlerVals) (.handlerVals) matching

private def trapHost : HostSemantics H := fun _ s _ out => out = .returned s .trap

private theorem trap_host_ok : HostOk (trapHost (H := H)) := by
  intro s fi h vs ps rs valid _ _ _ _
  refine ⟨⟨.returned s .trap,rfl⟩,?_⟩
  intro out eq
  change out = .returned s .trap at eq
  subst out
  exact ⟨valid,Extend.refl valid,trivial⟩

/-- An empty-host run stays typed even when the host carrier is inhabited.
The total trapping host is used only to apply the existing typing theorem;
the actual execution relation remains the empty host relation. -/
theorem hostfree_typed {source final : Config H} {results : List CValType}
    (typed : ConfigOk source results) (run : Steps P noHost source final) :
    ConfigOk final results := by
  induction run with
  | refl => exact typed
  | tail _ next ih =>
    exact (Step.preservation trap_host_ok ih (next.of_noHost trapHost)).1

theorem steps {source sourceFinal target : Config H} {mode : Mode}
    {results : List CValType} (sourceSteps : Steps P noHost source sourceFinal)
    (typed : ConfigOk source results) (matching : Matching mode source target) :
    ∃ targetFinal, Steps P noHost target targetFinal ∧ Matching mode sourceFinal targetFinal := by
  induction sourceSteps with
  | refl => exact ⟨target,.refl,matching⟩
  | @tail mid final previous next ih =>
    obtain ⟨targetMid,targetSteps,paired⟩ := ih
    have midTyped : ConfigOk mid results := hostfree_typed typed previous
    obtain ⟨targetFinal,targetStep,pairedFinal⟩ := step next paired
      (AdminScope.config_scope midTyped) (function_scopes midTyped.choose_spec.1.1)
    exact ⟨targetFinal,targetSteps.tail targetStep,pairedFinal⟩

theorem values {source sourceFinal target : Config H} {mode : Mode}
    {results : List CValType} {vs : List Val} (sourceSteps : Steps P noHost source sourceFinal)
    (typed : ConfigOk source results) (matching : Matching mode source target)
    (returned : sourceFinal.code = vals vs) :
    ∃ targetFinal, Steps P noHost target targetFinal ∧ Matching mode sourceFinal targetFinal ∧
      targetFinal.code = vals vs := by
  obtain ⟨final,run,paired⟩ := steps sourceSteps typed matching
  refine ⟨final,run,paired,?_⟩
  have code := paired.code
  rw [returned] at code
  exact code.values_left

theorem trap {source sourceFinal target : Config H} {mode : Mode}
    {results : List CValType} (sourceSteps : Steps P noHost source sourceFinal)
    (typed : ConfigOk source results) (matching : Matching mode source target)
    (trapped : sourceFinal.code = [.trap]) :
    ∃ targetFinal, Steps P noHost target targetFinal ∧ Matching mode sourceFinal targetFinal ∧
      targetFinal.code = [.trap] := by
  obtain ⟨final,run,paired⟩ := steps sourceSteps typed matching
  refine ⟨final,run,paired,?_⟩
  have code := paired.code
  rw [trapped] at code
  exact code.trap_singleton

/-- An uncaught exception retains its exact store address across linking. -/
theorem throw {source sourceFinal target : Config H} {mode : Mode}
    {results : List CValType} {address : Nat}
    (sourceSteps : Steps P noHost source sourceFinal)
    (typed : ConfigOk source results) (matching : Matching mode source target)
    (thrown : sourceFinal.code = throwing address) :
    ∃ targetFinal, Steps P noHost target targetFinal ∧ Matching mode sourceFinal targetFinal ∧
      targetFinal.code = throwing address := by
  obtain ⟨final,run,paired⟩ := steps sourceSteps typed matching
  refine ⟨final,run,paired,?_⟩
  have code := paired.code
  rw [thrown] at code
  exact code.throwing_left

end Silmaril.Wasm.Link.GC.WholeSimulation
