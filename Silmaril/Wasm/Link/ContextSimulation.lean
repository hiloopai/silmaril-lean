module

public import Silmaril.Wasm.Link.SimulationDefs

/-! # Recursive contexts for linked execution

Instruction suffixes and labels keep the current frame's mode. A nested frame
uses its own mode, so calls can cross between unchanged and relocated code.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.ContextSimulation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open AdminRelation Simulation

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem instrs {s s' : Store H} {f f' : Frame} {vs : List Val}
    {code out rest : List Execution.Core.Admin} {mode : Mode} {target : Config H}
    (sourceStep : Step P host ⟨s,f,code⟩ ⟨s',f',out⟩)
    (nonempty : vs ≠ [] ∨ rest ≠ [])
    (matching : Matching mode ⟨s,f,vals vs ++ code ++ rest⟩ target)
    (scope : AdminScope.Admins f.module.types.length (vals vs ++ code ++ rest))
    (inner : ∀ {t : Config H}, Matching mode ⟨s,f,code⟩ t →
      AdminScope.Admins f.module.types.length code →
      ∃ t', Step P host t t' ∧ Matching mode ⟨s',f',out⟩ t') :
    ∃ targetFinal, Step P host target targetFinal ∧
      Matching mode ⟨s',f',vals vs ++ out ++ rest⟩ targetFinal := by
  rcases target with ⟨st,ft,ct⟩
  have control := matching.code
  rw [List.append_assoc] at control
  obtain ⟨suffix,rfl,tail⟩ := control.values_prefix
  obtain ⟨code',rest',rfl,hcode,hrest⟩ := tail.split
  obtain ⟨final,step,paired⟩ := inner (t := ⟨st,ft,code'⟩) ⟨matching.stores,matching.frames,hcode⟩
    (AdminScope.split (AdminScope.split scope).1).2
  have nonempty' : vs ≠ [] ∨ rest' ≠ [] := by
    rcases nonempty with h | h
    · exact .inl h
    · right
      intro e
      have hl := hrest.length_eq
      rw [e] at hl
      exact h (List.length_eq_zero_iff.mp hl)
  refine ⟨⟨final.store,final.frame,vals vs ++ final.code ++ rest'⟩,
    by simpa only [List.append_assoc] using Step.ctxtInstrs step nonempty',
    ⟨paired.stores,paired.frames,?_⟩⟩
  have suffix : Control mode f'.module final.frame.module rest rest' := by
    rw [frame_module sourceStep,frame_module step]
    exact hrest
  exact ((Control.values _ _ _ vs).append paired.code).append suffix

theorem label {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
    {code out : List Execution.Core.Admin} {mode : Mode} {target : Config H}
    (_sourceStep : Step P host ⟨s,f,code⟩ ⟨s',f',out⟩)
    (matching : Matching mode ⟨s,f,[.label n cont code]⟩ target)
    (scope : AdminScope.Admins f.module.types.length [.label n cont code])
    (inner : ∀ {t : Config H}, Matching mode ⟨s,f,code⟩ t →
      AdminScope.Admins f.module.types.length code →
      ∃ t', Step P host t t' ∧ Matching mode ⟨s',f',out⟩ t') :
    ∃ targetFinal, Step P host target targetFinal ∧
      Matching mode ⟨s',f',[.label n cont out]⟩ targetFinal := by
  rcases target with ⟨st,ft,ct⟩
  obtain ⟨cont',code',rfl,hcont,hcode⟩ := matching.code.label_singleton
  have bodyScope := (AdminScope.label_scope.mp (AdminScope.admins_singleton_iff.mp scope)).2
  obtain ⟨final,step,paired⟩ := inner (t := ⟨st,ft,code'⟩)
    ⟨matching.stores,matching.frames,hcode⟩ bodyScope
  refine ⟨⟨final.store,final.frame,[.label n cont' final.code]⟩,
    .ctxtLabel step,⟨paired.stores,paired.frames,?_⟩⟩
  have continuation : Instructions mode cont cont' := hcont
  exact .label continuation paired.code .nil

theorem frame {s s' : Store H} {caller f f' : Frame} {n : Nat}
    {code out : List Execution.Core.Admin} {mode : Mode} {target : Config H}
    (_sourceStep : Step P host ⟨s,f,code⟩ ⟨s',f',out⟩)
    (matching : Matching mode ⟨s,caller,[.frame n f code]⟩ target)
    (scope : AdminScope.Admins caller.module.types.length [.frame n f code])
    (inner : ∀ {innerMode : Mode} {t : Config H}, Matching innerMode ⟨s,f,code⟩ t →
      AdminScope.Admins f.module.types.length code →
      ∃ t', Step P host t t' ∧ Matching innerMode ⟨s',f',out⟩ t') :
    ∃ targetFinal, Step P host target targetFinal ∧
      Matching mode ⟨s',caller,[.frame n f' out]⟩ targetFinal := by
  rcases target with ⟨st,ft,ct⟩
  obtain ⟨innerMode,fr,code',rfl,hframe,hcode⟩ := matching.code.frame_singleton
  have bodyScope := AdminScope.frame_scope.mp (AdminScope.admins_singleton_iff.mp scope)
  obtain ⟨final,step,paired⟩ := inner (innerMode := innerMode) (t := ⟨st,fr,code'⟩)
    ⟨matching.stores,hframe,hcode⟩ bodyScope
  exact ⟨⟨final.store,ft,[.frame n final.frame final.code]⟩,
    .ctxtFrame step,⟨paired.stores,matching.frames,.frame paired.frames paired.code .nil⟩⟩

theorem handler {s s' : Store H} {f f' : Frame} {n : Nat} {catches : List Catch}
    {code out : List Execution.Core.Admin} {mode : Mode} {target : Config H}
    (sourceStep : Step P host ⟨s,f,code⟩ ⟨s',f',out⟩)
    (matching : Matching mode ⟨s,f,[.handler n catches code]⟩ target)
    (scope : AdminScope.Admins f.module.types.length [.handler n catches code])
    (inner : ∀ {innerMode : Mode} {t : Config H}, Matching innerMode ⟨s,f,code⟩ t →
      AdminScope.Admins f.module.types.length code →
      ∃ t', Step P host t t' ∧ Matching innerMode ⟨s',f',out⟩ t') :
    ∃ targetFinal, Step P host target targetFinal ∧
      Matching mode ⟨s',f',[.handler n catches out]⟩ targetFinal := by
  rcases target with ⟨st,ft,ct⟩
  obtain ⟨rfl,modules,code',rest',rfl,hbody,empty⟩ := matching.code.handler_cons
  have emptyRest := empty.nil_left
  subst rest'
  change f.module = ft.module at modules
  have bodyScope := AdminScope.handler_scope.mp (AdminScope.admins_singleton_iff.mp scope)
  obtain ⟨final,step,paired⟩ := inner (innerMode := .same) (t := ⟨st,ft,code'⟩)
    ⟨matching.stores,matching.frames,by simpa only [modules] using hbody⟩ bodyScope
  have modules' : f'.module = final.frame.module := by
    rw [frame_module sourceStep,frame_module step]
    exact modules
  refine ⟨⟨final.store,final.frame,[.handler n catches final.code]⟩,
    .ctxtHandler step,⟨paired.stores,paired.frames,?_⟩⟩
  have output := paired.code
  change Control .same f'.module final.frame.module out final.code at output
  change Control .same f'.module final.frame.module _ _
  rw [← modules'] at output ⊢
  exact .handler output .nil

end Silmaril.Wasm.Link.GC.ContextSimulation
