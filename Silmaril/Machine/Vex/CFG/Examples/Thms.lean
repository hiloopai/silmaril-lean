module

import Silmaril.Machine.Vex.CFG.Rows.Thms
import Silmaril.Machine.Vex.CFG.Examples.Defs

namespace Silmaril.Machine.Vex.ControlFlow.Examples

private theorem caller_wf : FlatWellFormed partition false caller := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩ <;> simp [caller, Silmaril.Semantics.Region.Tree.FlatCFG.SourceClosed]

private theorem direct_wf {target : Label}
    (classified : (∃ callee, partition.owner target = some callee ∧ target = partition.entry callee) ∨
      partition.External target) : (direct target).WellFormed partition false := by
  refine ⟨caller_wf, ?_⟩
  intro origin site found
  cases origin <;> simp [direct] at found
  subst site
  exact ⟨rfl, rfl, classified, by rintro _ ⟨rfl⟩; rfl⟩

private theorem internal_wf : (direct .callee).WellFormed partition false := direct_wf (Or.inl ⟨true, rfl, rfl⟩)

private theorem external_wf : (direct .imported).WellFormed partition false := direct_wf (Or.inr ⟨rfl, rfl⟩)

example : (CallCFG.embed caller).InFlatImage partition false := ⟨caller, caller_wf, rfl⟩

example : (callFilling Label Bool).Reg (CallCFG.embed caller) (partition, false) {.start, .resume} .start ∅ := by
  apply callReg_embed.mpr
  refine ⟨caller_wf, by simp, ?_, ?_⟩
  · intro label member
    simp at member
    rcases member with rfl | rfl <;> rfl
  · ext edge; cases edge <;> simp [boundary, ordinaryEdges, caller]

example : (callFilling Label Bool).BB (CallCFG.embed caller) (partition, false) .start .start ∅ := by
  apply callBB_embed.mpr
  refine ⟨rfl, caller_wf, by simp, ?_, ?_⟩
  · intro label member
    simp at member
    subst label
    rfl
  · ext edge; cases edge <;> simp [boundary, ordinaryEdges, caller]

private theorem internal_edge : .call .callee ∈ (direct .callee).edges .start := ⟨_, rfl, rfl⟩

example : .fakeReturn .resume ∈ (direct .callee).edges .start := ⟨_, rfl, rfl⟩
example : .ordinary .resume ∉ (direct .callee).edges .start := by simp [CallCFG.edges, direct, caller]
example : (direct .callee).flow = (CallCFG.embed caller).flow := rfl

example : ¬ (direct .callee).InFlatImage partition false := by
  intro flat
  have noCalls := (CallCFG.inFlatImage_iff_noCalls internal_wf).mp flat
  have present : (direct .callee).calls .start = some ⟨.callee, some .resume⟩ := rfl
  rw [noCalls .start] at present
  cases present

example : (direct .callee).HasInternalCall partition := ⟨_, _, internal_edge, true, rfl⟩

example : callRow .callee {.call .callee, .fakeReturn .resume} := by
  refine ⟨rfl, internal_wf, by simp, ?_, ?_⟩
  · intro label member
    simp at member
    subst label
    rfl
  · ext edge
    cases edge with
    | ordinary => simp [boundary, CallCFG.edges, direct, caller]
    | call target => cases target <;> simp [boundary, CallCFG.edges, direct, caller]
    | fakeReturn next => cases next <;> simp [boundary, CallCFG.edges, direct, caller]

example : (direct .imported).HasExternalCall partition := ⟨.start, .imported, ⟨_, rfl, rfl⟩, rfl, rfl⟩

example : ¬ (direct .imported).HasInternalCall partition := by
  rintro ⟨origin, target, ⟨site, found, rfl⟩, callee, owned⟩
  cases origin <;> simp [direct] at found
  subst site
  cases owned

example : ¬ (direct .imported).InFlatImage partition false := by
  intro flat
  have noCalls := (CallCFG.inFlatImage_iff_noCalls external_wf).mp flat
  have present : (direct .imported).calls .start = some ⟨.imported, some .resume⟩ := rfl
  rw [noCalls .start] at present
  cases present

#print axioms CallCFG.inFlatImage_iff_noInternalCall
#print axioms commonReg_iff
#print axioms commonBB_iff

end Silmaril.Machine.Vex.ControlFlow.Examples
