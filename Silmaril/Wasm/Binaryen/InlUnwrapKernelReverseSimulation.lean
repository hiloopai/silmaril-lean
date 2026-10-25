module

public import Silmaril.Wasm.Binaryen.InlUnwrapKernelReverseStep

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded Det

variable {R : List Instr} {H : Type} {P : Profile}
variable {rank : List Admin → Nat} [LawfulCodeRank rank]
variable {F : FuncInst H → FuncInst H → Prop}

/-- The full recursive law is a compatible constant-family base-step law. -/
theorem typed_kernel_reverse_base_step
    (hF : ∀ fi gi, F fi gi → FuncRel (fun x y => UIL R y x) fi gi)
    (budget : ∃ S, ∀ i ∈ R, InstrB budU S i) (labels : instrsLabels R = []) :
    TypedBaseStepTo P F (fun x y => UIL R y x) (fun x y => KUL R y x)
      (fun x y => KUL R y x) rank where
  step := fun stores related _ typed selected =>
    KUL.typed_step_reverse hF budget labels related stores typed selected

omit [LawfulCodeRank rank] in
/-- Terminal normalization retains the final store relation and exact result. -/
theorem KUL.terminal_reverse
    (budget : ∃ S, ∀ i ∈ R, InstrB budU S i) (labels : instrsLabels R = [])
    {c d : Config H} {result : Result}
    (related : CfgRel F (fun x y => KUL R y x) c d) (typed : ContextTyped d)
    (terminal : c.code = result.toAdmin) :
    ∃ d', Steps P noHost d d' ∧ d'.code = result.toAdmin ∧ StoreRel F c.store d'.store := by
  exact Closure.kernel_terminal_case_store (typed_kernel_expanded_facts_reverse budget labels F)
    (related.mono (fun _ _ h => .base (Or.inl h))) typed terminal

/-- A genuine arbitrary-profile simulation over the full recursive relation.
The original target supplies typing; recursively introduced cuts are absorbed
after every actual selected step rather than accumulated as an external premise. -/
theorem typed_kernel_reverse_configSim
    (hF : ∀ fi gi, F fi gi → FuncRel (fun x y => UIL R y x) fi gi)
    (budget : ∃ S, ∀ i ∈ R, InstrB budU S i) (labels : instrsLabels R = []) :
    ∃ sim : ConfigSim P noHost
      (fun c d => CfgRel F (fun x y => KUL R y x) c d ∧ ContextTyped d),
      sim.toForwardSim.measure = fun c => rank c.code := by
  refine ⟨⟨⟨fun c => rank c.code, ?_⟩, ?_⟩, rfl⟩
  · intro c c' d selected relation
    obtain ⟨s, f, bare⟩ := c
    obtain ⟨t, g, original⟩ := d
    obtain ⟨⟨stores, frames, code⟩, typed⟩ := relation
    dsimp only at stores frames code typed selected ⊢
    subst g
    obtain ⟨d', progress, after⟩ := KUL.typed_step_reverse (rank := rank) hF budget labels code
      (ambient := []) stores (by simpa using typed) (by simpa using selected)
    have progress' : Relation.TransGen (Step P noHost) ⟨t, f, original⟩ d' ∨
        (d' = ⟨t, f, original⟩ ∧ rank c'.code < rank bare) := by
      simpa only [Execution.Core.vals_nil', List.nil_append] using progress
    refine ⟨d', progress', ⟨after.store, after.frame, KUL.of_core_reverse after.code⟩, ?_⟩
    rcases progress' with progress' | ⟨rfl, _⟩
    · exact typed.steps progress'.to_reflTransGen
    · exact typed
  · intro c d result relation terminal
    obtain ⟨d', run, result', _⟩ := KUL.terminal_reverse budget labels relation.1 relation.2 terminal
    exact ⟨d', run, result'⟩

/-- Every finite completed transformed run has an original run with the exact
same values/trap/exception and related final store, at the same profile. -/
theorem KUL.run_reverse
    (hF : ∀ fi gi, F fi gi → FuncRel (fun x y => UIL R y x) fi gi)
    (budget : ∃ S, ∀ i ∈ R, InstrB budU S i) (labels : instrsLabels R = [])
    {c d c' : Config H} {result : Result}
    (related : CfgRel F (fun x y => KUL R y x) c d) (typed : ContextTyped d)
    (run : Steps P noHost c c') (terminal : c'.code = result.toAdmin) :
    ∃ d', Steps P noHost d d' ∧ d'.code = result.toAdmin ∧ StoreRel F c'.store d'.store := by
  obtain ⟨sim, _⟩ := typed_kernel_reverse_configSim (rank := codeSize) hF budget labels
  obtain ⟨d₁, first, relation, typed₁⟩ := sim.toForwardSim.steps run ⟨related, typed⟩
  obtain ⟨d', last, same, stores⟩ := KUL.terminal_reverse budget labels relation typed₁ terminal
  exact ⟨d', first.trans last, same, stores⟩

/-- Infinite transformed executions also force original divergence; lawful
source-rank decreases prevent an infinite sequence of matched stutters. -/
theorem KUL.diverges_reverse
    (hF : ∀ fi gi, F fi gi → FuncRel (fun x y => UIL R y x) fi gi)
    (budget : ∃ S, ∀ i ∈ R, InstrB budU S i) (labels : instrsLabels R = [])
    {c d : Config H} (related : CfgRel F (fun x y => KUL R y x) c d)
    (typed : ContextTyped d) (diverges : Diverges P noHost c) : Diverges P noHost d := by
  obtain ⟨sim, _⟩ := typed_kernel_reverse_configSim (rank := codeSize) hF budget labels
  exact sim.toForwardSim.diverges diverges ⟨related, typed⟩

theorem KUL.behaviours_reverse
    (hF : ∀ fi gi, F fi gi → FuncRel (fun x y => UIL R y x) fi gi)
    (budget : ∃ S, ∀ i ∈ R, InstrB budU S i) (labels : instrsLabels R = [])
    {c d : Config H} (related : CfgRel F (fun x y => KUL R y x) c d)
    (typed : ContextTyped d) : behavioursOf P noHost c ⊆ behavioursOf P noHost d := by
  obtain ⟨sim, _⟩ := typed_kernel_reverse_configSim (rank := codeSize) hF budget labels
  exact sim.behavioursOf_subset ⟨related, typed⟩

end Silmaril.Wasm.Binaryen.Unwrap
