module

public import Silmaril.Wasm.Binaryen.MergeProfileEquivalence

@[expose] public section

/-! # Stateful export sessions across a merge chain

The initialization chain additionally records validity and allocation boundaries.
During execution, only the linking relation and source annotation scope, or a
global-address renaming, are needed. Both exact invocation transports retain
that relation on the actual final stores. This permits successive calls without
assuming numerical determinism or pairing unrelated equal-result runs.
-/

namespace Silmaril.Wasm.Binaryen.MergeChain

open Execution.Core Validation Numerics Link.GC

variable {H : Type}

/-- The execution invariant of one initialized merge link. -/
inductive SessionLink : Store H → Store H → Prop where
  | related {s t : Store H} (rel : StoreRelation.Related s t)
      (scope : MergeUntyped.StoreSc s) : SessionLink s t
  | renamed {s t : Store H} {p : Nat ≃ Nat}
      (rel : GlobalPermutation.Renamed p s t) : SessionLink s t

/-- The same finite chain, retaining only its execution invariants. -/
inductive SessionChain : Store H → Store H → Prop where
  | refl (s : Store H) : SessionChain s s
  | cons {s t u : Store H} (link : SessionLink s t)
      (tail : SessionChain t u) : SessionChain s u

theorem Chain.sessionChain {s t : Store H} (chain : Chain s t) : SessionChain s t := by
  induction chain with
  | refl => exact .refl _
  | cons link _ ih =>
    cases link with
    | related rel valid => exact .cons (.related rel (MergeUntyped.storeSc_of_ok valid)) ih
    | renamed rel _ _ => exact .cons (.renamed rel) ih

private theorem invokeOk_of_views {s t : Store H} {a : Nat} {vs : List Val}
    (tags : s.funcs[a]?.map FuncInst.type = t.funcs[a]?.map FuncInst.type)
    (values : ∀ v ty, ValOk s v ty → ValOk t v ty)
    (ok : InvokeOk s a vs) : InvokeOk t a vs := by
  obtain ⟨fi, ps, rs, lookup, expanded, args⟩ := ok
  rw [lookup, Option.map_some] at tags
  obtain ⟨fi', lookup', typeEq⟩ := Option.map_eq_some_iff.mp tags.symm
  refine ⟨fi', ps, rs, lookup', typeEq ▸ expanded, ?_⟩
  exact args.imp (fun v ty hv => values v ty hv)

theorem SessionLink.invokeOk_iff {s t : Store H} (link : SessionLink s t)
    (a : Nat) (vs : List Val) : InvokeOk s a vs ↔ InvokeOk t a vs := by
  cases link with
  | related rel _ =>
    exact ⟨invokeOk_of_views (rel.function_tag_lookup a) (fun v ty => (rel.valOk_iff v ty).mp),
      invokeOk_of_views (rel.function_tag_lookup a).symm (fun v ty => (rel.valOk_iff v ty).mpr)⟩
  | renamed rel =>
    exact ⟨invokeOk_of_views (rel.function_tag_lookup a) (fun v ty => (rel.valOk_iff v ty).mp),
      invokeOk_of_views (rel.function_tag_lookup a).symm (fun v ty => (rel.valOk_iff v ty).mpr)⟩

theorem SessionChain.invokeOk_iff {s t : Store H} (chain : SessionChain s t)
    (a : Nat) (vs : List Val) : InvokeOk s a vs ↔ InvokeOk t a vs := by
  induction chain with
  | refl => rfl
  | cons link _ ih => exact (link.invokeOk_iff a vs).trans ih

theorem SessionLink.invoke_result_forward {P : Profile} {s t : Store H}
    (link : SessionLink s t) {a : Nat} {vs : List Val} {c : Config H} {r : Result}
    (run : Steps P Simulation.noHost (invoke s a vs) c) (result : c.code = r.toAdmin) :
    ∃ d, Steps P Simulation.noHost (invoke t a vs) d ∧ d.code = r.toAdmin ∧
      SessionLink c.store d.store := by
  cases link with
  | related rel scope =>
    obtain ⟨d, run', matching, _, scope'⟩ := MergeUntyped.fwd_steps run
      (MergeUntyped.invoke_matching rel a vs) (MergeUntyped.invoke_scope s a vs) scope
    exact ⟨d, run', LinkObservation.paired_result matching result,
      .related matching.stores scope'⟩
  | renamed rel =>
    obtain ⟨store, run', rel', result'⟩ := GlobalRenameSimulation.invoke_result rel run result
    exact ⟨_, run', result', .renamed rel'⟩

theorem SessionLink.invoke_result_backward {P : Profile} {s t : Store H}
    (link : SessionLink s t) {a : Nat} {vs : List Val} {d : Config H} {r : Result}
    (run : Steps P Simulation.noHost (invoke t a vs) d) (result : d.code = r.toAdmin) :
    ∃ c, Steps P Simulation.noHost (invoke s a vs) c ∧ c.code = r.toAdmin ∧
      SessionLink c.store d.store := by
  cases link with
  | related rel scope =>
    obtain ⟨c, run', matching, _, scope'⟩ := MergeUntyped.bwd_steps run
      (MergeUntyped.invoke_matching rel a vs) (MergeUntyped.invoke_scope s a vs) scope
    exact ⟨c, run', MergeUntyped.terminal_back matching result,
      .related matching.stores scope'⟩
  | renamed rel =>
    obtain ⟨store, run', rel', result'⟩ := GlobalRenameSimulation.invoke_result rel.symm run result
    exact ⟨_, run', result', .renamed rel'.symm⟩

theorem SessionChain.invoke_result_forward {P : Profile} {s t : Store H}
    (chain : SessionChain s t) {a : Nat} {vs : List Val} {c : Config H} {r : Result}
    (run : Steps P Simulation.noHost (invoke s a vs) c) (result : c.code = r.toAdmin) :
    ∃ d, Steps P Simulation.noHost (invoke t a vs) d ∧ d.code = r.toAdmin ∧
      SessionChain c.store d.store := by
  induction chain generalizing c with
  | refl => exact ⟨c, run, result, .refl _⟩
  | cons link _ ih =>
    obtain ⟨middle, middleRun, middleResult, link'⟩ := link.invoke_result_forward run result
    obtain ⟨d, run', result', tail'⟩ := ih middleRun middleResult
    exact ⟨d, run', result', .cons link' tail'⟩

theorem SessionChain.invoke_result_backward {P : Profile} {s t : Store H}
    (chain : SessionChain s t) {a : Nat} {vs : List Val} {d : Config H} {r : Result}
    (run : Steps P Simulation.noHost (invoke t a vs) d) (result : d.code = r.toAdmin) :
    ∃ c, Steps P Simulation.noHost (invoke s a vs) c ∧ c.code = r.toAdmin ∧
      SessionChain c.store d.store := by
  induction chain generalizing d with
  | refl => exact ⟨d, run, result, .refl _⟩
  | cons link _ ih =>
    obtain ⟨middle, middleRun, middleResult, tail'⟩ := ih run result
    obtain ⟨c, run', result', link'⟩ := link.invoke_result_backward middleRun middleResult
    exact ⟨c, run', result', .cons link' tail'⟩

theorem SessionLink.behaviours_profile {P : Profile} {s t : Store H}
    (link : SessionLink s t) (a : Nat) (vs : List Val) :
    behaviours P Simulation.noHost t a vs = behaviours P Simulation.noHost s a vs := by
  cases link with
  | related rel scope => exact MergeUntyped.related_behaviours_profile rel scope a vs
  | renamed rel => exact MergeUntyped.renamed_behaviours rel a vs

theorem SessionChain.behaviours_profile {P : Profile} {s t : Store H}
    (chain : SessionChain s t) (a : Nat) (vs : List Val) :
    behaviours P Simulation.noHost t a vs = behaviours P Simulation.noHost s a vs := by
  induction chain with
  | refl => rfl
  | cons link _ ih => rw [ih, link.behaviours_profile]

theorem SessionChain.session_forward {P : Profile} {source target : ModuleInst}
    {s : Store H} {script : List Call} {bs : List (Behaviour Val)}
    (session : Session P Simulation.noHost source s script bs) :
    ∀ {t : Store H}, SessionChain s t →
      (∀ call ∈ script, exportFunc? source call.1 = exportFunc? target call.1) →
      Session P Simulation.noHost target t script bs := by
  induction session with
  | nil => exact fun _ _ => .nil
  | @stop s x vs rest invalid =>
    intro t chain exports
    apply Session.stop
    intro a lookup ok
    apply invalid a
    · rw [exports (x, vs) (by simp)]
      exact lookup
    · exact (chain.invokeOk_iff a vs).mpr ok
  | @done s x vs rest a c r bs lookup ok run result _ ih =>
    intro t chain exports
    obtain ⟨d, run', result', chain'⟩ := chain.invoke_result_forward run result
    exact .done (by rw [← exports (x, vs) (by simp)]; exact lookup)
      ((chain.invokeOk_iff a vs).mp ok) run' result'
      (ih chain' (fun call mem => exports call (List.mem_cons_of_mem _ mem)))
  | @diverge s x vs rest a lookup ok diverges =>
    intro t chain exports
    have targetDiverges : Behaviour.diverges ∈ behaviours P Simulation.noHost t a vs := by
      rw [chain.behaviours_profile]
      exact .inr ⟨rfl, diverges⟩
    rcases targetDiverges with ⟨_, r, _, _, impossible⟩ | ⟨_, diverges'⟩
    · exact (Result.toBehaviour_ne_diverges r impossible.symm).elim
    · exact .diverge (by rw [← exports (x, vs) (by simp)]; exact lookup)
        ((chain.invokeOk_iff a vs).mp ok) diverges'

theorem SessionChain.session_backward {P : Profile} {source target : ModuleInst}
    {t : Store H} {script : List Call} {bs : List (Behaviour Val)}
    (session : Session P Simulation.noHost target t script bs) :
    ∀ {s : Store H}, SessionChain s t →
      (∀ call ∈ script, exportFunc? source call.1 = exportFunc? target call.1) →
      Session P Simulation.noHost source s script bs := by
  induction session with
  | nil => exact fun _ _ => .nil
  | @stop t x vs rest invalid =>
    intro s chain exports
    apply Session.stop
    intro a lookup ok
    apply invalid a
    · rw [← exports (x, vs) (by simp)]
      exact lookup
    · exact (chain.invokeOk_iff a vs).mp ok
  | @done t x vs rest a d r bs lookup ok run result _ ih =>
    intro s chain exports
    obtain ⟨c, run', result', chain'⟩ := chain.invoke_result_backward run result
    exact .done (by rw [exports (x, vs) (by simp)]; exact lookup)
      ((chain.invokeOk_iff a vs).mpr ok) run' result'
      (ih chain' (fun call mem => exports call (List.mem_cons_of_mem _ mem)))
  | @diverge t x vs rest a lookup ok diverges =>
    intro s chain exports
    have sourceDiverges : Behaviour.diverges ∈ behaviours P Simulation.noHost s a vs := by
      rw [← chain.behaviours_profile]
      exact .inr ⟨rfl, diverges⟩
    rcases sourceDiverges with ⟨_, r, _, _, impossible⟩ | ⟨_, diverges'⟩
    · exact (Result.toBehaviour_ne_diverges r impossible.symm).elim
    · exact .diverge (by rw [exports (x, vs) (by simp)]; exact lookup)
        ((chain.invokeOk_iff a vs).mpr ok) diverges'

/-- Repeated calls share their actual final stores. The only export condition
concerns names that the supplied script actually requests. Invalid argument
requests stop on both sides; returned values, traps, exceptions and divergence
remain exact at every same numerical profile. -/
theorem Chain.session_iff_profile {P : Profile} {s t : Store H}
    {source target : ModuleInst} (chain : Chain s t)
    {script : List Call} {bs : List (Behaviour Val)}
    (exports : ∀ call ∈ script, exportFunc? source call.1 = exportFunc? target call.1) :
    Session P Simulation.noHost target t script bs ↔
      Session P Simulation.noHost source s script bs :=
  ⟨fun session => chain.sessionChain.session_backward session exports,
    fun session => chain.sessionChain.session_forward session exports⟩

end Silmaril.Wasm.Binaryen.MergeChain
