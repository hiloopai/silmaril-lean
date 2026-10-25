module

public import Silmaril.Wasm.Link.OrdinaryStoreRelation
public import Silmaril.Wasm.Link.GlobalRenameSimulation
public import Silmaril.Wasm.Link.GlobalRenameTyping
public import Silmaril.Wasm.Link.PreparedObservation

/-! # Complete executions after ordinary linked preparation

Actual ordinary preparations establish a global-address renaming from the
separate store to an intermediate store and the existing linking relation from
that store to the linked store. Renaming preserves invocation typing and actual
host-free executions, so composing the two simulations constructs a complete
linked execution. Runtime values, traps and exception addresses remain exact.
Under every deterministic profile `profile o` (source and linked runs sharing
the grow oracle `o`) every terminal linked execution agrees. Under the
nondeterministic spec profile only forward inclusion is proved
(`spec_separate_linked_result`; the converse requires occurrence-sensitive growth choices).
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.OrdinarySimulation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {o : SingleThreaded.GrowOracle}

/-- Final state is related through the same global-address permutation used
at preparation. The intermediate store also supplies the renamed frame/code
for the final linking relation. -/
def FinalRelation (p : Nat ≃ Nat) (source linked : Config H) : Prop :=
  ∃ intermediate : Store H, GlobalPermutation.Renamed p source.store intermediate ∧
    Simulation.Matching .same (GlobalRenameSimulation.config p intermediate source) linked

/-- Renaming and static linking compose for a complete typed invocation.
Neither an intermediate run nor a linked run is assumed. -/
theorem invoke_steps {p : Nat ≃ Nat} {source intermediate linked : Store H}
    {address : Nat} {args : List Val} {sourceFinal : Config H}
    (renamed : GlobalPermutation.Renamed p source intermediate)
    (stores : StoreRelation.Related intermediate linked)
    (valid : StoreOk source) (typed : InvokeOk source address args)
    (run : Steps P Simulation.noHost (invoke source address args) sourceFinal) :
    ∃ linkedFinal, Steps P Simulation.noHost (invoke linked address args) linkedFinal ∧
      FinalRelation p sourceFinal linkedFinal := by
  obtain ⟨intermediateFinal, renamedRun, renamedFinal⟩ :=
    GlobalRenameSimulation.invoke_steps renamed run
  obtain ⟨linkedFinal, linkedRun, linkedFinalRelation⟩ := PreparedSimulation.invoke_steps stores
    (GlobalRenameTyping.store_ok renamed valid) (GlobalRenameTyping.invoke_ok renamed typed) renamedRun
  exact ⟨linkedFinal, linkedRun, intermediateFinal, renamedFinal, linkedFinalRelation⟩

/-- A terminal source observation constructs a complete linked observation
with the exact original result and both final store relations. -/
theorem invoke_result {p : Nat ≃ Nat} {source intermediate linked : Store H}
    {address : Nat} {args : List Val} {sourceFinal : Config H} {result : Result}
    (renamed : GlobalPermutation.Renamed p source intermediate)
    (stores : StoreRelation.Related intermediate linked)
    (valid : StoreOk source) (typed : InvokeOk source address args)
    (run : Steps P Simulation.noHost (invoke source address args) sourceFinal)
    (returned : sourceFinal.code = result.toAdmin) :
    ∃ linkedFinal, Steps P Simulation.noHost (invoke linked address args) linkedFinal ∧
      FinalRelation p sourceFinal linkedFinal ∧ linkedFinal.code = result.toAdmin := by
  obtain ⟨intermediateFinal, renamedRun, renamedFinal, renamedResult⟩ :=
    GlobalRenameSimulation.invoke_result renamed run returned
  obtain ⟨linkedFinal, linkedRun, linkedFinalRelation, linkedResult⟩ :=
    PreparedObservation.invoke_result stores (GlobalRenameTyping.store_ok renamed valid)
      (GlobalRenameTyping.invoke_ok renamed typed) renamedRun renamedResult
  exact ⟨linkedFinal, linkedRun, ⟨intermediateFinal, renamedFinal, linkedFinalRelation⟩, linkedResult⟩

/-- Every terminal deterministic linked invocation agrees with the original
source result and retains both final relations through the permutation. -/
theorem invoke_agreement {p : Nat ≃ Nat} {source intermediate linked : Store H}
    {address : Nat} {args : List Val} {sourceFinal linkedFinal : Config H}
    {result observed : Result}
    (renamed : GlobalPermutation.Renamed p source intermediate)
    (stores : StoreRelation.Related intermediate linked)
    (valid : StoreOk source) (typed : InvokeOk source address args)
    (run : Steps (SingleThreaded.profile o) Simulation.noHost
      (invoke source address args) sourceFinal)
    (returned : sourceFinal.code = result.toAdmin)
    (linkedRun : Steps (SingleThreaded.profile o) Simulation.noHost
      (invoke linked address args) linkedFinal)
    (observedResult : linkedFinal.code = observed.toAdmin) :
    observed = result ∧ FinalRelation p sourceFinal linkedFinal := by
  obtain ⟨constructed, constructedRun, finalRelation, constructedResult⟩ :=
    invoke_result renamed stores valid typed run returned
  have equal := LinkObservation.terminal_unique constructedRun linkedRun
    ⟨result, constructedResult⟩ ⟨observed, observedResult⟩
  subst linkedFinal
  exact ⟨(LinkObservation.result_code_injective
    (constructedResult.symm.trans observedResult)).symm, finalRelation⟩

/-- Actual ordinary separate and linked preparations construct a complete
linked execution for every typed source invocation, including nonempty globals. -/
theorem separate_linked_steps {namespaceName provider consumer resultModule}
    (w : Recipe.Assembly namespaceName provider consumer resultModule)
    (linked : link? namespaceName provider consumer = some resultModule)
    {s : Store H} {cp cc cl : Config H} {startP startC startL : Option FuncIdx}
    (validInitial : StoreOk s)
    (hp : prepare? evalConst? s provider (Preparation.imports []) = some (cp, startP))
    (hc : prepare? evalConst? cp.store consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length + f.toNat))) =
        some (cc, startC))
    (hm : prepare? evalConst? s resultModule (Preparation.imports []) = some (cl, startL))
    {address : Nat} {args : List Val} {sourceFinal : Config H}
    (valid : StoreOk cc.store) (typed : InvokeOk cc.store address args)
    (run : Steps P Simulation.noHost (invoke cc.store address args) sourceFinal) :
    ∃ linkedFinal, Steps P Simulation.noHost (invoke cl.store address args) linkedFinal ∧
      FinalRelation (OrdinaryStoreRelation.permutation s provider consumer) sourceFinal linkedFinal := by
  obtain ⟨renamed, stores⟩ := OrdinaryStoreRelation.separate_linked w linked validInitial hp hc hm
  exact invoke_steps renamed stores valid typed run

/-- Actual ordinary preparations preserve the original terminal result and
the final relation through the provider-copy/consumer-initializer permutation. -/
theorem separate_linked_result {namespaceName provider consumer resultModule}
    (w : Recipe.Assembly namespaceName provider consumer resultModule)
    (linked : link? namespaceName provider consumer = some resultModule)
    {s : Store H} {cp cc cl : Config H} {startP startC startL : Option FuncIdx}
    (validInitial : StoreOk s)
    (hp : prepare? evalConst? s provider (Preparation.imports []) = some (cp, startP))
    (hc : prepare? evalConst? cp.store consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length + f.toNat))) =
        some (cc, startC))
    (hm : prepare? evalConst? s resultModule (Preparation.imports []) = some (cl, startL))
    {address : Nat} {args : List Val} {sourceFinal : Config H} {result : Result}
    (valid : StoreOk cc.store) (typed : InvokeOk cc.store address args)
    (run : Steps P Simulation.noHost (invoke cc.store address args) sourceFinal)
    (returned : sourceFinal.code = result.toAdmin) :
    ∃ linkedFinal, Steps P Simulation.noHost (invoke cl.store address args) linkedFinal ∧
      FinalRelation (OrdinaryStoreRelation.permutation s provider consumer) sourceFinal linkedFinal ∧
      linkedFinal.code = result.toAdmin := by
  obtain ⟨renamed, stores⟩ := OrdinaryStoreRelation.separate_linked w linked validInitial hp hc hm
  exact invoke_result renamed stores valid typed run returned

/-- Every terminal deterministic linked invocation after actual ordinary
preparation agrees with the separately prepared source invocation. -/
theorem separate_linked_agreement {namespaceName provider consumer resultModule}
    (w : Recipe.Assembly namespaceName provider consumer resultModule)
    (linked : link? namespaceName provider consumer = some resultModule)
    {s : Store H} {cp cc cl : Config H} {startP startC startL : Option FuncIdx}
    (validInitial : StoreOk s)
    (hp : prepare? evalConst? s provider (Preparation.imports []) = some (cp, startP))
    (hc : prepare? evalConst? cp.store consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length + f.toNat))) =
        some (cc, startC))
    (hm : prepare? evalConst? s resultModule (Preparation.imports []) = some (cl, startL))
    {address : Nat} {args : List Val} {sourceFinal linkedFinal : Config H}
    {result observed : Result}
    (valid : StoreOk cc.store) (typed : InvokeOk cc.store address args)
    (run : Steps (SingleThreaded.profile o) Simulation.noHost
      (invoke cc.store address args) sourceFinal)
    (returned : sourceFinal.code = result.toAdmin)
    (linkedRun : Steps (SingleThreaded.profile o) Simulation.noHost
      (invoke cl.store address args) linkedFinal)
    (observedResult : linkedFinal.code = observed.toAdmin) :
    observed = result ∧
      FinalRelation (OrdinaryStoreRelation.permutation s provider consumer) sourceFinal linkedFinal := by
  obtain ⟨renamed, stores⟩ := OrdinaryStoreRelation.separate_linked w linked validInitial hp hc hm
  exact invoke_agreement renamed stores valid typed run returned linkedRun observedResult

/-- Spec-profile forward inclusion after actual ordinary preparation: every
terminal source outcome under `Profile.spec false {}` is achieved by some linked
run with the same result. The converse needs a backward simulation or an
occurrence-indexed grow oracle; a fixed `(kind, address, size, delta)` oracle
cannot replay a run that fails and then succeeds the same grow (occurrence-sensitive growth-choice limitation). -/
theorem spec_separate_linked_result {namespaceName provider consumer resultModule}
    (w : Recipe.Assembly namespaceName provider consumer resultModule)
    (linked : link? namespaceName provider consumer = some resultModule)
    {s : Store H} {cp cc cl : Config H} {startP startC startL : Option FuncIdx}
    (validInitial : StoreOk s)
    (hp : prepare? evalConst? s provider (Preparation.imports []) = some (cp, startP))
    (hc : prepare? evalConst? cp.store consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length + f.toNat))) =
        some (cc, startC))
    (hm : prepare? evalConst? s resultModule (Preparation.imports []) = some (cl, startL))
    {address : Nat} {args : List Val} {sourceFinal : Config H} {result : Result}
    (valid : StoreOk cc.store) (typed : InvokeOk cc.store address args)
    (run : Steps (Profile.spec false {}) Simulation.noHost (invoke cc.store address args)
      sourceFinal)
    (returned : sourceFinal.code = result.toAdmin) :
    ∃ linkedFinal, Steps (Profile.spec false {}) Simulation.noHost
        (invoke cl.store address args) linkedFinal ∧
      FinalRelation (OrdinaryStoreRelation.permutation s provider consumer) sourceFinal linkedFinal ∧
      linkedFinal.code = result.toAdmin :=
  separate_linked_result w linked validInitial hp hc hm valid typed run returned

end Silmaril.Wasm.Link.GC.OrdinarySimulation
