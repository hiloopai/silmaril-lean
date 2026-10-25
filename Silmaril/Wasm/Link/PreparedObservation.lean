module

public import Silmaril.Wasm.Link.OrdinaryPreparation
public import Silmaril.Wasm.Link.LinkObservation

/-! # Terminal observations after actual linked preparation

A typed terminating source invocation supplies a linked invocation with the
same result. Under every deterministic profile `profile o` (source and linked
runs sharing the grow oracle `o`; see `LinkObservation`), every terminal linked
invocation has that result and retains the final linking relation. Under the
nondeterministic spec profile only the forward inclusion (`spec_*`) is proved.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.PreparedObservation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded AdminRelation Simulation

variable {H : Type} {P : Profile} {o : GrowOracle}

/-- A complete source observation constructs a complete target observation;
the result may contain values, a trap or an exception address. -/
theorem invoke_result {source target : Store H} {address : Nat} {args : List Val}
    {sourceFinal : Config H} {result : Result}
    (stores : StoreRelation.Related source target)
    (valid : StoreOk source) (typed : InvokeOk source address args)
    (run : Steps P noHost (invoke source address args) sourceFinal)
    (returned : sourceFinal.code = result.toAdmin) :
    ∃ targetFinal, Steps P noHost (invoke target address args) targetFinal ∧
      Matching .same sourceFinal targetFinal ∧ targetFinal.code = result.toAdmin := by
  obtain ⟨targetFinal, targetRun, matching⟩ :=
    PreparedSimulation.invoke_steps stores valid typed run
  exact ⟨targetFinal, targetRun, matching, LinkObservation.paired_result matching returned⟩

/-- Any terminal deterministic linked invocation agrees with the source
observation, including its related final store and frame. -/
theorem invoke_agreement {source target : Store H} {address : Nat} {args : List Val}
    {sourceFinal targetFinal : Config H} {result observed : Result}
    (stores : StoreRelation.Related source target)
    (valid : StoreOk source) (typed : InvokeOk source address args)
    (run : Steps (profile o) noHost (invoke source address args) sourceFinal)
    (returned : sourceFinal.code = result.toAdmin)
    (targetRun : Steps (profile o) noHost (invoke target address args) targetFinal)
    (observedResult : targetFinal.code = observed.toAdmin) :
    observed = result ∧ Matching .same sourceFinal targetFinal := by
  obtain ⟨fi, params, results, lookup, signature, configTyped⟩ := invoke_ok valid typed
  exact LinkObservation.result_agreement run configTyped
    (Matching.invoke stores lookup args) returned targetRun observedResult

/-- Actual successful single-allocation preparations suffice for constructing
the linked terminal observation; no target execution is a premise. -/
theorem separate_linked_result {namespaceName provider consumer resultModule}
    (w : Recipe.Assembly namespaceName provider consumer resultModule)
    (linked : link? namespaceName provider consumer = some resultModule)
    {s sp sc sl : Store H} {fp fc fl : Frame} {startP startC startL : Option FuncIdx}
    (hp : instantiateOnce? s provider (Preparation.imports []) = some (sp, fp, startP))
    (hc : instantiateOnce? sp consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length + f.toNat))) =
        some (sc, fc, startC))
    (hm : instantiateOnce? s resultModule (Preparation.imports []) = some (sl, fl, startL))
    {address : Nat} {args : List Val} {sourceFinal : Config H} {result : Result}
    (valid : StoreOk sc) (typed : InvokeOk sc address args)
    (run : Steps P noHost (invoke sc address args) sourceFinal)
    (returned : sourceFinal.code = result.toAdmin) :
    ∃ targetFinal, Steps P noHost (invoke sl address args) targetFinal ∧
      Matching .same sourceFinal targetFinal ∧ targetFinal.code = result.toAdmin :=
  invoke_result (StoreRelation.separate_linked w linked hp hc hm) valid typed run returned

/-- Every terminal run after actual linked single-allocation preparation has
the same observation as the complete typed source invocation. -/
theorem separate_linked_agreement {namespaceName provider consumer resultModule}
    (w : Recipe.Assembly namespaceName provider consumer resultModule)
    (linked : link? namespaceName provider consumer = some resultModule)
    {s sp sc sl : Store H} {fp fc fl : Frame} {startP startC startL : Option FuncIdx}
    (hp : instantiateOnce? s provider (Preparation.imports []) = some (sp, fp, startP))
    (hc : instantiateOnce? sp consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length + f.toNat))) =
        some (sc, fc, startC))
    (hm : instantiateOnce? s resultModule (Preparation.imports []) = some (sl, fl, startL))
    {address : Nat} {args : List Val} {sourceFinal targetFinal : Config H}
    {result observed : Result}
    (valid : StoreOk sc) (typed : InvokeOk sc address args)
    (run : Steps (profile o) noHost (invoke sc address args) sourceFinal)
    (returned : sourceFinal.code = result.toAdmin)
    (targetRun : Steps (profile o) noHost (invoke sl address args) targetFinal)
    (observedResult : targetFinal.code = observed.toAdmin) :
    observed = result ∧ Matching .same sourceFinal targetFinal :=
  invoke_agreement (StoreRelation.separate_linked w linked hp hc hm) valid typed
    run returned targetRun observedResult

/-- Global-free ordinary preparations construct the same complete terminal
observation as separate ordinary preparation. -/
theorem ordinary_result {namespaceName provider consumer resultModule}
    (w : Recipe.Assembly namespaceName provider consumer resultModule)
    (linked : link? namespaceName provider consumer = some resultModule)
    (providerGlobals : provider.globals = []) (consumerGlobals : consumer.globals = [])
    {s : Store H} {cp cc cl : Config H} {startP startC startL : Option FuncIdx}
    (hp : prepare? evalConst? s provider (Preparation.imports []) = some (cp, startP))
    (hc : prepare? evalConst? cp.store consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length + f.toNat))) =
        some (cc, startC))
    (hm : prepare? evalConst? s resultModule (Preparation.imports []) = some (cl, startL))
    {address : Nat} {args : List Val} {sourceFinal : Config H} {result : Result}
    (valid : StoreOk cc.store) (typed : InvokeOk cc.store address args)
    (run : Steps P noHost (invoke cc.store address args) sourceFinal)
    (returned : sourceFinal.code = result.toAdmin) :
    ∃ targetFinal, Steps P noHost (invoke cl.store address args) targetFinal ∧
      Matching .same sourceFinal targetFinal ∧ targetFinal.code = result.toAdmin :=
  invoke_result (OrdinaryPreparation.separate_linked w linked providerGlobals consumerGlobals
    hp hc hm) valid typed run returned

/-- Every terminal deterministic run after global-free ordinary linked
preparation agrees with the source observation and its final linking relation. -/
theorem ordinary_agreement {namespaceName provider consumer resultModule}
    (w : Recipe.Assembly namespaceName provider consumer resultModule)
    (linked : link? namespaceName provider consumer = some resultModule)
    (providerGlobals : provider.globals = []) (consumerGlobals : consumer.globals = [])
    {s : Store H} {cp cc cl : Config H} {startP startC startL : Option FuncIdx}
    (hp : prepare? evalConst? s provider (Preparation.imports []) = some (cp, startP))
    (hc : prepare? evalConst? cp.store consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length + f.toNat))) =
        some (cc, startC))
    (hm : prepare? evalConst? s resultModule (Preparation.imports []) = some (cl, startL))
    {address : Nat} {args : List Val} {sourceFinal targetFinal : Config H}
    {result observed : Result}
    (valid : StoreOk cc.store) (typed : InvokeOk cc.store address args)
    (run : Steps (profile o) noHost (invoke cc.store address args) sourceFinal)
    (returned : sourceFinal.code = result.toAdmin)
    (targetRun : Steps (profile o) noHost (invoke cl.store address args) targetFinal)
    (observedResult : targetFinal.code = observed.toAdmin) :
    observed = result ∧ Matching .same sourceFinal targetFinal :=
  invoke_agreement (OrdinaryPreparation.separate_linked w linked providerGlobals consumerGlobals
    hp hc hm) valid typed run returned targetRun observedResult

/-- Spec-profile forward inclusion after a related store: every terminal
source outcome under `Profile.spec false {}` is achieved by some linked run with
the same result. The converse needs a backward simulation or an
occurrence-indexed grow oracle (occurrence-sensitive growth-choice limitation). -/
theorem spec_invoke_result {source target : Store H} {address : Nat} {args : List Val}
    {sourceFinal : Config H} {result : Result}
    (stores : StoreRelation.Related source target)
    (valid : StoreOk source) (typed : InvokeOk source address args)
    (run : Steps (Profile.spec false {}) noHost (invoke source address args) sourceFinal)
    (returned : sourceFinal.code = result.toAdmin) :
    ∃ targetFinal, Steps (Profile.spec false {}) noHost (invoke target address args) targetFinal ∧
      Matching .same sourceFinal targetFinal ∧ targetFinal.code = result.toAdmin :=
  invoke_result stores valid typed run returned

/-- Spec-profile forward inclusion after actual single-allocation preparation
(the converse requires occurrence-sensitive growth choices). -/
theorem spec_separate_linked_result {namespaceName provider consumer resultModule}
    (w : Recipe.Assembly namespaceName provider consumer resultModule)
    (linked : link? namespaceName provider consumer = some resultModule)
    {s sp sc sl : Store H} {fp fc fl : Frame} {startP startC startL : Option FuncIdx}
    (hp : instantiateOnce? s provider (Preparation.imports []) = some (sp, fp, startP))
    (hc : instantiateOnce? sp consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length + f.toNat))) =
        some (sc, fc, startC))
    (hm : instantiateOnce? s resultModule (Preparation.imports []) = some (sl, fl, startL))
    {address : Nat} {args : List Val} {sourceFinal : Config H} {result : Result}
    (valid : StoreOk sc) (typed : InvokeOk sc address args)
    (run : Steps (Profile.spec false {}) noHost (invoke sc address args) sourceFinal)
    (returned : sourceFinal.code = result.toAdmin) :
    ∃ targetFinal, Steps (Profile.spec false {}) noHost (invoke sl address args) targetFinal ∧
      Matching .same sourceFinal targetFinal ∧ targetFinal.code = result.toAdmin :=
  separate_linked_result w linked hp hc hm valid typed run returned

/-- Spec-profile forward inclusion after global-free ordinary preparation
(the converse requires occurrence-sensitive growth choices). -/
theorem spec_ordinary_result {namespaceName provider consumer resultModule}
    (w : Recipe.Assembly namespaceName provider consumer resultModule)
    (linked : link? namespaceName provider consumer = some resultModule)
    (providerGlobals : provider.globals = []) (consumerGlobals : consumer.globals = [])
    {s : Store H} {cp cc cl : Config H} {startP startC startL : Option FuncIdx}
    (hp : prepare? evalConst? s provider (Preparation.imports []) = some (cp, startP))
    (hc : prepare? evalConst? cp.store consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length + f.toNat))) =
        some (cc, startC))
    (hm : prepare? evalConst? s resultModule (Preparation.imports []) = some (cl, startL))
    {address : Nat} {args : List Val} {sourceFinal : Config H} {result : Result}
    (valid : StoreOk cc.store) (typed : InvokeOk cc.store address args)
    (run : Steps (Profile.spec false {}) noHost (invoke cc.store address args) sourceFinal)
    (returned : sourceFinal.code = result.toAdmin) :
    ∃ targetFinal, Steps (Profile.spec false {}) noHost (invoke cl.store address args) targetFinal ∧
      Matching .same sourceFinal targetFinal ∧ targetFinal.code = result.toAdmin :=
  ordinary_result w linked providerGlobals consumerGlobals hp hc hm valid typed run returned

end Silmaril.Wasm.Link.GC.PreparedObservation
