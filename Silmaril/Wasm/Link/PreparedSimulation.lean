module

public import Silmaril.Wasm.Link.WholeSimulation
public import Silmaril.Wasm.Execution.Core.Soundness

/-! # Invocation after actual separate and linked preparation

The partial linker's actual output and the actual single-allocation initializer
runs establish the initial store relation. A typed source invocation then
supplies a complete target execution with the same returned values, trap or
uncaught exception.
The premises contain no target execution or assumed execution correspondence.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open AdminRelation

namespace Simulation

/-- Actual function lookup fixes the closed invocation annotation. Related
function definitions have the same closed type even when their bodies and
module views differ, so invocation begins in the unchanged empty caller. -/
theorem Matching.invoke {H : Type} {source target : Store H} {address : Nat} {fi : FuncInst H}
    (stores : StoreRelation.Related source target) (lookup : source.funcs[address]? = some fi)
    (args : List Val) : Matching .same (invoke source address args) (invoke target address args) := by
  obtain ⟨fi',targetLookup,paired⟩ := stores.function_lookup lookup
  refine ⟨stores,Frames.same {},?_⟩
  simp only [Silmaril.Wasm.Execution.Core.invoke,lookup,targetLookup,Option.map_some,Option.getD_some,← paired.type_eq]
  exact Control.same _ _

end Simulation

namespace PreparedSimulation

open Simulation

variable {H : Type} {P : Profile}

/-- A valid source invocation and its actual run suffice to derive a complete
target run. Source soundness supplies the scopes required by whole simulation. -/
theorem invoke_steps {source target : Store H} {address : Nat} {args : List Val}
    {sourceFinal : Config H} (stores : StoreRelation.Related source target)
    (valid : StoreOk source) (typed : InvokeOk source address args)
    (run : Steps P noHost (invoke source address args) sourceFinal) :
    ∃ targetFinal, Steps P noHost (invoke target address args) targetFinal ∧
      Matching .same sourceFinal targetFinal := by
  obtain ⟨fi,params,results,lookup,signature,configTyped⟩ := invoke_ok valid typed
  exact WholeSimulation.steps run configTyped (Matching.invoke stores lookup args)

/-- The actual target invocation returns the exact source runtime values. -/
theorem invoke_values {source target : Store H} {address : Nat} {args values : List Val}
    {sourceFinal : Config H} (stores : StoreRelation.Related source target)
    (valid : StoreOk source) (typed : InvokeOk source address args)
    (run : Steps P noHost (invoke source address args) sourceFinal)
    (returned : sourceFinal.code = vals values) :
    ∃ targetFinal, Steps P noHost (invoke target address args) targetFinal ∧
      Matching .same sourceFinal targetFinal ∧ targetFinal.code = vals values := by
  obtain ⟨fi,params,results,lookup,signature,configTyped⟩ := invoke_ok valid typed
  exact WholeSimulation.values run configTyped (Matching.invoke stores lookup args) returned

/-- The actual target invocation propagates the source terminal trap. -/
theorem invoke_trap {source target : Store H} {address : Nat} {args : List Val}
    {sourceFinal : Config H} (stores : StoreRelation.Related source target)
    (valid : StoreOk source) (typed : InvokeOk source address args)
    (run : Steps P noHost (invoke source address args) sourceFinal)
    (trapped : sourceFinal.code = [.trap]) :
    ∃ targetFinal, Steps P noHost (invoke target address args) targetFinal ∧
      Matching .same sourceFinal targetFinal ∧ targetFinal.code = [.trap] := by
  obtain ⟨fi,params,results,lookup,signature,configTyped⟩ := invoke_ok valid typed
  exact WholeSimulation.trap run configTyped (Matching.invoke stores lookup args) trapped

/-- An uncaught source exception reaches the same address in the actual target
invocation, with related final stores and frames. -/
theorem invoke_throw {source target : Store H} {address exception : Nat} {args : List Val}
    {sourceFinal : Config H} (stores : StoreRelation.Related source target)
    (valid : StoreOk source) (typed : InvokeOk source address args)
    (run : Steps P noHost (invoke source address args) sourceFinal)
    (thrown : sourceFinal.code = throwing exception) :
    ∃ targetFinal, Steps P noHost (invoke target address args) targetFinal ∧
      Matching .same sourceFinal targetFinal ∧ targetFinal.code = throwing exception := by
  obtain ⟨fi,params,results,lookup,signature,configTyped⟩ := invoke_ok valid typed
  exact WholeSimulation.throw run configTyped (Matching.invoke stores lookup args) thrown

/-- Actual separate initialization and initialization of the partial linker's
output establish invocation correspondence without an assumed simulation. -/
theorem separate_linked_steps {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (hl : link? namespaceName provider consumer = some result)
    {s sp sc sl : Store H} {fp fc fl : Frame} {startP startC startL : Option FuncIdx}
    (hp : instantiateOnce? s provider (Preparation.imports []) = some (sp,fp,startP))
    (hc : instantiateOnce? sp consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length+f.toNat))) = some (sc,fc,startC))
    (hm : instantiateOnce? s result (Preparation.imports []) = some (sl,fl,startL))
    {address : Nat} {args : List Val} {sourceFinal : Config H}
    (valid : StoreOk sc) (typed : InvokeOk sc address args)
    (run : Steps P noHost (invoke sc address args) sourceFinal) :
    ∃ targetFinal, Steps P noHost (invoke sl address args) targetFinal ∧
      Matching .same sourceFinal targetFinal :=
  invoke_steps (StoreRelation.separate_linked w hl hp hc hm) valid typed run

/-- Values returned after actual separate preparation are returned unchanged
by the invocation in the actual linked store, with all final state related. -/
theorem separate_linked_values {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (hl : link? namespaceName provider consumer = some result)
    {s sp sc sl : Store H} {fp fc fl : Frame} {startP startC startL : Option FuncIdx}
    (hp : instantiateOnce? s provider (Preparation.imports []) = some (sp,fp,startP))
    (hc : instantiateOnce? sp consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length+f.toNat))) = some (sc,fc,startC))
    (hm : instantiateOnce? s result (Preparation.imports []) = some (sl,fl,startL))
    {address : Nat} {args values : List Val} {sourceFinal : Config H}
    (valid : StoreOk sc) (typed : InvokeOk sc address args)
    (run : Steps P noHost (invoke sc address args) sourceFinal)
    (returned : sourceFinal.code = vals values) :
    ∃ targetFinal, Steps P noHost (invoke sl address args) targetFinal ∧
      Matching .same sourceFinal targetFinal ∧ targetFinal.code = vals values :=
  invoke_values (StoreRelation.separate_linked w hl hp hc hm) valid typed run returned

/-- A source trap after actual separate preparation has a complete matching
trap execution after preparation of the actual partial-linker output. -/
theorem separate_linked_trap {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (hl : link? namespaceName provider consumer = some result)
    {s sp sc sl : Store H} {fp fc fl : Frame} {startP startC startL : Option FuncIdx}
    (hp : instantiateOnce? s provider (Preparation.imports []) = some (sp,fp,startP))
    (hc : instantiateOnce? sp consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length+f.toNat))) = some (sc,fc,startC))
    (hm : instantiateOnce? s result (Preparation.imports []) = some (sl,fl,startL))
    {address : Nat} {args : List Val} {sourceFinal : Config H}
    (valid : StoreOk sc) (typed : InvokeOk sc address args)
    (run : Steps P noHost (invoke sc address args) sourceFinal)
    (trapped : sourceFinal.code = [.trap]) :
    ∃ targetFinal, Steps P noHost (invoke sl address args) targetFinal ∧
      Matching .same sourceFinal targetFinal ∧ targetFinal.code = [.trap] :=
  invoke_trap (StoreRelation.separate_linked w hl hp hc hm) valid typed run trapped

/-- An uncaught exception after actual separate preparation has a complete
matching execution after preparation of the partial-linker output. -/
theorem separate_linked_throw {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (hl : link? namespaceName provider consumer = some result)
    {s sp sc sl : Store H} {fp fc fl : Frame} {startP startC startL : Option FuncIdx}
    (hp : instantiateOnce? s provider (Preparation.imports []) = some (sp,fp,startP))
    (hc : instantiateOnce? sp consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length+f.toNat))) = some (sc,fc,startC))
    (hm : instantiateOnce? s result (Preparation.imports []) = some (sl,fl,startL))
    {address exception : Nat} {args : List Val} {sourceFinal : Config H}
    (valid : StoreOk sc) (typed : InvokeOk sc address args)
    (run : Steps P noHost (invoke sc address args) sourceFinal)
    (thrown : sourceFinal.code = throwing exception) :
    ∃ targetFinal, Steps P noHost (invoke sl address args) targetFinal ∧
      Matching .same sourceFinal targetFinal ∧ targetFinal.code = throwing exception :=
  invoke_throw (StoreRelation.separate_linked w hl hp hc hm) valid typed run thrown

end PreparedSimulation

end Silmaril.Wasm.Link.GC
