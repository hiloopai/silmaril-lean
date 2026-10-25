module

public import Silmaril.Wasm.Link.PreparedSimulation

/-! # Ordinary preparation of global-free linked modules

Ordinary Core preparation and single-allocation instantiation produce the same
store and frame when a module has no globals or segments. Consequently actual
ordinary preparations of a global-free provider, consumer and linker output
establish the checked store relation and complete invocation correspondence.
Modules with globals still need the ordinary allocator's address permutation.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.OrdinaryPreparation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile}

/-- With no globals or segments, actual ordinary preparation is exactly the
single-allocation initializer, including its returned store, frame and start. -/
theorem once_of_prepare {s : Store H} {m : Module} {xas : List ExternAddr}
    {c : Config H} {start : Option FuncIdx}
    (globals : m.globals = []) (elems : m.elems = []) (data : m.data = [])
    (run : prepare? evalConst? s m xas = some (c, start)) :
    instantiateOnce? s m xas = some (c.store, c.frame, start) := by
  rw [instantiateOnce?_of_nil globals]
  simp [instantiateDirect?, prepareDirect?, run, initSegments?, initElem?, initData?,
    elems, data, initElemList?, initDataList?]

/-- The linker's profile has no segment initialization. Its global-free
ordinary preparation therefore supplies the exact single-allocation run. -/
theorem once_of_profile_prepare {s : Store H} {m : Module} {xas : List ExternAddr}
    {c : Config H} {start : Option FuncIdx}
    (profile : inProfile m = true) (globals : m.globals = [])
    (run : prepare? evalConst? s m xas = some (c, start)) :
    instantiateOnce? s m xas = some (c.store, c.frame, start) := by
  simp only [inProfile, Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at profile
  exact once_of_prepare globals profile.1.1.2 profile.1.1.1.2 run

/-- Rewriting preserves empty global sections on both sides of a link. -/
theorem result_globals {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (providerGlobals : provider.globals = []) (consumerGlobals : consumer.globals = []) :
    result.globals = [] := by
  apply List.length_eq_zero_iff.mp
  rw [w.output]
  simp [w.providerGlobals_length, w.globals_length, providerGlobals, consumerGlobals]

/-- Three actual ordinary preparations establish the same store relation as
the single-allocation preparation theorem, without an assumed correspondence. -/
theorem separate_linked {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (linked : link? namespaceName provider consumer = some result)
    (providerGlobals : provider.globals = []) (consumerGlobals : consumer.globals = [])
    {s : Store H} {cp cc cl : Config H} {startP startC startL : Option FuncIdx}
    (hp : prepare? evalConst? s provider (Preparation.imports []) = some (cp, startP))
    (hc : prepare? evalConst? cp.store consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length + f.toNat))) =
        some (cc, startC))
    (hm : prepare? evalConst? s result (Preparation.imports []) = some (cl, startL)) :
    StoreRelation.Related cc.store cl.store := by
  have resultProfile : inProfile result = true := by rw [w.output]; rfl
  exact StoreRelation.separate_linked w linked
    (once_of_profile_prepare w.providerProfile providerGlobals hp)
    (once_of_profile_prepare w.consumerProfile consumerGlobals hc)
    (once_of_profile_prepare resultProfile (result_globals w providerGlobals consumerGlobals) hm)

/-- A typed invocation after ordinary separate preparation has a complete
matching execution after ordinary preparation of the actual linked output. -/
theorem separate_linked_steps {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (linked : link? namespaceName provider consumer = some result)
    (providerGlobals : provider.globals = []) (consumerGlobals : consumer.globals = [])
    {s : Store H} {cp cc cl : Config H} {startP startC startL : Option FuncIdx}
    (hp : prepare? evalConst? s provider (Preparation.imports []) = some (cp, startP))
    (hc : prepare? evalConst? cp.store consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length + f.toNat))) =
        some (cc, startC))
    (hm : prepare? evalConst? s result (Preparation.imports []) = some (cl, startL))
    {address : Nat} {args : List Val} {sourceFinal : Config H}
    (valid : StoreOk cc.store) (typed : InvokeOk cc.store address args)
    (run : Steps P Simulation.noHost (invoke cc.store address args) sourceFinal) :
    ∃ targetFinal, Steps P Simulation.noHost (invoke cl.store address args) targetFinal ∧
      Simulation.Matching .same sourceFinal targetFinal :=
  PreparedSimulation.invoke_steps
    (separate_linked w linked providerGlobals consumerGlobals hp hc hm) valid typed run

/-- Ordinary linked preparation preserves exact returned runtime values and
the relation between the actual final stores and configurations. -/
theorem separate_linked_values {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (linked : link? namespaceName provider consumer = some result)
    (providerGlobals : provider.globals = []) (consumerGlobals : consumer.globals = [])
    {s : Store H} {cp cc cl : Config H} {startP startC startL : Option FuncIdx}
    (hp : prepare? evalConst? s provider (Preparation.imports []) = some (cp, startP))
    (hc : prepare? evalConst? cp.store consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length + f.toNat))) =
        some (cc, startC))
    (hm : prepare? evalConst? s result (Preparation.imports []) = some (cl, startL))
    {address : Nat} {args values : List Val} {sourceFinal : Config H}
    (valid : StoreOk cc.store) (typed : InvokeOk cc.store address args)
    (run : Steps P Simulation.noHost (invoke cc.store address args) sourceFinal)
    (returned : sourceFinal.code = vals values) :
    ∃ targetFinal, Steps P Simulation.noHost (invoke cl.store address args) targetFinal ∧
      Simulation.Matching .same sourceFinal targetFinal ∧ targetFinal.code = vals values :=
  PreparedSimulation.invoke_values
    (separate_linked w linked providerGlobals consumerGlobals hp hc hm) valid typed run returned

/-- Ordinary linked preparation propagates a terminal source trap through a
complete target execution. -/
theorem separate_linked_trap {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (linked : link? namespaceName provider consumer = some result)
    (providerGlobals : provider.globals = []) (consumerGlobals : consumer.globals = [])
    {s : Store H} {cp cc cl : Config H} {startP startC startL : Option FuncIdx}
    (hp : prepare? evalConst? s provider (Preparation.imports []) = some (cp, startP))
    (hc : prepare? evalConst? cp.store consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length + f.toNat))) =
        some (cc, startC))
    (hm : prepare? evalConst? s result (Preparation.imports []) = some (cl, startL))
    {address : Nat} {args : List Val} {sourceFinal : Config H}
    (valid : StoreOk cc.store) (typed : InvokeOk cc.store address args)
    (run : Steps P Simulation.noHost (invoke cc.store address args) sourceFinal)
    (trapped : sourceFinal.code = [.trap]) :
    ∃ targetFinal, Steps P Simulation.noHost (invoke cl.store address args) targetFinal ∧
      Simulation.Matching .same sourceFinal targetFinal ∧ targetFinal.code = [.trap] :=
  PreparedSimulation.invoke_trap
    (separate_linked w linked providerGlobals consumerGlobals hp hc hm) valid typed run trapped

end Silmaril.Wasm.Link.GC.OrdinaryPreparation
