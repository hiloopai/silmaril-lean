module

public import Silmaril.Wasm.Link.VisibleInitializers
public import Silmaril.Wasm.Link.GlobalPermutation
public import Silmaril.Wasm.Link.StoreRelation

/-! # Actual ordinary initializer blocks across linking

Ordinary preparation evaluates globals and then copies their values during
module allocation. The extra provider copy is invisible to the consumer's
initializer frame. Relocated evaluation therefore produces the same values and
GC objects while the two final stores swap the provider-copy and consumer-init
blocks.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.OrdinaryInitializers

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Preparation

variable {H : Type}

private theorem address_bound {base count i a : Nat}
    (h : (addresses base count)[i]? = some a) : i < count := by
  simpa only [addresses_length] using (List.getElem?_eq_some_iff.mp h).1

private theorem address_value {base count i a : Nat}
    (h : (addresses base count)[i]? = some a) : a = base+i := by
  exact Option.some.inj (h.symm.trans (addresses_lookup (address_bound h)))

private theorem result_functions {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result) :
    result.funcs.length = provider.funcs.length + consumer.funcs.length := by
  rw [w.output]
  simp only [List.length_append, w.providerFuncs_length, w.funcs_length]

/-- Initializer function references use their future installed addresses.
The provider keeps these addresses in the linked function prefix. -/
theorem provider_initial_views {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (hl : link? namespaceName provider consumer = some result) (s : Store H) :
    Views.Successful Recipe.identity
      (ModuleInst.initial s provider (imports []))
      (ModuleInst.initial s result (imports [])) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y a rewrite lookup
    have hy : y = x := Option.some.inj (rewrite.symm.trans (Identity.function_identity x))
    subst y
    change (addresses s.funcs.length provider.funcs.length)[x.toNat]? = some a at lookup
    change (addresses s.funcs.length result.funcs.length)[x.toNat]? = some a
    rw [address_value lookup]
    apply addresses_lookup
    rw [result_functions w]
    have bound := address_bound lookup
    omega
  · intro x y a rewrite lookup
    simp only [ModuleInst.initial, imports_globals, List.getElem?_nil, reduceCtorEq] at lookup
  · intro x y d rewrite lookup
    have hy : y = x := Option.some.inj (rewrite.symm.trans (Identity.shift_zero x))
    subst y
    exact Allocation.link?_provider_type_lookup hl lookup

/-- Separate consumer initializers and linked initializers select the same
forward function addresses and closed GC tags before any consumer globals exist. -/
theorem consumer_initial_views {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (hl : link? namespaceName provider consumer = some result) (s sp : Store H)
    (count : sp.funcs.length = s.funcs.length + provider.funcs.length) :
    Views.Successful (Recipe.relocation provider w.imports)
      (ModuleInst.initial sp consumer (imports (w.imports.map (fun f => s.funcs.length+f.toNat))))
      (ModuleInst.initial s result (imports [])) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y a rewrite lookup
    change (if x.toNat < w.imports.length then w.imports[x.toNat]?
      else Idx.ofNat? (provider.funcs.length+(x.toNat-w.imports.length))) = some y at rewrite
    simp only [ModuleInst.initial, imports_funcs] at lookup
    change ((w.imports.map (fun f => s.funcs.length+f.toNat)) ++
      addresses sp.funcs.length consumer.funcs.length)[x.toNat]? = some a at lookup
    change (addresses s.funcs.length result.funcs.length)[y.toNat]? = some a
    by_cases imported : x.toNat < w.imports.length
    · rw [ite_eq_left imported] at rewrite
      rw [List.getElem?_append_left (by simpa only [List.length_map] using imported),
        List.getElem?_map, rewrite] at lookup
      have ha : a = s.funcs.length+y.toNat := Option.some.inj lookup.symm
      rw [ha]
      apply addresses_lookup
      rw [result_functions w]
      have bound := Resolution.assembly_imports_bounded w y (List.mem_of_getElem? rewrite)
      omega
    · rw [ite_eq_right imported] at rewrite
      have hy : y.toNat = provider.funcs.length+(x.toNat-w.imports.length) :=
        ((Idx.ofNat?_eq_some_iff _ _).mp rewrite).symm
      have after : (w.imports.map (fun f => s.funcs.length+f.toNat)).length ≤ x.toNat := by
        simpa only [List.length_map] using (Nat.le_of_not_gt imported)
      rw [List.getElem?_append_right after, List.length_map] at lookup
      rw [hy, address_value lookup, count, Nat.add_assoc]
      apply addresses_lookup
      rw [result_functions w]
      have bound := address_bound lookup
      omega
  · intro x y a rewrite lookup
    simp only [ModuleInst.initial, imports_globals, List.getElem?_nil, reduceCtorEq] at lookup
  · intro x y d rewrite lookup
    exact (Allocation.link?_consumer_type_lookup hl rewrite).trans lookup

/-- Module allocation copies globals and installs functions without changing
existing structures or arrays. -/
theorem allocation_heaps {source target : Store H} {m : Module} {as : List Nat}
    {values : List Val} {mi : ModuleInst}
    (run : allocModule? source m (imports as) values [] [] = some (target, mi)) :
    target.structs = source.structs ∧ target.arrays = source.arrays := by
  obtain ⟨_, _, _, _, _, _, _, shape⟩ := allocModule?_inv run
  rw [shape]
  exact ⟨rfl, rfl⟩

/-- Ordinary preparation in this profile changes no ambient tables, memories,
segments, exception tags or stored exceptions. -/
theorem prepare_static {source : Store H} {m : Module} {as : List Nat}
    {target : Config H} {start : Option FuncIdx} (profile : inProfile m = true)
    (run : prepare? evalConst? source m (imports as) = some (target, start)) :
    StoreRelation.Static source target.store := by
  obtain ⟨s₁, _, _, globalsRun, allocation, _, _, _⟩ := prepare_allocation profile run
  have static := StoreRelation.evalGlobals_static globalsRun
  obtain ⟨tagTypes, _, _, tagsRun, _, _, _, shape⟩ := allocModule?_inv allocation
  simp only [inProfile, Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at profile
  have memories := profile.1.1.1.1.1.1
  have tables := profile.1.1.1.1.1.2
  have tags := profile.1.1.1.1.2
  have data := profile.1.1.1.2
  have elems := profile.1.1.2
  simp only [tags, List.mapM_nil, Option.pure_def, Option.some.injEq] at tagsRun
  subst tagTypes
  simp only [memories, tables, data, elems, List.map_nil, List.zip_nil_left,
    List.append_nil] at shape
  rw [shape]
  exact ⟨static.tags, static.mems, static.tables, static.datas, static.elems, static.exns⟩

/-- Closing the linked globals and pairing the actual initializer values gives
exactly the provider and consumer blocks in source order. -/
theorem linked_global_instances {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (hl : link? namespaceName provider consumer = some result)
    {providerValues consumerValues : List Val}
    (providerLength : providerValues.length = provider.globals.length) :
    globalInstances result (providerValues ++ consumerValues) =
      globalInstances provider providerValues ++ globalInstances consumer consumerValues := by
  unfold globalInstances
  rw [Initializers.link_closed_global_types w hl,
    List.zipWith_append (by simpa only [Module.closedGlobalTypes, List.length_map] using
      providerLength.symm)]

/-- Actual separate and linked ordinary preparations produce equal global
values and GC heaps. The two global lists differ by exactly one block swap. -/
theorem separate_linked_blocks {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (hl : link? namespaceName provider consumer = some result)
    {s : Store H} {cp cc cl : Config H} {startP startC startL : Option FuncIdx}
    (hp : prepare? evalConst? s provider (imports []) = some (cp, startP))
    (hc : prepare? evalConst? cp.store consumer
      (imports (w.imports.map (fun f => s.funcs.length+f.toNat))) = some (cc, startC))
    (hm : prepare? evalConst? s result (imports []) = some (cl, startL)) :
    ∃ providerValues consumerValues : List Val,
      providerValues.length = provider.globals.length ∧
      consumerValues.length = consumer.globals.length ∧
      cc.store.globals = s.globals ++ globalInstances provider providerValues ++
        globalInstances provider providerValues ++ globalInstances consumer consumerValues ++
        globalInstances consumer consumerValues ∧
      cl.store.globals = s.globals ++ globalInstances provider providerValues ++
        globalInstances consumer consumerValues ++ globalInstances provider providerValues ++
        globalInstances consumer consumerValues ∧
      cc.store.structs = cl.store.structs ∧ cc.store.arrays = cl.store.arrays := by
  have resultProfile : inProfile result = true := by rw [w.output]; rfl
  obtain ⟨sP, fP, valuesP, _, globalsP, allocationP, bindingsP⟩ :=
    prepare?_gc_bindings w.providerProfile hp
  obtain ⟨sC, fC, valuesC, _, globalsC, allocationC, bindingsC⟩ :=
    prepare?_gc_bindings w.consumerProfile hc
  obtain ⟨sL, fL, valuesL, _, globalsL, allocationL, bindingsL⟩ :=
    prepare?_gc_bindings resultProfile hm
  have viewsP := provider_initial_views w hl s
  have relatedP : VisibleInitializers.Related Recipe.identity s s
      ⟨[], ModuleInst.initial s provider (imports [])⟩
      ⟨[], ModuleInst.initial s result (imports [])⟩ :=
    VisibleInitializers.Related.of_empty_globals viewsP rfl rfl rfl
  have rewriteP := Initializers.initializer_rewrite w.providerGlobalsRewrite
  rw [Identity.provider_globals w] at rewriteP
  obtain ⟨targetP, frameP, runP, dataP, _, _⟩ :=
    VisibleInitializers.globals_transport relatedP (VisibleInitializers.Bounded.empty rfl)
      (by simp only [ModuleInst.initial, imports_globals, Recipe.identity,
        List.length_nil, Nat.zero_add]) rewriteP globalsP
  have shapeP := (evalGlobals?_shape runP).2.2
  have viewsC := consumer_initial_views w hl s cp.store bindingsP.function_count
  have viewsC' : Views.Successful (Recipe.relocation provider w.imports)
      (ModuleInst.initial cp.store consumer
        (imports (w.imports.map (fun f => s.funcs.length+f.toNat)))) frameP.module := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y a rewrite lookup
      rw [shapeP]
      exact viewsC.functions rewrite lookup
    · intro x y a rewrite lookup
      simp only [ModuleInst.initial, imports_globals, List.getElem?_nil, reduceCtorEq] at lookup
    · intro x y d rewrite lookup
      rw [shapeP]
      exact viewsC.types rewrite lookup
  have heapsP := allocation_heaps allocationP
  have relatedC : VisibleInitializers.Related (Recipe.relocation provider w.imports)
      cp.store targetP
      ⟨[], ModuleInst.initial cp.store consumer
        (imports (w.imports.map (fun f => s.funcs.length+f.toNat)))⟩ frameP :=
    VisibleInitializers.Related.of_empty_globals viewsC' (imports_globals _)
      (heapsP.1.trans dataP.structs) (heapsP.2.trans dataP.arrays)
  have lengthC : frameP.module.globals.length =
      (Recipe.relocation provider w.imports).globals +
        (ModuleInst.initial cp.store consumer
          (imports (w.imports.map (fun f => s.funcs.length+f.toNat)))).globals.length := by
    rw [shapeP]
    simp only [ModuleInst.initial, imports_globals, Recipe.relocation, List.nil_append,
      List.length_map, List.length_range, Module.closedGlobalTypes, List.length_nil,
      Nat.add_zero]
  obtain ⟨targetC, frameC, runC, dataC, _, _⟩ :=
    VisibleInitializers.globals_transport relatedC
      (VisibleInitializers.Bounded.empty (imports_globals _)) lengthC
      (Initializers.initializer_rewrite w.globalsRewrite) globalsC
  have initializers : result.globals.map Global.init =
      provider.globals.map Global.init ++ w.globals.map Global.init := by
    have globals : result.globals = w.providerGlobals ++ w.globals :=
      congrArg Module.globals w.output
    rw [globals, Identity.provider_globals w, List.map_append]
  have mergedRun : evalGlobals? evalConst? s
      ⟨[], ModuleInst.initial s result (imports [])⟩
      (Module.closedGlobalTypes result) (result.globals.map Global.init) =
        some (targetC, frameC, valuesP ++ valuesC) := by
    rw [Initializers.link_closed_global_types w hl, initializers]
    exact Initializers.globals_append runP runC
  have resultEquality := Option.some.inj (mergedRun.symm.trans globalsL)
  have storeEquality : targetC = sL := congrArg Prod.fst resultEquality
  have valuesEquality : valuesP ++ valuesC = valuesL :=
    congrArg (fun p => p.2.2) resultEquality
  have heapsC := allocation_heaps allocationC
  have heapsL := allocation_heaps allocationL
  refine ⟨valuesP, valuesC, bindingsP.values_length, bindingsC.values_length, ?_, ?_, ?_, ?_⟩
  · rw [bindingsC.store_globals, bindingsP.store_globals]
  · rw [bindingsL.store_globals, ← valuesEquality,
      linked_global_instances w hl bindingsP.values_length]
    simp only [List.append_assoc]
  · rw [heapsC.1, heapsL.1, ← storeEquality]
    exact dataC.structs
  · rw [heapsC.2, heapsL.2, ← storeEquality]
    exact dataC.arrays

/-- Ambient state agrees, and global lookups agree under the actual ordinary
preparation's provider-copy/consumer-init block permutation. -/
structure Data (p : Nat ≃ Nat) (source target : Store H) : Prop
    extends StoreRelation.Static source target where
  globals : GlobalPermutation.Lookup p source.globals target.globals
  structs : source.structs = target.structs
  arrays : source.arrays = target.arrays

/-- The global permutation and equal GC heaps come from actual initializer and
allocator executions; no runtime correspondence is assumed. -/
theorem separate_linked_data {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (hl : link? namespaceName provider consumer = some result)
    {s : Store H} {cp cc cl : Config H} {startP startC startL : Option FuncIdx}
    (hp : prepare? evalConst? s provider (imports []) = some (cp, startP))
    (hc : prepare? evalConst? cp.store consumer
      (imports (w.imports.map (fun f => s.funcs.length+f.toNat))) = some (cc, startC))
    (hm : prepare? evalConst? s result (imports []) = some (cl, startL)) :
    Data (GlobalPermutation.blocks (s.globals.length + provider.globals.length)
      provider.globals.length consumer.globals.length) cc.store cl.store := by
  obtain ⟨valuesP, valuesC, lengthP, lengthC, sourceGlobals, targetGlobals, structs, arrays⟩ :=
    separate_linked_blocks w hl hp hc hm
  have resultProfile : inProfile result = true := by rw [w.output]; rfl
  have static := ((prepare_static w.providerProfile hp).trans
    (prepare_static w.consumerProfile hc)).symm.trans (prepare_static resultProfile hm)
  refine ⟨static, ?_, structs, arrays⟩
  rw [sourceGlobals, targetGlobals]
  have blockLengthP : (globalInstances provider valuesP).length = provider.globals.length := by
    simp only [globalInstances, List.length_zipWith, Module.closedGlobalTypes,
      List.length_map, lengthP, Nat.min_self]
  have blockLengthC : (globalInstances consumer valuesC).length = consumer.globals.length := by
    simp only [globalInstances, List.length_zipWith, Module.closedGlobalTypes,
      List.length_map, lengthC, Nat.min_self]
  simpa only [blockLengthP, blockLengthC] using
    GlobalPermutation.ordinary_blocks s.globals (globalInstances provider valuesP)
      (globalInstances consumer valuesC)

end Silmaril.Wasm.Link.GC.OrdinaryInitializers
