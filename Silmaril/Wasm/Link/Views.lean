module

public import Silmaril.Wasm.Link.PreparationOnce
public import Silmaril.Wasm.Link.Resolution
public import Silmaril.Wasm.Link.LinkExecution

/-! # Module views from actual single-allocation preparation

Separate provider/consumer instances and the linker's output name the same
function and global addresses. Successful source lookups embed in the linked
instance, including imports resolved to real provider definitions. This relates
the module views; initializer values and stored rewritten bodies remain a
separate part of execution preservation.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.Views

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Preparation

variable {H : Type}

theorem once_functions {s s' : Store H} {m : Module} {as : List Nat}
    {f : Frame} {start : Option FuncIdx} (hm : inProfile m = true)
    (hp : instantiateOnce? s m (imports as) = some (s', f, start)) :
    f.module.funcs = as ++ addresses s.funcs.length m.funcs.length := by
  obtain ⟨s₁, _, _, hg, ha, _, _⟩ := PreparationOnce.once_allocation hm hp
  obtain ⟨_, hsf, _⟩ := evalGlobals?_shape hg
  obtain ⟨_, _, _, _, _, _, hmi, _⟩ := allocModule?_inv ha
  rw [hmi]
  simp [Module.globalResidue, PreparationOnce.residueImports,
    ExternAddr.funcs_append, ExternAddr.funcs_globalAddrs, hsf, addresses]

theorem once_counts {s s' : Store H} {m : Module} {as : List Nat}
    {f : Frame} {start : Option FuncIdx} (hm : inProfile m = true)
    (hp : instantiateOnce? s m (imports as) = some (s', f, start)) :
    s'.funcs.length = s.funcs.length + m.funcs.length ∧
      s'.globals.length = s.globals.length + m.globals.length := by
  obtain ⟨s₁, _, values, hg, ha, _, _⟩ := PreparationOnce.once_allocation hm hp
  obtain ⟨hsg, hsf, _⟩ := evalGlobals?_shape hg
  have hv : values.length = m.globals.length := by
    simpa only [Module.closedGlobalTypes, List.length_map] using evalGlobals_values_length hg
  obtain ⟨functionTypes, hft, hs⟩ := PreparationOnce.residue_store hm ha
  have hlen := (forall₂_of_mapM hft).length_eq.symm
  rw [hs]
  constructor
  · simp [functionInstances, hsf, hlen]
  · rw [hsg]
    simp [Module.closedGlobalTypes, hv]

/-- Initializer evaluation and residue allocation retain every old stored
function, including provider definitions imported by a later consumer. -/
theorem once_function_retained {s s' : Store H} {m : Module} {as : List Nat}
    {f : Frame} {start : Option FuncIdx} (hm : inProfile m = true)
    (hp : instantiateOnce? s m (imports as) = some (s', f, start))
    {a : Nat} {fi : FuncInst H} (hf : s.funcs[a]? = some fi) :
    s'.funcs[a]? = some fi := by
  obtain ⟨_, _, _, hg, ha, _, _⟩ := PreparationOnce.once_allocation hm hp
  obtain ⟨_, hsf, _⟩ := evalGlobals?_shape hg
  obtain ⟨_, _, hs⟩ := PreparationOnce.residue_store hm ha
  rw [hs, hsf, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hf).1]
  exact hf

/-- Only successful source lookups must survive relocation. A linked suffix
can introduce entries where the provider's old lookup was unavailable. -/
structure Successful (r : Relocation) (source target : ModuleInst) : Prop where
  functions : ∀ {x y : FuncIdx} {a : Nat}, function? r x = some y →
    source.funcs[x.toNat]? = some a → target.funcs[y.toNat]? = some a
  globals : ∀ {x y : GlobalIdx} {a : Nat}, shiftIdx? r.globals x = some y →
    source.globals[x.toNat]? = some a → target.globals[y.toNat]? = some a
  types : ∀ {x y : TypeIdx} {d : DefType}, shiftIdx? r.types x = some y →
    source.types[x.toNat]? = some d → target.types[y.toNat]? = some d

theorem Successful.of_correspondence {r source target}
    (h : LinkExecution.Correspondence r source target) : Successful r source target :=
  ⟨fun hr hs => (h.functions hr).trans hs,
    fun hr hs => (h.globals hr).trans hs, fun hr hs => (h.types hr).trans hs⟩

private theorem address_bound {base count i a : Nat}
    (h : (addresses base count)[i]? = some a) : i < count := by
  simpa only [addresses_length] using (List.getElem?_eq_some_iff.mp h).1

private theorem address_value {base count i a : Nat}
    (h : (addresses base count)[i]? = some a) : a = base+i := by
  exact Option.some.inj (h.symm.trans (addresses_lookup (address_bound h)))

private theorem result_profile {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result) : inProfile result = true := by
  rw [w.output]
  rfl

private theorem result_lengths {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result) :
    result.funcs.length = provider.funcs.length + consumer.funcs.length ∧
      result.globals.length = provider.globals.length + consumer.globals.length := by
  rw [w.output]
  simp only [List.length_append, w.providerFuncs_length, w.funcs_length,
    w.providerGlobals_length, w.globals_length]
  exact ⟨trivial, trivial⟩

/-- A separately instantiated provider has the same successful index lookups
in the actual linked instance, at the same ambient store addresses. -/
theorem provider {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (hl : link? namespaceName provider consumer = some result)
    {s sp sl : Store H} {fp fl : Frame} {startP startL : Option FuncIdx}
    (hp : instantiateOnce? s provider (imports []) = some (sp, fp, startP))
    (hm : instantiateOnce? s result (imports []) = some (sl, fl, startL)) :
    Successful Recipe.identity fp.module fl.module := by
  have hpf := once_functions w.providerProfile hp
  have hlf := once_functions (result_profile w) hm
  have hpg := PreparationOnce.once_globals w.providerProfile hp
  have hlg := PreparationOnce.once_globals (result_profile w) hm
  have hpt := PreparationOnce.once_types w.providerProfile hp
  have hlt := PreparationOnce.once_types (result_profile w) hm
  have lens := result_lengths w
  simp only [List.nil_append] at hpf hlf
  rw [lens.1] at hlf
  rw [lens.2] at hlg
  rw [Allocation.link?_allocTypes hl] at hlt
  refine ⟨?_, ?_, ?_⟩
  · intro x y a hr hx
    have hy : y.toNat = x.toNat := by
      simpa only [Recipe.identity, function?, List.length_nil, Nat.not_lt_zero,
        ite_false, Nat.sub_zero, Nat.zero_add] using
        ((Idx.ofNat?_eq_some_iff _ _).mp hr).symm
    rw [hpf] at hx
    rw [hlf, hy]
    rw [address_value hx]
    exact addresses_lookup (by have := address_bound hx; omega)
  · intro x y a hr hx
    have hy := LinkExecution.shiftIdx?_toNat hr
    change y.toNat = 0+x.toNat at hy
    rw [hpg] at hx
    rw [hlg, hy, Nat.zero_add, address_value hx]
    exact addresses_lookup (by have := address_bound hx; omega)
  · intro x y d hr hx
    have hy := LinkExecution.shiftIdx?_toNat hr
    change y.toNat = 0+x.toNat at hy
    rw [hpt] at hx
    rw [hlt, hy, Nat.zero_add,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1]
    exact hx

/-- Resolved imports and relocated definitions in a separately instantiated
consumer select exactly the same addresses and closed tags in the linked
instance. The provider's actual once-allocation counts determine both offsets. -/
theorem consumer {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (hl : link? namespaceName provider consumer = some result)
    {s sp sc sl : Store H} {fp fc fl : Frame} {startP startC startL : Option FuncIdx}
    (hp : instantiateOnce? s provider (imports []) = some (sp, fp, startP))
    (hc : instantiateOnce? sp consumer
      (imports (w.imports.map (fun f => s.funcs.length+f.toNat))) = some (sc, fc, startC))
    (hm : instantiateOnce? s result (imports []) = some (sl, fl, startL)) :
    Successful (Recipe.relocation provider w.imports) fc.module fl.module := by
  have hcounts := once_counts w.providerProfile hp
  have hcf := once_functions w.consumerProfile hc
  have hlf := once_functions (result_profile w) hm
  have hcg := PreparationOnce.once_globals w.consumerProfile hc
  have hlg := PreparationOnce.once_globals (result_profile w) hm
  have hct := PreparationOnce.once_types w.consumerProfile hc
  have hlt := PreparationOnce.once_types (result_profile w) hm
  have lens := result_lengths w
  rw [hcounts.1] at hcf
  rw [hcounts.2] at hcg
  simp only [List.nil_append] at hlf
  rw [lens.1] at hlf
  rw [lens.2] at hlg
  rw [Allocation.link?_allocTypes hl] at hlt
  refine ⟨?_, ?_, ?_⟩
  · intro x y a hr hx
    change (if x.toNat < w.imports.length then w.imports[x.toNat]?
      else Idx.ofNat? (provider.funcs.length+(x.toNat-w.imports.length))) = some y at hr
    by_cases hi : x.toNat < w.imports.length
    · rw [ite_eq_left hi] at hr
      rw [hcf, List.getElem?_append_left (by simpa only [List.length_map] using hi),
        List.getElem?_map, hr] at hx
      have ha : a = s.funcs.length+y.toNat := Option.some.inj hx.symm
      rw [hlf, ha]
      apply addresses_lookup
      have hb := Resolution.assembly_imports_bounded w y (List.mem_of_getElem? hr)
      omega
    · rw [ite_eq_right hi] at hr
      have hy : y.toNat = provider.funcs.length+(x.toNat-w.imports.length) :=
        ((Idx.ofNat?_eq_some_iff _ _).mp hr).symm
      have hil : (w.imports.map (fun f => s.funcs.length+f.toNat)).length ≤ x.toNat := by
        simpa only [List.length_map] using Nat.le_of_not_gt hi
      rw [hcf, List.getElem?_append_right hil, List.length_map] at hx
      rw [hlf, hy, address_value hx, Nat.add_assoc]
      apply addresses_lookup
      have hb := address_bound hx
      omega
  · intro x y a hr hx
    have hy := LinkExecution.shiftIdx?_toNat hr
    change y.toNat = provider.globals.length+x.toNat at hy
    rw [hcg] at hx
    rw [hlg, hy, address_value hx, Nat.add_assoc]
    exact addresses_lookup (by have := address_bound hx; omega)
  · intro x y d hr hx
    have hy := LinkExecution.shiftIdx?_toNat hr
    change y.toNat = provider.typeDefinitions.length+x.toNat at hy
    rw [hct] at hx
    have hpLen : (allocTypes provider.types).length = provider.typeDefinitions.length :=
      Allocation.allocTypes_length provider.types
    rw [hlt, hy, ← hpLen,
      List.getElem?_append_right (Nat.le_add_right _ _)]
    simpa using hx

end Silmaril.Wasm.Link.GC.Views
