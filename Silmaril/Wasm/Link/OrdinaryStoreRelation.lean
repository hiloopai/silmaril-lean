module

public import Silmaril.Wasm.Link.GlobalPermutation
public import Silmaril.Wasm.Link.StoreRelation
public import Silmaril.Wasm.Link.OrdinaryInitializers

/-! # Function views after ordinary separate and linked preparation

The global permutation moves provider copies past consumer initializers.
Function addresses and closed tags stay fixed, and the resulting module views
support the existing linker simulation.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.OrdinaryStoreRelation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Preparation

variable {H : Type}

abbrev permutation (s : Store H) (provider consumer : Module) : Nat ≃ Nat :=
  GlobalPermutation.blocks (s.globals.length + provider.globals.length)
    provider.globals.length consumer.globals.length

/-- Normalize global values and every wasm function's module addresses. -/
def normalize (p : Nat ≃ Nat) (globals : List GlobalInst) (source : Store H) : Store H :=
  { source with globals := globals, funcs := source.funcs.map (GlobalPermutation.function p) }

theorem normalize_renamed {p : Nat ≃ Nat} {source : Store H} {globals : List GlobalInst}
    (h : GlobalPermutation.Lookup p source.globals globals) :
    GlobalPermutation.Renamed p source (normalize p globals source) :=
  ⟨h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem address_bound {base count i a : Nat}
    (h : (addresses base count)[i]? = some a) : i < count := by
  simpa only [addresses_length] using (List.getElem?_eq_some_iff.mp h).1

private theorem address_value {base count i a : Nat}
    (h : (addresses base count)[i]? = some a) : a = base + i :=
  Option.some.inj (h.symm.trans (addresses_lookup (address_bound h)))

theorem result_profile {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result) : inProfile result = true := by
  rw [w.output]
  rfl

theorem result_lengths {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result) :
    result.funcs.length = provider.funcs.length + consumer.funcs.length ∧
      result.globals.length = provider.globals.length + consumer.globals.length := by
  rw [w.output]
  simp only [List.length_append, w.providerFuncs_length, w.funcs_length,
    w.providerGlobals_length, w.globals_length]
  exact ⟨trivial, trivial⟩

/-- Renaming provider global addresses yields successful lookups in the
actual linked instance, while provider instructions retain their indices. -/
theorem provider_views {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (linked : link? namespaceName provider consumer = some result)
    {s : Store H} {cp cl : Config H} {startP startL : Option FuncIdx}
    (hp : prepare? evalConst? s provider (imports []) = some (cp, startP))
    (hl : prepare? evalConst? s result (imports []) = some (cl, startL)) :
    Views.Successful Recipe.identity
      (GlobalPermutation.moduleView (permutation s provider consumer) cp.frame.module)
      cl.frame.module := by
  obtain ⟨hpt, hpf, hpg⟩ := prepared_views w.providerProfile hp
  obtain ⟨hlt, hlf, hlg⟩ := prepared_views (result_profile w) hl
  have lens := result_lengths w
  simp only [List.nil_append] at hpf hlf
  rw [lens.1] at hlf
  rw [lens.2] at hlg
  rw [Allocation.link?_allocTypes linked] at hlt
  refine ⟨?_, ?_, ?_⟩
  · intro x y a hr hx
    change cp.frame.module.funcs[x.toNat]? = some a at hx
    have hy : y.toNat = x.toNat := by
      simpa only [Recipe.identity, function?, List.length_nil, Nat.not_lt_zero,
        ite_false, Nat.sub_zero, Nat.zero_add] using
        ((Idx.ofNat?_eq_some_iff _ _).mp hr).symm
    rw [hpf] at hx
    rw [hlf, hy, address_value hx]
    exact addresses_lookup (by have := address_bound hx; omega)
  · intro x y a hr hx
    change (cp.frame.module.globals.map (permutation s provider consumer))[x.toNat]? = some a at hx
    rw [hpg, List.getElem?_map] at hx
    obtain ⟨old, oldLookup, rfl⟩ := Option.map_eq_some_iff.mp hx
    have bound := address_bound oldLookup
    have hy := LinkExecution.shiftIdx?_toNat hr
    change y.toNat = 0 + x.toNat at hy
    rw [address_value oldLookup, GlobalPermutation.provider_address _ _ _ _ bound]
    rw [hlg, hy, Nat.zero_add]
    have hi := addresses_lookup
      (base := s.globals.length + (provider.globals.length + consumer.globals.length))
      (by omega : x.toNat < provider.globals.length + consumer.globals.length)
    simpa only [Nat.add_assoc] using hi
  · intro x y d hr hx
    change cp.frame.module.types[x.toNat]? = some d at hx
    have hy := LinkExecution.shiftIdx?_toNat hr
    change y.toNat = 0 + x.toNat at hy
    rw [hpt] at hx
    rw [hlt, hy, Nat.zero_add,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1]
    exact hx

/-- Consumer installed globals already have their linked addresses; imported
functions and relocated types retain the same successful bindings. -/
theorem consumer_views {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (linked : link? namespaceName provider consumer = some result)
    {s : Store H} {cp cc cl : Config H} {startP startC startL : Option FuncIdx}
    (hp : prepare? evalConst? s provider (imports []) = some (cp, startP))
    (hc : prepare? evalConst? cp.store consumer
      (imports (w.imports.map (fun f => s.funcs.length + f.toNat))) = some (cc, startC))
    (hl : prepare? evalConst? s result (imports []) = some (cl, startL)) :
    Views.Successful (Recipe.relocation provider w.imports)
      (GlobalPermutation.moduleView (permutation s provider consumer) cc.frame.module)
      cl.frame.module := by
  have counts := prepared_counts w.providerProfile hp
  obtain ⟨hct, hcf, hcg⟩ := prepared_views w.consumerProfile hc
  obtain ⟨hlt, hlf, hlg⟩ := prepared_views (result_profile w) hl
  have lens := result_lengths w
  rw [counts.1] at hcf
  rw [counts.2] at hcg
  simp only [List.nil_append] at hlf
  rw [lens.1] at hlf
  rw [lens.2] at hlg
  rw [Allocation.link?_allocTypes linked] at hlt
  refine ⟨?_, ?_, ?_⟩
  · intro x y a hr hx
    change cc.frame.module.funcs[x.toNat]? = some a at hx
    change (if x.toNat < w.imports.length then w.imports[x.toNat]?
      else Idx.ofNat? (provider.funcs.length + (x.toNat - w.imports.length))) = some y at hr
    by_cases hi : x.toNat < w.imports.length
    · rw [ite_eq_left hi] at hr
      rw [hcf, List.getElem?_append_left (by simpa only [List.length_map] using hi),
        List.getElem?_map, hr] at hx
      have ha : a = s.funcs.length + y.toNat := Option.some.inj hx.symm
      rw [hlf, ha]
      apply addresses_lookup
      have hb := Resolution.assembly_imports_bounded w y (List.mem_of_getElem? hr)
      omega
    · rw [ite_eq_right hi] at hr
      have hy : y.toNat = provider.funcs.length + (x.toNat - w.imports.length) :=
        ((Idx.ofNat?_eq_some_iff _ _).mp hr).symm
      have hil : (w.imports.map (fun f => s.funcs.length + f.toNat)).length ≤ x.toNat := by
        simpa only [List.length_map] using Nat.le_of_not_gt hi
      rw [hcf, List.getElem?_append_right hil, List.length_map] at hx
      rw [hlf, hy, address_value hx, Nat.add_assoc]
      apply addresses_lookup
      have hb := address_bound hx
      omega
  · intro x y a hr hx
    change (cc.frame.module.globals.map (permutation s provider consumer))[x.toNat]? = some a at hx
    rw [hcg, List.getElem?_map] at hx
    obtain ⟨old, oldLookup, rfl⟩ := Option.map_eq_some_iff.mp hx
    have bound := address_bound oldLookup
    have hy := LinkExecution.shiftIdx?_toNat hr
    change y.toNat = provider.globals.length + x.toNat at hy
    rw [address_value oldLookup, GlobalPermutation.consumer_address]
    rw [hlg, hy]
    have hi := addresses_lookup (base := s.globals.length + (provider.globals.length + consumer.globals.length))
      (by omega : provider.globals.length + x.toNat < provider.globals.length + consumer.globals.length)
    have valueEq : s.globals.length + 2 * provider.globals.length + consumer.globals.length + x.toNat =
        s.globals.length + (provider.globals.length + consumer.globals.length) +
          (provider.globals.length + x.toNat) := by omega
    rw [valueEq]
    exact hi
  · intro x y d hr hx
    change cc.frame.module.types[x.toNat]? = some d at hx
    have hy := LinkExecution.shiftIdx?_toNat hr
    change y.toNat = provider.typeDefinitions.length + x.toNat at hy
    rw [hct] at hx
    have hpLen : (allocTypes provider.types).length = provider.typeDefinitions.length :=
      Allocation.allocTypes_length provider.types
    rw [hlt, hy, ← hpLen, List.getElem?_append_right (Nat.le_add_right _ _)]
    simpa using hx

private theorem external_global_bound {s : Store H} {address : Nat} {type : CExternType}
    (valid : ExternAddrOk s (.global address) type) : address < s.globals.length := by
  generalize same : (ExternAddr.global address) = external at valid
  induction valid generalizing address with
  | global lookup => cases same; exact (List.getElem?_eq_some_iff.mp lookup).1
  | tag _ => cases same
  | mem _ => cases same
  | table _ => cases same
  | func _ => cases same
  | sub _ _ _ ih => exact ih same

private theorem global_list_fixed {s : Store H} {provider consumer : Module}
    {addresses : List Nat} {types : List CGlobalType}
    (valid : List.Forall₂ (fun a g => ExternAddrOk s (.global a) (.global g)) addresses types) :
    addresses.map (permutation s provider consumer) = addresses := by
  induction valid with
  | nil => rfl
  | @cons a g rest types typed _ ih =>
    simp only [List.map_cons, GlobalPermutation.ambient_address _ _ _ _
      (external_global_bound typed), ih]

/-- A well-typed ambient wasm module refers only to ambient global addresses.
Its global tables and exports are therefore fixed by the permutation. -/
theorem module_fixed {s : Store H} {provider consumer : Module} {mi : ModuleInst} {C : Context}
    (valid : ModuleInstOk s mi C) :
    GlobalPermutation.moduleView (permutation s provider consumer) mi = mi := by
  cases valid with
  | mk htypes htags hglobals hfuncs hmems htables hdatas helems hexports hdisjoint hexportAddrs hk =>
    have globals := global_list_fixed (provider := provider) (consumer := consumer) hglobals
    have exports : mi.exports.map (fun e =>
        { e with addr := GlobalPermutation.external (permutation s provider consumer) e.addr }) =
        mi.exports := by
      apply (List.map_congr_left ?_).trans (List.map_id' mi.exports)
      intro e he
      have fixed : GlobalPermutation.external (permutation s provider consumer) e.addr = e.addr := by
        cases ha : e.addr with
        | global address =>
          obtain ⟨type, typed⟩ := hexports e he
          rw [ha] at typed
          simp only [GlobalPermutation.external,
            GlobalPermutation.ambient_address _ _ _ _ (external_global_bound typed)]
        | tag address => rfl
        | mem address => rfl
        | table address => rfl
        | func address => rfl
      rw [fixed]
    simp only [GlobalPermutation.moduleView, globals, exports]

theorem function_fixed {s : Store H} {provider consumer : Module} {fi : FuncInst H}
    (valid : FuncInstOk s fi) :
    GlobalPermutation.function (permutation s provider consumer) fi = fi := by
  cases valid with
  | wasm _ moduleValid code _ _ =>
    simp only [GlobalPermutation.function, code, module_fixed moduleValid]
    simp only [← code]
  | host _ _ code =>
    simp only [GlobalPermutation.function, code]
    simp only [← code]

theorem function_list {s : Store H} {m : Module} {as : List Nat}
    {c : Config H} {start : Option FuncIdx} (profile : inProfile m = true)
    (run : prepare? evalConst? s m (imports as) = some (c, start)) :
    ∃ types, m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) = some types ∧
      c.store.funcs = s.funcs ++ functionInstances c.frame.module types m.funcs := by
  obtain ⟨_, _, _, types, _, _, bindings⟩ := prepare?_gc_bindings profile run
  exact ⟨types, bindings.functionTypes_ok, bindings.store_functions⟩

private theorem forall₂_lookup {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) {i : Nat} {x : α}
    (hx : xs[i]? = some x) : ∃ y, ys[i]? = some y ∧ R x y := by
  induction h generalizing i with
  | nil => simp at hx
  | @cons a b xs ys hab _ ih =>
    cases i with
    | zero => simp at hx; subst x; exact ⟨b, rfl, hab⟩
    | succ i => exact ih (by simpa using hx)

theorem defined_function {s : Store H} {m : Module} {as : List Nat}
    {c : Config H} {start : Option FuncIdx} (profile : inProfile m = true)
    (run : prepare? evalConst? s m (imports as) = some (c, start))
    {n : Nat} {fi : FuncInst H} (lookup : c.store.funcs[s.funcs.length+n]? = some fi) :
    ∃ fn d, m.funcs[n]? = some fn ∧ (allocTypes m.types)[fn.type.toNat]? = some d ∧
      fi = ⟨d, c.frame.module, .wasm fn⟩ := by
  obtain ⟨types, ht, hs⟩ := function_list profile run
  rw [hs, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    functionInstances, List.getElem?_map] at lookup
  obtain ⟨⟨d, fn⟩, hzip, heq⟩ := Option.map_eq_some_iff.mp lookup
  obtain ⟨hd, hfn⟩ := List.getElem?_zip_eq_some.mp hzip
  obtain ⟨d', hd', typeLookup⟩ := forall₂_lookup (forall₂_of_mapM ht) hfn
  have he : d' = d := Option.some.inj (hd'.symm.trans hd)
  subst d'
  exact ⟨fn, d, hfn, typeLookup, heq.symm⟩

theorem old_function {s : Store H} {m : Module} {as : List Nat}
    {c : Config H} {start : Option FuncIdx} (profile : inProfile m = true)
    (run : prepare? evalConst? s m (imports as) = some (c, start))
    {address : Nat} {fi : FuncInst H} (bound : address < s.funcs.length)
    (lookup : c.store.funcs[address]? = some fi) : s.funcs[address]? = some fi := by
  obtain ⟨_, _, hs⟩ := function_list profile run
  rw [hs, List.getElem?_append_left bound] at lookup
  exact lookup

theorem function_retained {s : Store H} {m : Module} {as : List Nat}
    {c : Config H} {start : Option FuncIdx} (profile : inProfile m = true)
    (run : prepare? evalConst? s m (imports as) = some (c, start))
    {address : Nat} {fi : FuncInst H} (lookup : s.funcs[address]? = some fi) :
    c.store.funcs[address]? = some fi := by
  obtain ⟨_, _, hs⟩ := function_list profile run
  rw [hs, List.getElem?_append_left (List.getElem?_eq_some_iff.mp lookup).1]
  exact lookup

private theorem forall₂_of_lookup {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (length : xs.length = ys.length)
    (lookup : ∀ (i : Nat) (x : α), xs[i]? = some x → ∃ y, ys[i]? = some y ∧ R x y) :
    List.Forall₂ R xs ys := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp length.symm
    subst ys
    exact .nil
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.length_cons, List.length_nil] at length; omega
    | cons y ys =>
      obtain ⟨y', hy', hr⟩ := lookup 0 x rfl
      have hy : y' = y := Option.some.inj hy'.symm
      subst y'
      refine .cons hr (ih (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using length) ?_)
      intro i x' hx
      exact lookup (i+1) x' hx

/-- Every function in the normalized separate ordinary store matches its
actual ambient, provider, or relocated consumer definition in the linked store. -/
theorem separate_linked_functions {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (linked : link? namespaceName provider consumer = some result)
    {s : Store H} {cp cc cl : Config H} {startP startC startL : Option FuncIdx}
    (valid : StoreOk s)
    (hp : prepare? evalConst? s provider (imports []) = some (cp, startP))
    (hc : prepare? evalConst? cp.store consumer
      (imports (w.imports.map (fun f => s.funcs.length + f.toNat))) = some (cc, startC))
    (hl : prepare? evalConst? s result (imports []) = some (cl, startL)) :
    List.Forall₂ StoreRelation.Function
      (cc.store.funcs.map (GlobalPermutation.function (permutation s provider consumer)))
      cl.store.funcs := by
  have profile := result_profile w
  have countP := (prepared_counts w.providerProfile hp).1
  have countC := (prepared_counts w.consumerProfile hc).1
  have countL := (prepared_counts profile hl).1
  have lens := (result_lengths w).1
  apply forall₂_of_lookup
  · rw [List.length_map, countC, countP, countL, lens, Nat.add_assoc]
  · intro address fi lookup
    rw [List.getElem?_map] at lookup
    obtain ⟨original, sourceLookup, rfl⟩ := Option.map_eq_some_iff.mp lookup
    by_cases ambient : address < s.funcs.length
    · have oldP : address < cp.store.funcs.length := by omega
      have hcp := old_function w.consumerProfile hc oldP sourceLookup
      have hs := old_function w.providerProfile hp ambient hcp
      have fixed := function_fixed (provider := provider) (consumer := consumer)
        (valid.funcs original (List.mem_of_getElem? hs))
      rw [fixed]
      exact ⟨original, function_retained profile hl hs, .same original⟩
    · by_cases providerPart : address < cp.store.funcs.length
      · have hcp := old_function w.consumerProfile hc providerPart sourceLookup
        have ha : s.funcs.length + (address-s.funcs.length) = address := by omega
        obtain ⟨fn, d, hfn, hd, he⟩ := defined_function w.providerProfile hp
          (n := address-s.funcs.length) (by simpa only [ha] using hcp)
        subst original
        obtain ⟨fn', hf', rewrite⟩ := w.provider_func_lookup hfn
        have same := Identity.func_identity rewrite
        subst fn'
        have hd' := Allocation.link?_provider_type_lookup linked hd
        have target := (prepared_function profile hl hf' hd').2
        exact ⟨_, by simpa only [ha] using target,
          .relocated Recipe.identity (provider_views w linked hp hl) (Functions.rewrite rewrite)⟩
      · have ha : cp.store.funcs.length + (address-cp.store.funcs.length) = address := by omega
        obtain ⟨fn, d, hfn, hd, he⟩ := defined_function w.consumerProfile hc
          (n := address-cp.store.funcs.length) (by simpa only [ha] using sourceLookup)
        subst original
        obtain ⟨fn', hf', rewrite⟩ := w.consumer_func_lookup hfn
        have parts := Functions.rewrite rewrite
        have hd' : (allocTypes result.types)[fn'.type.toNat]? = some d :=
          (Allocation.link?_consumer_type_lookup linked parts.type).trans hd
        have target := (prepared_function profile hl hf' hd').2
        have haddr : s.funcs.length + (provider.funcs.length + (address-cp.store.funcs.length)) =
            address := by omega
        exact ⟨_, by simpa only [haddr] using target,
          .relocated (Recipe.relocation provider w.imports)
            (consumer_views w linked hp hc hl) parts⟩

/-- Actual preparations provide both the address-renaming relation and the
existing linked-store relation; neither assumes execution preservation. -/
theorem separate_linked {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (linked : link? namespaceName provider consumer = some result)
    {s : Store H} {cp cc cl : Config H} {startP startC startL : Option FuncIdx}
    (valid : StoreOk s)
    (hp : prepare? evalConst? s provider (imports []) = some (cp, startP))
    (hc : prepare? evalConst? cp.store consumer
      (imports (w.imports.map (fun f => s.funcs.length + f.toNat))) = some (cc, startC))
    (hl : prepare? evalConst? s result (imports []) = some (cl, startL)) :
    GlobalPermutation.Renamed (permutation s provider consumer) cc.store
      (normalize (permutation s provider consumer) cl.store.globals cc.store) ∧
    StoreRelation.Related
      (normalize (permutation s provider consumer) cl.store.globals cc.store) cl.store := by
  have data := OrdinaryInitializers.separate_linked_data w linked hp hc hl
  refine ⟨normalize_renamed data.globals, ?_⟩
  exact ⟨⟨data.tags, rfl, data.mems, data.tables, data.datas, data.elems,
    data.structs, data.arrays, data.exns⟩, separate_linked_functions w linked valid hp hc hl⟩

end Silmaril.Wasm.Link.GC.OrdinaryStoreRelation
