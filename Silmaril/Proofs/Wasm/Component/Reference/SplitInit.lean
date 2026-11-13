module

public import Silmaril.Proofs.Wasm.Component.Reference.ShiftStep
public import Silmaril.Proofs.Wasm.Component.Reference.LinkWire

/-!
# The initial split invariant of a linked pair

The store split of `Silmaril.Wasm.Game.Linking` (`PartRel`, `Own`) starts from stores whose
functions run in module instances without tags, memories, tables or segments, and whose
globals and GC objects hold only references owned by the store. This file establishes that
starting point for the instances of `Linked2`:

* `ownOf t`: everything allocated in `t`; `StoreGood t`: wasm functions run in `Own.ModGood`
  module instances and globals, structures and arrays hold `ownOf t`-good values;
  `StoreGood.partRel` (the identity `PartRel` of `t` with itself), `StoreGood.mapH`
  (invariant under host renaming);
* `ModSplitOk.inProfile`: the split fragment is the profile of silmaril-lean's GC linker, so
  `Linking.Split.once_facts` applies: `storeGood_once` (a single-allocation instantiation over
  an import store), `storeGood_inst` (every game instance of a `ModSplitOk` module);
* `invoke_good`: the invocation of a function of a good store on scalar arguments is a good
  thread; with `steps_shift`, its host-free runs are relocated runs (`SplitGood`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel IOwn OnceFacts once_facts HeapGood)

variable {H : Type}

/-- Everything allocated in `t`. -/
def ownOf (t : Store H) : Own :=
  ⟨(· < t.structs.length), (· < t.arrays.length), (· < t.funcs.length), (· < t.globals.length)⟩

/-- **A good store**: wasm functions run in good module instances; globals, structures and
arrays hold good values. -/
structure StoreGood (t : Store H) : Prop where
  fn : ∀ (a : Nat) (fi : FuncInst H), t.funcs[a]? = some fi → ∀ c, fi.code = .wasm c → (ownOf t).ModGood fi.module
  gl : ∀ (a : Nat) (g : GlobalInst), t.globals[a]? = some g → (ownOf t).GoodVal g.value
  st : ∀ (a : Nat) (si : StructInst), t.structs[a]? = some si → ∀ fv ∈ si.fields, (ownOf t).GoodFV fv
  ar : ∀ (a : Nat) (ai : ArrayInst), t.arrays[a]? = some ai → ∀ fv ∈ ai.fields, (ownOf t).GoodFV fv

theorem getElem?_of_lt' {α : Type} {l : List α} {a : Nat} (h : a < l.length) :
    ∃ x, l[a]? = some x := ⟨l[a], List.getElem?_eq_getElem h⟩

/-- A good store is related to itself by the identity renaming, owning everything. -/
theorem StoreGood.partRel {t : Store H} (hg : StoreGood t) : PartRel Ren.id (ownOf t) t t where
  fn a ha := by
    obtain ⟨fi, hfi⟩ : ∃ fi, t.funcs[a]? = some fi := getElem?_of_lt' ha
    exact ⟨fi, hfi, fi, hfi, rfl, fun c hc => ⟨rfl, hg.fn a fi hfi c hc⟩⟩
  gl a ha := by
    obtain ⟨g, hga⟩ : ∃ g, t.globals[a]? = some g := getElem?_of_lt' ha
    exact ⟨g, hga, by simpa using hga, hg.gl a g hga⟩
  st a ha := by
    obtain ⟨si, hsi⟩ : ∃ si, t.structs[a]? = some si := getElem?_of_lt' ha
    exact ⟨si, hsi, by simpa using hsi, hg.st a si hsi⟩
  ar a ha := by
    obtain ⟨ai, hai⟩ : ∃ ai, t.arrays[a]? = some ai := getElem?_of_lt' ha
    exact ⟨ai, hai, by simpa using hai, hg.ar a ai hai⟩
  stInj _ _ _ _ h := h
  arInj _ _ _ _ h := h

section MapH

variable {H' : Type} (g : H → H')

theorem ownOf_mapH (t : Store H) : ownOf (Store.mapH g t) = ownOf t := by
  simp [ownOf, Store.mapH]

theorem FuncCode.mapH_eq_wasm {c : FuncCode H} {f : Func} :
    FuncCode.mapH g c = .wasm f ↔ c = .wasm f := by
  cases c <;> simp [FuncCode.mapH]

/-- **Goodness does not depend on host code.** -/
theorem storeGood_mapH_iff (t : Store H) : StoreGood (Store.mapH g t) ↔ StoreGood t := by
  rw [show StoreGood (Store.mapH g t) ↔ StoreGood (H := H') ⟨t.tags, t.globals, t.mems,
      t.tables, t.funcs.map (FuncInst.mapH g), t.datas, t.elems, t.structs, t.arrays, t.exns⟩
    from Iff.rfl]
  have hO : ownOf (H := H') ⟨t.tags, t.globals, t.mems, t.tables, t.funcs.map (FuncInst.mapH g),
      t.datas, t.elems, t.structs, t.arrays, t.exns⟩ = ownOf t := by simp [ownOf]
  constructor
  · rintro ⟨hfn, hgl, hst, har⟩
    refine ⟨fun a fi hfi c hc => ?_, fun a g' h => hO ▸ hgl a g' h,
      fun a si h => hO ▸ hst a si h, fun a ai h => hO ▸ har a ai h⟩
    have h1 : (t.funcs.map (FuncInst.mapH g))[a]? = some (FuncInst.mapH g fi) := by
      simp [List.getElem?_map, hfi]
    exact hO ▸ hfn a _ h1 c ((FuncCode.mapH_eq_wasm g).mpr hc)
  · rintro ⟨hfn, hgl, hst, har⟩
    refine ⟨fun a fi hfi c hc => ?_, fun a g' h => hO ▸ hgl a g' h,
      fun a si h => hO ▸ hst a si h, fun a ai h => hO ▸ har a ai h⟩
    obtain ⟨fi₀, h1, rfl⟩ : ∃ fi₀, t.funcs[a]? = some fi₀ ∧ FuncInst.mapH g fi₀ = fi := by
      simpa [List.getElem?_map] using hfi
    exact hO ▸ hfn a fi₀ h1 c ((FuncCode.mapH_eq_wasm g).mp hc)

end MapH

/-! ## Instantiation -/

theorem _root_.Silmaril.Wasm.Component.Reference.Linked2.ModSplitOk.inProfile {m : Module}
    (h : Silmaril.Wasm.Component.Reference.Linked2.ModSplitOk m) :
    Silmaril.Wasm.Link.GC.inProfile m = true := by
  have hi := h.imports
  simp only [Silmaril.Wasm.Link.GC.inProfile, h.tags, h.memories, h.tables, h.data, h.elems,
    h.start, List.isEmpty_nil, Option.isNone_none, Bool.true_and]
  exact hi

/-- **A single-allocation instantiation over an import store is good**: a store whose
functions are host functions and which has no globals, structures or arrays. -/
theorem storeGood_once {s s' : Store H} {m : Module} {as : List Nat} {f' : Frame}
    {st : Option FuncIdx} (hm : Silmaril.Wasm.Link.GC.inProfile m = true)
    (hp : instantiateOnce? s m (Silmaril.Wasm.Link.GC.Preparation.imports as) = some (s', f', st))
    (hs : ∀ fi ∈ s.funcs, ∀ c, fi.code ≠ .wasm c) (hgl : s.globals = []) (hst : s.structs = [])
    (har : s.arrays = []) (has : ∀ a ∈ as, a < s.funcs.length) :
    StoreGood s' ∧ (ownOf s').ModGood f'.module := by
  have hO : OnceFacts s s' m as f'.module := once_facts hm hp
  have hfl : s'.funcs.length = s.funcs.length + m.funcs.length := hO.funcs_len
  have hgll : s'.globals.length = m.globals.length := by simpa [hgl] using hO.globals_len
  have hF : ∀ a ∈ f'.module.funcs, a < s'.funcs.length := by
    intro a ha
    rw [hO.funcs_mi, List.mem_append, List.mem_map] at ha
    rcases ha with ha | ⟨k, hk, rfl⟩
    · exact lt_of_lt_of_le (has a ha) (by omega)
    · rw [List.mem_range] at hk; omega
  have hMG : (ownOf s').ModGood f'.module :=
    ⟨hO.tags, hO.mems, hO.tables, hO.elems, hO.datas, fun a ha => by
      rw [hO.globals_mi, hgl, List.mem_map] at ha
      obtain ⟨k, hk, rfl⟩ := ha
      show 0 + k < s'.globals.length
      rw [List.mem_range] at hk; omega, hF⟩
  have hmono : ∀ {v : Val}, (IOwn s.structs.length s.arrays.length (· ∈ f'.module.funcs) s').GoodVal v →
      (ownOf s').GoodVal v :=
    fun h => Own.GoodVal.mono (O := IOwn s.structs.length s.arrays.length (· ∈ f'.module.funcs) s')
      (O' := ownOf s') (fun _ h => h.2) (fun _ h => h.2) hF h
  have hmonoFV : ∀ {v : FieldVal},
      (IOwn s.structs.length s.arrays.length (· ∈ f'.module.funcs) s').GoodFV v →
      (ownOf s').GoodFV v :=
    fun h => Own.GoodFV.mono (O := IOwn s.structs.length s.arrays.length (· ∈ f'.module.funcs) s')
      (O' := ownOf s') (fun _ h => h.2) (fun _ h => h.2) hF h
  refine ⟨⟨fun a fi hfi c hc => ?_, fun a g hga => ?_, fun a si hsi fv hfv => ?_,
    fun a ai hai fv hfv => ?_⟩, hMG⟩
  · show (ownOf s').ModGood fi.module
    by_cases ha : a < s.funcs.length
    · obtain ⟨fi₀, h0⟩ : ∃ fi₀, s.funcs[a]? = some fi₀ := getElem?_of_lt' ha
      have he : fi₀ = fi := Option.some.inj
        ((Silmaril.Proofs.Wasm.Game.Linking.Split.prefix_getElem? hO.funcs_prefix h0).symm.trans hfi)
      exact absurd hc (he ▸ hs fi₀ (List.mem_of_getElem? h0) c)
    · obtain ⟨k, rfl⟩ : ∃ k, a = s.funcs.length + k := ⟨a - s.funcs.length, by omega⟩
      have hk : k < m.funcs.length := by
        have := (List.getElem?_eq_some_iff.mp hfi).1; omega
      obtain ⟨d, fn, hnew⟩ := hO.funcs_new k hk
      rw [hnew, Option.some.injEq] at hfi
      subst hfi
      exact hMG
  · have ha : a ∈ f'.module.globals := by
      rw [hO.globals_mi, hgl, List.mem_map]
      exact ⟨a, List.mem_range.mpr (hgll ▸ (List.getElem?_eq_some_iff.mp hga).1), by simp⟩
    exact hmono (hO.good_globals a ha g hga)
  · exact hmonoFV (hO.heap.st a si (by simp [hst]) hsi fv hfv)
  · exact hmonoFV (hO.heap.ar a ai (by simp [har]) hai fv hfv)

theorem funcs_length_of_all : ∀ {l : List CExternType}, (∀ xt ∈ l, ∃ d, xt = .func d) →
    (CExternType.funcs l).length = l.length
  | [], _ => rfl
  | x :: l, h => by
    obtain ⟨d, rfl⟩ := h x (List.mem_cons_self ..)
    simp [CExternType.funcs, funcs_length_of_all (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- **Every game instance of a module of the split fragment has a good store.** -/
theorem storeGood_inst {m : Module} {mt : CModuleType} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hm : Silmaril.Wasm.Component.Reference.Linked2.ModSplitOk m) (hI : Silmaril.Wasm.Game.IsInstance m mt I) : StoreGood I.store := by
  obtain ⟨f, hf, -⟩ := hI.instantiated
  have hlen : (CExternType.funcs mt.imports).length = mt.imports.length :=
    funcs_length_of_all hI.funcImports
  refine (storeGood_once hm.inProfile hf ?_ rfl rfl rfl ?_).1
  · intro fi hfi c
    obtain ⟨j, -, rfl⟩ := List.mem_mapIdx.mp hfi
    simp
  · intro a ha
    rw [List.mem_range] at ha
    simpa [Silmaril.Wasm.Game.importStore, hlen] using ha

/-! ## Invocations -/

/-- **An invocation is a good thread**: the empty frame, scalar arguments and an owned
function. -/
theorem invoke_good {t : Store H} {a : Nat} (ha : a < t.funcs.length) {vs : List Val}
    (hvs : ∀ v ∈ vs, ∀ r, v ≠ .ref r) :
    (ownOf t).FrameGood (invoke t a vs).frame ∧ (ownOf t).CodeGood (invoke t a vs).code := by
  refine ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, nofun, nofun⟩, nofun⟩, ?_⟩
  refine (ownOf t).codeGood_append.mpr ⟨(ownOf t).codeGood_vals.mpr fun v hv => ?_, ?_⟩
  · cases v with
    | ref r => exact absurd rfl (hvs _ hv r)
    | num => trivial
    | vec => trivial
  · exact Own.CodeGood.cons_ref ha (by simp [Own.CodeGood])

/-- **The invocation of a function of a good store is in the split fragment.** -/
theorem splitGood_invoke {t : Store H} (hg : StoreGood t) {a : Nat} (ha : a < t.funcs.length)
    {vs : List Val} (hvs : ∀ v ∈ vs, ∀ r, v ≠ .ref r) : SplitGood (invoke t a vs) :=
  ⟨Ren.id, ownOf t, t, hg.partRel, (invoke_good ha hvs).1, (invoke_good ha hvs).2⟩

end Silmaril.Proofs.Wasm.Component.Reference
