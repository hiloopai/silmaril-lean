module

public import Silmaril.Proofs.Wasm.Game.Linking.Split.InitEval

/-!
# Static linking, separation: the initial invariant

Original module documentation:

# The initial split of the shared store (M3 step B, #1977)

Game semantics of WebAssembly modules (tracking issue #1982), milestone M3, step (B).

`static_nonempty`: the initial stores of a `Setup` satisfy `Static`.

* The provider owns its functions (`fp.module.funcs`), its globals and the GC objects its
  initialisers allocated (addresses between `base` and `sp`); the consumer owns its functions,
  the stubs, its globals and the GC objects its initialisers allocated (between `sp` and
  `sc`). The two are disjoint (consumer allocations follow the provider's).
* The stores are related by the identity renamings: `sc` extends `sp` (`OnceFacts`), and
  `scs = stubOut sc` (`Setup.scs_eq_stubOut`) differs from `sc` only in the code of the stubs.
* The export addresses of the linked module are provider functions (hence stubs,
  `Setup.exports_stubbed`) or consumer functions (they follow the provider's).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Game.Linking.Split

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game Silmaril.Proofs.Wasm.Game.GamesAux Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Proofs.Wasm.Game.Linking Silmaril.Wasm.Link.GC

/-! ### The identity renaming -/

@[simp] theorem Ren.id_ref : ∀ r : Ref, Ren.id.ref r = r
  | .i31 _ => rfl
  | .null => rfl
  | .struct _ => rfl
  | .array _ => rfl
  | .func _ => rfl
  | .exn _ => rfl
  | .host _ => rfl
  | .extern r => by simp [Ren.ref_extern, Ren.id_ref r]

@[simp] theorem Ren.id_val (v : Val) : Ren.id.val v = v := by
  cases v <;> simp [Ren.val]

@[simp] theorem Ren.id_fval (v : FieldVal) : Ren.id.fval v = v := by
  cases v <;> simp [Ren.fval]

@[simp] theorem Ren.id_sinst (si : StructInst) : Ren.id.sinst si = si := by
  have : (Ren.id.fval) = fun v => v := funext Ren.id_fval
  simp [Ren.sinst, this]

@[simp] theorem Ren.id_ainst (ai : ArrayInst) : Ren.id.ainst ai = ai := by
  have : (Ren.id.fval) = fun v => v := funext Ren.id_fval
  simp [Ren.ainst, this]

@[simp] theorem Ren.id_ginst (g : GlobalInst) : Ren.id.ginst g = g := by
  simp [Ren.ginst]

@[simp] theorem Ren.id_st (a : Nat) : Ren.id.st a = a := rfl
@[simp] theorem Ren.id_ar (a : Nat) : Ren.id.ar a = a := rfl

/-! ### Helpers -/

theorem prefix_getElem? {α : Type _} {l₁ l₂ : List α} (h : l₁ <+: l₂) {i : Nat} {x : α}
    (hx : l₁[i]? = some x) : l₂[i]? = some x := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1]
  exact hx

theorem getElem?_isSome_of_lt {α : Type _} {l : List α} {i : Nat} (h : i < l.length) :
    ∃ x, l[i]? = some x := ⟨l[i], List.getElem?_eq_getElem h⟩

theorem stubOut_funcs (b : Nat) (st : List Nat) (s : Store Nat) (a : Nat) :
    (stubOut b st s).funcs[a]? = s.funcs[a]?.map (fun fi =>
      if b ≤ a ∧ a - b ∈ st then { fi with code := .host (st.idxOf (a - b)) } else fi) := by
  simp [stubOut, List.getElem?_mapIdx]

@[simp] theorem stubOut_globals (b : Nat) (st : List Nat) (s : Store Nat) :
    (stubOut b st s).globals = s.globals := rfl
@[simp] theorem stubOut_structs (b : Nat) (st : List Nat) (s : Store Nat) :
    (stubOut b st s).structs = s.structs := rfl
@[simp] theorem stubOut_arrays (b : Nat) (st : List Nat) (s : Store Nat) :
    (stubOut b st s).arrays = s.arrays := rfl

theorem goodVal_congr {O O' : Own} (hst : ∀ a, O.st a → O'.st a) (har : ∀ a, O.ar a → O'.ar a)
    (hfn : ∀ a, O.fn a → O'.fn a) {v : Val} (h : O.GoodVal v) : O'.GoodVal v :=
  Own.GoodVal.mono hst har hfn h

theorem goodFV_congr {O O' : Own} (hst : ∀ a, O.st a → O'.st a) (har : ∀ a, O.ar a → O'.ar a)
    (hfn : ∀ a, O.fn a → O'.fn a) {v : FieldVal} (h : O.GoodFV v) : O'.GoodFV v :=
  Own.GoodFV.mono hst har hfn h

theorem linked_profile (S : Setup) : inProfile S.linked = true := by
  rw [S.assembly.output]; rfl

theorem linked_funcs_length (S : Setup) :
    S.linked.funcs.length = S.provider.funcs.length + S.consumer.funcs.length := by
  have h1 := mapM_some_length S.assembly.providerFuncsRewrite
  have h2 := S.assembly.funcs_length
  rw [S.assembly.output]
  simp [h1, h2]

/-! ### The static facts -/

variable (S : Setup)

/-- What the provider owns. -/
def _root_.Silmaril.Wasm.Game.Linking.Setup.provOwn : Own where
  st a := S.base.structs.length ≤ a ∧ a < S.sp.structs.length
  ar a := S.base.arrays.length ≤ a ∧ a < S.sp.arrays.length
  fn a := a ∈ S.fp.module.funcs
  gl a := a ∈ S.fp.module.globals

/-- The stub addresses. -/
def _root_.Silmaril.Wasm.Game.Linking.Setup.IsStub (a : Nat) : Prop := S.base.funcs.length ≤ a ∧ a - S.base.funcs.length ∈ S.stubs

/-- What the consumer owns. -/
def _root_.Silmaril.Wasm.Game.Linking.Setup.consOwn : Own where
  st a := S.sp.structs.length ≤ a ∧ a < S.sc.structs.length
  ar a := S.sp.arrays.length ≤ a ∧ a < S.sc.arrays.length
  fn a := a ∈ S.fc.module.funcs ∨ S.IsStub a
  gl a := a ∈ S.fc.module.globals

/-! ### The parts of the initial invariant -/

private theorem prov_facts : OnceFacts S.base S.sp S.provider [] S.fp.module :=
  once_facts S.assembly.providerProfile S.provInst

private theorem cons_facts : OnceFacts S.sp S.sc S.consumer
    (S.assembly.imports.map (fun f => S.base.funcs.length + f.toNat)) S.fc.module :=
  once_facts S.assembly.consumerProfile S.sharedInst

private theorem linked_facts : OnceFacts S.base S.sl S.linked [] S.fl.module :=
  once_facts (linked_profile S) S.linkedInst

/-- A global of an instantiated module is a global of the new store. -/
private theorem OnceFacts.global_lt {s s' : Store Nat} {m : Module} {as : List Nat}
    {mi : ModuleInst} (O : OnceFacts s s' m as mi) {a : Nat} (ha : a ∈ mi.globals) :
    a < s'.globals.length := by
  obtain ⟨j, hj, hja⟩ : ∃ j, j < m.globals.length ∧ s.globals.length + j = a := by
    simpa only [O.globals_mi, List.mem_map, List.mem_range] using ha
  rw [O.globals_len]
  omega

/-- The provider world has no host function. -/
private theorem sp_wasm (hS : S.Scalar) (a : Nat) (fi : FuncInst Nat)
    (h : S.sp.funcs[a]? = some fi) : ∃ c, fi.code = .wasm c := by
  cases hc : fi.code with
  | wasm c => exact ⟨c, rfl⟩
  | host k =>
    obtain ⟨hlt, -⟩ := hS.provider.host_type a fi k h hc
    exact absurd hlt (by simp [Setup.providerI])

/-- The shared world has no host function. -/
private theorem sc_wasm (hS : S.Scalar) (a : Nat) (fi : FuncInst Nat)
    (h : S.sc.funcs[a]? = some fi) : ∃ c, fi.code = .wasm c := by
  cases hc : fi.code with
  | wasm c => exact ⟨c, rfl⟩
  | host k =>
    obtain ⟨hlt, -⟩ := hS.shared.host_type a fi k h hc
    exact absurd hlt (by simp [Setup.sharedI])

/-- The provider functions, in the provider and the shared worlds. -/
private theorem prov_func (k : Nat) (hk : k < S.provider.funcs.length) :
    ∃ fi : FuncInst Nat, S.sp.funcs[S.base.funcs.length + k]? = some fi ∧
      S.sc.funcs[S.base.funcs.length + k]? = some fi ∧ fi.module = S.fp.module ∧
        ∃ c, fi.code = .wasm c := by
  obtain ⟨d, fn, h⟩ := (prov_facts S).funcs_new k hk
  exact ⟨_, h, prefix_getElem? (cons_facts S).funcs_prefix h, rfl, fn, rfl⟩

private theorem sp_funcs_length :
    S.sp.funcs.length = S.base.funcs.length + S.provider.funcs.length := by
  simpa using (prov_facts S).funcs_len

/-- The provider functions are the addresses following the base store. -/
private theorem prov_fn_iff {a : Nat} : a ∈ S.fp.module.funcs ↔
    ∃ k, k < S.provider.funcs.length ∧ S.base.funcs.length + k = a := by
  simp only [(prov_facts S).funcs_mi, List.nil_append, List.mem_map, List.mem_range]

private theorem prov_modGood : S.provOwn.ModGood S.fp.module :=
  have P := prov_facts S
  ⟨P.tags, P.mems, P.tables, P.elems, P.datas, fun _ h => h, fun _ h => h⟩

private theorem cons_modGood : S.consOwn.ModGood S.fc.module :=
  have C : OnceFacts S.sp S.sc S.consumer
      (S.assembly.imports.map (fun f => S.base.funcs.length + f.toNat)) S.fc.module :=
    cons_facts S
  ⟨C.tags, C.mems, C.tables, C.elems, C.datas, fun _ h => h, fun _ h => .inl h⟩

/-- The provider part of the initial stores. -/
private theorem prov_rel : PartRel Ren.id S.provOwn S.sp S.sc := by
  have P : OnceFacts S.base S.sp S.provider [] S.fp.module := prov_facts S
  have C : S.sp.globals <+: S.sc.globals ∧ S.sp.structs <+: S.sc.structs ∧
      S.sp.arrays <+: S.sc.arrays :=
    ⟨(cons_facts S).globals, (cons_facts S).structs, (cons_facts S).arrays⟩
  have hO' : (∀ a, (IOwn S.base.structs.length S.base.arrays.length (· ∈ S.fp.module.funcs)
      S.sp).st a → S.provOwn.st a) ∧
      (∀ a, (IOwn S.base.structs.length S.base.arrays.length (· ∈ S.fp.module.funcs)
        S.sp).ar a → S.provOwn.ar a) ∧
      (∀ a, (IOwn S.base.structs.length S.base.arrays.length (· ∈ S.fp.module.funcs)
        S.sp).fn a → S.provOwn.fn a) :=
    ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩
  refine ⟨fun a (ha : a ∈ S.fp.module.funcs) => ?_, fun a (ha : a ∈ S.fp.module.globals) => ?_,
    fun a ha => ?_, fun a ha => ?_, fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩
  · obtain ⟨k, hk, hka⟩ := (prov_fn_iff S).mp ha
    obtain ⟨fi, h1, h2, hm, -⟩ := prov_func S k hk
    exact hka ▸ ⟨fi, h1, fi, h2, rfl, fun _ _ => ⟨rfl, hm ▸ prov_modGood S⟩⟩
  · obtain ⟨g, hg⟩ := getElem?_isSome_of_lt (P.global_lt ha)
    exact ⟨g, hg, by simpa using prefix_getElem? C.1 hg,
      goodVal_congr hO'.1 hO'.2.1 hO'.2.2 (P.good_globals a ha g hg)⟩
  · obtain ⟨si, hsi⟩ := getElem?_isSome_of_lt ha.2
    exact ⟨si, hsi, by simpa using prefix_getElem? C.2.1 hsi, fun fv hfv =>
      goodFV_congr hO'.1 hO'.2.1 hO'.2.2 (P.heap.st a si ha.1 hsi fv hfv)⟩
  · obtain ⟨ai, hai⟩ := getElem?_isSome_of_lt ha.2
    exact ⟨ai, hai, by simpa using prefix_getElem? C.2.2 hai, fun fv hfv =>
      goodFV_congr hO'.1 hO'.2.1 hO'.2.2 (P.heap.ar a ai ha.1 hai fv hfv)⟩

/-- A stub of the consumer world: the provider function, with host code. -/
private theorem cons_fn_stub {a : Nat} (hst : S.IsStub a) :
    ∃ fi, (stubOut S.base.funcs.length S.stubs S.sc).funcs[a]? = some fi ∧
      ∃ fi', S.sc.funcs[a]? = some fi' ∧ fi'.type = fi.type ∧
        ∀ c, fi.code = .wasm c → fi' = fi ∧ S.consOwn.ModGood fi.module := by
  obtain ⟨hB, hk⟩ := hst
  obtain ⟨fi, -, h2, -, -⟩ := prov_func S (a - S.base.funcs.length) (S.stubs_lt _ hk)
  have hfi : S.sc.funcs[a]? = some fi := by simpa only [Nat.add_sub_cancel' hB] using h2
  have hst' : S.base.funcs.length ≤ a ∧ a - S.base.funcs.length ∈ S.stubs := ⟨hB, hk⟩
  refine ⟨{ fi with code := .host (S.stubs.idxOf (a - S.base.funcs.length)) }, ?_, fi, hfi,
    rfl, fun c hc => by cases hc⟩
  rw [stubOut_funcs, hfi]
  simp only [Option.map_some, hst', and_self, ite_true]

/-- A consumer function that is not a stub: unchanged by `stubOut`. -/
private theorem cons_fn_own {a : Nat} (ha : a ∈ S.fc.module.funcs) (hst : ¬ S.IsStub a) :
    ∃ fi, (stubOut S.base.funcs.length S.stubs S.sc).funcs[a]? = some fi ∧
      ∃ fi', S.sc.funcs[a]? = some fi' ∧ fi'.type = fi.type ∧
        ∀ c, fi.code = .wasm c → fi' = fi ∧ S.consOwn.ModGood fi.module := by
  have C : OnceFacts S.sp S.sc S.consumer
      (S.assembly.imports.map (fun f => S.base.funcs.length + f.toNat)) S.fc.module :=
    cons_facts S
  have hst' : ¬ (S.base.funcs.length ≤ a ∧ a - S.base.funcs.length ∈ S.stubs) := hst
  rcases List.mem_append.mp (C.funcs_mi ▸ ha) with hi | hn
  · obtain ⟨x, hx, hxa⟩ := List.mem_map.mp hi
    have hstub : S.IsStub a :=
      hxa ▸ ⟨Nat.le_add_right _ _, by simpa using S.imports_stubbed x hx⟩
    exact absurd hstub hst
  · obtain ⟨k, hk, hka⟩ : ∃ k, k < S.consumer.funcs.length ∧ S.sp.funcs.length + k = a := by
      simpa only [List.mem_map, List.mem_range] using hn
    obtain ⟨d, fn, h⟩ := C.funcs_new k hk
    have hfi : S.sc.funcs[a]? = some ⟨d, S.fc.module, .wasm fn⟩ := hka ▸ h
    refine ⟨_, ?_, _, hfi, rfl, fun _ _ => ⟨rfl, cons_modGood S⟩⟩
    rw [stubOut_funcs, hfi]
    simp only [Option.map_some, hst', ite_false]

/-- The consumer part of the initial stores. -/
private theorem cons_rel : PartRel Ren.id S.consOwn S.scs S.sc := by
  have C : OnceFacts S.sp S.sc S.consumer
      (S.assembly.imports.map (fun f => S.base.funcs.length + f.toNat)) S.fc.module :=
    cons_facts S
  have hO' : (∀ a, (IOwn S.sp.structs.length S.sp.arrays.length (· ∈ S.fc.module.funcs)
      S.sc).st a → S.consOwn.st a) ∧
      (∀ a, (IOwn S.sp.structs.length S.sp.arrays.length (· ∈ S.fc.module.funcs)
        S.sc).ar a → S.consOwn.ar a) ∧
      (∀ a, (IOwn S.sp.structs.length S.sp.arrays.length (· ∈ S.fc.module.funcs)
        S.sc).fn a → S.consOwn.fn a) :=
    ⟨fun _ h => h, fun _ h => h, fun _ h => Or.inl h⟩
  rw [S.scs_eq_stubOut]
  refine ⟨fun a ha => ?_, fun a (ha : a ∈ S.fc.module.globals) => ?_, fun a ha => ?_,
    fun a ha => ?_, fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩
  · by_cases hst : S.IsStub a
    · exact cons_fn_stub S hst
    · exact cons_fn_own S (ha.resolve_right hst) hst
  · obtain ⟨g, hg⟩ := getElem?_isSome_of_lt (C.global_lt ha)
    exact ⟨g, by simpa using hg, by simpa using hg,
      goodVal_congr hO'.1 hO'.2.1 hO'.2.2 (C.good_globals a ha g hg)⟩
  · obtain ⟨si, hsi⟩ := getElem?_isSome_of_lt ha.2
    exact ⟨si, by simpa using hsi, by simpa using hsi, fun fv hfv =>
      goodFV_congr hO'.1 hO'.2.1 hO'.2.2 (C.heap.st a si ha.1 hsi fv hfv)⟩
  · obtain ⟨ai, hai⟩ := getElem?_isSome_of_lt ha.2
    exact ⟨ai, by simpa using hai, by simpa using hai, fun fv hfv =>
      goodFV_congr hO'.1 hO'.2.1 hO'.2.2 (C.heap.ar a ai ha.1 hai fv hfv)⟩

/-- The provider and consumer globals are disjoint. -/
private theorem gl_disjoint (a : Nat) (ha : S.provOwn.gl a) : ¬ S.consOwn.gl a := by
  intro (hb : a ∈ S.fc.module.globals)
  have hlt : a < S.sp.globals.length := (prov_facts S).global_lt ha
  obtain ⟨j', -, he⟩ : ∃ j, j < S.consumer.globals.length ∧ S.sp.globals.length + j = a := by
    simpa only [(cons_facts S).globals_mi, List.mem_map, List.mem_range] using hb
  omega

/-- The address of a stub is the corresponding provider export. -/
private theorem stub_addr (hS : S.Scalar) {a : Nat}
    (hst : S.base.funcs.length ≤ a ∧ a - S.base.funcs.length ∈ S.stubs) :
    ∃ hlt : S.stubs.idxOf (a - S.base.funcs.length) < S.stubTypes.length,
      S.providerI.addr ⟨_, hlt⟩ = a ∧ S.provOwn.fn a := by
  have hlen : S.stubs.length = S.stubTypes.length := by
    simpa [Setup.providerI] using hS.provider.addrs_length
  have hidx : S.stubs.idxOf (a - S.base.funcs.length) < S.stubs.length :=
    List.idxOf_lt_length_of_mem hst.2
  refine ⟨by omega, ?_, (prov_fn_iff S).mpr ⟨_, S.stubs_lt _ hst.2, Nat.add_sub_cancel' hst.1⟩⟩
  simp only [ScalarInstance.addr, Setup.providerI]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hidx]
  simp only [Option.map_some, Option.getD_some, List.getElem_idxOf]
  omega

/-- Host functions of the consumer world are the stubs. -/
private theorem stub_spec (hS : S.Scalar) (a : Nat) (fi : FuncInst Nat) (h : Nat)
    (hfi : S.scs.funcs[a]? = some fi) (hcode : fi.code = .host h) :
    ∃ hlt : h < S.stubTypes.length, S.providerI.addr ⟨h, hlt⟩ = a ∧ S.provOwn.fn a := by
  have hfi' : (S.sc.funcs[a]?.map fun fi =>
      if S.base.funcs.length ≤ a ∧ a - S.base.funcs.length ∈ S.stubs then
        { fi with code := .host (S.stubs.idxOf (a - S.base.funcs.length)) } else fi) = some fi := by
    rw [← stubOut_funcs, ← S.scs_eq_stubOut]
    exact hfi
  obtain ⟨fi₀, h₀, hfi₀⟩ := Option.map_eq_some_iff.mp hfi'
  by_cases hst : S.base.funcs.length ≤ a ∧ a - S.base.funcs.length ∈ S.stubs
  · have hh : S.stubs.idxOf (a - S.base.funcs.length) = h := by
      simpa only [← hfi₀, hst, and_self, ite_true, FuncCode.host.injEq] using hcode
    exact hh ▸ stub_addr S hS hst
  · obtain ⟨c, hc⟩ := sc_wasm S hS a fi₀ h₀
    have hc' : fi.code = .wasm c := by simpa only [← hfi₀, hst, ite_false] using hc
    exact absurd (hcode.symm.trans hc') (by simp)

/-- The export addresses of the linked module are owned by the consumer. -/
private theorem exports_spec (hS : S.Scalar) (j : Fin S.exportTypes.length) :
    S.consOwn.fn (S.consumerI.addr j) := by
  have hl : (exportFuncAddrs S.fl.module).length = S.exportTypes.length := by
    simpa [Setup.consumerI] using hS.consumer.addrs_length
  have hj : j.val < (exportFuncAddrs S.fl.module).length := by
    have hj' : j.val < S.exportTypes.length := j.2
    omega
  have hmem : S.consumerI.addr j ∈ exportFuncAddrs S.fl.module := by
    simp only [ScalarInstance.addr, Setup.consumerI]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    exact List.getElem_mem hj
  obtain ⟨i, hi, hia⟩ : ∃ i, i < S.provider.funcs.length + S.consumer.funcs.length ∧
      S.base.funcs.length + i = S.consumerI.addr j := by
    simpa only [(linked_facts S).funcs_mi, List.nil_append, List.mem_map, List.mem_range,
      linked_funcs_length] using (linked_facts S).exports _ hmem
  by_cases hip : i < S.provider.funcs.length
  · exact .inr ⟨by omega, S.exports_stubbed _ hmem (by omega) (by omega)⟩
  · have hk : i - S.provider.funcs.length < S.consumer.funcs.length := by omega
    have hka : S.sp.funcs.length + (i - S.provider.funcs.length) = S.consumerI.addr j := by
      rw [sp_funcs_length]
      omega
    refine .inl ((cons_facts S).funcs_mi ▸ List.mem_append_right _ ?_)
    exact List.mem_map.mpr ⟨_, List.mem_range.mpr hk, hka⟩

/-- The initial stores satisfy `Static`, with the explicit ownership `provOwn`, `consOwn`. -/
theorem static_spec (hS : S.Scalar) :
    ∃ St : Static S, St.Op = S.provOwn ∧ St.Oc = S.consOwn := by
  have hst : ∀ a b, S.provOwn.st a → S.consOwn.st b → Ren.id.st a ≠ Ren.id.st b :=
    fun _ _ ha hb => Nat.ne_of_lt (Nat.lt_of_lt_of_le ha.2 hb.1)
  have har : ∀ a b, S.provOwn.ar a → S.consOwn.ar b → Ren.id.ar a ≠ Ren.id.ar b :=
    fun _ _ ha hb => Nat.ne_of_lt (Nat.lt_of_lt_of_le ha.2 hb.1)
  have hrel : Rel4 S.provOwn S.consOwn Ren.id S.provOwn Ren.id S.consOwn S.sc S.sp S.scs :=
    ⟨prov_rel S, cons_rel S, rfl, rfl, rfl, rfl, gl_disjoint S, hst, har⟩
  exact ⟨⟨S.provOwn, S.consOwn, hrel, stub_spec S hS, sp_wasm S hS, exports_spec S hS⟩, rfl, rfl⟩

theorem static_nonempty (hS : S.Scalar) : Nonempty (Static S) :=
  (static_spec S hS).elim fun St _ => ⟨St⟩

end Silmaril.Proofs.Wasm.Game.Linking.Split
