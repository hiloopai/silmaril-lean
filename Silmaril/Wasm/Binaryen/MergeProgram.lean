module

public import Silmaril.Wasm.Binaryen.MergeReverse
public import Silmaril.Wasm.Binaryen.Behaviour

@[expose] public section

/-! # One step of an N-ary merge, at the level of instances

`merge?` links each module, its imports pointed at one namespace, after the
merge of the earlier ones. Separate instantiation instantiates it against the
earlier instances. One step relates the two:

* `step_forward`: if the merge so far is instantiated and the separate store is
  joined to it by a chain, the separate instantiation of the next module gives the
  merged instantiation, joined by a chain again; the exports of the merged instance
  agree with those of every earlier instance and of the new one (`kind`);
* `step_backward`: if the merged module instantiates, so does the next module
  separately.

Import module names carry no execution content (`renamespace`), and exports are
compared through `kind`: absent, a function address, or something else.
-/

namespace Silmaril.Wasm.Binaryen.MergeChain

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Link.GC Silmaril.Wasm.Link.GC.Preparation

variable {H : Type}

theorem empty_funcs : ({} : Store H).funcs.length = 0 := rfl

/-! ## Import module names carry no content -/

/-- Point every import at namespace `ns` (`retarget` of the merge). -/
def renamespace (ns : String) (m : Module) : Module :=
  { m with imports := m.imports.map fun i => { i with moduleName := ns } }

theorem prepare_renamespace (ev : Store H → Frame → Expr → Option (Store H × Val))
    (s : Store H) (ns : String) (m : Module) (xas : List ExternAddr) :
    prepare? ev s (renamespace ns m) xas = prepare? ev s m xas := rfl

theorem inProfile_renamespace (ns : String) (m : Module) :
    Link.GC.inProfile (renamespace ns m) = Link.GC.inProfile m := by
  simp [Link.GC.inProfile, renamespace, List.all_map, Function.comp_def]

theorem forall₂_map_left' {α β γ : Type} {f : α → γ} {R : γ → β → Prop} {S : α → β → Prop}
    (hRS : ∀ a b, R (f a) b → S a b) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R (l.map f) l' → List.Forall₂ S l l' := by
  intro l
  induction l with
  | nil =>
    intro l' h
    simp only [List.map_nil] at h
    cases h
    exact .nil
  | cons a l ih =>
    intro l' h
    simp only [List.map_cons] at h
    cases h with
    | cons h t => exact .cons (hRS _ _ h) (ih t)

theorem moduleOk_renamespace {ns : String} {m : Module} {mt : CModuleType}
    (h : ModuleOk (renamespace ns m) mt) : ModuleOk m mt := by
  cases h with
  | mk htypes himports hC' hC htags hglobals hmems htables hfuncs hdata helems hstart hexports
      hdisjoint =>
    exact ModuleOk.mk htypes
      (forall₂_map_left' (f := fun (i : Import) => { i with moduleName := ns }) (fun _ _ h => h) himports)
      hC' hC htags hglobals hmems htables hfuncs hdata helems hstart hexports hdisjoint

theorem valid_renamespace {X : Store H} {ns : String} {m : Module} {as : List Nat}
    (h : Valid X (renamespace ns m) as) : Valid X m as := by
  obtain ⟨xtE, xtI, hm, hx⟩ := h
  exact ⟨xtE, xtI, moduleOk_renamespace hm, hx⟩

/-! ## Validity and readiness -/

theorem Chain.valid_back {X Y : Store H} (hc : Chain X Y) {m : Module} {as : List Nat}
    (hv : Valid Y m as) : Valid X m as := by
  obtain ⟨xtE, xtI, hm, hx⟩ := hv
  exact ⟨xtE, xtI, hm, forall₂_externAddrOk (fun a => (hc.tag_lookup a).symm) hx⟩

theorem valid_closed {X : Store H} {m : Module} {mt : CModuleType} (hm : ModuleOk m mt)
    (hi : m.imports = []) : Valid X m [] := by
  obtain ⟨xtI, xtE⟩ := mt
  refine ⟨xtE, xtI, hm, ?_⟩
  cases hm with
  | mk _ himports _ _ _ _ _ _ _ _ _ _ _ _ =>
    rw [hi] at himports
    cases himports
    exact .nil

/-- A prepared profile module with no code left is ready. -/
theorem ready_of_prepare {P : Profile} {host : HostSemantics H} {s s' : Store H} {m : Module}
    {as : List Nat} {mi : ModuleInst} (hv : Valid s m as)
    (hp : prepare? evalConst? s m (imports as) = some (⟨s', { module := mi }, []⟩, none)) :
    Ready P host s m (imports as) s' mi :=
  ⟨⟨s', { module := mi }, []⟩, ⟨s', { module := mi }, []⟩,
    (prepare?_iff hv).mp (by rw [hp]; rfl), .refl, rfl, rfl, rfl⟩

/-- A ready profile module was prepared with no code left. -/
theorem prepare_of_ready {P : Profile} {s s' : Store H} {m : Module} {as : List Nat}
    {mi : ModuleInst} (hm : Link.GC.inProfile m = true)
    (h : Ready P Simulation.noHost s m (imports as) s' mi) :
    prepare? evalConst? s m (imports as) = some (⟨s', { module := mi }, []⟩, none) := by
  obtain ⟨c, c', hi, hst, hcode, hs', hmi⟩ := h
  have hc := instantiate?_evalConst_complete hi
  rw [prepare?_instantiate?] at hc
  obtain ⟨⟨c₀, st⟩, hp, hw⟩ := Option.map_eq_some_iff.mp hc
  obtain ⟨-, -, -, -, -, hloc, hcode₀, hst₀⟩ := prepare_allocation hm hp
  subst hst₀
  have hw' : c = c₀ := by rw [← hw]; rfl
  subst hw'
  rcases Relation.ReflTransGen.cases_head hst with rfl | ⟨d, hd, -⟩
  · rcases c with ⟨cs, ⟨cl, cm⟩, cc⟩
    have h1 : cl = [] := hloc
    have h2 : cc = [] := hcode₀
    have h3 : cs = s' := hs'
    have h4 : cm = mi := hmi
    subst h1 h2 h3 h4
    exact hp
  · exfalso
    rcases c with ⟨cs, cf, cc⟩
    have h2 : cc = [] := hcode₀
    subst h2
    exact SingleThreaded.Det.not_step_vals (W := []) hd

theorem moduleOk_of_ready {P : Profile} {host : HostSemantics H} {s s' : Store H} {m : Module}
    {xas : List ExternAddr} {mi : ModuleInst} (h : Ready P host s m xas s' mi) :
    ∃ mt, ModuleOk m mt := by
  obtain ⟨c, -, hi, -⟩ := h
  obtain ⟨xtE, xtI, hm, -⟩ := hi.valid
  exact ⟨_, hm⟩

/-! ## Exports -/

/-- The function address an export instance names, if any. -/
def addrFunc : ExternAddr → Option Nat
  | .func a => some a
  | _ => none

/-- The function address an export index names in a view, if any. -/
def idxFunc (funcs : List Nat) : ExternIdx → Option Nat
  | .func x => funcs[x.toNat]?
  | _ => none

/-- How an instance exports `y`: not at all, a function address, or something else. -/
def kind (mi : ModuleInst) (y : String) : Option (Option Nat) :=
  (mi.exports.find? (fun e => e.name == y)).map fun e => addrFunc e.addr

/-- How a module exports `y`, through function addresses `funcs`. -/
def mkind (funcs : List Nat) (m : Module) (y : String) : Option (Option Nat) :=
  (m.exports.find? (fun e => e.name == y)).map fun e => idxFunc funcs e.index

theorem exportFunc_kind (mi : ModuleInst) (y : String) :
    exportFunc? mi y = (kind mi y).bind id := by
  unfold exportFunc? kind
  cases mi.exports.find? (fun e => e.name == y) with
  | none => rfl
  | some e =>
    rcases e with ⟨n, _ | _ | _ | _ | a⟩ <;> rfl

theorem find_forall₂ {α β γ : Type} {R : α → β → Prop} {na : α → String} {nb : β → String}
    {ga : α → γ} {gb : β → γ} (hR : ∀ a b, R a b → na a = nb b ∧ ga a = gb b)
    {l : List α} {l' : List β} (h : List.Forall₂ R l l') (y : String) :
    (l.find? (fun a => na a == y)).map ga = (l'.find? (fun b => nb b == y)).map gb := by
  induction h with
  | nil => rfl
  | @cons a b l l' hab _ ih =>
    obtain ⟨hn, hg⟩ := hR a b hab
    have hb : (na a == y) = (nb b == y) := by rw [hn]
    simp only [List.find?_cons, hb]
    cases nb b == y
    · exact ih
    · exact congrArg some hg

theorem allocExport_kind {mi : ModuleInst} {e : Export} {xi : ExportInst}
    (h : allocExport? mi e = some xi) :
    e.name = xi.name ∧ idxFunc mi.funcs e.index = addrFunc xi.addr := by
  rcases e with ⟨name, idx⟩
  cases idx <;>
  · simp only [allocExport?, Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp [idxFunc, addrFunc, ha]

theorem mapM_some_of_mem {α β : Type} {f : α → Option β} {l : List α} {l' : List β}
    (h : l.mapM f = some l') {a : α} (ha : a ∈ l) : ∃ b, f a = some b := by
  obtain ⟨b, -, hb⟩ :=
    forall₂_mem_left (List.mapM_some_forall₂ (R := fun a b => f a = some b) (fun h => h) h) a ha
  exact ⟨b, hb⟩

/-- A prepared instance exports as its module does, through its function addresses. -/
theorem prepared_kind {s : Store H} {m : Module} {as : List Nat} {c : Config H}
    {st : Option FuncIdx} (hm : Link.GC.inProfile m = true)
    (hp : prepare? evalConst? s m (imports as) = some (c, st)) (y : String) :
    kind c.frame.module y = mkind c.frame.module.funcs m y := by
  obtain ⟨s₁, f₁, values, -, ha, -, -, -⟩ := prepare_allocation hm hp
  obtain ⟨tagTypes, funcTypes, xi, -, -, hx, hmi, -⟩ := allocModule?_inv ha
  have h := find_forall₂ (R := fun e xi' => allocExport? _ e = some xi')
    (fun _ _ h => allocExport_kind h) (List.mapM_some_forall₂ (fun h => h) hx) y
  unfold kind mkind
  rw [hmi]
  exact h.symm

/-- An exported function index of a prepared module is in range. -/
theorem prepared_range {s : Store H} {m : Module} {as : List Nat} {c : Config H}
    {st : Option FuncIdx} (hm : Link.GC.inProfile m = true)
    (hp : prepare? evalConst? s m (imports as) = some (c, st)) {e : Export} (he : e ∈ m.exports)
    {x : FuncIdx} (hx : e.index = .func x) : ∃ a, c.frame.module.funcs[x.toNat]? = some a := by
  obtain ⟨s₁, f₁, values, -, ha, -, -, -⟩ := prepare_allocation hm hp
  obtain ⟨tagTypes, funcTypes, xi, -, -, hxs, hmi, -⟩ := allocModule?_inv ha
  obtain ⟨b, hb⟩ := mapM_some_of_mem hxs he
  rcases e with ⟨name, idx⟩
  have hidx : idx = .func x := hx
  subst hidx
  simp only [allocExport?, Option.map_map, Option.map_eq_some_iff] at hb
  obtain ⟨a, ha, -⟩ := hb
  rw [hmi]
  exact ⟨a, ha⟩

theorem export_cases {r : Relocation} {name : String} {idx : ExternIdx} {e' : Export}
    (h : export? r ⟨name, idx⟩ = some e') :
    (∃ x y, idx = .func x ∧ function? r x = some y ∧ e' = ⟨name, .func y⟩) ∨
      (∃ g g', idx = .global g ∧ shiftIdx? r.globals g = some g' ∧ e' = ⟨name, .global g'⟩) := by
  cases idx <;> simp only [export?, Option.bind_eq_bind, Option.map_eq_map,
    Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.pure_def, Option.some.injEq,
    Option.bind_none, reduceCtorEq] at h
  case func x =>
    obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := h
    exact .inl ⟨x, y, rfl, hy, h.symm⟩
  case global g =>
    obtain ⟨_, ⟨g', hg, rfl⟩, h⟩ := h
    exact .inr ⟨g, g', rfl, hg, h.symm⟩

theorem export_name {r : Relocation} {e e' : Export} (h : export? r e = some e') :
    e'.name = e.name := by
  rcases e with ⟨name, idx⟩
  rcases export_cases h with ⟨_, _, -, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ <;> rfl

theorem forall₂_mem' {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') : List.Forall₂ (fun a b => R a b ∧ a ∈ l ∧ b ∈ l') l l' := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih =>
    refine .cons ⟨hab, by simp, by simp⟩ (List.Forall₂.imp ?_ ih)
    intro a b ⟨hr, ha, hb⟩
    exact ⟨hr, List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb⟩

/-- The linked module exports every name either part exports. -/
theorem find_result {ns : String} {provider consumer result : Module}
    (w : Recipe.Assembly ns provider consumer result) {y : String}
    (h : (provider.exports.find? (fun e => e.name == y)).isSome ∨
      (consumer.exports.find? (fun e => e.name == y)).isSome) :
    (result.exports.find? (fun e => e.name == y)).isSome := by
  have hro : result.exports = provider.exports ++ w.exports := congrArg Module.exports w.output
  rw [hro, List.find?_isSome]
  rcases h with h | h
  · obtain ⟨e, he, hn⟩ := List.find?_isSome.mp h
    exact ⟨e, List.mem_append_left _ he, hn⟩
  · obtain ⟨e, he, hn⟩ := List.find?_isSome.mp h
    obtain ⟨e', he', h'⟩ := forall₂_mem_left (List.mapM_some_forall₂
      (R := fun e e' => export? (Recipe.relocation provider w.imports) e = some e')
      (fun h => h) w.exportsRewrite) e he
    refine ⟨e', List.mem_append_right _ he', ?_⟩
    show (e'.name == y) = true
    rw [export_name h']
    exact hn

/-- **Provider exports survive linking.** -/
theorem kind_provider {ns : String} {provider consumer result : Module}
    (w : Recipe.Assembly ns provider consumer result) {cP cR : Config H}
    {stP stR : Option FuncIdx}
    (hP : prepare? evalConst? ({} : Store H) provider (imports []) = some (cP, stP))
    (hR : prepare? evalConst? ({} : Store H) result (imports []) = some (cR, stR)) {y : String}
    (hy : (provider.exports.find? (fun e => e.name == y)).isSome) :
    kind cR.frame.module y = kind cP.frame.module y := by
  rw [prepared_kind (result_profile w) hR, prepared_kind w.providerProfile hP]
  unfold mkind
  have hro : result.exports = provider.exports ++ w.exports := congrArg Module.exports w.output
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hy
  rw [hro, List.find?_append, he, Option.some_or]
  dsimp only [Option.map]
  congr 1
  have hfP := (prepared_views w.providerProfile hP).2.1
  have hfR := (prepared_views (result_profile w) hR).2.1
  have hlen : provider.funcs.length ≤ result.funcs.length := by
    have funcs : result.funcs = w.providerFuncs ++ w.funcs := congrArg Module.funcs w.output
    rw [funcs, List.length_append, w.providerFuncs_length]
    omega
  cases hx : e.index with
  | func x =>
    obtain ⟨a, ha⟩ := prepared_range w.providerProfile hP (List.mem_of_find?_eq_some he) hx
    rw [hfP, List.nil_append] at ha
    have hlt : x.toNat < provider.funcs.length := by
      simpa using (List.getElem?_eq_some_iff.mp ha).1
    simp only [idxFunc]
    rw [hfP, hfR, List.nil_append, List.nil_append, addresses_lookup hlt,
      addresses_lookup (by omega)]
  | tag _ => rfl
  | global _ => rfl
  | memory _ => rfl
  | table _ => rfl

/-- **Consumer exports survive linking**: the consumer instantiated separately
against the provider's exports exports as the linked instance does. -/
theorem kind_consumer {ns : String} {provider q result : Module}
    (w : Recipe.Assembly ns provider (renamespace ns q) result) {s : Store H}
    {cQ cR : Config H} {stQ stR : Option FuncIdx}
    (hR : prepare? evalConst? ({} : Store H) result (imports []) = some (cR, stR))
    (hQ : prepare? evalConst? s q
      (imports (w.imports.map (fun f => ({} : Store H).funcs.length + f.toNat))) =
        some (cQ, stQ))
    (hlen : s.funcs.length = provider.funcs.length)
    (hnodup : (result.exports.map Export.name).Nodup) {y : String}
    (hy : (q.exports.find? (fun e => e.name == y)).isSome) :
    kind cQ.frame.module y = kind cR.frame.module y := by
  have hq : Link.GC.inProfile q = true := by
    rw [← inProfile_renamespace ns q]; exact w.consumerProfile
  rw [prepared_kind hq hQ, prepared_kind (result_profile w) hR]
  unfold mkind
  have hro : result.exports = provider.exports ++ w.exports := congrArg Module.exports w.output
  have hrel : List.Forall₂ (fun e e' => export? (Recipe.relocation provider w.imports) e = some e')
      q.exports w.exports :=
    List.mapM_some_forall₂ (fun h => h) w.exportsRewrite
  have hnone : provider.exports.find? (fun e => e.name == y) = none := by
    rw [List.find?_eq_none]
    intro e₁ he₁ hn₁
    obtain ⟨e₂, he₂, hn₂⟩ := List.find?_isSome.mp hy
    obtain ⟨e₃, he₃, h₃⟩ := forall₂_mem_left hrel e₂ he₂
    have hn₃ := export_name h₃
    rw [hro, List.map_append, List.nodup_append] at hnodup
    refine hnodup.2.2 e₁.name (List.mem_map_of_mem he₁) e₃.name (List.mem_map_of_mem he₃) ?_
    simp only [beq_iff_eq] at hn₁ hn₂
    rw [hn₃, hn₁, hn₂]
  rw [hro, List.find?_append, hnone, Option.none_or]
  refine find_forall₂ (R := fun e e' => export? (Recipe.relocation provider w.imports) e = some e' ∧
    e ∈ q.exports ∧ e' ∈ w.exports) ?_ (forall₂_mem' hrel) y
  rintro ⟨name, idx⟩ e' ⟨h, he, he'⟩
  rcases export_cases h with ⟨x, y', rfl, hy', rfl⟩ | ⟨g, g', rfl, -, rfl⟩
  · refine ⟨rfl, ?_⟩
    show cQ.frame.module.funcs[x.toNat]? = cR.frame.module.funcs[y'.toNat]?
    obtain ⟨a, ha⟩ := prepared_range hq hQ he rfl
    obtain ⟨b, hb⟩ := prepared_range (result_profile w) hR
      (by rw [hro]; exact List.mem_append_right _ he') rfl
    rw [(prepared_views hq hQ).2.1] at ha ⊢
    rw [(prepared_views (result_profile w) hR).2.1, List.nil_append] at hb ⊢
    have hbR : y'.toNat < result.funcs.length := by
      simpa using (List.getElem?_eq_some_iff.mp hb).1
    rw [addresses_lookup hbR]
    unfold function? at hy'
    simp only [Recipe.relocation] at hy'
    by_cases hlt : x.toNat < w.imports.length
    · simp only [hlt, ↓reduceIte] at hy'
      rw [List.getElem?_append_left (by simpa using hlt)]
      simp [List.getElem?_map, hy']
    · simp only [hlt, ↓reduceIte] at hy'
      have hge := hlt
      have hy'' := (Idx.ofNat?_eq_some_iff _ _).mp hy'
      rw [List.getElem?_append_right (by simpa using hge)] at ha ⊢
      simp only [List.length_map] at ha ⊢
      have hq' : x.toNat - w.imports.length < q.funcs.length := by
        simpa using (List.getElem?_eq_some_iff.mp ha).1
      rw [addresses_lookup hq', hlen, ← hy'', empty_funcs]
      simp
  · exact ⟨rfl, rfl⟩

/-! ## Imports of the next module -/

theorem forall₂_of_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, l.length = l'.length →
      (∀ (i : Nat) a b, l[i]? = some a → l'[i]? = some b → R a b) → List.Forall₂ R l l'
  | [], [], _, _ => .nil
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | a :: l, b :: l', hl, h =>
    .cons (h 0 a b rfl rfl) (forall₂_of_getElem? (by simpa using hl)
      (fun i x y hx hy => h (i + 1) x y (by simpa using hx) (by simpa using hy)))

theorem forall₂_lookup_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β} {i : Nat} {b : β},
      List.Forall₂ R l l' → l'[i]? = some b → ∃ a, l[i]? = some a ∧ R a b
  | _, _, _, _, .nil, h => by simp at h
  | a :: _, _ :: _, 0, _, .cons hab _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨a, rfl, hab⟩
  | _ :: _, _ :: _, i + 1, _, .cons _ t, h => by
    simpa using forall₂_lookup_right t (by simpa using h)

theorem forall₂_lookup_left {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β} {i : Nat} {a : α},
      List.Forall₂ R l l' → l[i]? = some a → ∃ b, l'[i]? = some b ∧ R a b
  | _, _, _, _, .nil, h => by simp at h
  | _ :: _, b :: _, 0, _, .cons hab _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨b, rfl, hab⟩
  | _ :: _, _ :: _, i + 1, _, .cons _ t, h => by
    simpa using forall₂_lookup_left t (by simpa using h)

/-- The type of a function export of an import-free valid module is the type
its function is allocated at. -/
theorem export_type {m : Module} {mt : CModuleType} {exported : Export} {type : DefType}
    {f : FuncIdx} (hv : validate? m = some mt) (hp : m.imports = [])
    (he : (exported, CExternType.func type) ∈ m.exports.zip mt.exports)
    (hx : exported.index = .func f) :
    ∃ fn, m.funcs[f.toNat]? = some fn ∧ (allocTypes m.types)[fn.type.toNat]? = some type := by
  cases validate?_sound hv with
  | mk htypes hi hC' hC _ _ _ _ hf _ _ _ hexports _ =>
    have hI := hi.length_eq
    rw [hp] at hI
    have hI' := List.length_eq_zero_iff.mp hI.symm
    have hxok := List.forall₂_zip hexports he
    change ExternIdxOk _ exported.index (.func type) at hxok
    rw [hx] at hxok
    subst hC hC'
    cases hxok with
    | func hl =>
      simp only [hI', CExternType.funcs, List.nil_append] at hl
      obtain ⟨fn, hfn, hok⟩ := forall₂_lookup_right hf hl
      cases hok with
      | mk hd _ _ _ =>
        refine ⟨fn, hfn, ?_⟩
        rw [allocTypes_eq htypes]
        simpa [Context.type?] using hd

theorem consumer_import_funcs {ns : String} {provider consumer result : Module}
    (w : Recipe.Assembly ns provider consumer result) :
    ∀ xt ∈ w.consumerType.imports, ∃ d, xt = .func d := by
  have hok : ModuleOk consumer w.consumerType := validate?_sound w.consumerValidation
  revert hok
  generalize w.consumerType = ct
  intro hok
  rcases ct with ⟨xtI, xtE⟩
  cases hok with
  | mk _ himports _ _ _ _ _ _ _ _ _ _ _ _ => exact import_types_funcs w.consumerProfile himports

/-- An imported function's closed signature is valid in the empty runtime context. -/
theorem consumer_import_typeOk {ns : String} {provider consumer result : Module}
    (w : Recipe.Assembly ns provider consumer result) {i : Nat} {expected : DefType}
    (ht : w.consumerType.imports[i]? = some (.func expected)) :
    ExternTypeOk {} (.func expected) := by
  have hok := validate?_sound w.consumerValidation
  generalize w.consumerType = ct at hok ht
  rcases ct with ⟨xtI, xtE⟩
  cases hok with
  | mk htypes himports _ _ _ _ _ _ _ _ _ _ _ _ =>
    obtain ⟨entry, hi, hentry⟩ := forall₂_lookup_right himports ht
    obtain ⟨closed, valid⟩ := hentry
    cases he : entry.type <;> simp [Context.closeExtern?, he, Option.map_eq_some_iff] at closed
    rename_i index
    have member : expected ∈ _ := List.mem_of_getElem? closed
    cases valid with
    | func _ expands =>
      exact ExternTypeOk.func (htypes.tyOk_empty' expected member) expands

/-- **The consumer's imports are typed** by the provider's prepared functions. -/
theorem consumer_valid {ns : String} {provider consumer result : Module}
    (w : Recipe.Assembly ns provider consumer result) {s : Store H} {cp : Config H}
    {startP : Option FuncIdx}
    (hp : prepare? evalConst? s provider (imports []) = some (cp, startP)) :
    Valid cp.store consumer (w.imports.map (fun f => s.funcs.length + f.toNat)) := by
  have hok : ModuleOk consumer w.consumerType := validate?_sound w.consumerValidation
  refine ⟨w.consumerType.exports, w.consumerType.imports, hok, ?_⟩
  apply forall₂_of_getElem?
  · simp only [imports, List.length_map, w.imports_length,
      Recipe.validation_imports_length w.consumerValidation]
  · intro i a xt ha hxt
    obtain ⟨expected, rfl⟩ := consumer_import_funcs w xt (List.mem_of_getElem? hxt)
    have hlen : i < consumer.imports.length := by
      rw [← Recipe.validation_imports_length w.consumerValidation]
      exact (List.getElem?_eq_some_iff.mp hxt).1
    obtain ⟨f, -, exported, actual, hf, -, -, hfind, hx, subtype⟩ :=
      w.import_lookup (List.getElem?_eq_getElem hlen) hxt
    obtain ⟨fn, hfn, hd⟩ := export_type w.providerValidation w.providerImports
      (List.mem_of_find?_eq_some hfind) hx
    have hpf := (prepared_function w.providerProfile hp hfn hd).2
    simp only [imports, List.map_map, List.getElem?_map, hf, Option.map_some,
      Option.some.injEq, Function.comp_apply] at ha
    subst ha
    exact ExternAddrOk.sub (ExternAddrOk.func hpf)
      (consumer_import_typeOk w hxt) (ExternSub.func subtype)

theorem find_zip {β : Type} {y : String} :
    ∀ {l : List Export} {l' : List β} {a : Export} {b : β},
      (l.zip l').find? (fun (e, _) => e.name == y) = some (a, b) →
        l.find? (fun e => e.name == y) = some a
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | e :: l, b' :: l', a, b, h => by
    simp only [List.zip_cons_cons, List.find?_cons] at h ⊢
    cases hb : (e.name == y)
    · simp only [hb] at h ⊢
      exact find_zip h
    · simp only [hb, Option.some.injEq, Prod.mk.injEq] at h ⊢
      exact h.1

/-- **An import of the next module names a function export of the merge so far.** -/
theorem import_kind {ns : String} {acc q r : Module}
    (w : Recipe.Assembly ns acc (renamespace ns q) r) {cA : Config H} {stA : Option FuncIdx}
    (hA : prepare? evalConst? ({} : Store H) acc (imports []) = some (cA, stA))
    {j : Nat} {imp : Import} (hj : q.imports[j]? = some imp) :
    ∃ f, w.imports[j]? = some f ∧
      kind cA.frame.module imp.name = some (some (({} : Store H).funcs.length + f.toNat)) := by
  have hlen : j < w.consumerType.imports.length := by
    rw [Recipe.validation_imports_length w.consumerValidation]
    have := (List.getElem?_eq_some_iff.mp hj).1
    simpa [renamespace] using this
  obtain ⟨expected, hexp⟩ := consumer_import_funcs w _ (List.getElem_mem hlen)
  have ht : w.consumerType.imports[j]? = some (.func expected) := by
    rw [List.getElem?_eq_getElem hlen, hexp]
  have hi : (renamespace ns q).imports[j]? = some { imp with moduleName := ns } := by
    simp [renamespace, hj]
  obtain ⟨f, -, exported, _, hf, -, -, hfind, hx, _⟩ := w.import_lookup hi ht
  refine ⟨f, hf, ?_⟩
  rw [prepared_kind w.providerProfile hA]
  unfold mkind
  have hfa : acc.exports.find? (fun e => e.name == imp.name) = some exported := find_zip hfind
  have hbound := Resolution.exported_function_bound w.providerValidation w.providerImports
    (List.mem_of_find?_eq_some hfind) hx
  rw [hfa]
  dsimp only [Option.map]
  rw [hx, (prepared_views w.providerProfile hA).2.1]
  simp only [idxFunc, List.nil_append]
  rw [addresses_lookup hbound]

/-! ## One step -/

/-- **Forward step.** -/
theorem step_forward {ns : String} {acc q r : Module}
    (w : Recipe.Assembly ns acc (renamespace ns q) r)
    (hl : link? ns acc (renamespace ns q) = some r) {sA : Store H} {miA : ModuleInst}
    (hA : prepare? evalConst? ({} : Store H) acc (imports []) =
      some (⟨sA, { module := miA }, []⟩, none))
    {s s' : Store H} {miQ : ModuleInst} (hchain : Chain s sA)
    (hQ : prepare? evalConst? s q
      (imports (w.imports.map (fun f => ({} : Store H).funcs.length + f.toNat))) =
        some (⟨s', { module := miQ }, []⟩, none)) :
    ∃ sl miR, prepare? evalConst? ({} : Store H) r (imports []) =
        some (⟨sl, { module := miR }, []⟩, none) ∧ Chain s' sl ∧
      (∀ y, (acc.exports.find? (fun e => e.name == y)).isSome → kind miR y = kind miA y) ∧
      (∀ y, (q.exports.find? (fun e => e.name == y)).isSome → kind miQ y = kind miR y) := by
  have hq : Link.GC.inProfile q = true := by
    rw [← inProfile_renamespace ns q]; exact w.consumerProfile
  have hvA : Valid ({} : Store H) acc [] :=
    valid_closed (validate?_sound w.providerValidation) w.providerImports
  have okA : StoreOk sA := prepare_storeOk storeOk_empty hvA hA
  have hvQ' := consumer_valid w hA
  have hvQs := hchain.valid_back (valid_renamespace hvQ')
  obtain ⟨cs', hQ', hc'⟩ := Chain.prepare hq hchain hQ hvQs
  have hQr : prepare? evalConst? sA (renamespace ns q)
      (imports (w.imports.map (fun f => ({} : Store H).funcs.length + f.toNat))) =
        some (⟨cs', { module := miQ }, []⟩, none) := by
    rw [prepare_renamespace]; exact hQ'
  obtain ⟨sl, miR, hR⟩ := merged_exists w hl hA hQr
  have okc : StoreOk cs' := prepare_storeOk okA hvQ' hQr
  have hlc := link_chain w hl hA hQr hR okc
  refine ⟨sl, miR, hR, hc'.append hlc, ?_, ?_⟩
  · intro y hy
    exact kind_provider w hA hR hy
  · intro y hy
    have hcA : sA.funcs.length = ({} : Store H).funcs.length + acc.funcs.length :=
      (prepared_counts w.providerProfile hA).1
    have hlen : s.funcs.length = acc.funcs.length := by
      rw [hchain.funcs_length, hcA, empty_funcs, Nat.zero_add]
    obtain ⟨mt, hmt⟩ := link?_valid hl
    have hnd : (r.exports.map Export.name).Nodup := by
      cases hmt with
      | mk _ _ _ _ _ _ _ _ _ _ _ _ _ hdisjoint => exact hdisjoint
    exact kind_consumer w hR hQ hlen hnd hy

/-- **Backward step.** -/
theorem step_backward {ns : String} {acc q r : Module}
    (w : Recipe.Assembly ns acc (renamespace ns q) r)
    (hl : link? ns acc (renamespace ns q) = some r) {sA : Store H} {miA : ModuleInst}
    (hA : prepare? evalConst? ({} : Store H) acc (imports []) =
      some (⟨sA, { module := miA }, []⟩, none))
    {s : Store H} (hchain : Chain s sA) {cl : Config H} {stL : Option FuncIdx}
    (hR : prepare? evalConst? ({} : Store H) r (imports []) = some (cl, stL)) :
    ∃ s' miQ, prepare? evalConst? s q
        (imports (w.imports.map (fun f => ({} : Store H).funcs.length + f.toNat))) =
          some (⟨s', { module := miQ }, []⟩, none) ∧
      Valid s q (w.imports.map (fun f => ({} : Store H).funcs.length + f.toNat)) := by
  have hq : Link.GC.inProfile q = true := by
    rw [← inProfile_renamespace ns q]; exact w.consumerProfile
  obtain ⟨cp, startP, hp, cc, startC, hc⟩ := separate_exists w hl hR
  rw [hA, Option.some.injEq, Prod.mk.injEq] at hp
  obtain ⟨rfl, -⟩ := hp
  have hvQs := hchain.valid_back (valid_renamespace (consumer_valid w hA))
  rcases cc with ⟨cs', cf, ccode⟩
  have hc' : prepare? evalConst? sA q
      (imports (w.imports.map (fun f => ({} : Store H).funcs.length + f.toNat))) =
        some (⟨cs', cf, ccode⟩, startC) := by
    rw [← prepare_renamespace evalConst? sA ns q]; exact hc
  obtain ⟨cs, hcs⟩ := Chain.prepare_back hq hchain hc'
  obtain ⟨-, -, -, -, -, hloc, hcode, hst⟩ := prepare_allocation hq hcs
  rcases cf with ⟨loc, mi⟩
  have h1 : loc = [] := hloc
  have h2 : ccode = [] := hcode
  subst h1 h2 hst
  exact ⟨cs, mi, hcs, hvQs⟩

end Silmaril.Wasm.Binaryen.MergeChain
