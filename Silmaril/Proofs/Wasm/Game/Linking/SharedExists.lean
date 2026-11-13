module

public import Silmaril.Proofs.Wasm.Game.Linking.InitReverse
public import Silmaril.Proofs.Wasm.Game.Linking.FuncCode

/-!
# Static linking: the shared instantiation exists

Original module documentation:

# The shared and stub instantiations exist (M3, #1977)

Game semantics of WebAssembly modules (tracking issue #1982), milestone M3. From a successful
static link and successful instantiations of the provider and of the linked module, the
consumer instantiates in the provider's store against the provider functions it imports
(`shared_exists`, #1936's shared world), and also in the provider's store with any function
list of the same length (`withFuncs_exists`; used for the store with host stubs).

Route: the consumer's initializers succeed by reverse initializer transport
(`Linking.globals_reflect`) from the consumer part of the linked run, and the allocation of
its global-free residue succeeds because every lookup it makes (function types, function and
global exports) is the source of a lookup that succeeded in the linked allocation.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.Linking

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Link.GC
  Silmaril.Wasm.Link.GC.Initializers

variable {H : Type}

theorem mapM_some_of_forall {α β : Type} {g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, ∃ b, g x = some b) → ∃ r, l.mapM g = some r
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
    obtain ⟨b, hb⟩ := h x (by simp)
    obtain ⟨r, hr⟩ := mapM_some_of_forall (l := l) (fun y hy => h y (by simp [hy]))
    exact ⟨b :: r, by simp [List.mapM_cons, hb, hr]⟩

theorem mapM_some_mem {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM g = some r → ∀ x ∈ l, ∃ b, g x = some b
  | [], _, _, x, hx => by simp at hx
  | y :: l, r, h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, -⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, hb⟩
    · exact mapM_some_mem hbs x hx

theorem profile_sections' {m : Module} (hp : inProfile m = true) :
    m.memories = [] ∧ m.tables = [] ∧ m.tags = [] ∧ m.data = [] ∧ m.elems = [] ∧
      m.start = none := by
  simp only [inProfile, Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at hp
  exact ⟨hp.1.1.1.1.1.1, hp.1.1.1.1.1.2, hp.1.1.1.1.2,
    hp.1.1.1.2, hp.1.1.2, hp.1.2⟩

/-- The converse of `PreparationOnce.once_allocation`: in the linker's profile, a successful
initializer run and a successful residue allocation are a successful single instantiation. -/
theorem once_of_allocation {s s₁ s' : Store H} {m : Module} {as : List Nat} {f₁ : Frame}
    {vs : List Val} {mi : ModuleInst} (hm : inProfile m = true)
    (hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m (Preparation.imports as)⟩
      (Module.closedGlobalTypes m) (m.globals.map Global.init) = some (s₁, f₁, vs))
    (ha : allocModule? s₁ m.globalResidue (PreparationOnce.residueImports s m as) [] [] [] =
      some (s', mi)) :
    ∃ p, instantiateOnce? s m (Preparation.imports as) = some p := by
  obtain ⟨_, ht, _, hd, he, hs⟩ := profile_sections' hm
  have ha' := ha
  simp only [Module.globalResidue, PreparationOnce.residueImports, ht, hd, he, hs] at ha'
  cases h : instantiateOnce? s m (Preparation.imports as) with
  | some p => exact ⟨p, rfl⟩
  | none =>
    exfalso
    unfold instantiateOnce? at h
    simp only [hg] at h
    unfold instantiateDirect? prepareDirect? prepare? at h
    simp [Module.globalResidue, ht, hd, he, hs, evalGlobals?, evalExprs?, evalExprss?] at h
    simp [ha'] at h
    simp [initSegments?, initElemList?, initDataList?, initElem?, initData?] at h

/-- The module instance that the residue allocation uses to allocate exports, in the
linker's profile with no global values (`allocModule?` of the residue). -/
def residueExportsInst (s : Store H) (m : Module) (xas : List ExternAddr) : ModuleInst :=
  { tags := ExternAddr.tags xas, globals := ExternAddr.globals xas,
    mems := ExternAddr.mems xas, tables := ExternAddr.tables xas,
    funcs := ExternAddr.funcs xas ++ (List.range m.funcs.length).map (s.funcs.length + ·) }

/-- Residue allocation in the linker's profile succeeds when the function types and the
exports resolve. -/
theorem residue_alloc_exists {s : Store H} {m : Module} {xas : List ExternAddr}
    (hm : inProfile m = true) {ft : List DefType}
    (hf : m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) = some ft)
    {xi : List ExportInst}
    (he : m.exports.mapM (allocExport? (residueExportsInst s m xas)) = some xi) :
    ∃ p, allocModule? s m.globalResidue xas [] [] [] = some p := by
  obtain ⟨hmem, htab, htag, hdat, helem, _⟩ := profile_sections' hm
  have he' := he
  simp only [residueExportsInst] at he'
  cases h : allocModule? s m.globalResidue xas [] [] [] with
  | some p => exact ⟨p, rfl⟩
  | none =>
    exfalso
    unfold allocModule? at h
    simp [Module.globalResidue, hmem, htab, htag, hdat, helem, allocMany] at h
    simp [hf, he'] at h

theorem allocExport?_of_func {mi : ModuleInst} {e : Export} {x : FuncIdx} {a : Nat}
    (hx : e.index = .func x) (ha : mi.funcs[x.toNat]? = some a) :
    allocExport? mi e = some ⟨e.name, .func a⟩ := by
  unfold allocExport?
  simp only [hx, ha, Option.map_some]

theorem allocExport?_of_global {mi : ModuleInst} {e : Export} {x : GlobalIdx} {a : Nat}
    (hx : e.index = .global x) (ha : mi.globals[x.toNat]? = some a) :
    allocExport? mi e = some ⟨e.name, .global a⟩ := by
  unfold allocExport?
  simp only [hx, ha, Option.map_some]

theorem allocExport?_func_lookup {mi : ModuleInst} {e : Export} {x : FuncIdx} {b : ExportInst}
    (hx : e.index = .func x) (hb : allocExport? mi e = some b) :
    ∃ a, mi.funcs[x.toNat]? = some a := by
  unfold allocExport? at hb
  simp only [hx, Option.map_map, Option.map_eq_some_iff] at hb
  obtain ⟨a, ha, -⟩ := hb
  exact ⟨a, ha⟩

theorem allocExport?_global_lookup {mi : ModuleInst} {e : Export} {x : GlobalIdx}
    {b : ExportInst} (hx : e.index = .global x) (hb : allocExport? mi e = some b) :
    ∃ a, mi.globals[x.toNat]? = some a := by
  unfold allocExport? at hb
  simp only [hx, Option.map_map, Option.map_eq_some_iff] at hb
  obtain ⟨a, ha, -⟩ := hb
  exact ⟨a, ha⟩

/-! ## The consumer side of a link -/

section Consumer

variable {namespaceName : String} {provider consumer result : Module}
  (w : Recipe.Assembly namespaceName provider consumer result)

theorem result_lengths' (w : Recipe.Assembly namespaceName provider consumer result) :
    result.funcs.length = provider.funcs.length + consumer.funcs.length ∧
      result.globals.length = provider.globals.length + consumer.globals.length := by
  rw [w.output]
  simp only [List.length_append, w.providerFuncs_length, w.funcs_length,
    w.providerGlobals_length, w.globals_length]
  exact ⟨trivial, trivial⟩

/-- The function addresses that the consumer's imports resolve to. -/
def importAddrs (base : Nat) : List Nat := w.imports.map (fun f => base + f.toNat)

theorem function?_cases {x y : FuncIdx}
    (hr : function? (Recipe.relocation provider w.imports) x = some y) :
    (x.toNat < w.imports.length ∧ w.imports[x.toNat]? = some y) ∨
      (w.imports.length ≤ x.toNat ∧
        y.toNat = provider.funcs.length + (x.toNat - w.imports.length)) := by
  change (if x.toNat < w.imports.length then w.imports[x.toNat]?
    else Idx.ofNat? (provider.funcs.length + (x.toNat - w.imports.length))) = some y at hr
  by_cases hi : x.toNat < w.imports.length
  · rw [ite_eq_left hi] at hr
    exact .inl ⟨hi, hr⟩
  · rw [ite_eq_right hi] at hr
    exact .inr ⟨Nat.le_of_not_gt hi, ((Idx.ofNat?_eq_some_iff _ _).mp hr).symm⟩

/-- The function view of the initial consumer instance (imports resolved by `w`, own
functions from `n`) in the initial linked instance (functions from `base`). -/
private theorem initial_funcs_view {base n : Nat}
    (hcount : n = base + provider.funcs.length) {x y : FuncIdx} {a : Nat}
    (hr : function? (Recipe.relocation provider w.imports) x = some y)
    (hx : (importAddrs w base ++ Preparation.addresses n consumer.funcs.length)[x.toNat]? =
      some a) :
    (Preparation.addresses base (provider.funcs.length + consumer.funcs.length))[y.toNat]? =
      some a := by
  have hlenI : (importAddrs w base).length = w.imports.length := by simp [importAddrs]
  rcases function?_cases w hr with ⟨hi, hy⟩ | ⟨hi, hy⟩
  · have hx' : (importAddrs w base)[x.toNat]? = some a :=
      (List.getElem?_append_left (hlenI ▸ hi : x.toNat < (importAddrs w base).length)).symm.trans hx
    have ha : base + y.toNat = a := by
      simpa only [importAddrs, List.getElem?_map, hy, Option.map_some, Option.some.injEq] using hx'
    have hb : y.toNat < provider.funcs.length :=
      Resolution.assembly_imports_bounded w y (List.mem_of_getElem? hy)
    rw [← ha]
    exact Preparation.addresses_lookup (by omega)
  · show (Preparation.addresses base (provider.funcs.length + consumer.funcs.length))[y.toNat]? =
      some a
    have hx' : (Preparation.addresses n consumer.funcs.length)[x.toNat - w.imports.length]? =
        some a := by
      simpa only [hlenI] using (List.getElem?_append_right
        (hlenI ▸ hi : (importAddrs w base).length ≤ x.toNat)).symm.trans hx
    have hb : x.toNat - w.imports.length < consumer.funcs.length := by
      simpa only [Preparation.addresses_length] using (List.getElem?_eq_some_iff.mp hx').1
    have ha : n + (x.toNat - w.imports.length) = a :=
      Option.some.inj ((Preparation.addresses_lookup hb).symm.trans hx')
    rw [hy, Preparation.addresses_lookup (by omega), ← ha]
    congr 1
    omega

/-- The reflection of `initial_funcs_view`: a function of the linked instance that the
relocation reaches is a function of the consumer instance. -/
private theorem initial_funcs_reflect {base n : Nat} {x y : FuncIdx} {a : Nat}
    (hr : function? (Recipe.relocation provider w.imports) x = some y)
    (ha : (Preparation.addresses base (provider.funcs.length + consumer.funcs.length))[y.toNat]? =
      some a) :
    ∃ a', (importAddrs w base ++ Preparation.addresses n consumer.funcs.length)[x.toNat]? =
      some a' := by
  have hlenI : (importAddrs w base).length = w.imports.length := by simp [importAddrs]
  have hb : y.toNat < provider.funcs.length + consumer.funcs.length := by
    simpa only [Preparation.addresses_length] using (List.getElem?_eq_some_iff.mp ha).1
  have hx : x.toNat < (importAddrs w base ++ Preparation.addresses n consumer.funcs.length).length := by
    simp only [List.length_append, hlenI, Preparation.addresses_length]
    rcases function?_cases w hr with ⟨hi, -⟩ | ⟨hi, hy⟩ <;> omega
  exact ⟨_, List.getElem?_eq_getElem hx⟩

/-- Views of the initial consumer instance (in the provider's store) in the initial linked
instance, and their reflection. -/
theorem initial_views (hl : link? namespaceName provider consumer = some result)
    {s sp : Store H} (hcount : sp.funcs.length = s.funcs.length + provider.funcs.length) :
    Views.Successful (Recipe.relocation provider w.imports)
        (ModuleInst.initial sp consumer (Preparation.imports (importAddrs w s.funcs.length)))
        (ModuleInst.initial s result (Preparation.imports [])) ∧
      Reflects (Recipe.relocation provider w.imports)
        (ModuleInst.initial sp consumer (Preparation.imports (importAddrs w s.funcs.length)))
        (ModuleInst.initial s result (Preparation.imports [])) := by
  have lens : result.funcs.length = provider.funcs.length + consumer.funcs.length ∧
      result.globals.length = provider.globals.length + consumer.globals.length :=
    result_lengths' w
  have hlf : (ModuleInst.initial s result (Preparation.imports [])).funcs =
      Preparation.addresses s.funcs.length (provider.funcs.length + consumer.funcs.length) := by
    simp only [ModuleInst.initial, Preparation.imports_funcs, List.nil_append, lens.1,
      Preparation.addresses]
  have hcf : (ModuleInst.initial sp consumer
      (Preparation.imports (importAddrs w s.funcs.length))).funcs =
      importAddrs w s.funcs.length ++
        Preparation.addresses sp.funcs.length consumer.funcs.length := by
    simp only [ModuleInst.initial, Preparation.imports_funcs, Preparation.addresses]
  have hcg : (ModuleInst.initial sp consumer
      (Preparation.imports (importAddrs w s.funcs.length))).globals = [] := by
    simp only [ModuleInst.initial, Preparation.imports_globals]
  refine ⟨⟨fun hr hx => ?_, fun hr hx => ?_, fun hr hx => ?_⟩,
    ⟨fun hr ha => ?_, fun hr hx => ?_⟩⟩
  · rw [hlf]
    exact initial_funcs_view w hcount hr (hcf ▸ hx)
  · exact absurd (hcg ▸ hx) (by simp)
  · rw [ModuleInst.initial, Allocation.link?_consumer_type_lookup hl hr]
    exact hx
  · rw [hcf]
    exact initial_funcs_reflect w hr (hlf ▸ ha)
  · exact ⟨_, (Allocation.link?_consumer_type_lookup hl hr).symm.trans hx⟩

/-- One step of `evalGlobals?`: evaluate the first initializer, allocate its global, and
evaluate the rest in the extended frame. -/
private theorem evalGlobals?_cons_inv {s r : Store H} {f f' : Frame} {type : CGlobalType}
    {types : List CGlobalType} {e : Expr} {es : List Expr} {vs : List Val}
    (run : evalGlobals? evalConst? s f (type :: types) (e :: es) = some (r, f', vs)) :
    ∃ source value values, evalConst? s f e = some (source, value) ∧
      evalGlobals? evalConst? (allocGlobal source type value).1
        { f with module := { f.module with globals := f.module.globals ++
          [(allocGlobal source type value).2] } } types es = some (r, f', values) ∧
      vs = value :: values := by
  simp only [evalGlobals?] at run
  split at run
  · cases run
  · rename_i source value he
    split at run
    · cases run
    · rename_i result final values hg
      cases run
      exact ⟨source, value, values, he, hg, rfl⟩

theorem globals_split {s : Store H} {f : Frame} :
    ∀ {t₁ t₂ : List CGlobalType} {e₁ e₂ : List Expr} {r : Store H × Frame × List Val},
      t₁.length = e₁.length →
      evalGlobals? evalConst? s f (t₁ ++ t₂) (e₁ ++ e₂) = some r →
      ∃ s' f' v₁ v₂, evalGlobals? evalConst? s f t₁ e₁ = some (s', f', v₁) ∧
        evalGlobals? evalConst? s' f' t₂ e₂ = some (r.1, r.2.1, v₂) := by
  intro t₁
  induction t₁ generalizing s f with
  | nil =>
    intro t₂ e₁ e₂ r hl h
    cases e₁ with
    | nil => exact ⟨s, f, [], r.2.2, rfl, by simpa using h⟩
    | cons => simp at hl
  | cons t t₁ ih =>
    intro t₂ e₁ e₂ r hl h
    cases e₁ with
    | nil => simp at hl
    | cons e e₁ =>
      have hl' : t₁.length = e₁.length := by
        simpa only [List.length_cons, Nat.add_right_cancel_iff] using hl
      obtain ⟨s₁, v, vs, hv, hg, -⟩ := evalGlobals?_cons_inv (r := r.1) (f' := r.2.1) h
      obtain ⟨s', f', v₁, v₂, h₁, h₂⟩ := ih hl' hg
      exact ⟨s', f', v :: v₁, v₂, by simp only [evalGlobals?, hv, h₁], h₂⟩

/-- **The consumer's initializers succeed in the provider's store.** -/
theorem consumer_globals_exist (hl : link? namespaceName provider consumer = some result)
    {s sp sl : Store H} {fp fl : Frame} {startP startL : Option FuncIdx}
    (hp : instantiateOnce? s provider (Preparation.imports []) = some (sp, fp, startP))
    (hm : instantiateOnce? s result (Preparation.imports []) = some (sl, fl, startL)) :
    ∃ s₁ f₁ vs, evalGlobals? evalConst? sp
      ⟨[], ModuleInst.initial sp consumer (Preparation.imports (importAddrs w s.funcs.length))⟩
      (Module.closedGlobalTypes consumer) (consumer.globals.map Global.init) =
        some (s₁, f₁, vs) := by
  have hprofile : inProfile result = true := by rw [w.output]; rfl
  obtain ⟨sP, fP, vsP, hgp, hap, _, _⟩ := PreparationOnce.once_allocation w.providerProfile hp
  obtain ⟨sL, fL, vsL, hgl, hal, _, _⟩ := PreparationOnce.once_allocation hprofile hm
  -- the provider's initializers, transported to the linked instance
  have tablesP := initial_tables w.providerProfile hp
  have tablesL := initial_tables hprofile hm
  have viewP : Views.Successful Recipe.identity
      (ModuleInst.initial s provider (Preparation.imports []))
      (ModuleInst.initial s result (Preparation.imports [])) :=
    empty_globals_views (Views.provider w hl hp hm) tablesP.1 tablesL.1 tablesP.2 tablesL.2
      (Preparation.imports_globals [])
  have rewriteP : List.Forall₂ (fun e e' => instructions? Recipe.identity e = some e')
      (provider.globals.map Global.init) (provider.globals.map Global.init) := by
    simpa only [Identity.provider_globals w] using initializer_rewrite w.providerGlobalsRewrite
  obtain ⟨targetP, frameP, htp, dataP, _, _⟩ :=
    globals_transport (right := ⟨[], ModuleInst.initial s result (Preparation.imports [])⟩)
      (Initializers.Data.refl s) viewP
      (by simp only [ModuleInst.initial, Preparation.imports_globals, Recipe.identity,
        List.length_nil, Nat.zero_add]) rewriteP hgp
  -- the linked initializers split into the provider's and the consumer's
  have hinits : result.globals.map Global.init =
      provider.globals.map Global.init ++ w.globals.map Global.init := by
    have hg : result.globals = w.providerGlobals ++ w.globals := congrArg Module.globals w.output
    rw [hg, Identity.provider_globals w, List.map_append]
  have hgl' : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s result (Preparation.imports [])⟩
      (Module.closedGlobalTypes provider ++ Module.closedGlobalTypes consumer)
      (provider.globals.map Global.init ++ w.globals.map Global.init) = some (sL, fL, vsL) := by
    rw [← link_closed_global_types w hl, ← hinits]
    exact hgl
  obtain ⟨s', f', v₁, v₂, h₁, h₂⟩ := globals_split
    (by simp [Module.closedGlobalTypes]) hgl'
  obtain ⟨rfl, rfl, rfl⟩ : targetP = s' ∧ frameP = f' ∧ vsP = v₁ := by
    simpa only [Option.some.injEq, Prod.mk.injEq] using htp.symm.trans h₁
  -- the consumer's initializers, reflected back to the provider's store
  have hcount : sp.funcs.length = s.funcs.length + provider.funcs.length :=
    (Views.once_counts w.providerProfile hp).1
  obtain ⟨views₀, refl₀⟩ := initial_views w hl (s := s) (sp := sp) hcount
  have funcsP : frameP.module.funcs =
      (ModuleInst.initial s result (Preparation.imports [])).funcs := by
    rw [(evalGlobals?_shape htp).2.2]
  have typesP : frameP.module.types =
      (ModuleInst.initial s result (Preparation.imports [])).types := by
    rw [(evalGlobals?_shape htp).2.2]
  have hcg : (ModuleInst.initial sp consumer
      (Preparation.imports (importAddrs w s.funcs.length))).globals = [] := by
    simp only [ModuleInst.initial, Preparation.imports_globals]
  have viewC : Views.Successful (Recipe.relocation provider w.imports)
      (ModuleInst.initial sp consumer (Preparation.imports (importAddrs w s.funcs.length)))
      frameP.module :=
    empty_globals_views views₀ rfl funcsP rfl typesP hcg
  have reflC : Reflects (Recipe.relocation provider w.imports)
      (ModuleInst.initial sp consumer (Preparation.imports (importAddrs w s.funcs.length)))
      frameP.module :=
    ⟨fun hr ha => refl₀.functions hr (funcsP ▸ ha),
      fun hr hd => refl₀.types hr (typesP ▸ hd)⟩
  have lengthC : frameP.module.globals.length =
      (Recipe.relocation provider w.imports).globals +
        (ModuleInst.initial sp consumer
          (Preparation.imports (importAddrs w s.funcs.length))).globals.length := by
    rw [(evalGlobals?_shape htp).2.2]
    simp only [ModuleInst.initial, Preparation.imports_globals, List.nil_append,
      List.length_map, List.length_range, Module.closedGlobalTypes, Recipe.relocation,
      List.length_nil, Nat.add_zero]
  have dataInputC : Initializers.Data sp targetP :=
    (residue_data w.providerProfile hap).symm.trans dataP
  obtain ⟨res, fin, hres⟩ := globals_reflect (left := ⟨[], ModuleInst.initial sp consumer
      (Preparation.imports (importAddrs w s.funcs.length))⟩) dataInputC viewC reflC lengthC
    (initializer_rewrite w.globalsRewrite) h₂
  exact ⟨res, fin, _, hres⟩

private theorem forall₂_lookup' {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) {i : Nat} {x : α}
    (hx : xs[i]? = some x) : ∃ y, ys[i]? = some y ∧ R x y := by
  induction h generalizing i with
  | nil => simp at hx
  | @cons a b xs ys hab _ ih =>
    cases i with
    | zero => simp at hx; subst x; exact ⟨b, rfl, hab⟩
    | succ i => exact ih (by simpa using hx)

/-- Relocating a function relocates its type index. -/
private theorem func?_type {r : Relocation} {f f' : Func} (h : func? r f = some f') :
    shiftIdx? r.types f.type = some f'.type := by
  simp only [func?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨t, ht, l, -, b', -, rfl⟩ := h
  exact ht

/-- **The consumer's residue allocates**, against any store and any import addresses with
the right numbers of functions and globals: every lookup it makes is the source of a lookup
that succeeded in the linked allocation. -/
theorem consumer_alloc_exists (hl : link? namespaceName provider consumer = some result)
    {s sl : Store H} {fl : Frame} {startL : Option FuncIdx}
    (hm : instantiateOnce? s result (Preparation.imports []) = some (sl, fl, startL))
    (s₁ : Store H) (xas : List ExternAddr)
    (hxf : (ExternAddr.funcs xas).length = w.imports.length)
    (hxg : (ExternAddr.globals xas).length = consumer.globals.length) :
    ∃ p, allocModule? s₁ consumer.globalResidue xas [] [] [] = some p := by
  have hprofile : inProfile result = true := by rw [w.output]; rfl
  obtain ⟨sL, fL, vsL, hgl, hal, _, _⟩ := PreparationOnce.once_allocation hprofile hm
  obtain ⟨tagTypes, funcTypes, xi, -, hft, hxi, -, -⟩ := allocModule?_inv hal
  have hft' : result.funcs.mapM (fun fn => (allocTypes result.types)[fn.type.toNat]?) =
      some funcTypes := by
    simpa only [Module.globalResidue] using hft
  simp only [Module.globalResidue] at hxi
  have lens : result.funcs.length = provider.funcs.length + consumer.funcs.length ∧
      result.globals.length = provider.globals.length + consumer.globals.length :=
    result_lengths' w
  -- the function types resolve
  obtain ⟨ft, hf⟩ : ∃ ft, consumer.funcs.mapM
      (fun fn => (allocTypes consumer.types)[fn.type.toNat]?) = some ft := by
    apply mapM_some_of_forall
    intro fn hfn
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hfn
    obtain ⟨f', hf', hr⟩ := w.consumer_func_lookup hi
    obtain ⟨b, hb⟩ := mapM_some_mem hft' f' (List.mem_of_getElem? hf')
    have hty : shiftIdx? (Recipe.relocation provider w.imports).types fn.type = some f'.type :=
      func?_type hr
    exact ⟨b, by rw [← Allocation.link?_consumer_type_lookup hl hty]; exact hb⟩
  -- the exports resolve
  obtain ⟨xi', he⟩ : ∃ xi', consumer.exports.mapM
      (allocExport? (residueExportsInst s₁ consumer xas)) = some xi' := by
    apply mapM_some_of_forall
    intro e hem
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hem
    obtain ⟨e', he', hr⟩ := forall₂_lookup' (forall₂_of_mapM w.exportsRewrite) hi
    have hmem : e' ∈ result.exports := by
      rw [w.output]
      exact List.mem_append_right _ (List.mem_of_getElem? he')
    obtain ⟨b, hb⟩ := mapM_some_mem hxi e' hmem
    cases hx : e.index with
    | func x =>
      show ∃ b, allocExport? (residueExportsInst s₁ consumer xas) e = some b
      obtain ⟨y, hy, hey⟩ : ∃ y, function? (Recipe.relocation provider w.imports) x = some y ∧
          e'.index = .func y := by
        simp only [export?, hx, Option.bind_eq_bind, Option.map_eq_map, Option.map_eq_some_iff,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hr
        obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hr
        exact ⟨y, hy, rfl⟩
      obtain ⟨a, ha⟩ := allocExport?_func_lookup hey hb
      have hbound : y.toNat < provider.funcs.length + consumer.funcs.length := by
        simpa [PreparationOnce.residueImports, ExternAddr.funcs_append,
          ExternAddr.funcs_globalAddrs, lens.1] using (List.getElem?_eq_some_iff.mp ha).1
      have hlt : x.toNat < (residueExportsInst s₁ consumer xas).funcs.length := by
        simp only [residueExportsInst, List.length_append, List.length_map, List.length_range]
        rcases function?_cases w hy with ⟨hi, -⟩ | ⟨hi, hy'⟩ <;> omega
      exact ⟨_, allocExport?_of_func hx (List.getElem?_eq_getElem hlt)⟩
    | global g =>
      show ∃ b, allocExport? (residueExportsInst s₁ consumer xas) e = some b
      obtain ⟨y, hy, hey⟩ : ∃ y, shiftIdx? (Recipe.relocation provider w.imports).globals g =
          some y ∧ e'.index = .global y := by
        simp only [export?, hx, Option.bind_eq_bind, Option.map_eq_map, Option.map_eq_some_iff,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hr
        obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hr
        exact ⟨y, hy, rfl⟩
      obtain ⟨a, ha⟩ := allocExport?_global_lookup hey hb
      have hbound : y.toNat < provider.globals.length + consumer.globals.length := by
        simpa [PreparationOnce.residueImports, ExternAddr.globals_append,
          ExternAddr.globals_globalAddrs, lens.2] using (List.getElem?_eq_some_iff.mp ha).1
      have hy' : y.toNat = provider.globals.length + g.toNat := LinkExecution.shiftIdx?_toNat hy
      have hlt : g.toNat < (residueExportsInst s₁ consumer xas).globals.length := by
        simp only [residueExportsInst]
        omega
      exact ⟨_, allocExport?_of_global hx (List.getElem?_eq_getElem hlt)⟩
    | tag x => exact absurd hr (by simp [export?, hx])
    | memory x => exact absurd hr (by simp [export?, hx])
    | table x => exact absurd hr (by simp [export?, hx])
  exact residue_alloc_exists w.consumerProfile hf he

/-- **#1936's shared instantiation exists.** -/
theorem shared_exists (hl : link? namespaceName provider consumer = some result)
    {s sp sl : Store H} {fp fl : Frame} {startP startL : Option FuncIdx}
    (hp : instantiateOnce? s provider (Preparation.imports []) = some (sp, fp, startP))
    (hm : instantiateOnce? s result (Preparation.imports []) = some (sl, fl, startL)) :
    ∃ sc fc, instantiateOnce? sp consumer
      (Preparation.imports (importAddrs w s.funcs.length)) = some (sc, fc, none) := by
  obtain ⟨s₁, f₁, vs, hg⟩ := consumer_globals_exist w hl hp hm
  obtain ⟨⟨s', mi⟩, ha⟩ := consumer_alloc_exists w hl hm s₁
    (PreparationOnce.residueImports sp consumer (importAddrs w s.funcs.length))
    (by simp [PreparationOnce.residueImports, ExternAddr.funcs_append,
      ExternAddr.funcs_globalAddrs, importAddrs])
    (by simp [PreparationOnce.residueImports, ExternAddr.globals_append,
      ExternAddr.globals_globalAddrs])
  obtain ⟨⟨sc, fc, st⟩, h⟩ := once_of_allocation w.consumerProfile hg ha
  obtain ⟨_, _, _, _, _, _, hst⟩ := PreparationOnce.once_allocation w.consumerProfile h
  subst hst
  exact ⟨sc, fc, h⟩

/-- **The consumer also instantiates in the provider's store with its function list replaced**
(same length), e.g. with host stubs. -/
theorem withFuncs_exists (hl : link? namespaceName provider consumer = some result)
    {s sp sl : Store H} {fp fl : Frame} {startP startL : Option FuncIdx}
    (hp : instantiateOnce? s provider (Preparation.imports []) = some (sp, fp, startP))
    (hm : instantiateOnce? s result (Preparation.imports []) = some (sl, fl, startL))
    (g : List (FuncInst H)) (hgl : g.length = sp.funcs.length) :
    ∃ t fc, instantiateOnce? (withFuncs g sp) consumer
      (Preparation.imports (importAddrs w s.funcs.length)) = some (t, fc, none) := by
  obtain ⟨s₁, f₁, vs, hge⟩ := consumer_globals_exist w hl hp hm
  have hge' := evalGlobals?_withFuncs g hge
  have hinit : ModuleInst.initial (withFuncs g sp) consumer
      (Preparation.imports (importAddrs w s.funcs.length)) =
      ModuleInst.initial sp consumer (Preparation.imports (importAddrs w s.funcs.length)) := by
    simp only [ModuleInst.initial, withFuncs, hgl]
  rw [← hinit] at hge'
  obtain ⟨⟨s', mi⟩, ha⟩ := consumer_alloc_exists w hl hm (withFuncs g s₁)
    (PreparationOnce.residueImports (withFuncs g sp) consumer (importAddrs w s.funcs.length))
    (by simp [PreparationOnce.residueImports, ExternAddr.funcs_append,
      ExternAddr.funcs_globalAddrs, importAddrs])
    (by simp [PreparationOnce.residueImports, ExternAddr.globals_append,
      ExternAddr.globals_globalAddrs])
  obtain ⟨⟨t, fc, st⟩, h⟩ := once_of_allocation w.consumerProfile hge' ha
  obtain ⟨_, _, _, _, _, _, hst⟩ := PreparationOnce.once_allocation w.consumerProfile h
  subst hst
  exact ⟨t, fc, h⟩

end Consumer

end Silmaril.Proofs.Wasm.Game.Linking
