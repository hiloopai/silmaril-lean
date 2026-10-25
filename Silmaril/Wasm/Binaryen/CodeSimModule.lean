module

public import Silmaril.Wasm.Binaryen.EquivH
public import Silmaril.Wasm.Execution.Core.Sim.Transport
public import Silmaril.Wasm.Execution.Core.Soundness.InstantiationAlloc
public import Silmaril.Wasm.Binaryen.InlStore

@[expose] public section

/-! # From the code simulation to export refinement of modules

The code-simulation tooling (`Execution/Core/Sim`) relates **configurations** whose
stores hold `InstrsRel BI`-related function bodies. A Binaryen pass changes the
function bodies of a module. This file lifts the tooling to modules (operational simulation development, items 2
and 3):

* `ModuleBodiesRel BI m m'`: Core modules equal except for pointwise
  `InstrsRel BI`-related function bodies (same types and locals).
* `instantiate_bodiesRel`: instantiating related modules from one store gives
  configurations with equal frame and code and `StoreRel (FuncRel BI)`-related stores
  (`allocModule?` allocates the same addresses; the only difference is the code
  stored in the allocated function instances).
* `exportRefines_of_bodiesRel`: with a `BaseSim` for `BI`, every observation
  (instantiation run, then a session of export invocations sharing the store) of `m`
  is one of `m'`; invocations are transported with their final stores by
  `Sim.closure_run_transport`.
* `exportEquiv_dce`: the instance for dead-suffix deletion (`Sim.dceBI`), for every
  code-parametric host.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics

/-- Core modules equal except for pointwise related function bodies of the same
type and locals. -/
structure ModuleBodiesRel (BI : List Instr → List Instr → Prop) (m m' : Module) : Prop where
  other : ({ m with funcs := [] } : Module) = ({ m' with funcs := [] } : Module)
  funcs : List.Forall₂ (fun f g : Func => f.type = g.type ∧ f.locals = g.locals ∧
    Sim.InstrsRel BI f.body g.body) m.funcs m'.funcs

/-- Pointwise-determined images along a `Forall₂`-related pair of lists agree. -/
theorem forall₂_det_of_forall₂ {α β γ : Type _} {S : α → β → Prop} {R₁ : α → γ → Prop}
    {R₂ : β → γ → Prop} (hR : ∀ a b c₁ c₂, S a b → R₁ a c₁ → R₂ b c₂ → c₁ = c₂) :
    ∀ {l : List α} {l' : List β} {l₁ l₂ : List γ}, List.Forall₂ S l l' →
      List.Forall₂ R₁ l l₁ → List.Forall₂ R₂ l' l₂ → l₁ = l₂
  | _, _, _, _, .nil, .nil, .nil => rfl
  | _, _, _, _, .cons hs hss, .cons h₁ hs₁, .cons h₂ hs₂ => by
    rw [hR _ _ _ _ hs h₁ h₂, forall₂_det_of_forall₂ hR hss hs₁ hs₂]

/-- `ExternIdxOk` only reads the entity components of the context. -/
theorem externIdxOk_det_of {C₁ C₂ : Context} (htg : C₁.tags = C₂.tags)
    (hgl : C₁.globals = C₂.globals) (hme : C₁.mems = C₂.mems) (htb : C₁.tables = C₂.tables)
    (hfn : C₁.funcs = C₂.funcs) {x : ExternIdx} {t₁ t₂ : CExternType}
    (h₁ : ExternIdxOk C₁ x t₁) (h₂ : ExternIdxOk C₂ x t₂) : t₁ = t₂ := by
  cases h₁ <;> cases h₂ <;> simp_all

namespace ModuleBodiesRel

variable {BI : List Instr → List Instr → Prop} {m m' : Module}

theorem flip (h : ModuleBodiesRel BI m m') : ModuleBodiesRel (fun a b => BI b a) m' m :=
  ⟨h.other.symm, List.Forall₂.flip (h.funcs.imp fun _ _ ⟨ht, hl, hb⟩ =>
    ⟨ht.symm, hl.symm, hb.flip⟩)⟩

theorem dce_symm (h : ModuleBodiesRel Sim.dceBI m m') : ModuleBodiesRel Sim.dceBI m' m := by
  have h' := h.flip
  rwa [Sim.dceBI_flip] at h'

/-- Related modules have the same module type: validation of the non-body parts
determines it (as in `ModuleOk.unique`). -/
theorem moduleOk_type (h : ModuleBodiesRel BI m m') {mt mt' : CModuleType}
    (hm : ModuleOk m mt) (hm' : ModuleOk m' mt') : mt = mt' := by
  obtain ⟨other, hfs⟩ := h
  cases m
  cases m'
  obtain ⟨ht₁, hi₁, rfl, rfl, hj₁, hg₁, -, htb₁, hf₁, -, he₁, -, hx₁, -⟩ := hm
  obtain ⟨ht₂, hi₂, rfl, rfl, hj₂, hg₂, -, htb₂, hf₂, -, he₂, -, hx₂, -⟩ := hm'
  injection other
  subst_vars
  obtain rfl := TypesOk.det ht₁ ht₂
  obtain rfl := List.Forall₂.det' (fun _ _ _ a b => Option.some.inj (a.1.symm.trans b.1)) hi₁ hi₂
  obtain rfl := forall₂_det_of_forall₂ (fun f g _ _ hfg a b => by
    cases a with | mk hd _ _ _ => cases b with | mk hd' _ _ _ =>
      rw [← hfg.1] at hd'
      exact Option.some.inj (hd.symm.trans hd')) hfs hf₁ hf₂
  obtain rfl := List.Forall₂.det' (fun _ _ _ a b => Option.some.inj (a.1.symm.trans b.1)) hj₁ hj₂
  obtain rfl := GlobalsOk.det rfl hg₁ hg₂
  obtain rfl := List.Forall₂.det' (fun _ _ _ a b => a.1.trans b.1.symm) htb₁ htb₂
  obtain rfl := List.Forall₂.det' (fun _ _ _ a b => a.1.trans b.1.symm) he₁ he₂
  obtain rfl := forall₂_det_of_forall₂ (S := Eq) (R₁ := ExportOk _) (R₂ := ExportOk _)
    (fun _ _ _ _ he a b => by
      subst he
      exact externIdxOk_det_of rfl rfl rfl rfl rfl a b)
    (List.forall₂_same.mpr fun _ _ => rfl) hx₁ hx₂
  rfl

end ModuleBodiesRel

/-- Related modules agree off their function lists. -/
theorem ModuleBodiesRel.eq_withFuncs {BI : List Instr → List Instr → Prop} {m m' : Module}
    (h : ModuleBodiesRel BI m m') : m' = { m with funcs := m'.funcs } := by
  obtain ⟨other, -⟩ := h
  cases m
  cases m'
  injection other
  subst_vars
  rfl

/-- `mapM` along a `Forall₂`-related pair of lists with pointwise equal images. -/
theorem mapM_forall₂ {α β γ : Type} {S : α → β → Prop} {T : α → Option γ} {T' : β → Option γ}
    (hT : ∀ a b, S a b → T a = T' b) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ S l l' → l.mapM T = l'.mapM T'
  | _, _, .nil => rfl
  | _, _, .cons h hs => by rw [List.mapM_cons, List.mapM_cons, hT _ _ h, mapM_forall₂ hT hs]

theorem forall₂_append' {α β : Type _} {R : α → β → Prop} :
    ∀ {a : List α} {b : List β} {c : List α} {d : List β}, List.Forall₂ R a b →
      List.Forall₂ R c d → List.Forall₂ R (a ++ c) (b ++ d)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons x hs, h => .cons x (forall₂_append' hs h)

/-- `FuncRel`-related function lists have the same types. -/
theorem funcRel_types {H : Type} {BI : List Instr → List Instr → Prop} :
    ∀ {X Y : List (FuncInst H)}, List.Forall₂ (Sim.FuncRel BI) X Y →
      X.map FuncInst.type = Y.map FuncInst.type
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    rw [List.map_cons, List.map_cons, (h : Sim.FuncRel BI _ _).1, funcRel_types hs]

/-- The function instances allocated for related bodies are related. -/
theorem forall₂_allocFuncs {H : Type} {BI : List Instr → List Instr → Prop} (mi : ModuleInst) :
    ∀ {fs gs : List Func}, List.Forall₂ (fun f g : Func => f.type = g.type ∧
      f.locals = g.locals ∧ Sim.InstrsRel BI f.body g.body) fs gs → ∀ ts : List DefType,
      List.Forall₂ (Sim.FuncRel (H := H) BI)
        ((ts.zip fs).map fun p => (⟨p.1, mi, .wasm p.2⟩ : FuncInst H))
        ((ts.zip gs).map fun p => (⟨p.1, mi, .wasm p.2⟩ : FuncInst H))
  | _, _, .nil, ts => by
    simp only [List.zip_nil_right, List.map_nil]
    exact .nil
  | _, _, .cons _ _, [] => by
    simp only [List.zip_nil_left, List.map_nil]
    exact .nil
  | _, _, .cons h hs, t :: ts => by
    simp only [List.zip_cons_cons, List.map_cons]
    exact .cons ⟨rfl, rfl, h⟩ (forall₂_allocFuncs mi hs ts)

/-- Stores equal off their functions, with `FuncRel`-related functions, are related. -/
theorem storeRel_of_funcs {H : Type} {BI : List Instr → List Instr → Prop} {s t : Store H}
    (hother : ({ s with funcs := [] } : Store H) = ({ t with funcs := [] } : Store H))
    (hf : List.Forall₂ (Sim.FuncRel BI) s.funcs t.funcs) : Sim.StoreRel (Sim.FuncRel BI) s t :=
  ⟨funcRel_types hf, hother, hf⟩

/-- `allocModule?` for modules with related bodies: the same module instance, and
stores related by `FuncRel`. -/
theorem allocModule?_bodiesRel {H : Type} {BI : List Instr → List Instr → Prop} {m : Module}
    {gs : List Func} (hfs : List.Forall₂ (fun f g : Func => f.type = g.type ∧
      f.locals = g.locals ∧ Sim.InstrsRel BI f.body g.body) m.funcs gs)
    {s s₄ : Store H} {xas : List ExternAddr} {valsG : List Val} {refsT : List Ref}
    {refsE : List (List Ref)} {mi : ModuleInst}
    (h : allocModule? s m xas valsG refsT refsE = some (s₄, mi)) :
    ∃ s₄', allocModule? s { m with funcs := gs } xas valsG refsT refsE = some (s₄', mi) ∧
      Sim.StoreRel (Sim.FuncRel BI) s₄ s₄' := by
  have hT : ∀ dts : List DefType, gs.mapM (fun fn => dts[fn.type.toNat]?) =
      m.funcs.mapM (fun fn => dts[fn.type.toNat]?) := fun dts =>
    (mapM_forall₂ (fun f g hfg => by simp only [hfg.1]) hfs).symm
  have hlen : gs.length = m.funcs.length := hfs.length_eq.symm
  unfold allocModule? at h ⊢
  simp only [Option.bind_eq_bind, hT, hlen] at h ⊢
  obtain ⟨tagTypes, ht, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨funcTypes, hf, h⟩ := Option.bind_eq_some_iff.mp h
  rw [ht, hf]
  simp only [Option.bind_some, allocMany_tag_eq, allocMany_global_eq, allocMany_mem_eq,
    allocMany_table_eq, allocMany_data_eq, allocMany_elem_eq] at h ⊢
  obtain ⟨xi, hx, h⟩ := Option.bind_eq_some_iff.mp h
  rw [hx]
  simp only [Option.bind_some, allocMany_func_eq] at h ⊢
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  refine ⟨_, rfl, storeRel_of_funcs rfl ?_⟩
  exact forall₂_append' (List.forall₂_same.mpr fun x _ => Sim.FuncRel.refl x)
    (forall₂_allocFuncs _ hfs _)

/-- `StoreRel` stores differ only in their function list. -/
theorem storeRel_eq_withFuncs {H : Type} {F : FuncInst H → FuncInst H → Prop} {s t : Store H}
    (h : Sim.StoreRel F s t) : InlS.withFuncs s t.funcs = t := by
  have := h.other
  cases s
  cases t
  injection this
  subst_vars
  rfl

/-- `StoreRel` stores accept the same invocations. -/
theorem invokeOk_of_storeRel {H : Type} {F : FuncInst H → FuncInst H → Prop} {s t : Store H}
    (h : Sim.StoreRel F s t) {a : Nat} {vs : List Val} (hok : InvokeOk s a vs) :
    InvokeOk t a vs := by
  obtain ⟨fi, ps, rs, hf, he, hv⟩ := hok
  obtain ⟨gi, hg, hty⟩ := InlS.SameTypes.get (X := t.funcs) (Y := s.funcs) h.types.symm hf
  refine ⟨gi, ps, rs, hg, by rw [hty]; exact he, ?_⟩
  rw [← storeRel_eq_withFuncs h]
  exact hv.imp fun _ _ hv => InlS.valOk_withFuncs h.types.symm hv

/-- **Session transport.** A session from a store is one from any store with
`FuncRel BI`-related functions, given a `BaseSim` for `BI`. -/
theorem session_transport {H : Type} {P : Profile} {host : HostSemantics H}
    {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}
    {rank : List Admin → Nat} [Sim.LawfulCodeRank rank]
    (hhost : Sim.HostRespects (Sim.FuncRel BI) host)
    (hB : Sim.BaseSim P host (Sim.FuncRel BI) BI B rank) {mi : ModuleInst} {s : Store H}
    {script : List Call} {bs : List (Behaviour Val)} (hs : Session P host mi s script bs) :
    ∀ {t : Store H}, Sim.StoreRel (Sim.FuncRel BI) s t → Session P host mi t script bs := by
  have hcfg : ∀ {s t : Store H} (a : Nat) (vs : List Val), Sim.StoreRel (Sim.FuncRel BI) s t →
      Sim.CfgRel (Sim.FuncRel BI) (Sim.AdminsRel BI B) (invoke s a vs) (invoke t a vs) := by
    intro s t a vs hst
    refine ⟨hst, rfl, ?_⟩
    have hcode : (invoke s a vs).code = (invoke t a vs).code := by
      simp only [invoke, ← List.getElem?_map, hst.types]
    rw [hcode]
    exact Sim.AdminsRel.refl _
  induction hs with
  | nil => intro _ _; exact .nil
  | stop h =>
    intro t hst
    exact .stop fun a ha hok => h a ha (invokeOk_of_storeRel hst.symm hok)
  | done ha hok run hr _ ih =>
    intro t hst
    obtain ⟨d, hd, hdc, hst'⟩ :=
      Sim.closure_run_transport (fun _ _ h => h) hhost hB (hcfg _ _ hst) run hr
    exact .done ha (invokeOk_of_storeRel hst hok) hd hdc (ih hst')
  | diverge ha hok hd =>
    intro t hst
    exact .diverge ha (invokeOk_of_storeRel hst hok)
      (Sim.closure_diverges_transport (fun _ _ h => h) hhost hB (hcfg _ _ hst) hd)

/-- **Instantiation of related modules.** Equal frame and code; the stores differ
only in the bodies of the allocated functions. -/
theorem instantiate_bodiesRel {H : Type} {P : Profile} {host : HostSemantics H}
    {BI : List Instr → List Instr → Prop} {m m' : Module} (hrel : ModuleBodiesRel BI m m')
    (hm' : ∃ mt, ModuleOk m' mt) {s : Store H} {xas : List ExternAddr} {c : Config H}
    (hI : Instantiate P host s m xas c) :
    ∃ c', Instantiate P host s m' xas c' ∧ c'.frame = c.frame ∧ c'.code = c.code ∧
      Sim.StoreRel (Sim.FuncRel BI) c.store c'.store := by
  obtain ⟨⟨xtE, xtI, hmt, hxas⟩, hbd, s₁, s₂, s₃, s₄, f₁, f₂, f₃, vG, rT, rE, mi, hG, hT, hE, hA,
    rfl⟩ := hI
  obtain ⟨mt', hmt'⟩ := hm'
  obtain rfl := hrel.moduleOk_type hmt hmt'
  obtain ⟨gs, rfl⟩ : ∃ gs, m' = { m with funcs := gs } := ⟨_, hrel.eq_withFuncs⟩
  have hfs := hrel.funcs
  have hlen : gs.length = m.funcs.length := hfs.length_eq.symm
  obtain ⟨s₄', hA', hst⟩ := allocModule?_bodiesRel hfs hA
  have hinit : ModuleInst.initial s { m with funcs := gs } xas = ModuleInst.initial s m xas := by
    simp only [ModuleInst.initial, hlen]
  refine ⟨_, ⟨⟨xtE, xtI, hmt', hxas⟩, hbd, s₁, s₂, s₃, s₄', f₁, f₂, f₃, vG, rT, rE, mi, ?_, hT,
    hE, hA', rfl⟩, rfl, rfl, hst⟩
  rw [hinit]
  exact hG

/-- **Export refinement from the code simulation.** If the base relation `BI`
admits a `BaseSim` (`Sim/Closure/Basic.lean`) and the host respects the function
relation, then a module refines every module with related bodies, under `Eq`. -/
theorem exportRefines_of_bodiesRel {H : Type} {P : Profile} {host : HostSemantics H}
    {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}
    {rank : List Admin → Nat} [Sim.LawfulCodeRank rank]
    (hB : Sim.BaseSim P host (Sim.FuncRel BI) BI B rank)
    (hhost : Sim.HostRespects (Sim.FuncRel BI) host)
    {m m' : Module} (hrel : ModuleBodiesRel BI m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportRefines (· = ·) P host m m' := by
  refine ⟨fun s xas c' _ hI' => ?_, fun s xas script _ bs hbs => ?_⟩
  · obtain ⟨c, hc, -⟩ := instantiate_bodiesRel hrel.flip hm hI'
    exact ⟨c, hc⟩
  · obtain ⟨c, hI, hcase⟩ := hbs
    obtain ⟨c', hI', hfr, hco, hst⟩ := instantiate_bodiesRel hrel hm' hI
    have hcfg : Sim.CfgRel (Sim.FuncRel BI) (Sim.AdminsRel BI B) c c' :=
      ⟨hst, hfr.symm, by rw [hco]; exact Sim.AdminsRel.refl _⟩
    refine ⟨bs, ⟨c', hI', ?_⟩, SessionRel.refl (fun _ => rfl) bs⟩
    rcases hcase with ⟨c₁, bs', hS, hcode, hsess, rfl⟩ | ⟨c₁, r, hS, hcode, hr, rfl⟩ | ⟨hd, rfl⟩
    · obtain ⟨d, hd, hdc, hst'⟩ := Sim.closure_run_transport (r := .values [])
        (fun _ _ h => h) hhost hB hcfg hS (by simp [hcode, Result.toAdmin, vals])
      refine Or.inl ⟨d, bs', hd, by simpa [Result.toAdmin, vals] using hdc, ?_, rfl⟩
      rw [hfr]
      exact session_transport hhost hB hsess hst'
    · obtain ⟨d, hd, hdc, -⟩ := Sim.closure_run_transport (fun _ _ h => h) hhost hB hcfg hS hcode
      exact Or.inr (Or.inl ⟨d, r, hd, hdc, hr, rfl⟩)
    · exact Or.inr (Or.inr ⟨Sim.closure_diverges_transport (fun _ _ h => h) hhost hB hcfg hd, rfl⟩)

/-- **DCE on modules**: modules with dead-suffix-related bodies are export
equivalent for every code-parametric host. -/
theorem exportEquiv_dce {H : Type} {P : Profile} {host : HostSemantics H}
    (hhost : Sim.HostParametric host) {m m' : Module} (hrel : ModuleBodiesRel Sim.dceBI m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportEquiv (· = ·) P host m m' :=
  have hhost₀ : Sim.HostRespects (Sim.FuncRel Sim.dceBI) host :=
    hhost.respects (fun f => Sim.FuncRel.refl f)
  have hB : Sim.BaseSim P host (Sim.FuncRel Sim.dceBI) Sim.dceBI Sim.dceB :=
    Sim.dceBaseSim (fun _ _ h => h) hhost₀
  ⟨exportRefines_of_bodiesRel hB hhost₀ hrel hm hm',
    (exportRefines_of_bodiesRel hB hhost₀ hrel.dce_symm hm' hm).mono fun _ _ h => h.symm⟩

end Silmaril.Wasm.Binaryen
