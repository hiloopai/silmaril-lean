module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.BwdSim
public import Silmaril.Wasm.Binaryen.CodeSimModule
public import Silmaril.Wasm.Execution.Core.Soundness

/-!
# The tail-call rewrite on modules

* `allocModule?_rel`, `instantiate_rel`: instantiating modules equal off their function lists,
  with pointwise related functions, gives configurations with equal frame and code and related
  stores (copies of silmaril-lean's `allocModule?_bodiesRel` and `instantiate_bodiesRel` for a
  function relation that is not the closure `FuncRel BI`);
* `instantiate_tail`, `instantiate_untail`: the instances for a module and its tail rewrite, in
  both directions, with `StoreRel FRel`;
* `session_fwd`, `session_bwd`: sessions of export invocations transport between `FRel`-related
  valid stores, by the forward and backward simulations;
* **`exportRefines_tail`**, **`exportRefines_untail`**, **`exportEquiv_tail`**: a valid module
  and its tail rewrite are exactly export-equivalent, at every profile and every code-parametric
  host meeting `HostOk`.

`allocModule?_rel`, `forall₂_allocFuncs'` and `instantiate_rel` follow silmaril-lean's proofs
(`Binaryen/CodeSimModule.lean`), generalised in the function relation; the rest is new.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc tailModule)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## Instantiation -/

theorem types_of_forall₂ {G : FuncInst H → FuncInst H → Prop}
    (hGt : ∀ x y, G x y → x.type = y.type) :
    ∀ {X Y : List (FuncInst H)}, List.Forall₂ G X Y → X.map FuncInst.type = Y.map FuncInst.type
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    rw [List.map_cons, List.map_cons, hGt _ _ h, types_of_forall₂ hGt hs]

theorem storeRel_of_funcs' {G : FuncInst H → FuncInst H → Prop}
    (hGt : ∀ x y, G x y → x.type = y.type) {s t : Store H}
    (hother : ({ s with funcs := [] } : Store H) = ({ t with funcs := [] } : Store H))
    (hf : List.Forall₂ G s.funcs t.funcs) : StoreRel G s t :=
  ⟨types_of_forall₂ hGt hf, hother, hf⟩

/-- The function instances allocated for related functions are related. -/
theorem forall₂_allocFuncs' {G : FuncInst H → FuncInst H → Prop} {Q : Func → Func → Prop}
    (hQG : ∀ (t : DefType) (mi : ModuleInst) (f g : Func), Q f g →
      G ⟨t, mi, .wasm f⟩ ⟨t, mi, .wasm g⟩) (mi : ModuleInst) :
    ∀ {fs gs : List Func}, List.Forall₂ Q fs gs → ∀ ts : List DefType,
      List.Forall₂ G
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
    exact .cons (hQG _ _ _ _ h) (forall₂_allocFuncs' hQG mi hs ts)

/-- `allocModule?` for modules with related functions: the same module instance, and related
stores. -/
theorem allocModule?_rel {G : FuncInst H → FuncInst H → Prop} {Q : Func → Func → Prop}
    (hGr : ∀ x, G x x) (hGt : ∀ x y, G x y → x.type = y.type)
    (hQt : ∀ f g, Q f g → f.type = g.type)
    (hQG : ∀ (t : DefType) (mi : ModuleInst) (f g : Func), Q f g →
      G ⟨t, mi, .wasm f⟩ ⟨t, mi, .wasm g⟩)
    {m : Module} {gs : List Func} (hfs : List.Forall₂ Q m.funcs gs)
    {s s₄ : Store H} {xas : List ExternAddr} {valsG : List Val} {refsT : List Ref}
    {refsE : List (List Ref)} {mi : ModuleInst}
    (h : allocModule? s m xas valsG refsT refsE = some (s₄, mi)) :
    ∃ s₄', allocModule? s { m with funcs := gs } xas valsG refsT refsE = some (s₄', mi) ∧
      StoreRel G s₄ s₄' := by
  have hT : ∀ dts : List DefType, gs.mapM (fun fn => dts[fn.type.toNat]?) =
      m.funcs.mapM (fun fn => dts[fn.type.toNat]?) := fun dts =>
    (mapM_forall₂ (fun f g hfg => by simp only [hQt f g hfg]) hfs).symm
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
  refine ⟨_, rfl, storeRel_of_funcs' hGt rfl ?_⟩
  exact forall₂_append' (List.forall₂_same.mpr fun x _ => hGr x)
    (forall₂_allocFuncs' hQG _ hfs _)

/-- **Instantiation of modules with related functions.** Equal frame and code; related
stores. -/
theorem instantiate_rel {G : FuncInst H → FuncInst H → Prop} {Q : Func → Func → Prop}
    (hGr : ∀ x, G x x) (hGt : ∀ x y, G x y → x.type = y.type)
    (hQt : ∀ f g, Q f g → f.type = g.type)
    (hQG : ∀ (t : DefType) (mi : ModuleInst) (f g : Func), Q f g →
      G ⟨t, mi, .wasm f⟩ ⟨t, mi, .wasm g⟩)
    {BI : List Instr → List Instr → Prop} {m m' : Module} (hrel : ModuleBodiesRel BI m m')
    (hQ : List.Forall₂ Q m.funcs m'.funcs)
    (hm' : ∃ mt, ModuleOk m' mt) {s : Store H} {xas : List ExternAddr} {c : Config H}
    (hI : Instantiate P host s m xas c) :
    ∃ c', Instantiate P host s m' xas c' ∧ c'.frame = c.frame ∧ c'.code = c.code ∧
      StoreRel G c.store c'.store := by
  obtain ⟨⟨xtE, xtI, hmt, hxas⟩, hbd, s₁, s₂, s₃, s₄, f₁, f₂, f₃, vG, rT, rE, mi, hG, hT, hE, hA,
    rfl⟩ := hI
  obtain ⟨mt', hmt'⟩ := hm'
  obtain rfl := hrel.moduleOk_type hmt hmt'
  obtain ⟨gs, rfl⟩ : ∃ gs, m' = { m with funcs := gs } := ⟨_, hrel.eq_withFuncs⟩
  have hfs : List.Forall₂ Q m.funcs gs := hQ
  have hlen : gs.length = m.funcs.length := hfs.length_eq.symm
  obtain ⟨s₄', hA', hst⟩ := allocModule?_rel hGr hGt hQt hQG hfs hA
  have hinit : ModuleInst.initial s { m with funcs := gs } xas = ModuleInst.initial s m xas := by
    simp only [ModuleInst.initial, hlen]
  refine ⟨_, ⟨⟨xtE, xtI, hmt', hxas⟩, hbd, s₁, s₂, s₃, s₄', f₁, f₂, f₃, vG, rT, rE, mi, ?_, hT,
    hE, hA', rfl⟩, rfl, rfl, hst⟩
  rw [hinit]
  exact hG

/-- A module and its tail rewrite have related bodies (`ModuleBodiesRel` for the rewrite). -/
theorem tail_bodiesRel (m : Module) :
    ModuleBodiesRel (fun a b => b = tailL a) m (tailModule m) := by
  refine ⟨rfl, ?_⟩
  show List.Forall₂ _ m.funcs (m.funcs.map tailFunc)
  induction m.funcs with
  | nil => exact .nil
  | cons f fs ih => exact .cons ⟨rfl, rfl, .base rfl⟩ ih

theorem tail_forall₂ (m : Module) :
    List.Forall₂ (fun f g => g = tailFunc f) m.funcs (tailModule m).funcs := by
  show List.Forall₂ _ m.funcs (m.funcs.map tailFunc)
  induction m.funcs with
  | nil => exact .nil
  | cons f fs ih => exact .cons rfl ih

/-- **Instantiating the tail rewrite** alongside the module. -/
theorem instantiate_tail {m : Module} (hm' : ∃ mt, ModuleOk (tailModule m) mt) {s : Store H}
    {xas : List ExternAddr} {c : Config H} (hI : Instantiate P host s m xas c) :
    ∃ c', Instantiate P host s (tailModule m) xas c' ∧ c'.frame = c.frame ∧ c'.code = c.code ∧
      StoreRel FRel c.store c'.store :=
  instantiate_rel FRel.refl (fun _ _ h => h.1) (fun f g h => by subst h; rfl)
    (fun _ _ f g h => by subst h; exact ⟨rfl, rfl, Or.inr rfl⟩) (tail_bodiesRel m)
    (tail_forall₂ m) hm' hI

/-- **Instantiating the module** alongside its tail rewrite. -/
theorem instantiate_untail {m : Module} (hm : ∃ mt, ModuleOk m mt) {s : Store H}
    {xas : List ExternAddr} {c' : Config H} (hI : Instantiate P host s (tailModule m) xas c') :
    ∃ c, Instantiate P host s m xas c ∧ c.frame = c'.frame ∧ c.code = c'.code ∧
      StoreRel FRel c.store c'.store := by
  obtain ⟨c, hc, hfr, hco, hst⟩ := instantiate_rel (G := fun a b => FRel b a)
    (Q := fun g f => g = tailFunc f) (fun x => FRel.refl x) (fun _ _ h => h.1.symm)
    (fun f g h => by subst h; rfl) (fun _ _ f g h => by subst h; exact ⟨rfl, rfl, Or.inr rfl⟩)
    (tail_bodiesRel m).flip (tail_forall₂ m).flip hm hI
  exact ⟨c, hc, hfr, hco, hst.symm⟩

/-! ## Sessions -/

theorem configOk_steps (hok : HostOk host) {c d : Config H} (h : Steps P host c d)
    {ts : List CValType} (hc : ConfigOk c ts) : ConfigOk d ts := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => exact (Step.preservation hok ih hs).1

theorem storeOk_of_configOk {c : Config H} {ts : List CValType} (h : ConfigOk c ts) :
    StoreOk c.store := by
  obtain ⟨_, ⟨hs, _⟩, _⟩ := h
  exact hs

theorem invoke_code {s t : Store H} (hst : StoreRel FRel s t) (a : Nat) (vs : List Val) :
    (invoke s a vs).code = (invoke t a vs).code := by
  simp only [invoke, ← List.getElem?_map, hst.types]

/-- **Forward session transport.** -/
theorem session_fwd (hhost : HostRespects FRel host) (hok : HostOk host) {mi : ModuleInst}
    {s : Store H} {script : List Call} {bs : List (Behaviour Val)}
    (hs : Session P host mi s script bs) :
    ∀ {t : Store H}, StoreOk s → StoreOk t → StoreRel FRel s t → Session P host mi t script bs := by
  induction hs with
  | nil => intro _ _ _ _; exact .nil
  | stop h =>
    intro t _ _ hst
    exact .stop fun a ha hi => h a ha (invokeOk_of_storeRel hst.symm hi)
  | done ha hi run hr _ ih =>
    intro t hs ht hst
    have hi' := invokeOk_of_storeRel hst hi
    obtain ⟨_, _, _, -, -, hc⟩ := invoke_ok hs hi
    obtain ⟨_, _, _, -, -, hd⟩ := invoke_ok ht hi'
    have hcfg : FRelCfg (invoke _ _ _) (invoke t _ _) :=
      ⟨hst, rfl, by rw [invoke_code hst]; exact R.refl true false _, ⟨_, hc⟩, ⟨_, hd⟩⟩
    obtain ⟨d, hd', hdc, hst'⟩ := fwd_run hhost hok hcfg run hr
    exact .done ha hi' hd' hdc (ih (storeOk_of_configOk (configOk_steps hok run hc))
      (storeOk_of_configOk (configOk_steps hok hd' hd)) hst')
  | diverge ha hi hdv =>
    intro t hs ht hst
    have hi' := invokeOk_of_storeRel hst hi
    obtain ⟨_, _, _, -, -, hc⟩ := invoke_ok hs hi
    obtain ⟨_, _, _, -, -, hd⟩ := invoke_ok ht hi'
    have hcfg : FRelCfg (invoke _ _ _) (invoke t _ _) :=
      ⟨hst, rfl, by rw [invoke_code hst]; exact R.refl true false _, ⟨_, hc⟩, ⟨_, hd⟩⟩
    exact .diverge ha hi' (fwd_diverges hhost hok hcfg hdv)

/-- **Backward session transport.** -/
theorem session_bwd (hhostB : HostRespects (fun g f => FRel f g) host) (hok : HostOk host)
    {mi : ModuleInst} {t : Store H} {script : List Call} {bs : List (Behaviour Val)}
    (hs : Session P host mi t script bs) :
    ∀ {s : Store H}, StoreOk t → StoreOk s → StoreRel FRel s t → Session P host mi s script bs := by
  induction hs with
  | nil => intro _ _ _ _; exact .nil
  | stop h =>
    intro s _ _ hst
    exact .stop fun a ha hi => h a ha (invokeOk_of_storeRel hst hi)
  | done ha hi run hr _ ih =>
    intro s ht hs hst
    have hi' := invokeOk_of_storeRel hst.symm hi
    obtain ⟨_, _, _, -, -, hc⟩ := invoke_ok ht hi
    obtain ⟨_, _, _, -, -, hd⟩ := invoke_ok hs hi'
    have hcfg : BRelCfg (invoke _ _ _) (invoke s _ _) :=
      ⟨hst, rfl, by rw [invoke_code hst]; exact R.refl false false _, ⟨_, hc⟩, ⟨_, hd⟩⟩
    obtain ⟨d, hd', hdc, hst'⟩ := bwd_run hhostB hok hcfg run hr
    exact .done ha hi' hd' hdc (ih (storeOk_of_configOk (configOk_steps hok run hc))
      (storeOk_of_configOk (configOk_steps hok hd' hd)) hst')
  | diverge ha hi hdv =>
    intro s ht hs hst
    have hi' := invokeOk_of_storeRel hst.symm hi
    obtain ⟨_, _, _, -, -, hc⟩ := invoke_ok ht hi
    obtain ⟨_, _, _, -, -, hd⟩ := invoke_ok hs hi'
    have hcfg : BRelCfg (invoke _ _ _) (invoke s _ _) :=
      ⟨hst, rfl, by rw [invoke_code hst]; exact R.refl false false _, ⟨_, hc⟩, ⟨_, hd⟩⟩
    exact .diverge ha hi' (bwd_diverges hhostB hok hcfg hdv)

/-! ## Export refinement -/

/-- **The tail rewrite refines the module**: every observation of a valid module is one of its
tail rewrite. -/
theorem exportRefines_tail (hhost : HostRespects FRel host) (hok : HostOk host) {m : Module}
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk (tailModule m) mt) :
    ExportRefines (· = ·) P host m (tailModule m) := by
  refine ⟨fun s xas c' _ hI' => ?_, fun s xas script hs bs hbs => ?_⟩
  · obtain ⟨c, hc, -⟩ := instantiate_untail hm hI'
    exact ⟨c, hc⟩
  · obtain ⟨c, hI, hcase⟩ := hbs
    obtain ⟨c', hI', hfr, hco, hst⟩ := instantiate_tail hm' hI
    have hc := Instantiate.ok hok hs hI
    have hc' := Instantiate.ok hok hs hI'
    have hcfg : FRelCfg c c' :=
      ⟨hst, hfr.symm, by rw [hco]; exact R.refl true false _, ⟨_, hc⟩, ⟨_, hc'⟩⟩
    refine ⟨bs, ⟨c', hI', ?_⟩, SessionRel.refl (fun _ => rfl) bs⟩
    rcases hcase with ⟨c₁, bs', hS, hcode, hsess, rfl⟩ | ⟨c₁, r, hS, hcode, hr, rfl⟩ | ⟨hd, rfl⟩
    · obtain ⟨d, hd, hdc, hst'⟩ := fwd_run hhost hok (r := .values []) hcfg hS
        (by simp [hcode, Result.toAdmin, vals])
      refine Or.inl ⟨d, bs', hd, by simpa [Result.toAdmin, vals] using hdc, ?_, rfl⟩
      rw [hfr]
      exact session_fwd hhost hok hsess (storeOk_of_configOk (configOk_steps hok hS hc))
        (storeOk_of_configOk (configOk_steps hok hd hc')) hst'
    · obtain ⟨d, hd, hdc, -⟩ := fwd_run hhost hok hcfg hS hcode
      exact Or.inr (Or.inl ⟨d, r, hd, hdc, hr, rfl⟩)
    · exact Or.inr (Or.inr ⟨fwd_diverges hhost hok hcfg hd, rfl⟩)

/-- **The module refines its tail rewrite**: every observation of the tail rewrite of a valid
module is one of the module. -/
theorem exportRefines_untail (hhostB : HostRespects (fun g f => FRel f g) host)
    (hok : HostOk host) {m : Module} (hm : ∃ mt, ModuleOk m mt)
    (hm' : ∃ mt, ModuleOk (tailModule m) mt) :
    ExportRefines (· = ·) P host (tailModule m) m := by
  refine ⟨fun s xas c _ hI => ?_, fun s xas script hs bs hbs => ?_⟩
  · obtain ⟨c', hc', -⟩ := instantiate_tail hm' hI
    exact ⟨c', hc'⟩
  · obtain ⟨c', hI', hcase⟩ := hbs
    obtain ⟨c, hI, hfr, hco, hst⟩ := instantiate_untail hm hI'
    have hc := Instantiate.ok hok hs hI
    have hc' := Instantiate.ok hok hs hI'
    have hcfg : BRelCfg c' c :=
      ⟨hst, hfr.symm, by rw [hco]; exact R.refl false false _, ⟨_, hc'⟩, ⟨_, hc⟩⟩
    refine ⟨bs, ⟨c, hI, ?_⟩, SessionRel.refl (fun _ => rfl) bs⟩
    rcases hcase with ⟨c₁, bs', hS, hcode, hsess, rfl⟩ | ⟨c₁, r, hS, hcode, hr, rfl⟩ | ⟨hd, rfl⟩
    · obtain ⟨d, hd, hdc, hst'⟩ := bwd_run hhostB hok (r := .values []) hcfg hS
        (by simp [hcode, Result.toAdmin, vals])
      refine Or.inl ⟨d, bs', hd, by simpa [Result.toAdmin, vals] using hdc, ?_, rfl⟩
      rw [hfr]
      exact session_bwd hhostB hok hsess (storeOk_of_configOk (configOk_steps hok hS hc'))
        (storeOk_of_configOk (configOk_steps hok hd hc)) hst'
    · obtain ⟨d, hd, hdc, -⟩ := bwd_run hhostB hok hcfg hS hcode
      exact Or.inr (Or.inl ⟨d, r, hd, hdc, hr, rfl⟩)
    · exact Or.inr (Or.inr ⟨bwd_diverges hhostB hok hcfg hd, rfl⟩)

/-- **A valid module and its tail rewrite are exactly export-equivalent**, at every profile and
every code-parametric host meeting `HostOk`. -/
theorem exportEquiv_tail (hpar : HostParametric host) (hok : HostOk host) {m : Module}
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk (tailModule m) mt) :
    ExportEquiv (· = ·) P host m (tailModule m) :=
  ⟨exportRefines_tail (hpar.respects FRel.refl) hok hm hm',
    (exportRefines_untail (hpar.respects (fun f => FRel.refl f)) hok hm hm').mono
      fun _ _ h => h.symm⟩

end Silmaril.Raw.Wasm.LimeCompile.TailSim
