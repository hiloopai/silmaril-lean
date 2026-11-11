module

public import Silmaril.Proofs.Wasm.SSA.CoreCert.Caller
public import Silmaril.Wasm.Binaryen.CodeSimTyped

@[expose] public section

/-!
# Modules with equivalent strict leaf functions are export equivalent (proofs)

`ModRel P m m'`: Core modules equal except for their function list, pointwise of the same
type index, and either equal or equivalent strict leaf functions (`LeafFun`, at the defined
type that allocation assigns). Then, under the closed host and at the profile `P`:

* `instantiate_modRel`: instantiating `m` and `m'` from one store gives configurations with the
  same frame and code and `SRel P`-related stores (the module types are the same, allocation
  assigns the same addresses; the shape of silmaril's `instantiate_bodiesRel`);
* `exportRefines_modRel`, `exportEquiv_modRel`: `ExportRefines`/`ExportEquiv (· = ·)`: every
  observation (instantiation run, then any session of export invocations sharing the store) is
  matched, by `run_transport` and `div_transport` with the typing of the left module's
  configurations (`Instantiate.ok`, closed-host preservation). Imports are allowed; host calls
  are left unchanged (and never return under the closed host).
-/

namespace Silmaril.Proofs.Wasm.SSA.CoreCert

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SSA
open Silmaril.Wasm.SSA.CoreCert
open Silmaril.Wasm.Binaryen (closedHost ExportRefines ExportEquiv SessionRel Session Call)

variable {H : Type} {P : Numerics.Profile}

/-- Related modules have the same module type (as silmaril's `ModuleBodiesRel.moduleOk_type`,
which reads only the types of the functions). -/
theorem ModRel.moduleOk_type {m m' : Module} (h : ModRel P m m') {mt mt' : Validation.CModuleType}
    (hm : Validation.ModuleOk m mt) (hm' : Validation.ModuleOk m' mt') : mt = mt' := by
  obtain ⟨other, hfs⟩ := h
  cases m
  cases m'
  obtain ⟨ht₁, hi₁, rfl, rfl, hj₁, hg₁, -, htb₁, hf₁, -, he₁, -, hx₁, -⟩ := hm
  obtain ⟨ht₂, hi₂, rfl, rfl, hj₂, hg₂, -, htb₂, hf₂, -, he₂, -, hx₂, -⟩ := hm'
  injection other
  subst_vars
  obtain rfl : _ = _ := Validation.TypesOk.det ht₁ ht₂
  obtain rfl : _ = _ := Validation.List.Forall₂.det' (fun _ _ _ a b => Option.some.inj (a.1.symm.trans b.1)) hi₁ hi₂
  obtain rfl : _ = _ := Binaryen.forall₂_det_of_forall₂ (fun f g _ _ hfg a b => by
    cases a with | mk hd _ _ _ => cases b with | mk hd' _ _ _ =>
      rw [← hfg.1] at hd'
      exact Option.some.inj (hd.symm.trans hd')) hfs hf₁ hf₂
  obtain rfl : _ = _ := Validation.List.Forall₂.det' (fun _ _ _ a b => Option.some.inj (a.1.symm.trans b.1)) hj₁ hj₂
  obtain rfl : _ = _ := Validation.GlobalsOk.det rfl hg₁ hg₂
  obtain rfl : _ = _ := Validation.List.Forall₂.det' (fun _ _ _ a b => a.1.trans b.1.symm) htb₁ htb₂
  obtain rfl : _ = _ := Validation.List.Forall₂.det' (fun _ _ _ a b => a.1.trans b.1.symm) he₁ he₂
  obtain rfl : _ = _ := Binaryen.forall₂_det_of_forall₂ (S := Eq) (R₁ := Validation.ExportOk _)
    (R₂ := Validation.ExportOk _)
    (fun _ _ _ _ he a b => by
      subst he
      exact Binaryen.externIdxOk_det_of rfl rfl rfl rfl rfl a b)
    (List.forall₂_same.mpr fun _ _ => rfl) hx₁ hx₂
  rfl

theorem ModRel.eq_withFuncs {m m' : Module} (h : ModRel P m m') :
    m' = { m with funcs := m'.funcs } := by
  obtain ⟨other, -⟩ := h
  cases m
  cases m'
  injection other
  subst_vars
  rfl

/-! ## Allocation -/

theorem mapM_some_forall₂ {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM g = some l' → List.Forall₂ (fun a b => g a = some b) l l'
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact .nil
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact .cons hb (mapM_some_forall₂ hbs)

theorem forall₂_allocFuncs_frel {m : Module} (mi : ModuleInst) :
    ∀ {fs gs : List Func} {ts : List Validation.DefType}, List.Forall₂ (FunRel P m) fs gs →
      List.Forall₂ (fun fn dt => (allocTypes m.types)[fn.type.toNat]? = some dt) fs ts →
      List.Forall₂ (FRel (H := H) P)
        ((ts.zip fs).map fun p => (⟨p.1, mi, .wasm p.2⟩ : FuncInst H))
        ((ts.zip gs).map fun p => (⟨p.1, mi, .wasm p.2⟩ : FuncInst H))
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons hfg hs, .cons hdt hts => by
    simp only [List.zip_cons_cons, List.map_cons]
    refine .cons ?_ (forall₂_allocFuncs_frel mi hs hts)
    rcases hfg.2 with rfl | hl
    · exact .inl rfl
    · exact .inr ((hl _ hdt).leafPair mi)

theorem frel_types : ∀ {X Y : List (FuncInst H)}, List.Forall₂ (FRel P) X Y →
    X.map FuncInst.type = Y.map FuncInst.type
  | _, _, .nil => rfl
  | _, _, .cons h hs => by rw [List.map_cons, List.map_cons, h.type_eq, frel_types hs]

/-- `allocModule?` for related modules: the same module instance, `SRel`-related stores. -/
theorem allocModule?_modRel {m : Module} {gs : List Func} (hfs : List.Forall₂ (FunRel P m) m.funcs gs)
    {s s₄ : Store H} {xas : List ExternAddr} {valsG : List Val} {refsT : List Ref}
    {refsE : List (List Ref)} {mi : ModuleInst}
    (h : allocModule? s m xas valsG refsT refsE = some (s₄, mi)) :
    ∃ s₄', allocModule? s { m with funcs := gs } xas valsG refsT refsE = some (s₄', mi) ∧
      SRel P s₄ s₄' := by
  have hT : ∀ dts : List Validation.DefType, gs.mapM (fun fn => dts[fn.type.toNat]?) =
      m.funcs.mapM (fun fn => dts[fn.type.toNat]?) := fun dts =>
    (Binaryen.mapM_forall₂ (fun f g hfg => by simp only [hfg.1]) hfs).symm
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
  refine ⟨_, rfl, ?_⟩
  have hfr : ∀ (l : List (FuncInst H)) (mi : ModuleInst), List.Forall₂ (FRel (H := H) P)
      (l ++ (funcTypes.zip m.funcs).map fun p => (⟨p.1, mi, .wasm p.2⟩ : FuncInst H))
      (l ++ (funcTypes.zip gs).map fun p => (⟨p.1, mi, .wasm p.2⟩ : FuncInst H)) := fun l mi =>
    Binaryen.forall₂_append' (List.forall₂_same.mpr fun x _ => (Or.inl rfl : FRel (H := H) P x x))
      (forall₂_allocFuncs_frel _ hfs (mapM_some_forall₂ hf))
  exact ⟨frel_types (hfr _ _), rfl, hfr _ _⟩

/-- **Instantiation of related modules**: equal frame and code, `SRel`-related stores. -/
theorem instantiate_modRel {host : HostSemantics H} {m m' : Module} (hrel : ModRel P m m')
    (hm' : ∃ mt, Validation.ModuleOk m' mt) {s : Store H} {xas : List ExternAddr} {c : Config H}
    (hI : Instantiate P host s m xas c) :
    ∃ c', Instantiate P host s m' xas c' ∧ c'.frame = c.frame ∧ c'.code = c.code ∧
      SRel P c.store c'.store := by
  obtain ⟨⟨xtE, xtI, hmt, hxas⟩, hbd, s₁, s₂, s₃, s₄, f₁, f₂, f₃, vG, rT, rE, mi, hG, hT, hE, hA,
    rfl⟩ := hI
  obtain ⟨mt', hmt'⟩ := hm'
  obtain rfl := ModRel.moduleOk_type hrel hmt hmt'
  obtain ⟨gs, rfl⟩ : ∃ gs, m' = { m with funcs := gs } := ⟨_, ModRel.eq_withFuncs hrel⟩
  have hfs := hrel.funcs
  have hlen : gs.length = m.funcs.length := hfs.length_eq.symm
  obtain ⟨s₄', hA', hst⟩ := allocModule?_modRel hfs hA
  have hinit : ModuleInst.initial s { m with funcs := gs } xas = ModuleInst.initial s m xas := by
    simp only [ModuleInst.initial, hlen]
  refine ⟨_, ⟨⟨xtE, xtI, hmt', hxas⟩, hbd, s₁, s₂, s₃, s₄', f₁, f₂, f₃, vG, rT, rE, mi, ?_, hT,
    hE, hA', rfl⟩, rfl, rfl, hst⟩
  rw [hinit]
  exact hG

/-! ## Sessions and exports -/

/-- **Session transport** from a typed store to an `SRel`-related one. -/
theorem session_transport {mi : ModuleInst} {s : Store H} {script : List Call}
    {bs : List (Behaviour Val)} (hs : Session P closedHost mi s script bs) :
    ∀ {t : Store H}, StoreOk s → SRel P s t → Session P closedHost mi t script bs := by
  induction hs with
  | nil => intro _ _ _; exact .nil
  | stop h =>
    intro t _ hst
    exact .stop fun a ha hok => h a ha (Binaryen.invokeOk_of_storeRel hst.symm hok)
  | done ha hok run hr _ ih =>
    intro t hs hst
    obtain ⟨_, _, _, -, -, hcS⟩ := Silmaril.Wasm.Execution.Core.invoke_ok hs hok
    obtain ⟨d, hd, hdc, hst'⟩ := run_transport run hr (invoke_rel hst hs hok)
    exact .done ha (Binaryen.invokeOk_of_storeRel hst hok) hd hdc
      (ih (Silmaril.Wasm.SingleThreaded.ConfigOk.storeOk (Binaryen.Unwrap.preserves_closed hcS run))
        hst')
  | diverge ha hok hd =>
    intro t hs hst
    exact .diverge ha (Binaryen.invokeOk_of_storeRel hst hok)
      (div_transport (invoke_rel hst hs hok) hd)

/-- **Export refinement of modules with equivalent strict leaf functions**, closed host. -/
theorem exportRefines_modRel {m m' : Module} (hrel : ModRel P m m')
    (hm : ∃ mt, Validation.ModuleOk m mt) (hm' : ∃ mt, Validation.ModuleOk m' mt) :
    ExportRefines (· = ·) P (closedHost (H := H)) m m' := by
  refine ⟨fun s xas c' _ hI' => ?_, fun s xas script hs bs hbs => ?_⟩
  · obtain ⟨c, hc, -⟩ := instantiate_modRel hrel.symm hm hI'
    exact ⟨c, hc⟩
  · obtain ⟨c, hI, hcase⟩ := hbs
    obtain ⟨c', hI', hfr, hco, hst⟩ := instantiate_modRel hrel hm' hI
    have hcS : ConfigOk c [] := Instantiate.ok Silmaril.Wasm.SingleThreaded.divHost_ok hs
      (Binaryen.Unwrap.instantiate_of_closed_unwrap Silmaril.Wasm.SingleThreaded.divHost hI)
    have hR : Rel P c c' := ⟨hst, hfr.symm, .inl hco.symm, Sim.ContextTyped.of_configOk hcS⟩
    refine ⟨bs, ⟨c', hI', ?_⟩, SessionRel.refl (fun _ => rfl) bs⟩
    rcases hcase with ⟨c₁, bs', hS, hcode, hsess, rfl⟩ | ⟨c₁, r, hS, hcode, hr, rfl⟩ | ⟨hd, rfl⟩
    · obtain ⟨d, hd, hdc, hst'⟩ := run_transport (r := .values []) hS
        (by simp [hcode, Result.toAdmin, vals]) hR
      refine Or.inl ⟨d, bs', hd, by simpa [Result.toAdmin, vals] using hdc, ?_, rfl⟩
      rw [hfr]
      exact session_transport hsess (Silmaril.Wasm.SingleThreaded.ConfigOk.storeOk
        (Binaryen.Unwrap.preserves_closed hcS hS)) hst'
    · obtain ⟨d, hd, hdc, -⟩ := run_transport hS hcode hR
      exact Or.inr (Or.inl ⟨d, r, hd, hdc, hr, rfl⟩)
    · exact Or.inr (Or.inr ⟨div_transport hR hd, rfl⟩)

/-- **Export equivalence of modules with equivalent strict leaf functions**, closed host. -/
theorem exportEquiv_modRel {m m' : Module} (hrel : ModRel P m m')
    (hm : ∃ mt, Validation.ModuleOk m mt) (hm' : ∃ mt, Validation.ModuleOk m' mt) :
    ExportEquiv (· = ·) P (closedHost (H := H)) m m' :=
  ⟨exportRefines_modRel hrel hm hm', (exportRefines_modRel hrel.symm hm' hm).mono
    fun _ _ h => h.symm⟩

end Silmaril.Proofs.Wasm.SSA.CoreCert
