module

public import Silmaril.Wasm.Binaryen.DirectizeRun
public import Silmaril.Wasm.Binaryen.CodeSimModule

@[expose] public section

/-! # Directize: corresponding instantiations

Instantiating a module and the module with Directize-rewritten bodies from one store gives
configurations with equal frame and code and `DirSim.SR`-related stores: the allocated
functions of the rewritten module have related bodies at the module's instance, every
other function is the same (`instantiate_dir`, `instantiate_dir'`, after
`CodeSimModule.instantiate_bodiesRel`).
-/

namespace Silmaril.Wasm.Binaryen

namespace DirectizeInst

open Execution.Core Validation Numerics

variable {H : Type} {ok : DirSim.SiteOk}

variable (ok) in
/-- Function lists with equal types and locals, and bodies related at every instance. -/
def BodiesRel (fs gs : List Func) : Prop :=
  List.Forall₂ (fun f g : Func => f.type = g.type ∧ f.locals = g.locals ∧
    ∀ mi, DirSim.GIL ok mi mi f.body g.body) fs gs

theorem forall₂_allocFuncsD (mi : ModuleInst) :
    ∀ {fs gs : List Func}, BodiesRel ok fs gs → ∀ ts : List DefType,
      List.Forall₂ (DirSim.FR (H := H) ok mi)
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
    refine .cons ?_ (forall₂_allocFuncsD mi hs ts)
    unfold DirSim.FR DirSim.FC
    exact ⟨rfl, rfl, h.1, h.2.1, h.2.2 mi⟩

theorem allocModule?_dir {m : Module} {gs : List Func} (hfs : BodiesRel ok m.funcs gs)
    {s s₄ : Store H} {xas : List ExternAddr} {valsG : List Val} {refsT : List Ref}
    {refsE : List (List Ref)} {mi : ModuleInst}
    (h : allocModule? s m xas valsG refsT refsE = some (s₄, mi)) :
    ∃ s₄', allocModule? s { m with funcs := gs } xas valsG refsT refsE = some (s₄', mi) ∧
      DirSim.SR ok mi s₄ s₄' := by
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
  refine ⟨_, rfl, ⟨?_, rfl⟩⟩
  exact forall₂_append' (List.forall₂_same.mpr fun x _ => DirSim.FR.refl x)
    (forall₂_allocFuncsD _ hfs _)


theorem instantiate_dir {P : Profile} {host : HostSemantics H} {m m' : Module}
    (hrel : ModuleBodiesRel (fun _ _ => True) m m') (hd : BodiesRel ok m.funcs m'.funcs)
    (hm' : ∃ mt, ModuleOk m' mt) {s : Store H} {xas : List ExternAddr} {c : Config H}
    (hI : Instantiate P host s m xas c) :
    ∃ c', Instantiate P host s m' xas c' ∧ c'.frame = c.frame ∧ c'.code = c.code ∧
      DirSim.SR ok c.frame.module c.store c'.store := by
  obtain ⟨⟨xtE, xtI, hmt, hxas⟩, hbd, s₁, s₂, s₃, s₄, f₁, f₂, f₃, vG, rT, rE, mi, hG, hT, hE, hA,
    rfl⟩ := hI
  obtain ⟨mt', hmt'⟩ := hm'
  obtain rfl := hrel.moduleOk_type hmt hmt'
  obtain ⟨gs, rfl⟩ : ∃ gs, m' = { m with funcs := gs } := ⟨_, hrel.eq_withFuncs⟩
  have hlen : gs.length = m.funcs.length := hd.length_eq.symm
  obtain ⟨s₄', hA', hst⟩ := allocModule?_dir hd hA
  have hinit : ModuleInst.initial s { m with funcs := gs } xas = ModuleInst.initial s m xas := by
    simp only [ModuleInst.initial, hlen]
  refine ⟨_, ⟨⟨xtE, xtI, hmt', hxas⟩, hbd, s₁, s₂, s₃, s₄', f₁, f₂, f₃, vG, rT, rE, mi, ?_, hT,
    hE, hA', rfl⟩, rfl, rfl, hst⟩
  rw [hinit]
  exact hG


theorem allocModule?_dir' {m : Module} {gs : List Func} (hfs : BodiesRel ok m.funcs gs)
    {s s₄' : Store H} {xas : List ExternAddr} {valsG : List Val} {refsT : List Ref}
    {refsE : List (List Ref)} {mi : ModuleInst}
    (h : allocModule? s { m with funcs := gs } xas valsG refsT refsE = some (s₄', mi)) :
    ∃ s₄, allocModule? s m xas valsG refsT refsE = some (s₄, mi) ∧
      DirSim.SR ok mi s₄ s₄' := by
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
  refine ⟨_, rfl, ⟨?_, rfl⟩⟩
  exact forall₂_append' (List.forall₂_same.mpr fun x _ => DirSim.FR.refl x)
    (forall₂_allocFuncsD _ hfs _)


theorem instantiate_dir' {P : Profile} {host : HostSemantics H} {m m' : Module}
    (hrel : ModuleBodiesRel (fun _ _ => True) m m') (hd : BodiesRel ok m.funcs m'.funcs)
    (hm : ∃ mt, ModuleOk m mt) {s : Store H} {xas : List ExternAddr} {c' : Config H}
    (hI : Instantiate P host s m' xas c') :
    ∃ c, Instantiate P host s m xas c ∧ c'.frame = c.frame ∧ c'.code = c.code ∧
      DirSim.SR ok c.frame.module c.store c'.store := by
  obtain ⟨gs, rfl⟩ : ∃ gs, m' = { m with funcs := gs } := ⟨_, hrel.eq_withFuncs⟩
  obtain ⟨⟨xtE, xtI, hmt', hxas⟩, hbd, s₁, s₂, s₃, s₄', f₁, f₂, f₃, vG, rT, rE, mi, hG, hT, hE,
    hA', rfl⟩ := hI
  obtain ⟨mt, hmt⟩ := hm
  obtain rfl := hrel.moduleOk_type hmt hmt'
  have hlen : gs.length = m.funcs.length := hd.length_eq.symm
  obtain ⟨s₄, hA, hst⟩ := allocModule?_dir' hd hA'
  have hinit : ModuleInst.initial s { m with funcs := gs } xas = ModuleInst.initial s m xas := by
    simp only [ModuleInst.initial, hlen]
  refine ⟨_, ⟨⟨xtE, xtI, hmt, hxas⟩, hbd, s₁, s₂, s₃, s₄, f₁, f₂, f₃, vG, rT, rE, mi, ?_, hT,
    hE, hA, rfl⟩, rfl, rfl, hst⟩
  rw [← hinit]
  exact hG

end DirectizeInst

end Silmaril.Wasm.Binaryen
