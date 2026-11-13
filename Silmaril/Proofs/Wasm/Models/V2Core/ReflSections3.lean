module

public import Silmaril.Proofs.Wasm.Models.V2Core.ReflSections2

/-!
# Reflecting tables, memories, element and data segments, functions, the start function and
exports

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core.Reflect

open Silmaril.Wasm.V2.Validation (globalToC tableToC resultToC liftResult)
open Silmaril.Wasm.Validation (TypeCtx TyOk)

/-! ## Tables and memories -/

/-- A table of the image reflects. -/
theorem table_one {D : KCtx} {t : Silmaril.Wasm.V2.TableType} {tt : Silmaril.Wasm.Validation.CTableType}
    (h : Silmaril.Wasm.Validation.TableOk D t.toCoreTable tt) :
    tt = tableToC t ∧ Silmaril.Wasm.V2.TableType.Ok t := by
  have e : tt = tableToC t := h.1.trans (Silmaril.Wasm.V2.Validation.closeTableType_toCore D t)
  exact ⟨e, tableTypeOk_of (e ▸ h.2.1)⟩

theorem tables_refl {D : KCtx} {ts : List Silmaril.Wasm.V2.TableType}
    {tts : List Silmaril.Wasm.Validation.CTableType}
    (h : List.Forall₂ (Silmaril.Wasm.Validation.TableOk D)
      (ts.map Silmaril.Wasm.V2.TableType.toCoreTable) tts) :
    tts = ts.map tableToC ∧ List.Forall₂ Silmaril.Wasm.V2.Validation.TableOk ts ts := by
  obtain ⟨e, hok⟩ := forall₂_map_eq (fun _ _ h => table_one h) h
  exact ⟨e, by simpa using forall₂_map_self (f := id) fun t ht => ⟨rfl, hok t ht⟩⟩

theorem mems_refl {ms : List Silmaril.Wasm.V2.MemoryType}
    (h : ∀ mt ∈ ms.map Silmaril.Wasm.V2.MemoryType.toCore, Silmaril.Wasm.Validation.MemOk mt) :
    List.Forall₂ Silmaril.Wasm.V2.Validation.MemOk ms ms := by
  have hok : ∀ mt ∈ ms, Silmaril.Wasm.V2.Validation.MemOk mt mt := fun mt hmt =>
    ⟨rfl, memTypeOk_of (h _ (List.mem_map_of_mem hmt))⟩
  simpa using forall₂_map_self (f := id) hok

/-! ## Element segments -/

/-- The mode of an element segment of the image reflects. -/
theorem elemMode_one {Cp : VCtx} {D : KCtx} (hK : RelK Cp D)
    (htab : D.tables = Cp.tables.map tableToC) {md : Silmaril.Wasm.V2.ElemMode}
    {cmd : Silmaril.Wasm.ElemMode} {rt : Silmaril.Wasm.V2.RefType}
    (hc : Silmaril.Wasm.V2.ElemMode.toCore md = some cmd)
    (h : Silmaril.Wasm.Validation.ElemModeOk D cmd rt.toC)
    (hs : ∀ x off, cmd = .active x off → Silmaril.Wasm.Models.simpleConst off = true)
    (hb : ∀ x off, md = .active x off →
      ∀ y, Silmaril.Wasm.V2.Instr.globalGet y ∈ off → y.toNat < Cp.globals.length) :
    Silmaril.Wasm.V2.Validation.ElemModeOk Cp md rt := by
  match md, hc, h with
  | .passive, hc, _ => exact .passive
  | .declare, hc, _ => exact .declare
  | .active x off, hc, h =>
    obtain ⟨off', hoff', rfl⟩ := Option.map_eq_some_iff.mp hc
    cases h with
    | active ht hsub ho =>
      obtain ⟨tt, htt, e⟩ := getElem?_map_some (htab ▸ ht)
      obtain ⟨rfl, -, rfl⟩ := Silmaril.Wasm.Validation.CTableType.mk.inj e
      have hrt : rt = tt.element := refToC_sub' hK.wf.types hK.recs hsub
      exact .active htt hrt.symm (const_refl hK hoff' (hs x off' rfl)
        (tv := .num (.int .i32)) ho (hb x off rfl))

/-- An element segment of the image reflects. -/
theorem elem_one {Cp : VCtx} {D : KCtx} (hK : RelK Cp D) (htab : D.tables = Cp.tables.map tableToC)
    {e : Silmaril.Wasm.V2.Elem} {ce : Silmaril.Wasm.Elem}
    (hce : Silmaril.Wasm.V2.Elem.toCore e = some ce) {rt : Silmaril.Wasm.Validation.CRefType}
    (h : Silmaril.Wasm.Validation.ElemOk D ce rt)
    (hsi : ∀ ex ∈ ce.init, Silmaril.Wasm.Models.simpleConst ex = true)
    (hso : ∀ x off, ce.mode = .active x off → Silmaril.Wasm.Models.simpleConst off = true)
    (hbi : ∀ ex ∈ e.init, ∀ y, Silmaril.Wasm.V2.Instr.globalGet y ∈ ex → y.toNat < Cp.globals.length)
    (hbo : ∀ x off, e.mode = .active x off →
      ∀ y, Silmaril.Wasm.V2.Instr.globalGet y ∈ off → y.toNat < Cp.globals.length) :
    rt = e.type.toC ∧ Silmaril.Wasm.V2.Validation.ElemOk Cp e e.type := by
  obtain ⟨init, hinit, hce'⟩ := Option.bind_eq_some_iff.mp hce
  obtain ⟨cmode, hcmode, rfl⟩ := Option.map_eq_some_iff.mp hce'
  have hrt : rt = e.type.toC := h.1.trans (Silmaril.Wasm.V2.Validation.closeRef_toCore D e.type)
  subst hrt
  refine ⟨rfl, rfl, fun ex hex => ?_, elemMode_one hK htab hcmode h.2.2.2 hso hbo⟩
  obtain ⟨ex', hex', hmem⟩ := mapM_mem_of hinit ex hex
  exact const_refl hK hex' (hsi ex' hmem) (tv := .ref e.type) (h.2.2.1 ex' hmem) (hbi ex hex)

/-- A data segment of the image reflects. -/
theorem data_one {Cp : VCtx} {D : KCtx} (hK : RelK Cp D)
    (hmem : D.mems = Cp.mems.map Silmaril.Wasm.V2.MemoryType.toCore) {d : Silmaril.Wasm.V2.Data}
    {cd : Silmaril.Wasm.Data} (hcd : Silmaril.Wasm.V2.Data.toCore d = some cd)
    (h : Silmaril.Wasm.Validation.DataOk D cd)
    (hs : ∀ x off, cd.mode = .active x off → x.toNat = 0 ∧ Silmaril.Wasm.Models.simpleConst off = true)
    (hb : ∀ x off, d.mode = .active x off →
      ∀ y, Silmaril.Wasm.V2.Instr.globalGet y ∈ off → y.toNat < Cp.globals.length) :
    Silmaril.Wasm.V2.Validation.DataOk Cp d := by
  obtain ⟨cmode, hcmode, rfl⟩ := Option.map_eq_some_iff.mp hcd
  unfold Silmaril.Wasm.V2.Validation.DataOk
  cases hdm : d.mode with
  | passive => exact .passive
  | active x off =>
    rw [hdm] at hcmode
    obtain ⟨off', hoff', rfl⟩ := Option.map_eq_some_iff.mp hcmode
    obtain ⟨hx0, hs'⟩ := hs x off' rfl
    cases h with
    | active hm ho =>
      have hm0 : D.mems[0]? = some _ := hx0 ▸ hm
      obtain ⟨mt, hmt, e⟩ := getElem?_map_some (hmem ▸ hm0)
      have ha := congrArg Silmaril.Wasm.MemoryType.address e
      simp only [Silmaril.Wasm.V2.MemoryType.toCore] at ha
      subst ha
      exact .active hx0 hmt (const_refl hK hoff' hs' (tv := .num (.int .i32)) ho (hb x off hdm))

/-! ## Functions -/

/-- `Rel` survives entering a function body. -/
theorem Rel.funcBody {Cm : VCtx} {C : KCtx} (hR : Rel Cm C) (hl : Cm.locals = [])
    (hlab : Cm.labels = []) (ft : Silmaril.Wasm.V2.FuncType) (locs : List Silmaril.Wasm.V2.ValType)
    (lts : List Silmaril.Wasm.Validation.LocalType)
    (hlts : lts.map Silmaril.Wasm.Validation.LocalType.type = locs.map Silmaril.Wasm.V2.ValType.toC) :
    Rel (Cm.withFuncFrame (ft.params ++ locs) (liftResult ft.results) (liftResult ft.results))
      (C.funcBody (ft.params.map Silmaril.Wasm.V2.ValType.toC)
        (ft.results.map Silmaril.Wasm.V2.ValType.toC) lts) :=
  { hR with
    locals := fun y => by
      have e : ((ft.params.map Silmaril.Wasm.V2.ValType.toC).map
          (fun t => (⟨.set, t⟩ : Silmaril.Wasm.Validation.LocalType)) ++ lts).map
            Silmaril.Wasm.Validation.LocalType.type =
          (ft.params ++ locs).map Silmaril.Wasm.V2.ValType.toC := by
        simp [hlts, List.map_map, Function.comp_def]
      simp only [Silmaril.Wasm.Validation.Context.funcBody,
        Silmaril.Wasm.V2.Validation.Context.withFuncFrame, hl, List.nil_append]
      rw [← List.getElem?_map, ← List.getElem?_map, e]
    labels := by
      simp [Silmaril.Wasm.Validation.Context.funcBody,
        Silmaril.Wasm.V2.Validation.Context.withFuncFrame, hlab]
    return_ := by
      simp [Silmaril.Wasm.Validation.Context.funcBody,
        Silmaril.Wasm.V2.Validation.Context.withFuncFrame] }

/-- The declared locals of a function of the image have image types. -/
theorem locals_types {C : KCtx} :
    ∀ {locs : List Silmaril.Wasm.V2.ValType} {lts : List Silmaril.Wasm.Validation.LocalType},
      List.Forall₂ (Silmaril.Wasm.Validation.LocalOk C) (locs.map Silmaril.Wasm.V2.ValType.toCore) lts →
        lts.map Silmaril.Wasm.Validation.LocalType.type = locs.map Silmaril.Wasm.V2.ValType.toC
  | [], _, .nil => rfl
  | _ :: _, _, .cons h hs => by
    cases h <;> simp [locals_types hs, Silmaril.Wasm.V2.Validation.closeVal_toCore]

/-- The defined type of a 2.0 function type determines it. -/
theorem toDefType_inj {ft ft' : Silmaril.Wasm.V2.FuncType} (e : ft.toDefType = ft'.toDefType) :
    ft = ft' := by
  have h := Silmaril.Wasm.V2.FuncType.toDefType_expand ft
  rw [e, Silmaril.Wasm.V2.FuncType.toDefType_expand ft'] at h
  simp only [Option.some.injEq, Silmaril.Wasm.Validation.Ty.func.injEq] at h
  have hp := congrArg Silmaril.Wasm.Validation.Ty.toList h.1
  have hr := congrArg Silmaril.Wasm.Validation.Ty.toList h.2
  simp only [Silmaril.Wasm.Validation.Ty.toList_ofList] at hp hr
  have inj := List.map_injective_iff.mpr Silmaril.Wasm.V2.ValType.toC_injective
  cases ft; cases ft'
  simp only [Silmaril.Wasm.V2.FuncType.mk.injEq]
  exact ⟨(inj hp).symm, (inj hr).symm⟩

/-- A function of the image reflects. -/
theorem func_one {Cm : VCtx} {C : KCtx} (hR : Rel Cm C) (hl : Cm.locals = []) (hlab : Cm.labels = [])
    {f : Silmaril.Wasm.V2.Func} {b : Silmaril.Wasm.Func} (hb : Silmaril.Wasm.V2.Func.toCore f = some b)
    {ft : Silmaril.Wasm.V2.FuncType} (h : Silmaril.Wasm.Validation.FuncOk C b ft.toDefType) :
    Silmaril.Wasm.V2.Validation.FuncOk Cm f ft := by
  obtain ⟨body, hbody, rfl⟩ := Option.map_eq_some_iff.mp hb
  cases h with
  | mk hd he hlo hbo =>
    obtain ⟨ft₀, hft₀, e₀⟩ := hR.types_get hd
    obtain rfl : ft = ft₀ := (toDefType_inj e₀).symm
    obtain ⟨hp, hr⟩ := expand_toDefType_inv he
    have hRb := hR.funcBody hl hlab ft f.locals _ (locals_types hlo)
    rw [hp, hr] at hbo
    have v := instrs_refl hRb hbody hbo
    simp only [erT, ers_map_toC, ers] at v
    exact .mk hft₀ v

/-! ## Start and exports -/

theorem start_one {Cm : VCtx} {C : KCtx} (hR : Rel Cm C) {x : Silmaril.Wasm.FuncIdx}
    (h : Silmaril.Wasm.Validation.StartOk C x) : Silmaril.Wasm.V2.Validation.StartOk Cm x := by
  obtain ⟨d, hd, he⟩ := h
  obtain ⟨ft, hft, rfl⟩ := hR.funcs_get hd
  obtain ⟨hp, hr⟩ := expand_toDefType_inv he
  have hp' : ft.params = [] := List.map_eq_nil_iff.mp hp.symm
  have hr' : ft.results = [] := List.map_eq_nil_iff.mp hr.symm
  have e : ft = ⟨[], []⟩ := by cases ft; simp_all
  show Cm.funcs[x.toNat]? = some ⟨[], []⟩
  rw [← e]
  exact hft

theorem export_one {Cm : VCtx} {C : KCtx} (hR : Rel Cm C) {ix : Silmaril.Wasm.V2.ExternIdx}
    {cx : Silmaril.Wasm.Validation.CExternType}
    (h : Silmaril.Wasm.Validation.ExternIdxOk C ix.toCore cx) :
    ∃ vx, Silmaril.Wasm.V2.Validation.ExternIdxOk Cm ix vx ∧ cx = vx.toCore := by
  cases ix <;> cases h
  case func.func hd =>
    obtain ⟨ft, hft, e⟩ := hR.funcs_get hd
    exact ⟨.func ft, .func hft, by rw [← e]; rfl⟩
  case global.global hg =>
    obtain ⟨gt, hgt, e⟩ := hR.globals_get hg
    exact ⟨.global gt, .global hgt, by rw [← e]; rfl⟩
  case table.table ht =>
    obtain ⟨tt, htt, e⟩ := hR.tables_get ht
    exact ⟨.table tt, .table htt, by rw [← e]; rfl⟩
  case memory.mem hm =>
    obtain ⟨mt, hmt, e⟩ := hR.mems_get hm
    exact ⟨.memory mt, .memory hmt, by rw [← e]; rfl⟩

theorem exports_refl {Cm : VCtx} {C : KCtx} (hR : Rel Cm C) {es : List Silmaril.Wasm.V2.Export}
    {xtE : List Silmaril.Wasm.Validation.CExternType}
    (h : List.Forall₂ (Silmaril.Wasm.Validation.ExportOk C) (es.map Silmaril.Wasm.V2.Export.toCore) xtE) :
    ∃ xt, List.Forall₂ (Silmaril.Wasm.V2.Validation.ExportOk Cm) es xt :=
  let ⟨xt, h', _⟩ := forall₂_lift (f := Silmaril.Wasm.V2.Export.toCore)
    (R := Silmaril.Wasm.Validation.ExportOk C) (S := Silmaril.Wasm.V2.Validation.ExportOk Cm)
    (g := Silmaril.Wasm.V2.ExternType.toCore) (fun a _ h => export_one (ix := a.index) hR h) h
  ⟨xt, h'⟩

end Silmaril.Proofs.Wasm.Models.V2Core.Reflect
