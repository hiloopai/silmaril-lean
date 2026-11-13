module

public import Silmaril.Wasm.Models.V2CoreInstDom.Thms

/-!
# `domInstDet` at a non-empty store

An earlier step put the empty 2.0 store with the closed host in `domInstDet g`
(`V2CoreInstDom.domInstDet_emptyPt`). This file generalises its two steps:

* `instantiate_noImports`: a valid 2.0 module without imports instantiates in **every** 2.0
  store, under every host, at every profile; the store it starts from is host-free when the
  given store is. The constant initialisers read no global (the module has none to import), and
  `allocModule?` only reads the lengths of the store's lists.
* `dataPt`: the 2.0 store holding one (empty) data segment, with the closed host. It is in
  `domInstDet g` at every grow policy (`domInstDet_dataPt`). Its store is non-empty, but holds
  nothing a module can import, so Core instantiates only import-free modules there, as in the empty
  case.

The proofs are new; the import-free steps follow `V2CoreInstDom`'s.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreInstData

open Silmaril.Wasm.V2 Silmaril.Wasm.V2.Execution Silmaril.Wasm.V2.Validation
open Silmaril.Wasm (FuncIdx GlobalIdx)
open Silmaril.Wasm.Numerics (Profile GrowKind)
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec
  Silmaril.Wasm.Models.V2CoreInstDet
open Silmaril.Proofs.Wasm.Models.V2Sound (HostFree divV hostOk_divV closed_safe
  behavioursOf_nonempty_of_safe)
open Silmaril.Proofs.Wasm.Models.V2CoreInstDom (SegBounded noHost forall₂_of_exists mapM_some
  exists_of_forall₂ lt_of_getElem? instExport?_isSome ctx_of_moduleOk hostFree_allocModule
  imports_of_toCore segBounded_of_core)

variable {H : Type}

/-! ## Import-free modules instantiate in every store -/

/-- The initial frame of an import-free instantiation in `s`. -/
abbrev fs (s : Store H) (m : Module) : Frame := Frame.initial s m []

/-- A constant expression of a context with no more functions than `m` and no globals denotes a
value in any store, at `m`'s initial frame. -/
theorem const_denotes (s : Store H) {C : Context} {m : Module} {e : Expr} {t : ValType}
    (h : ExprOkConst C e t) (hf : C.funcs.length ≤ m.funcs.length) (hg : C.globals = []) :
    ∃ v, constExpr? s (fs s m).module e = some v := by
  have hF : ∀ x : FuncIdx, x.toNat < C.funcs.length →
      ((fs s m).module.funcAddr? x).isSome := fun x hx => by
    simp [fs, Frame.initial, ModuleInst.initial, ModuleInst.funcAddr?, ExternAddr.funcs]
    omega
  have hG : ∀ x : GlobalIdx, x.toNat < C.globals.length → ∃ a,
      (fs s m).module.globalAddr? x = some a ∧ (s.globalInst? a).isSome :=
    fun x hx => absurd hx (by simp [hg])
  obtain ⟨v, hv, -⟩ := exprOkConst_evalExpr (P := Profile.spec false default) (host := noHost)
    (s := s) (f := fs s m) h hF hG
  exact ⟨v, hv⟩

/-- At a reference type, the value is a reference. -/
theorem const_ref_denotes (s : Store H) {C : Context} {m : Module} {e : Expr} {rt : RefType}
    (h : ExprOkConst C e (.ref rt)) (hf : C.funcs.length ≤ m.funcs.length) (hg : C.globals = []) :
    ∃ r, constExpr? s (fs s m).module e = some (Val.ref r) := by
  obtain ⟨v, hv⟩ := const_denotes s h hf hg
  have hty : v.type = .ref rt :=
    constExpr?_type (f := fs s m) h hv fun x _ _ _ hx => absurd hx (by simp [hg])
  cases v with
  | ref r => exact ⟨r, hv⟩
  | num n => exact absurd hty (by simp [Val.type])
  | vec w => exact absurd hty (by simp [Val.type])

/-- `allocModule?` succeeds in any store for a valid import-free module, given initialiser lists
of the right lengths. -/
theorem allocModule_some (s : Store H) {m : Module} {xt : List ExternType}
    (hm : ModuleOk m [] xt) {vs : List Val} {rss : List (List Ref)}
    (hvs : m.globals.length = vs.length) (hrss : m.elems.length = rss.length) :
    ∃ r, allocModule? s m [] vs rss = some r := by
  cases hm with
  | mk htypes himports hglobals htables hmems helems hdatas hfuncs hstart hexports hmemsle
      hnames hC hC' =>
    rename_i ft' ft gt tt mt rt C C'
    obtain ⟨fts, hfts⟩ : ∃ fts, (m.funcs.mapM fun fn => m.types[fn.type.toNat]?) = some fts :=
      mapM_some fun fn hfn => by
        obtain ⟨t, ⟨hx, -⟩⟩ := exists_of_forall₂ hfuncs fn hfn
        have hx' : ft'[fn.type.toNat]? = some t := by subst hC; exact hx
        have hlt : fn.type.toNat < m.types.length := htypes.length_eq ▸ lt_of_getElem? hx'
        simp [hlt]
    have hlen : ft.length = m.funcs.length ∧ gt.length = m.globals.length ∧
        tt.length = m.tables.length ∧ mt.length = m.memories.length :=
      ⟨hfuncs.length_eq.symm, hglobals.length_eq.symm, htables.length_eq.symm,
        hmems.length_eq.symm⟩
    obtain ⟨xi, hxi⟩ : ∃ xi, m.exports.mapM (instExport?
        (ExternAddr.funcs [] ++ (List.range m.funcs.length).map (s.funcs.length + ·))
        (ExternAddr.globals [] ++ (List.range m.globals.length).map (s.globals.length + ·))
        (ExternAddr.tables [] ++ (List.range m.tables.length).map (s.tables.length + ·))
        (ExternAddr.mems [] ++ (List.range m.memories.length).map (s.mems.length + ·))) =
          some xi :=
      mapM_some fun e he => by
        obtain ⟨t, ht⟩ := exists_of_forall₂ hexports e he
        subst hC
        refine instExport?_isSome ht ?_ ?_ ?_ ?_ <;>
          simp [ExternType.funcs, ExternType.globals, ExternType.tables, ExternType.mems,
            ExternAddr.funcs, ExternAddr.globals, ExternAddr.tables, ExternAddr.mems, hlen]
    simp only [allocModule?, hfts, ← hvs, ← hrss, hxi]
    exact ⟨_, rfl⟩

/-- **A valid import-free 2.0 module instantiates in every store**, under every host, and the
configuration's store is host-free when the given store is. -/
theorem instantiate_noImports (P : Profile) {m : Module} {xt : List ExternType}
    (hm : ModuleOk m [] xt) (hb : SegBounded m) (s : Store H) (hs : HostFree s) :
    ∃ c : Config H, (∀ host : HostSemantics H, Instantiate P host s m [] c) ∧
      HostFree c.store := by
  obtain ⟨C', hglobals, helems, hf, hg⟩ : ∃ C' : Context,
      (∀ g ∈ m.globals, ExprOkConst C' g.init g.type.value) ∧
      (∀ e ∈ m.elems, ∀ ex ∈ e.init, ExprOkConst C' ex (.ref e.type)) ∧
      C'.funcs.length ≤ m.funcs.length ∧ C'.globals = [] := ctx_of_moduleOk hm
  obtain ⟨vs, hvs⟩ : ∃ vs, List.Forall₂ (fun (g : Global) (v : Val) =>
      constExpr? s (fs s m).module g.init = some v) m.globals vs :=
    forall₂_of_exists fun g hg' => const_denotes s (hglobals g hg') hf hg
  obtain ⟨rss, hrss⟩ : ∃ rss, List.Forall₂ (fun (e : Elem) (rs : List Ref) =>
      List.Forall₂ (fun (ex : Expr) (r : Ref) =>
        constExpr? s (fs s m).module ex = some (Val.ref r)) e.init rs)
      m.elems rss :=
    forall₂_of_exists fun e he =>
      forall₂_of_exists fun ex hex => const_ref_denotes s (helems e he ex hex) hf hg
  obtain ⟨⟨s', mi⟩, hal⟩ := allocModule_some s hm hvs.length_eq hrss.length_eq
  refine ⟨⟨s', { module := mi }, expression (runElems m ++ runDatas m ++
    (match m.start with | some x => [Instr.call x] | none => []))⟩, fun host => ?_,
    hostFree_allocModule hal hs⟩
  refine ⟨⟨[], xt, hm, .nil⟩, hb, vs, rss, s', mi, ?_, ?_, hal, rfl⟩
  · exact hvs.imp fun _ _ h => evalExpr_of_constExpr? h
  · exact hrss.imp fun _ _ h => h.imp fun _ _ h => evalExpr_of_constExpr? h

end Silmaril.Proofs.Wasm.Models.V2CoreInstData

namespace Silmaril.Proofs.Wasm.Models.V2CoreInstData

open Silmaril.Wasm.V2 Silmaril.Wasm.V2.Execution Silmaril.Wasm.V2.Validation
open Silmaril.Wasm.Numerics (Profile GrowKind)
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec
  Silmaril.Wasm.Models.V2CoreInstDet
open Silmaril.Proofs.Wasm.Models.V2Sound (HostFree divV hostOk_divV closed_safe
  behavioursOf_nonempty_of_safe)
open Silmaril.Proofs.Wasm.Models.V2CoreInstDom (imports_of_toCore segBounded_of_core)

/-! ## A point with a non-empty store -/

/-- The 2.0 store holding one empty data segment. -/
def dataStore : Store Nat := { datas := [{ bytes := ByteArray.empty }] }

/-- `dataStore` with the closed host. -/
def dataPt : Pt Nat := (dataStore, closedV)

theorem dataStore_ne_empty : dataStore.datas ≠ [] := by simp [dataStore]

/-- `dataPt` is in `v20instHT`'s domain at every profile. -/
theorem dataPt_dom (P : Profile) : (v20instHT P).dom dataPt := by
  refine ⟨⟨⟨fun _ _ h => by simp [dataPt, dataStore] at h,
    fun _ _ h => by simp [dataPt, dataStore] at h,
    fun _ _ h => by simp [dataPt, dataStore] at h,
    fun _ _ h => by simp [dataPt, dataStore] at h⟩, rfl,
    Silmaril.Proofs.Wasm.Models.V2Core.closedV_preserves,
    Silmaril.Proofs.Wasm.Models.V2Core.closedV_keeps⟩, hostEmbV_none, ?_⟩
  intro fi hfi
  have e : (ptCore dataPt).1.funcs = [] := rfl
  rw [e] at hfi
  simp at hfi

/-- **No external address is typed in `dataPt`'s Core store**: it has no tag, global, memory,
table or function. -/
theorem not_externAddrOk_data {xa : Silmaril.Wasm.Execution.Core.ExternAddr}
    {xt : Silmaril.Wasm.Validation.CExternType} :
    ¬ Silmaril.Wasm.Execution.Core.ExternAddrOk (ptCore dataPt).1 xa xt := by
  intro h
  induction h with
  | tag h => exact absurd h (by simp [show (ptCore dataPt).1.tags = [] from rfl])
  | global h => exact absurd h (by simp [show (ptCore dataPt).1.globals = [] from rfl])
  | mem h => exact absurd h (by simp [show (ptCore dataPt).1.mems = [] from rfl])
  | table h => exact absurd h (by simp [show (ptCore dataPt).1.tables = [] from rfl])
  | func h => exact absurd h (by simp [show (ptCore dataPt).1.funcs = [] from rfl])
  | sub _ _ _ ih => exact ih

/-- `dataStore` is typed. -/
theorem storeOk_dataStore : StoreOk dataStore := by
  constructor <;> simp [dataStore, DataInstOk]

theorem hostFree_dataStore : HostFree dataStore := fun _ h => by simp [dataStore] at h

/-- **`dataPt` is in `domInstDet g`**, at every grow policy. -/
theorem domInstDet_dataPt (g : GrowKind → Nat → Nat → Nat → Bool) : domInstDet g dataPt := by
  refine ⟨dataPt_dom _, fun m cm xas hval hcm ⟨C, hC⟩ => ?_⟩
  obtain ⟨xtE, xtI, hok, hxas⟩ := hC.valid
  have hxas0 : xas = [] := by
    cases xas with
    | nil => rfl
    | cons x xs =>
      cases hxas with
      | cons h _ => exact absurd h not_externAddrOk_data
  subst hxas0
  have hxtI : xtI = [] := List.forall₂_nil_left_iff.mp hxas
  subst hxtI
  have hcimp : cm.imports = [] := by
    cases hok with
    | mk _ himports => exact List.forall₂_nil_right_iff.mp himports
  have himp : m.imports = [] := by
    rw [imports_of_toCore hcm] at hcimp
    exact List.map_eq_nil_iff.mp hcimp
  obtain ⟨ixt, xt, hm⟩ := hval
  have hixt : ixt = [] := by
    cases hm with
    | mk _ himports =>
      rw [himp] at himports
      exact List.forall₂_nil_left_iff.mp himports
  subst hixt
  obtain ⟨c, hinst, hfree⟩ := instantiate_noImports (Profile.deterministic g) hm
    (segBounded_of_core hcm hC.bounded) dataStore hostFree_dataStore
  refine ⟨c, hinst closedV, ?_⟩
  obtain ⟨hok', -⟩ := Instantiate.ok hostOk_divV storeOk_dataStore (hinst divV)
  exact behavioursOf_nonempty_of_safe fun _ hsteps => (closed_safe hfree hok' hsteps).2.2

end Silmaril.Proofs.Wasm.Models.V2CoreInstData
