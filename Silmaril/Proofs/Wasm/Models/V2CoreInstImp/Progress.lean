module

public import Silmaril.Wasm.Models.V2CoreInstData.Thms
public import Silmaril.Wasm.Versions.Soundness.Thms

/-!
# 2.0 instantiation progress with imports

An earlier step proved that a valid 2.0 module **without imports** instantiates in every store
(`V2CoreInstData.instantiate_noImports`). Here the imports may be anything, provided the
supplied addresses match them (`List.Forall₂ (ExternAddrOk s) xas ixt`, which is also
`Instantiate.valid`'s premise):

* the global and element initialisers are constant expressions over the imported globals and the
  imported and predicted functions. Every imported global names an instance of `s`
  (`globalInst_of_externAddrOk`), and the address lists `ModuleInst.initial` builds have the
  lengths the context asks for (`funcs_length`, `globals_length`), so each initialiser denotes a
  value (`const_denotes_imp`) of its type (`const_ref_denotes_imp`);
* `allocModule?` succeeds: function types, export indices and initialiser lengths are in range
  (`allocModule_some_imp`);
* the store is host-free afterwards when it was before.

`instantiate_imports` packages them. The proofs are new; they follow `V2CoreInstDom`'s.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreInstImp

open Silmaril.Wasm.V2 Silmaril.Wasm.V2.Execution Silmaril.Wasm.V2.Validation
open Silmaril.Wasm (FuncIdx GlobalIdx)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Models.V2Sound (HostFree)
open Silmaril.Proofs.Wasm.Models.V2CoreInstDom (SegBounded noHost forall₂_of_exists mapM_some
  exists_of_forall₂ lt_of_getElem? instExport?_isSome hostFree_allocModule)

variable {H : Type}

/-! ## Imported addresses -/

/-- A typed global address names a global instance of the store, of exactly the expected type
(2.0's `Globaltype_sub` is equality). -/
theorem globalInst_of_externAddrOk {s : Store H} {xa : ExternAddr} {xt : ExternType}
    (h : ExternAddrOk s xa xt) :
    ∀ a gt, xa = .global a → xt = .global gt → ∃ gi, s.globalInst? a = some gi ∧ gi.type = gt := by
  induction h with
  | func _ => intro a gt h; cases h
  | @global a' gi hg => intro a gt ha hgt; cases ha; cases hgt; exact ⟨gi, hg, rfl⟩
  | table _ => intro a gt h; cases h
  | mem _ => intro a gt h; cases h
  | sub _ _ hsub ih =>
    intro a gt ha hgt
    subst hgt
    cases hsub with
    | global hg => exact ih a _ ha (congrArg ExternType.global hg)

/-- The imported global addresses and the imported global types correspond pointwise. -/
theorem globals_forall₂ {s : Store H} {xas : List ExternAddr} {ixt : List ExternType}
    (h : List.Forall₂ (ExternAddrOk s) xas ixt) :
    List.Forall₂ (fun a gt => ∃ gi, s.globalInst? a = some gi ∧ gi.type = gt)
      (ExternAddr.globals xas) (ExternType.globals ixt) :=
  (ExternAddrOk.forall₂_globals h).imp fun a gt hx => globalInst_of_externAddrOk hx a gt rfl rfl

theorem funcs_length {s : Store H} {xas : List ExternAddr} {ixt : List ExternType}
    (h : List.Forall₂ (ExternAddrOk s) xas ixt) :
    (ExternAddr.funcs xas).length = (ExternType.funcs ixt).length :=
  (ExternAddrOk.forall₂_funcs h).length_eq

theorem tables_length {s : Store H} {xas : List ExternAddr} {ixt : List ExternType}
    (h : List.Forall₂ (ExternAddrOk s) xas ixt) :
    (ExternAddr.tables xas).length = (ExternType.tables ixt).length :=
  (ExternAddrOk.forall₂_tables h).length_eq

theorem mems_length {s : Store H} {xas : List ExternAddr} {ixt : List ExternType}
    (h : List.Forall₂ (ExternAddrOk s) xas ixt) :
    (ExternAddr.mems xas).length = (ExternType.mems ixt).length :=
  (ExternAddrOk.forall₂_mems h).length_eq

/-! ## Constant expressions -/

/-- The initial frame of an instantiation with imports `xas` in `s`. -/
abbrev fi (s : Store H) (m : Module) (xas : List ExternAddr) : Frame := Frame.initial s m xas

/-- The context the initialisers are checked in: the imported globals, and the imported and the
module's own functions. -/
theorem ctx_of_moduleOk_imp {m : Module} {ixt xt : List ExternType} (hm : ModuleOk m ixt xt) :
    ∃ C' : Context,
      (∀ g ∈ m.globals, ExprOkConst C' g.init g.type.value) ∧
      (∀ e ∈ m.elems, ∀ ex ∈ e.init, ExprOkConst C' ex (.ref e.type)) ∧
      C'.funcs.length ≤ (ExternType.funcs ixt).length + m.funcs.length ∧
      C'.globals = ExternType.globals ixt := by
  cases hm with
  | mk htypes himports hglobals htables hmems helems hdatas hfuncs hstart hexports hmemsle
      hnames hC hC' =>
    rename_i ft' ft gt tt mt rt C C'
    refine ⟨C', fun g hg => ?_, fun e he ex hex => ?_, ?_, ?_⟩
    · obtain ⟨t, ht, -, hok⟩ := exists_of_forall₂ hglobals g hg
      exact ht ▸ hok
    · obtain ⟨rt, hrt, hok, -⟩ := exists_of_forall₂ helems e he
      exact hrt ▸ hok ex hex
    · simp [hC', hfuncs.length_eq]
    · simp [hC']

/-- The function lookups the initialisers can make succeed. -/
theorem funcs_isSome {s : Store H} {m : Module} {xas : List ExternAddr} {ixt : List ExternType}
    (hx : List.Forall₂ (ExternAddrOk s) xas ixt) (x : FuncIdx)
    (hlt : x.toNat < (ExternType.funcs ixt).length + m.funcs.length) :
    ((fi s m xas).module.funcAddr? x).isSome := by
  have hl := funcs_length hx
  simp only [fi, Frame.initial, ModuleInst.initial, ModuleInst.funcAddr?, List.getElem?_append]
  split <;> simp <;> omega

/-- A lookup in the right list of a `Forall₂` has a related lookup in the left list. -/
theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {i : Nat} {b : β}, l₂[i]? = some b →
      ∃ a, l₁[i]? = some a ∧ R a b
  | _, _, .nil, _, _, hb => by simp at hb
  | _, _, .cons hab _, 0, _, hb => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
    exact ⟨_, rfl, hb ▸ hab⟩
  | _, _, .cons _ h, _ + 1, _, hb => by
    simpa only [List.getElem?_cons_succ] using forall₂_getElem? h (by simpa using hb)

/-- The global lookups the initialisers can make succeed, at the expected types. -/
theorem globals_ok {s : Store H} {m : Module} {xas : List ExternAddr} {ixt : List ExternType}
    (hx : List.Forall₂ (ExternAddrOk s) xas ixt) (x : GlobalIdx) (gt : GlobalType)
    (hgt : (ExternType.globals ixt)[x.toNat]? = some gt) :
    ∃ a gi, (fi s m xas).module.globalAddr? x = some a ∧ s.globalInst? a = some gi ∧
      gi.type = gt := by
  obtain ⟨a, ha, gi, hgi, hty⟩ := forall₂_getElem? (globals_forall₂ hx) hgt
  exact ⟨a, gi, ha, hgi, hty⟩

/-- A constant expression of the module's context denotes a value at the initial frame. -/
theorem const_denotes_imp {s : Store H} {m : Module} {xas : List ExternAddr}
    {ixt : List ExternType} (hx : List.Forall₂ (ExternAddrOk s) xas ixt) {C : Context} {e : Expr}
    {t : ValType} (h : ExprOkConst C e t)
    (hf : C.funcs.length ≤ (ExternType.funcs ixt).length + m.funcs.length)
    (hg : C.globals = ExternType.globals ixt) :
    ∃ v, constExpr? s (fi s m xas).module e = some v := by
  have hF : ∀ x : FuncIdx, x.toNat < C.funcs.length → ((fi s m xas).module.funcAddr? x).isSome :=
    fun x hlt => funcs_isSome hx x (Nat.lt_of_lt_of_le hlt hf)
  have hG : ∀ x : GlobalIdx, x.toNat < C.globals.length → ∃ a,
      (fi s m xas).module.globalAddr? x = some a ∧ (s.globalInst? a).isSome := by
    intro x hlt
    have hgt : (ExternType.globals ixt)[x.toNat]? = some ((ExternType.globals ixt)[x.toNat]'
        (hg ▸ hlt)) := List.getElem?_eq_getElem _
    obtain ⟨a, gi, ha, hgi, -⟩ := globals_ok (m := m) hx x _ hgt
    exact ⟨a, ha, by simp [hgi]⟩
  obtain ⟨v, hv, -⟩ := exprOkConst_evalExpr (P := Profile.spec false default) (host := noHost)
    (s := s) (f := fi s m xas) h hF hG
  exact ⟨v, hv⟩

/-- At a reference type, the value is a reference. -/
theorem const_ref_denotes_imp {s : Store H} (hs : StoreOk s) {m : Module} {xas : List ExternAddr}
    {ixt : List ExternType} (hx : List.Forall₂ (ExternAddrOk s) xas ixt) {C : Context} {e : Expr}
    {rt : RefType} (h : ExprOkConst C e (.ref rt))
    (hf : C.funcs.length ≤ (ExternType.funcs ixt).length + m.funcs.length)
    (hg : C.globals = ExternType.globals ixt) :
    ∃ r, constExpr? s (fi s m xas).module e = some (Val.ref r) := by
  obtain ⟨v, hv⟩ := const_denotes_imp hx h hf hg
  have hglob : ∀ (x : GlobalIdx) (gt : GlobalType) (a : GlobalAddr) (gi : GlobalInst),
      C.globals[x.toNat]? = some gt → (fi s m xas).module.globalAddr? x = some a →
      s.globalInst? a = some gi → gi.value.type = gt.value := by
    intro x gt a gi hgt ha hgi
    obtain ⟨a', gi', ha', hgi', hty⟩ := globals_ok (m := m) hx x gt (hg ▸ hgt)
    have e₁ : a' = a := Option.some.inj (ha'.symm.trans ha)
    have e₂ : gi' = gi := Option.some.inj (hgi'.symm.trans (e₁ ▸ hgi))
    have hok : GlobalInstOk s gi := hs.globals gi (List.mem_of_getElem? hgi)
    rw [hok.2.type_eq, ← e₂, hty]
  have hty : v.type = .ref rt := constExpr?_type h hv hglob
  cases v with
  | ref r => exact ⟨r, hv⟩
  | num n => exact absurd hty (by simp [Val.type])
  | vec w => exact absurd hty (by simp [Val.type])

/-! ## Allocation and instantiation -/

/-- The export resolution of `allocModule?` succeeds when the supplied addresses match the
imports. -/
theorem exports_some {s : Store H} {m : Module} {ixt xt : List ExternType} {xas : List ExternAddr}
    (hm : ModuleOk m ixt xt) (hx : List.Forall₂ (ExternAddrOk s) xas ixt) :
    ∃ xi, m.exports.mapM (instExport?
        (ExternAddr.funcs xas ++ (List.range m.funcs.length).map (s.funcs.length + ·))
        (ExternAddr.globals xas ++ (List.range m.globals.length).map (s.globals.length + ·))
        (ExternAddr.tables xas ++ (List.range m.tables.length).map (s.tables.length + ·))
        (ExternAddr.mems xas ++ (List.range m.memories.length).map (s.mems.length + ·))) =
      some xi := by
  have hf := funcs_length hx
  have hg := (globals_forall₂ hx).length_eq
  have ht := tables_length hx
  have hme := mems_length hx
  cases hm with
  | mk htypes himports hglobals htables hmems helems hdatas hfuncs hstart hexports hmemsle
      hnames hC hC' =>
    rename_i ft' ft gt tt mt rt C C'
    have hlen : ft.length = m.funcs.length ∧ gt.length = m.globals.length ∧
        tt.length = m.tables.length ∧ mt.length = m.memories.length :=
      ⟨hfuncs.length_eq.symm, hglobals.length_eq.symm, htables.length_eq.symm,
        hmems.length_eq.symm⟩
    exact mapM_some fun e he => by
      obtain ⟨t, ht'⟩ := exists_of_forall₂ hexports e he
      subst hC
      refine instExport?_isSome ht' ?_ ?_ ?_ ?_ <;> simp [hlen, hf, hg, ht, hme]

/-- `allocModule?` succeeds for a valid module whose imports the addresses match, given
initialiser lists of the right lengths. -/
theorem allocModule_some_imp {s : Store H} {m : Module} {ixt xt : List ExternType}
    {xas : List ExternAddr} (hm : ModuleOk m ixt xt) (hx : List.Forall₂ (ExternAddrOk s) xas ixt)
    {vs : List Val} {rss : List (List Ref)} (hvs : m.globals.length = vs.length)
    (hrss : m.elems.length = rss.length) :
    ∃ r, allocModule? s m xas vs rss = some r := by
  obtain ⟨xi, hxi⟩ := exports_some hm hx
  obtain ⟨fts, hfts⟩ : ∃ fts, (m.funcs.mapM fun fn => m.types[fn.type.toNat]?) = some fts := by
    cases hm with
    | mk htypes himports hglobals htables hmems helems hdatas hfuncs hstart hexports hmemsle
        hnames hC hC' =>
      rename_i ft' ft gt tt mt rt C C'
      exact mapM_some fun fn hfn => by
        obtain ⟨t, ⟨hx', -⟩⟩ := exists_of_forall₂ hfuncs fn hfn
        have hx'' : ft'[fn.type.toNat]? = some t := by subst hC; exact hx'
        have hlt : fn.type.toNat < m.types.length := htypes.length_eq ▸ lt_of_getElem? hx''
        simp [hlt]
  simp only [allocModule?, hfts, ← hvs, ← hrss, hxi]
  exact ⟨_, rfl⟩

/-- **A valid 2.0 module instantiates in every typed store whose addresses match its imports**,
under every host and at every profile (given `$instantiate`'s segment bounds), and the
configuration's store is host-free when the given store is. -/
theorem instantiate_imports (P : Profile) {s : Store H} (hs : StoreOk s) (hfree : HostFree s)
    {m : Module} {ixt xt : List ExternType} {xas : List ExternAddr} (hm : ModuleOk m ixt xt)
    (hx : List.Forall₂ (ExternAddrOk s) xas ixt) (hb : SegBounded m) :
    ∃ c : Config H, (∀ host : HostSemantics H, Instantiate P host s m xas c) ∧
      HostFree c.store := by
  obtain ⟨C', hglobals, helems, hf, hg⟩ := ctx_of_moduleOk_imp hm
  obtain ⟨vs, hvs⟩ : ∃ vs, List.Forall₂ (fun (g : Global) (v : Val) =>
      constExpr? s (fi s m xas).module g.init = some v) m.globals vs :=
    forall₂_of_exists fun g hg' => const_denotes_imp hx (hglobals g hg') hf hg
  obtain ⟨rss, hrss⟩ : ∃ rss, List.Forall₂ (fun (e : Elem) (rs : List Ref) =>
      List.Forall₂ (fun (ex : Expr) (r : Ref) =>
        constExpr? s (fi s m xas).module ex = some (Val.ref r)) e.init rs)
      m.elems rss :=
    forall₂_of_exists fun e he =>
      forall₂_of_exists fun ex hex => const_ref_denotes_imp hs hx (helems e he ex hex) hf hg
  obtain ⟨⟨s', mi⟩, hal⟩ := allocModule_some_imp hm hx hvs.length_eq hrss.length_eq
  refine ⟨⟨s', { module := mi }, expression (runElems m ++ runDatas m ++
    (match m.start with | some x => [Instr.call x] | none => []))⟩, fun host => ?_,
    hostFree_allocModule hal hfree⟩
  refine ⟨⟨ixt, xt, hm, hx⟩, hb, vs, rss, s', mi, ?_, ?_, hal, rfl⟩
  · exact hvs.imp fun _ _ h => evalExpr_of_constExpr? h
  · exact hrss.imp fun _ _ h => h.imp fun _ _ h => evalExpr_of_constExpr? h

end Silmaril.Proofs.Wasm.Models.V2CoreInstImp
