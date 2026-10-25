module

public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Execution.Core.Instantiation
public import Silmaril.Wasm.Validation.Instructions.Properties
public import Silmaril.Wasm.Validation.Instructions.RangeRefs
public import Silmaril.Wasm.Execution.Core.Soundness.InstantiationAlloc

@[expose] public section

/-! # Typing of invocation and instantiation (helpers for `invoke_ok`, `Instantiate.ok`)

* `AdminsOk.single'` — a single administrative instruction, given its result type is valid;
* `Module.initCode` — the source code run by `$instantiate` (element segments, data
  segments, start call), and `Module.initCode_ok` — it is typed in the module context;
* `InstrsOk.rangeRefs` — code typed in a context types in the context whose `REFS`
  are all function indices (the `REFS` of `Moduleinst_ok`);
* `Instantiate.alloc_ok` — the allocated store is valid and the new module instance
  is typed against the module context.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

@[simp] theorem Context.initLocals_nil (C : Context) : C.initLocals [] = C := rfl

/-- A single administrative instruction (`Instrs_ok2/seq` + `empty` + `frame`). -/
theorem AdminsOk.single' {s : Store H} {C : Context} {a : Admin} {t₁ t₂ : List CValType}
    (h : AdminOk s C a (.plain t₁ t₂)) (hok : ResultOk C.toTypeCtx t₂) :
    AdminsOk s C [a] (.plain t₁ t₂) := by
  have h0 : AdminsOk s C [] (.plain t₂ t₂) := by
    simpa using (AdminsOk.frame (ts := t₂) (AdminsOk.nil (s := s) (C := C)) hok)
  simpa using AdminsOk.cons (xs₁ := []) h (by simp) h0

/-! Local copies of `GroupOk2.get` / `TyOk.def_congr` (`Validation/Subtyping/Properties.lean`,
which currently does not build on the integration tip: duplicate `Ty.toList_subst`). -/

theorem GroupOk2.get' {Δ : TypeCtx} : ∀ (subs : Ty (.list .sub)) {m k : Nat} {st : CSubType},
    GroupOk2 Δ (.group subs) m → subs.toList[k]? = some st → SubOk2 Δ st (m + k)
  | .nil, _, _, _, _, h => by simp at h
  | .cons s l, m, 0, st, hg, h => by
      cases hg with
      | cons h1 _ =>
        simp only [Ty.toList_cons, List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        simpa using h1
  | .cons s l, m, k + 1, st, hg, h => by
      cases hg with
      | cons _ h2 =>
        have := GroupOk2.get' l h2 (by simpa using h)
        rwa [show m + 1 + k = m + (k + 1) by omega] at this

theorem TyOk.def_congr' {Δ₁ Δ₂ : TypeCtx} (ht : Δ₁.types = Δ₂.types) {d : DefType}
    (h : TyOk Δ₁ d) : TyOk Δ₂ d := by
  cases h with
  | defn hg hi =>
    have e : ∀ X, Δ₁.withRecs X = Δ₂.withRecs X := by
      intro X; cases Δ₁; cases Δ₂; simp_all [TypeCtx.withRecs]
    exact .defn (e _ ▸ hg) hi

/-- Substituting valid type uses for the `REC` variables of a context. -/
theorem TyOk.subst_recs {Δ Δ' : TypeCtx} (hT : Δ'.types = Δ.types) {σ : Subst}
    (hidx : ∀ x, σ (.idx x) = none)
    (hrec : ∀ i st, Δ'.recs[i]? = some st → ∃ u, σ (.recv i) = some u ∧ TyOk Δ u) :
    ∀ {k : TKind} (t : Ty k), TyOk Δ' t → TyOk Δ (t.subst σ) := by
  intro k t
  induction t with
  | idx x =>
    intro h; cases h with
    | idx hx => simp only [Ty.subst, hidx, Option.getD_none]; exact .idx (hT ▸ hx)
  | recv i =>
    intro h; cases h with
    | recv hx =>
      obtain ⟨u, hu, hok⟩ := hrec _ _ hx
      simp only [Ty.subst, hu, Option.getD_some]; exact hok
  | defn g i ih =>
    intro h; cases h with
    | @defn _ subs _ hg hi =>
      have : subs.subst σ.minusRecs = subs := by
        rw [Ty.subst_of_none]
        intro v; cases v <;> simp [Subst.minusRecs, hidx]
      simp only [Ty.subst, this]
      exact TyOk.def_congr' hT (.defn hg hi)
  | _ =>
    intro h
    cases h <;> simp only [Ty.subst] <;> constructor <;> simp_all

theorem TyOk.toList_forall {Δ : TypeCtx} {k : TKind} :
    ∀ {l : Ty (.list k)}, TyOk Δ l → ∀ t ∈ l.toList, TyOk Δ t
  | .nil, _ => by simp
  | .cons a l, h => by
    cases h with
    | cons ha hl =>
      intro t ht
      simp only [Ty.toList_cons, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact ha
      · exact TyOk.toList_forall hl t ht

/-- The parameter and result types of a valid function type are valid.
(Metatheory of expansion: substitution preserves `TyOk`.) -/
theorem Expand.resultOk {d : DefType} {ps rs : Ty (.list .val)} (hd : TyOk {} d)
    (he : Expand d (.func ps rs)) : ResultOk {} ps.toList ∧ ResultOk {} rs.toList := by
  obtain ⟨hu⟩ := he
  cases hd with
  | @defn _ subs i hg hi =>
    simp only [unrolldt, unrollrt, Ty.subs] at hu
    rw [Ty.toList_subst, List.getElem?_map] at hu
    cases hst : subs.toList[i]? with
    | none => simp [hst] at hu
    | some st =>
      rw [hst] at hu
      simp only [Option.map_some, Option.some.injEq] at hu
      have hso := GroupOk2.get' subs hg hst
      cases st with
      | sub fin0 sups0 ct0 =>
        simp only [Ty.subst, Ty.sub.injEq] at hu
        obtain ⟨-, -, hct⟩ := hu
        have hct0 : TyOk (({} : TypeCtx).withRecs subs.toList) ct0 := by
          cases hso <;> assumption
        have hok : TyOk ({} : TypeCtx) (Ty.func ps rs) := by
          rw [← hct]
          refine TyOk.subst_recs (Δ := {}) (Δ' := ({} : TypeCtx).withRecs subs.toList) rfl ?_ ?_ ct0 hct0
          · intro x; rfl
          · intro j st hj
            have hj' : j < subs.length := by
              have := (List.getElem?_eq_some_iff.1 hj).1
              simpa [TypeCtx.withRecs, Ty.length] using this
            exact ⟨_, by simp [hj'], .dt (.defn hg hj')⟩
        cases hok with
        | func hp hr => exact ⟨TyOk.toList_forall hp, TyOk.toList_forall hr⟩

/-! ## The code run by `$instantiate` -/

/-- `instr_S?`. -/
def _root_.Silmaril.Wasm.Module.startCode (m : Module) : List Instr :=
  match m.start with
  | some x => [.call x]
  | none => []

/-- `instr_E* instr_D* instr_S?`. -/
def _root_.Silmaril.Wasm.Module.initCode (m : Module) : List Instr :=
  ((List.range m.elems.length).zip m.elems |>.flatMap fun (i, e) => runElem i e) ++
    ((List.range m.data.length).zip m.data |>.flatMap fun (i, d) => runData i d) ++
    m.startCode

theorem _root_.Silmaril.Wasm.Module.expression_initCode (m : Module) :
    expression m.initCode =
      expression ((List.range m.elems.length).zip m.elems |>.flatMap fun (i, e) => runElem i e) ++
      expression ((List.range m.data.length).zip m.data |>.flatMap fun (i, d) => runData i d) ++
      (match m.start with | some x => [.plain (.call x)] | none => []) := by
  simp only [Module.initCode, expression, List.map_append]
  congr 1
  unfold Module.startCode
  cases m.start <;> rfl

/-- Sequencing code of empty type. -/
theorem InstrsOk.flatMap_nil {C : Context} {α : Type} {l : List α} {f : α → List Instr}
    (h : ∀ x ∈ l, InstrsOk C (f x) (.plain [] [])) : InstrsOk C (l.flatMap f) (.plain [] []) := by
  induction l with
  | nil => exact InstrsOk.nil
  | cons x xs ih =>
    rw [List.flatMap_cons]
    simpa using InstrsOk.append (xs₁ := []) (xs₂ := []) (h x (by simp)) (by simp)
      (ih fun y hy => h y (by simp [hy]))

theorem InstrsOk.append_nil_nil {C : Context} {is₁ is₂ : List Instr}
    (h₁ : InstrsOk C is₁ (.plain [] [])) (h₂ : InstrsOk C is₂ (.plain [] [])) :
    InstrsOk C (is₁ ++ is₂) (.plain [] []) := by
  simpa using InstrsOk.append (xs₁ := []) (xs₂ := []) h₁ (by simp) h₂

theorem InstrsOk.append_plain {C : Context} {is₁ is₂ : List Instr} {t₁ t₂ t₃ : List CValType}
    (h₁ : InstrsOk C is₁ (.plain t₁ t₂)) (h₂ : InstrsOk C is₂ (.plain t₂ t₃)) :
    InstrsOk C (is₁ ++ is₂) (.plain t₁ t₃) := by
  simpa using InstrsOk.append (xs₁ := []) (xs₂ := []) h₁ (by simp) h₂

/-- A single instruction, framed. -/
theorem InstrsOk.single_frame {C : Context} {i : Instr} {ts t₁ t₂ : List CValType}
    (h : InstrOk C i (.plain t₁ t₂)) (hok : ResultOk C.toTypeCtx ts) :
    InstrsOk C [i] (.plain (ts ++ t₁) (ts ++ t₂)) :=
  InstrsOk.frame (InstrsOk.single h (by simp)) hok

theorem mem_zip_range {α : Type} {l : List α} {i : Nat} {x : α}
    (h : (i, x) ∈ (List.range l.length).zip l) : l[i]? = some x := by
  rw [List.mem_iff_getElem?] at h
  obtain ⟨j, hj⟩ := h
  rw [List.getElem?_zip_eq_some] at hj
  obtain ⟨h₁, h₂⟩ := hj
  rw [List.getElem?_range] at h₁
  · simp at h₁; subst h₁; exact h₂
  · have := (List.getElem?_eq_some_iff.mp h₂).1; exact this

/-- The tail `(CONST I32 0) (CONST I32 n) init drop` of an active segment program. -/
theorem InstrsOk.segTail {C : Context} {a : AddrType} {n : BitVec 32} {init drp : Instr}
    (hinit : InstrOk C init (.plain [a.valType, .i32, .i32] []))
    (hdrop : InstrOk C drp (.plain [] [])) :
    InstrsOk C [.intConst .i32 0, .intConst .i32 n, init, drp] (.plain [a.valType] []) := by
  have ha : TyOk C.toTypeCtx a.valType := by cases a <;> exact TyOk.num _
  have hi : TyOk C.toTypeCtx Ty.i32 := TyOk.num _
  have h₁ : InstrsOk C [.intConst .i32 0] (.plain [a.valType] [a.valType, .i32]) := by
    exact InstrsOk.single_frame (ts := [a.valType])
      (InstrOk.numeric (NumericInstrOk.intConst (C := C) .i32 0)) (by simp [ResultOk, ha])
  have h₂ : InstrsOk C [.intConst .i32 n] (.plain [a.valType, .i32] [a.valType, .i32, .i32]) := by
    exact InstrsOk.single_frame (ts := [a.valType, .i32])
      (InstrOk.numeric (NumericInstrOk.intConst (C := C) .i32 n)) (by simp [ResultOk, ha, hi])
  have h₃ : InstrsOk C [init] (.plain [a.valType, .i32, .i32] []) := InstrsOk.single hinit (by simp)
  have h₄ : InstrsOk C [drp] (.plain [] []) := InstrsOk.single hdrop (by simp)
  exact InstrsOk.append_plain (is₁ := [_]) h₁
    (InstrsOk.append_plain (is₁ := [_]) h₂ (InstrsOk.append_plain (is₁ := [_]) h₃ h₄))

theorem runElem_ok {C : Context} {i : Nat} {e : Elem} {rt : CRefType} (hi : i < 2 ^ 32)
    (hC : C.elems[i]? = some rt) (he : ElemOk C e rt) :
    InstrsOk C (runElem i e) (.plain [] []) := by
  obtain ⟨-, -, -, hmode⟩ := he
  have hx : C.elems[(⟨Fin.ofNat (2 ^ 32) i⟩ : ElemIdx).toNat]? = some rt := by
    have : (⟨Fin.ofNat (2 ^ 32) i⟩ : ElemIdx).toNat = i := by
      simp only [Idx.toNat, Fin.val_ofNat]; exact Nat.mod_eq_of_lt hi
    rw [this]; exact hC
  unfold runElem
  cases hm : e.mode with
  | passive => exact InstrsOk.nil
  | declarative => exact InstrsOk.single (.table (.elemDrop hx)) (by simp)
  | active y off =>
    have hmode' : ElemModeOk C (.active y off) rt := hm ▸ hmode
    cases hmode' with
    | active htab hs ho =>
    exact InstrsOk.append_plain ho.typed
      (InstrsOk.segTail (.table (.tableInit htab hx hs)) (.table (.elemDrop hx)))

theorem runData_ok {C : Context} {i : Nat} {d : Data}
    (hC : i < C.datas.length) (hd : DataOk C d) :
    InstrsOk C (runData i d) (.plain [] []) := by
  have hx : C.datas[(⟨Fin.ofNat (2 ^ 32) i⟩ : DataIdx).toNat]? = some () := by
    have : (⟨Fin.ofNat (2 ^ 32) i⟩ : DataIdx).toNat < C.datas.length := by
      simp only [Idx.toNat, Fin.val_ofNat]
      exact lt_of_le_of_lt (Nat.mod_le _ _) hC
    rw [List.getElem?_eq_getElem this]
  unfold runData
  cases hmode : d.mode with
  | passive => exact InstrsOk.nil
  | active y off =>
    have hm : DataModeOk C (.active y off) := hmode ▸ hd
    cases hm with
    | active hmem ho =>
    exact InstrsOk.append_plain ho.typed
      (InstrsOk.segTail (.memory (.memoryInit hmem hx)) (.memory (.dataDrop hx)))

/-- The code run by `$instantiate` is typed in the module context. -/
theorem _root_.Silmaril.Wasm.Module.initCode_ok {C : Context} {m : Module} {rts : List CRefType}
    (helems : List.Forall₂ (ElemOk C) m.elems rts) (hCe : C.elems = rts)
    (hdata : ∀ d ∈ m.data, DataOk C d) (hCd : C.datas = m.data.map fun _ => ())
    (hstart : ∀ x, m.start = some x → StartOk C x) (hbound : m.elems.length ≤ 2 ^ 32) :
    InstrsOk C m.initCode (.plain [] []) := by
  unfold Module.initCode
  refine InstrsOk.append_nil_nil (InstrsOk.append_nil_nil ?_ ?_) ?_
  · refine InstrsOk.flatMap_nil ?_
    rintro ⟨i, e⟩ hie
    have hget := mem_zip_range hie
    have hi : i < m.elems.length := (List.getElem?_eq_some_iff.mp hget).1
    obtain ⟨rt, hrt, hok⟩ : ∃ rt, rts[i]? = some rt ∧ ElemOk C e rt := by
      have hlen := helems.length_eq
      have hi' : i < rts.length := hlen ▸ hi
      refine ⟨rts[i], by simp, ?_⟩
      have := List.forall₂_iff_get.mp helems
      have h2 := this.2 i hi hi'
      simp only [List.get_eq_getElem] at h2
      rwa [(List.getElem?_eq_some_iff.mp hget).2] at h2
    exact runElem_ok (by omega) (hCe ▸ hrt) hok
  · refine InstrsOk.flatMap_nil ?_
    rintro ⟨i, d⟩ hid
    have hget := mem_zip_range hid
    have hi : i < m.data.length := (List.getElem?_eq_some_iff.mp hget).1
    exact runData_ok (by rw [hCd]; simpa using hi) (hdata d (List.mem_of_getElem? hget))
  · unfold Module.startCode
    cases hs : m.start with
    | none => exact InstrsOk.nil
    | some x =>
      obtain ⟨d, hd, hexp⟩ := hstart x hs
      exact InstrsOk.single (.call hd hexp) (by simp)

/-- Weakening `REFS` to all function indices: `ref.func x` already requires
`C.FUNCS[x]` to exist. -/
theorem InstrsOk.rangeRefs {C : Context} {is : List Instr} {it : InstrType}
    (h : InstrsOk C is it) : InstrsOk { C with refs := List.range C.funcs.length } is it :=
  Validation.InstrsOk.rangeRefs h

/-! ## Allocation -/

/-- The store produced by `$instantiate` is valid and the new module instance is
typed against the module context (with `REFS` all function indices). The
premises are those of `Module_ok`. This is the forward-reference argument of
`$instantiate`: the initializers are evaluated in `moduleinst_0`, whose function
addresses are only allocated by `$allocmodule`. -/
theorem Instantiate.alloc_ok {P : Profile} {host : HostSemantics H} {s : Store H} {m : Module}
    {xas : List ExternAddr} (hs : StoreOk s)
    {dts : List DefType} {xtI : List CExternType} {jts : List DefType}
    {gts : List CGlobalType} {tts : List CTableType} {fdts : List DefType}
    {rts : List CRefType} {xtE : List CExternType} {C' C : Context}
    (htypes : TypesOk {} m.types dts)
    (himports : List.Forall₂ (ImportOk { types := dts }) m.imports xtI)
    (hC' : C' = { types := dts, globals := CExternType.globals xtI,
                  funcs := CExternType.funcs xtI ++ fdts, refs := funcIdxNonFuncs m })
    (hC : C = { C' with
                tags := CExternType.tags xtI ++ jts, globals := C'.globals ++ gts,
                mems := CExternType.mems xtI ++ m.memories,
                tables := CExternType.tables xtI ++ tts,
                datas := m.data.map fun _ => (), elems := rts })
    (htags : List.Forall₂ (TagOk C') m.tags jts)
    (hglobals : GlobalsOk C' m.globals gts)
    (hmems : ∀ mt ∈ m.memories, MemOk mt)
    (htables : List.Forall₂ (TableOk C') m.tables tts)
    (hfuncs : List.Forall₂ (FuncOk C) m.funcs fdts)
    (_hdata : ∀ d ∈ m.data, DataOk C d)
    (helems : List.Forall₂ (ElemOk C) m.elems rts)
    (_hstart : ∀ x, m.start = some x → StartOk C x)
    (hexports : List.Forall₂ (ExportOk C) m.exports xtE)
    (hdisjoint : (m.exports.map Export.name).Nodup)
    (hxas : List.Forall₂ (ExternAddrOk s) xas xtI)
    {s₁ s₂ s₃ s₄ : Store H} {f₁ f₂ f₃ : Frame} {valsG : List Val} {refsT : List Ref}
    {refsE : List (List Ref)} {mi : ModuleInst}
    (hg : EvalGlobals P host s ⟨[], ModuleInst.initial s m xas⟩
      (m.globals.map fun g => ⟨g.type.mutability,
        (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩)
      (m.globals.map Global.init) s₁ f₁ valsG)
    (ht : EvalExprs P host s₁ f₁ (m.tables.map Table.init) s₂ f₂ refsT)
    (he : EvalExprss P host s₂ f₂ (m.elems.map Elem.init) s₃ f₃ refsE)
    (ha : allocModule? s₃ m xas valsG refsT refsE = some (s₄, mi)) :
    StoreOk s₄ ∧ ModuleInstOk s₄ mi { C with refs := List.range C.funcs.length } :=
  Instantiate.alloc_ok_aux hs htypes himports hC' hC htags hglobals hmems htables hfuncs helems
    hexports hdisjoint hxas hg ht he ha

end Silmaril.Wasm.Execution.Core
