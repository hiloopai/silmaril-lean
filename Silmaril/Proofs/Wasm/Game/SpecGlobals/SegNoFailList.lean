module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.SegNoFailSeg
public import Silmaril.Proofs.Wasm.Game.SpecGlobals.InstGen

/-!
# Segment initialisation of a validated module never fails

`segments_not_fail`: for a validated module (`ModuleOk m ⟨xtI, xtE⟩`) instantiated by the
specification's `prepare?` into a well-typed store against typed addresses, silmaril-lean's
trap-aware direct segment initialisation `initSegmentsT?` of the prepared configuration is never
`.fail`: it initialises every segment or traps. The prepared store is well typed and its module
instance typed against the module context (`Instantiate.alloc_ok`); every segment then succeeds
or traps (`elemSeg_some_or_trap`, `dataSeg_some_or_trap`) and keeps the invariant
(`elemSeg_inv`, `dataSeg_inv`).

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.SingleThreaded

/-! ## Weakening the context's references -/

/-- The module context with all function indices as references. -/
abbrev ctxRR (C : Context) : Context := { C with refs := List.range C.funcs.length }

theorem instrConst_rr {C : Context} {i : Instr} (h : InstrConst C i) : InstrConst (ctxRR C) i := by
  cases h with
  | globalGet h => exact .globalGet h
  | binop hop => exact .binop hop
  | _ => constructor

theorem exprOkConst_rr {C : Context} {e : Expr} {t : CValType} (h : ExprOkConst C e t) :
    ExprOkConst (ctxRR C) e t :=
  ⟨Execution.Core.InstrsOk.rangeRefs h.typed, fun i hi => instrConst_rr (h.const i hi)⟩

theorem elemModeOk_rr {C : Context} {md : ElemMode} {rt : CRefType} (h : ElemModeOk C md rt) :
    ElemModeOk (ctxRR C) md rt := by
  cases h with
  | passive => exact .passive
  | declarative => exact .declarative
  | active htab hs ho => exact .active htab hs (exprOkConst_rr ho)

theorem elemOk_rr {C : Context} {e : Elem} {rt : CRefType} (h : ElemOk C e rt) :
    ElemOk (ctxRR C) e rt :=
  ⟨h.1, h.2.1, fun ex hex => exprOkConst_rr (h.2.2.1 ex hex), elemModeOk_rr h.2.2.2⟩

theorem dataModeOk_rr {C : Context} {md : DataMode} (h : DataModeOk C md) :
    DataModeOk (ctxRR C) md := by
  cases h with
  | passive => exact .passive
  | active hmem ho => exact .active hmem (exprOkConst_rr ho)

theorem dataOk_rr {C : Context} {d : Data} (h : DataOk C d) : DataOk (ctxRR C) d :=
  dataModeOk_rr h

/-! ## Lists of segments -/

variable {f : Frame} {C : Context}

theorem elemSegT_of_some {s s₁ : Store Nat} {k : Nat} {e : Elem}
    (h : initElemSeg? evalConst? s f k e = some s₁) : initElemSegT? evalConst? s f k e = .ok s₁ := by
  simp only [initElemSegT?, h]

theorem dataSegT_of_some {s s₁ : Store Nat} {k : Nat} {d : Data}
    (h : initDataSeg? evalConst? s f k d = some s₁) : initDataSegT? evalConst? s f k d = .ok s₁ := by
  simp only [initDataSegT?, h]

/-- One element segment: initialised (with the invariant) or trapped. -/
theorem elemSegT_cases {s : Store Nat} {k : Nat} {e : Elem} {rt : CRefType} (hs : StoreOk s)
    (hf : FrameOk s f C) (hk : k < 2 ^ 32) (hCe : C.elems[k]? = some rt) (he : ElemOk C e rt) :
    (∃ s₁, initElemSegT? evalConst? s f k e = .ok s₁ ∧ StoreOk s₁ ∧ FrameOk s₁ f C) ∨
      ∃ s₁, initElemSegT? evalConst? s f k e = .trap s₁ := by
  cases h : initElemSeg? evalConst? s f k e with
  | some s₁ => exact .inl ⟨s₁, elemSegT_of_some h, elemSeg_inv hs hf hk hCe he h⟩
  | none =>
    rcases elemSeg_some_or_trap hs hf hk hCe he with ⟨s₁, h₁⟩ | ⟨s₁, h₁⟩
    · rw [h] at h₁
      cases h₁
    · exact .inr ⟨s₁, by simp only [initElemSegT?, h, h₁]⟩

/-- One data segment: initialised (with the invariant) or trapped. -/
theorem dataSegT_cases {s : Store Nat} {k : Nat} {d : Data} (hs : StoreOk s) (hf : FrameOk s f C)
    (hk : k < 2 ^ 32) (hCd : k < C.datas.length) (hd : DataOk C d) :
    (∃ s₁, initDataSegT? evalConst? s f k d = .ok s₁ ∧ StoreOk s₁ ∧ FrameOk s₁ f C) ∨
      ∃ s₁, initDataSegT? evalConst? s f k d = .trap s₁ := by
  cases h : initDataSeg? evalConst? s f k d with
  | some s₁ => exact .inl ⟨s₁, dataSegT_of_some h, dataSeg_inv hs hf hCd hd h⟩
  | none =>
    rcases dataSeg_some_or_trap hs hf hk hCd hd with ⟨s₁, h₁⟩ | ⟨s₁, h₁⟩
    · rw [h] at h₁
      cases h₁
    · exact .inr ⟨s₁, by simp only [initDataSegT?, h, h₁]⟩

/-- Validated element segments are initialised (keeping the invariant) or trap. -/
theorem elemList_cases : ∀ (l : List (Nat × Elem)) (s : Store Nat), StoreOk s → FrameOk s f C →
    (∀ p ∈ l, p.1 < 2 ^ 32 ∧ ∃ rt, C.elems[p.1]? = some rt ∧ ElemOk C p.2 rt) →
    (∃ s₁, initElemListT? evalConst? s f l = .ok s₁ ∧ StoreOk s₁ ∧ FrameOk s₁ f C) ∨
      ∃ s₁, initElemListT? evalConst? s f l = .trap s₁
  | [], s, hs, hf, _ => .inl ⟨s, rfl, hs, hf⟩
  | (k, e) :: l, s, hs, hf, hl => by
    obtain ⟨hk, rt, hCe, he⟩ := hl (k, e) List.mem_cons_self
    have hl' : ∀ p ∈ l, p.1 < 2 ^ 32 ∧ ∃ rt, C.elems[p.1]? = some rt ∧ ElemOk C p.2 rt :=
      fun p hp => hl p (List.mem_cons_of_mem _ hp)
    rcases elemSegT_cases hs hf hk hCe he with ⟨s₁, h₁, hs₁, hf₁⟩ | ⟨s₁, h₁⟩
    · have hrest := elemList_cases l s₁ hs₁ hf₁ hl'
      simpa only [initElemListT?, h₁] using hrest
    · exact .inr ⟨s₁, by simp only [initElemListT?, h₁]⟩

/-- Validated data segments are initialised or trap. -/
theorem dataList_cases : ∀ (l : List (Nat × Data)) (s : Store Nat), StoreOk s → FrameOk s f C →
    (∀ p ∈ l, p.1 < 2 ^ 32 ∧ p.1 < C.datas.length ∧ DataOk C p.2) →
    (∃ s₁, initDataListT? evalConst? s f l = .ok s₁) ∨
      ∃ s₁, initDataListT? evalConst? s f l = .trap s₁
  | [], s, _, _, _ => .inl ⟨s, rfl⟩
  | (k, d) :: l, s, hs, hf, hl => by
    obtain ⟨hk, hCd, hd⟩ := hl (k, d) List.mem_cons_self
    have hl' : ∀ p ∈ l, p.1 < 2 ^ 32 ∧ p.1 < C.datas.length ∧ DataOk C p.2 :=
      fun p hp => hl p (List.mem_cons_of_mem _ hp)
    rcases dataSegT_cases hs hf hk hCd hd with ⟨s₁, h₁, hs₁, hf₁⟩ | ⟨s₁, h₁⟩
    · have hrest := dataList_cases l s₁ hs₁ hf₁ hl'
      simpa only [initDataListT?, h₁] using hrest
    · exact .inr ⟨s₁, by simp only [initDataListT?, h₁]⟩

/-- **Validated segments never fail**: in a typed frame over a well-typed store, the direct
trap-aware initialisation of a module's segments succeeds or traps. -/
theorem initSegmentsT_not_fail {s : Store Nat} {m : Module} (hs : StoreOk s) (hf : FrameOk s f C)
    (he : ∀ p ∈ (List.range m.elems.length).zip m.elems,
      p.1 < 2 ^ 32 ∧ ∃ rt, C.elems[p.1]? = some rt ∧ ElemOk C p.2 rt)
    (hd : ∀ p ∈ (List.range m.data.length).zip m.data,
      p.1 < 2 ^ 32 ∧ p.1 < C.datas.length ∧ DataOk C p.2) :
    initSegmentsT? evalConst? s f m ≠ .fail := by
  rcases elemList_cases _ s hs hf he with ⟨s₁, h₁, hs₁, hf₁⟩ | ⟨s₁, h₁⟩
  · rcases dataList_cases _ s₁ hs₁ hf₁ hd with ⟨s₂, h₂⟩ | ⟨s₂, h₂⟩
    · simp only [initSegmentsT?, h₁, h₂, ne_eq, reduceCtorEq, not_false_eq_true]
    · simp only [initSegmentsT?, h₁, h₂, ne_eq, reduceCtorEq, not_false_eq_true]
  · simp only [initSegmentsT?, h₁, ne_eq, reduceCtorEq, not_false_eq_true]

/-! ## Validated modules -/

theorem withStart_frame (c : Config Nat) (st : Option FuncIdx) : (c.withStart st).frame = c.frame := by
  cases st <;> rfl

theorem withStart_store' (c : Config Nat) (st : Option FuncIdx) : (c.withStart st).store = c.store := by
  cases st <;> rfl

/-- The element segments of a validated module, indexed. -/
theorem elems_facts {C : Context} {m : Module} {rts : List CRefType}
    (helems : List.Forall₂ (ElemOk C) m.elems rts) (hCe : C.elems = rts)
    (hbound : m.elems.length ≤ 2 ^ 32) :
    ∀ p ∈ (List.range m.elems.length).zip m.elems,
      p.1 < 2 ^ 32 ∧ ∃ rt, (ctxRR C).elems[p.1]? = some rt ∧ ElemOk (ctxRR C) p.2 rt := by
  rintro ⟨i, e⟩ hie
  have hget : m.elems[i]? = some e := mem_zip_range hie
  have hi : i < m.elems.length := (List.getElem?_eq_some_iff.mp hget).1
  have hi' : i < rts.length := helems.length_eq ▸ hi
  have h2 : ElemOk C (m.elems[i]) (rts[i]) := by
    have h := (List.forall₂_iff_get.mp helems).2 i hi hi'
    simpa only [List.get_eq_getElem] using h
  have he : m.elems[i] = e := (List.getElem?_eq_some_iff.mp hget).2
  refine ⟨by omega, rts[i], ?_, ?_⟩
  · show C.elems[i]? = some rts[i]
    rw [hCe]
    exact List.getElem?_eq_getElem hi'
  · rw [← he]
    exact elemOk_rr h2

/-- The data segments of a validated module, indexed. -/
theorem data_facts {C : Context} {m : Module} (hdata : ∀ d ∈ m.data, DataOk C d)
    (hCd : C.datas = m.data.map fun _ => ()) (hbound : m.data.length ≤ 2 ^ 32) :
    ∀ p ∈ (List.range m.data.length).zip m.data,
      p.1 < 2 ^ 32 ∧ p.1 < (ctxRR C).datas.length ∧ DataOk (ctxRR C) p.2 := by
  rintro ⟨i, d⟩ hid
  have hget : m.data[i]? = some d := mem_zip_range hid
  have hi : i < m.data.length := (List.getElem?_eq_some_iff.mp hget).1
  have hlen : (ctxRR C).datas.length = m.data.length := by
    show C.datas.length = _
    rw [hCd, List.length_map]
  exact ⟨by omega, by rw [hlen]; exact hi, dataOk_rr (hdata d (List.mem_of_getElem? hget))⟩

/-- **Segment initialisation of a validated module never fails**: the trap-aware direct
initialisation of the configuration the specification prepares succeeds or traps. -/
theorem prepare_segments_not_fail {s : Store Nat} {m : Module} {xas : List ExternAddr}
    {xtI xtE : List CExternType} {c : Config Nat} {st : Option FuncIdx}
    (hm : ModuleOk m ⟨xtI, xtE⟩) (hs : StoreOk s) (hxas : List.Forall₂ (ExternAddrOk s) xas xtI)
    (hp : prepare? evalConst? s m xas = some (c, st)) :
    initSegmentsT? evalConst? c.store c.frame m ≠ .fail := by
  have hi := (prepare?_sound (P := profile neverFail) (host := divHost (H := Nat))
    evalConst?_evalSound hp ⟨xtE, xtI, hm, hxas⟩).2
  obtain ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, valsG, refsT, refsE, mi, hg, ht, he, ha, hc⟩ := hi.run
  have hcs : c.store = s₄ := by rw [← withStart_store' c st, hc]
  have hcf : c.frame = { module := mi } := by rw [← withStart_frame c st, hc]
  cases hm with
  | mk htypes himports hC' hC htags hglobals hmems htables hfuncs hdata helems hstart
      hexports hdisjoint =>
    rename_i C' C
    obtain ⟨hs₄, hmi⟩ := Instantiate.alloc_ok hs htypes himports hC' hC htags hglobals hmems
      htables hfuncs hdata helems hstart hexports hdisjoint hxas hg ht he ha
    have hf : FrameOk s₄ { module := mi } (ctxRR C) := ⟨ctxRR C, [], hmi, .nil, by simp⟩
    have hCd : C.datas = m.data.map fun _ => () := by rw [hC]
    rw [hcs, hcf]
    exact initSegmentsT_not_fail hs₄ hf (elems_facts helems (by rw [hC]) hi.bounded.1)
      (data_facts hdata hCd hi.bounded.2.1)

end Silmaril.Proofs.Wasm.Game.SpecGlobals
