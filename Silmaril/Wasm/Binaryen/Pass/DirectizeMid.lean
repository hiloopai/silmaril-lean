module

public import Silmaril.Wasm.Binaryen.Pass.DirectizePre
public import Silmaril.Wasm.Binaryen.Pass.DirectizeFrozen
public import Silmaril.Wasm.Binaryen.Pass.DirectizeCount
public import Silmaril.Wasm.Binaryen.Pass.DirectizeCast
public import Silmaril.Wasm.Binaryen.Pass.DirectizeRewrite
public import Silmaril.Wasm.Binaryen.Pass.DirectizeSlot
public import Silmaril.Wasm.Binaryen.Pass.DirectizeEval
public import Silmaril.Wasm.Binaryen.GcProfile
public import Silmaril.Wasm.Execution.Core.Soundness.ConstEval
public import Silmaril.Wasm.Execution.Core.Soundness.InstantiationAlloc

@[expose] public section

/-! # Directize: the invariant after the element segments

For a module that passes Directize's actual entry guards (`frozen`, `elemsOk`,
`i32Only` and its data guard), every instantiation configuration corresponds to the
rewritten module at any numerical profile (`pre_inst_profile`): after the element segments the slot of every site holds its callee and the
callee has the call's type (`DInv`), and no code that can run writes a site's table
(`Frozen`).
-/

namespace Silmaril.Wasm.Binaryen

namespace DirectizeMid

open Execution.Core Validation Numerics SingleThreaded ElemInit DirectizeInit Directize

variable {H : Type}

/-- The type indices Directize reads. -/
def tysOf (m : BModule) : List TypeIdx :=
  Exe.funcTypeIdxs { m.base with funcs := m.funcs.map fun f => ⟨f.type, [], []⟩ }

theorem i32Only_constSeg {m : BModule} (h : i32Only m = true)
    {e : Elem} (he : e ∈ m.base.elems) : ConstSeg e := by
  unfold i32Only at h
  simp only [Bool.and_eq_true] at h
  have h := List.all_eq_true.mp h.1.2 e he
  intro y off hm
  rw [hm] at h
  split at h
  · rename_i o heq; cases heq; exact ⟨o, rfl⟩
  · cases h
  · rename_i hcontra
    exact False.elim (hcontra y off rfl)

theorem i32Only_init {m : BModule} (h : i32Only m = true)
    {e : Elem} (he : e ∈ m.base.elems) : ∀ x ∈ e.init, ∃ g, x = [.refFunc g] := by
  intro x hx
  unfold i32Only at h
  simp only [Bool.and_eq_true] at h
  have := List.all_eq_true.mp (List.all_eq_true.mp h.2 e he) x hx
  split at this
  · exact ⟨_, rfl⟩
  · cases this

theorem pairwise_zip_range {α : Type _} (l : List α) :
    ((List.range l.length).zip l).Pairwise (fun p q => p.1 ≠ q.1) := by
  have h : ((List.range l.length).zip l).map Prod.fst = List.range l.length :=
    List.map_fst_zip (by simp)
  have hn := List.nodup_range (n := l.length)
  rw [← h] at hn
  exact List.pairwise_map.mp hn

theorem mem_zip_range {α : Type _} {l : List α} {p : Nat × α} (h : p ∈ (List.range l.length).zip l) :
    p.1 < l.length ∧ l[p.1]? = some p.2 := by
  obtain ⟨i, x⟩ := p
  rw [List.mem_iff_getElem?] at h
  obtain ⟨j, hj⟩ := h
  rw [List.getElem?_zip_eq_some] at hj
  obtain ⟨h1, h2⟩ := hj
  rw [List.getElem?_range (by have := (List.getElem?_eq_some_iff.mp h2).1; omega)] at h1
  cases h1
  exact ⟨(List.getElem?_eq_some_iff.mp h2).1, h2⟩

theorem inGcProfile_elems {m : BModule} (h : m.inGcProfile = true) :
    ∀ e ∈ m.base.elems, gcElem e = true := by
  unfold BModule.inGcProfile at h; simp only [Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.1.1.1.1.2

theorem inGcProfile_tables {m : BModule} (h : m.inGcProfile = true) :
    ∀ t ∈ m.base.tables, gcTable t = true := by
  unfold BModule.inGcProfile at h; simp only [Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.1.1.1.1.1.2

/-- The widened GC profile supplies `gcData`, while `pre_inst` gets its narrower
`profileData` premise from Directize's explicit entry guard. -/
theorem inGcProfile_data {m : BModule} (h : m.inGcProfile = true) :
    ∀ d ∈ m.base.data, gcData d = true := by
  unfold BModule.inGcProfile at h; simp only [Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.1.1.1.1.1.1.1.2

theorem frozen_imports {m : BModule} (h : frozen m = true) :
    m.base.imports.all (fun i => match i.type with | .table _ => false | _ => true) = true := by
  unfold frozen at h; simp only [Bool.and_eq_true] at h; exact h.1.1

theorem frozen_funcs {m : BModule} (h : frozen m = true) :
    ∀ f ∈ m.funcs, mutatesList f.body = false := by
  unfold frozen at h; simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at h
  intro f hf; simpa using h.2 f hf

theorem elemsOk_table {m : BModule} (h : elemsOk m = true) {e : Elem} (he : e ∈ m.base.elems)
    {y : TableIdx} {off : Expr} (hm : e.mode = .active y off) : y.toNat < m.base.tables.length := by
  have := List.all_eq_true.mp h e he
  rw [hm] at this
  simpa using this

theorem mapM_getElem? {α β : Type _} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ i : Nat, l'[i]? = (l[i]?).bind f
  | [], l', h, i => by simp at h; subst h; simp
  | a :: l, l', h, i => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨b, hb, l'', hl'', rfl⟩ := h
    cases i with
    | zero => simp [hb]
    | succ i => simpa using mapM_getElem? hl'' i

theorem mapM_length {α β : Type _} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l'.length = l.length
  | [], l', h => by simp at h; subst h; rfl
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨b, -, l'', hl'', rfl⟩ := h
    simp [mapM_length hl'']

section profile

variable {P : Profile}

/-- **The instantiations of a Directize module and of its rewrite correspond.** -/
theorem pre_inst_profile {m : BModule} (hfz : frozen m = true)
    (hel : elemsOk m = true) (h32 : i32Only m = true)
    (hdataProfile : m.base.data.all profileData = true) {s : Store H} {xas : List ExternAddr} {c c' : Config H}
    (hs : StoreOk s) (hI : Instantiate P closedHost s m.lower xas c) (hfr : c'.frame = c.frame)
    (hcode : c'.code = c.code)
    (hSR : DirSim.SR (siteOk m (tysOf m)) c.frame.module c.store c'.store) :
    DirSim.InitAligned P (siteOk m (tysOf m)) c.frame.module c c' := by
  have hcok := Instantiate.ok divHost_ok hs (Unwrap.instantiate_of_closed_unwrap divHost hI)
  have hs4 := ConfigOk.storeOk hcok
  obtain ⟨⟨xtE, xtI, hmt, hxas⟩, hbd, s₁, s₂, s₃, s₄, f₁, f₂, f₃, vG, rT, rE, mi, hG, hT, hE, hA,
    rfl⟩ := hI
  obtain ⟨st', fr', co'⟩ := c'
  simp only at hfr hcode hSR hs4 ⊢
  subst hfr hcode
  obtain ⟨Gs, hGs, rfl⟩ := hSR.cases
  rw [List.append_assoc]
  obtain ⟨tagTypes, funcTypes, xi, htt, hft, hxi, hmi, hs4eq⟩ := allocModule?_inv hA
  have hrE : rE.length = m.base.elems.length := by
    simpa [BModule.lower] using DirectizeEval.evalExprss_length hE
  have hrT : rT.length = m.base.tables.length := by
    simpa [BModule.lower] using DirectizeEval.evalExprs_length hT
  cases hmt with
  | mk htypes himports hC' hC htags hglobals hmems htables hfuncs hdata helems hstart hexports
      hdisjoint =>
  have hxT : ExternAddr.tables xas = [] :=
    DirectizeCount.externAddr_tables_nil himports hxas (frozen_imports hfz)
  have hsh := (initEval_ok hs htypes himports hC' hC htags hglobals htables hfuncs helems hxas hG
    hT hE).1
  have hmiT : mi.tables = List.range' s₃.tables.length m.base.tables.length := by
    rw [hmi]; simp [hxT, hrT, BModule.lower]
  have hmiE : mi.elems = List.range' s₃.elems.length m.base.elems.length := by
    rw [hmi]; simp [hrE, BModule.lower]
  have hs4T : s₄.tables.length = s₃.tables.length + m.base.tables.length := by
    rw [hs4eq]; simp [hrT, BModule.lower]
  have hs4E : s₄.elems.length = s₃.elems.length + m.base.elems.length := by
    rw [hs4eq]; simp [hrE, BModule.lower]
  refine DirectizePre.pre_of_segments_profile hGs ?_ ?_ ?_
  · intro p hp
    obtain ⟨-, hget⟩ := mem_zip_range hp
    exact i32Only_constSeg h32 (List.mem_of_getElem? hget)
  · intro p hp
    obtain ⟨hlt, hget⟩ := mem_zip_range hp
    have hlt' : p.1 < 2 ^ 32 := by have := hbd.1; simp [BModule.lower] at this hlt; omega
    refine ⟨⟨s₃.elems.length + p.1, s₄.elems[s₃.elems.length + p.1]'(by
      simp [BModule.lower] at hlt; omega), ?_⟩, fun y off hm => ?_⟩
    · have hk : Idx.toNat (⟨Fin.ofNat (2 ^ 32) p.1⟩ : ElemIdx) = p.1 := by
        show p.1 % 2 ^ 32 = p.1
        exact Nat.mod_eq_of_lt hlt'
      simp only [BModule.lower] at hlt
      have h4 : s₃.elems.length + p.1 < s₄.elems.length := by omega
      simp only [Store.elem?, hk, hmiE, List.getElem?_range' hlt, Nat.one_mul,
        Option.bind_eq_bind, List.getElem?_eq_getElem h4, Option.bind_some, Option.pure_def]
    · have hy : y.toNat < m.base.tables.length :=
        elemsOk_table hel (List.mem_of_getElem? (by simpa [BModule.lower] using hget)) hm
      have h4 : s₃.tables.length + y.toNat < s₄.tables.length := by omega
      exact ⟨s₃.tables.length + y.toNat, s₄.tables[s₃.tables.length + y.toNat], by
        simp only [Store.table?, hmiT, List.getElem?_range' hy, Nat.one_mul,
          Option.bind_eq_bind, List.getElem?_eq_getElem h4, Option.bind_some, Option.pure_def]⟩
  · intro s₅ h5 hf5
    have hnew : ∀ fi ∈ (funcTypes.zip m.lower.funcs).map (fun p => (⟨p.1, mi, .wasm p.2⟩ : FuncInst H)),
        ∀ code : Func, fi.code = .wasm code → ∀ W, TableFrozen.InstrsK W code.body := by
      intro fi hfi code hcode W
      obtain ⟨⟨d, fn⟩, hmem, rfl⟩ := List.mem_map.mp hfi
      simp only [FuncCode.wasm.injEq] at hcode
      subst hcode
      have hfn := (List.of_mem_zip hmem).2
      simp only [BModule.lower, List.mem_map] at hfn
      obtain ⟨bf, hbf, rfl⟩ := hfn
      exact DirectizeFrozen.lowerList_K (frozen_funcs hfz bf hbf)
    have hfs : s₅.funcs = s.funcs ++ (funcTypes.zip m.lower.funcs).map
        (fun p => (⟨p.1, mi, .wasm p.2⟩ : FuncInst H)) := by
      rw [hf5, hs4eq, ← hsh.funcs]
    refine ⟨?_, fun t k y fx hok ta hta => ⟨DirectizeFrozen.storeK_of hs ?_ hnew hfs, ?_⟩⟩
    · intro t k y fx hok
      unfold siteOk target? at hok
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hok
      obtain ⟨fn, hslot, fty, hfty, hif⟩ := hok
      split at hif
      swap
      · cases hif
      rename_i hcond
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
      obtain ⟨rfl, hge⟩ := hcond
      have hfx : fn = fx.toNat := (Idx.ofNat?_eq_some_iff _ _).mp hif
      subst hfx
      -- the table
      have htl : t.toNat < m.base.tables.length := by
        unfold slot? at hslot; split at hslot
        · assumption
        · cases hslot
      -- the callee
      have hnI : (ExternAddr.funcs xas).length = m.numImportedFuncs :=
        DirectizeCount.externAddr_funcs_length_eq himports hxas
      have hty : (tysOf m) = m.base.importedFunctions ++ m.funcs.map (·.type) := by
        simp [tysOf, Exe.funcTypeIdxs, Module.importedFunctions, Function.comp_def]
        rfl
      simp only [BModule.numImportedFuncs] at hge hnI
      rw [hty, List.getElem?_append_right hge] at hfty
      set g := fx.toNat - m.base.importedFunctions.length with hg
      have hfty' : (m.funcs.map (·.type))[g]? = some fty := hfty
      have hgl : g < m.funcs.length := by
        have := (List.getElem?_eq_some_iff.mp hfty').1; simpa using this
      have hmiF : mi.funcs[fx.toNat]? = some (s₃.funcs.length + g) := by
        rw [hmi]
        simp only
        rw [List.getElem?_append_right (by omega), hnI]
        simp only [BModule.lower, List.length_map, ← hg]
        rw [List.getElem?_map, List.getElem?_range hgl]
        rfl
      -- the table and its slot
      have hmiTt : mi.tables[t.toNat]? = some (s₃.tables.length + t.toNat) := by
        rw [hmiT, List.getElem?_range' htl, Nat.one_mul]
      have hT' : ∀ y' : TableIdx, mi.tables[y'.toNat]? = some (s₃.tables.length + t.toNat) ↔
          y'.toNat = t.toNat := by
        intro y'
        rw [hmiT]
        constructor
        · intro h
          rw [List.getElem?_eq_some_iff] at h
          obtain ⟨hl, he⟩ := h
          rw [List.getElem_range'] at he
          omega
        · intro h
          rw [h, List.getElem?_range' htl, Nat.one_mul]
      have hlen : ∀ ti, s₄.tables[s₃.tables.length + t.toNat]? = some ti →
          ti.refs.length ≤ 2 ^ 32 := by
        intro ti hti
        have hok4 := hs4.tables ti (List.mem_of_getElem? hti)
        have hmem : ti ∈ ((m.lower.tables.map fun t => (⟨t.type.address, t.type.limits,
            (liftRef t.type.element).substAll ((allocTypes m.lower.types).map .dt)⟩ : CTableType)).zip
            rT).map (fun p => (⟨p.1, List.replicate p.1.limits.min.val p.2⟩ : TableInst)) := by
          rw [hs4eq] at hti
          simp only at hti
          rw [List.getElem?_append_right (by omega)] at hti
          exact List.mem_of_getElem? hti
        obtain ⟨⟨tt', r'⟩, hp, rfl⟩ := List.mem_map.mp hmem
        obtain ⟨tt, htt, rfl⟩ := List.mem_map.mp (List.of_mem_zip hp).1
        have haddr : tt.type.address = .i32 := by
          have ht := h32
          unfold i32Only at ht
          simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at ht
          exact ht.1.1 tt (by simpa [BModule.lower] using htt)
        obtain ⟨⟨hv, -⟩, hl, -⟩ := hok4
        dsimp only at hv hl
        rw [haddr] at hv
        simp only [List.length_replicate] at hl ⊢
        have : (2 : Nat) ^ AddrType.i32.width - 1 < 2 ^ 32 := by decide
        have := hv.1
        omega
      have hseg : ∀ p ∈ (List.range m.lower.elems.length).zip m.lower.elems,
          SegOk s₄ { module := mi } (fun i => rE.getD i []) p (s₃.elems.length + p.1) := by
        intro p hp
        obtain ⟨hlt, hget⟩ := mem_zip_range hp
        have hlt' : p.1 < 2 ^ 32 := by have := hbd.1; omega
        have hk : Idx.toNat (ElemInit.eidx p.1) = p.1 := by
          show p.1 % 2 ^ 32 = p.1
          exact Nat.mod_eq_of_lt hlt'
        simp only [BModule.lower] at hlt
        refine ⟨i32Only_constSeg h32 (List.mem_of_getElem? hget),
          by rw [hk, hmiE, List.getElem?_range' hlt, Nat.one_mul], ?_,
          hbd.2.2.2 p.2 (List.mem_of_getElem? hget)⟩
        have hrl : p.1 < rE.length := by omega
        have hm' : (s₄.elems[s₃.elems.length + p.1]?).map ElemInst.refs = some rE[p.1] := by
          rw [hs4eq]
          simp [hrl, hlt, BModule.lower]
        obtain ⟨ei, hei, hrefs⟩ := Option.map_eq_some_iff.mp hm'
        exact ⟨ei, hei, by rw [hrefs]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrl]⟩
      have hpw : ((List.range m.lower.elems.length).zip m.lower.elems).Pairwise
          (fun p q => s₃.elems.length + p.1 ≠ s₃.elems.length + q.1) :=
        (pairwise_zip_range _).imp (fun h e => h (by omega))
      have hslotS := ElemInit.initElemList?_slot (evalConst?_constOffsets _)
        (fun i => s₃.elems.length + i) h5 hseg hpw hlen (k := k.toNat)
      -- the entries of the segments
      have hconstT : ∀ e ∈ m.lower.tables.map Table.init, ∀ i ∈ e, i.IsConstI := by
        intro e he i hi
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
        obtain ⟨tt, -, h⟩ := forall₂_mem_left' htables t ht
        exact (h.2.2.const i hi).isConstI
      obtain ⟨-, -, hff₁⟩ := EvalGlobals.shape hG (GlobalsOk.const hglobals)
      obtain ⟨-, rfl, -⟩ := EvalExprs.shape hT hconstT
      have hfm : f₂.module.funcs = mi.funcs := by
        rw [hff₁, hmi]
        simp [ModuleInst.initial, hsh.funcs]
      obtain ⟨-, -, hev⟩ := DirectizeEval.evalExprss_refFuncs hE (by
        intro es hes e he
        obtain ⟨el, hel, rfl⟩ := List.mem_map.mp hes
        exact i32Only_init h32 (by simpa [BModule.lower] using hel) e he)
      have hR : ∀ p ∈ (List.range m.base.elems.length).zip m.base.elems, ∀ (j : Nat) (g' : FuncIdx),
          p.2.init[j]? = some [Instr.refFunc g'] →
            (rE.getD p.1 [])[j]? = some (Ref.func ((mi.funcs[g'.toNat]?).getD 0)) := by
        intro p hp j g' hj
        obtain ⟨-, hget⟩ := mem_zip_range hp
        obtain ⟨a', ha', hr'⟩ := hev p.1 p.2.init (by simp [BModule.lower, hget]) j g' hj
        rw [hfm] at ha'
        rw [hr', ha']
        rfl
      have hfold := Directize.slot_of_slot? hslot (mi := mi) (R := fun i => rE.getD i [])
        (A := fun g => (mi.funcs[g]?).getD 0) hT' (le_refl _) hR
        (slotAt s₄ (s₃.tables.length + t.toNat) k.toNat)
      have hsl : slotAt s₅ (s₃.tables.length + t.toNat) k.toNat =
          some (.func (s₃.funcs.length + g)) := by
        rw [hslotS]
        simp only [hmiF, Option.getD_some] at hfold
        exact hfold
      unfold slotAt at hsl
      obtain ⟨ti, hti, hk⟩ := Option.bind_eq_some_iff.mp hsl
      -- the callee and its type
      have hlft : funcTypes.length = m.funcs.length := by
        simpa [BModule.lower] using mapM_length hft
      have hft' := mapM_getElem? hft g
      rw [List.getElem?_eq_getElem (show g < funcTypes.length by omega)] at hft'
      have hfl : m.lower.funcs[g]? = some ((m.funcs[g]'hgl).mapBody BExpr.lowerList) := by
        simp [BModule.lower, hgl]
      have hfty'' : (m.funcs[g]'hgl).type = fty := by
        simpa [hgl] using hfty'
      rw [hfl] at hft'
      simp only [Option.bind_some] at hft'
      have hdg : (allocTypes m.lower.types)[fty.toNat]? = some funcTypes[g] := by
        rw [← hfty'']; exact hft'.symm
      have hf4 : (s₄.funcs[s₃.funcs.length + g]?).map FuncInst.type = some funcTypes[g] := by
        rw [hs4eq]
        simp [hlft, hgl, BModule.lower]
      obtain ⟨fi, hfi, hfit⟩ := Option.map_eq_some_iff.mp hf4
      have hTy : TyOk {} fi.type := by
        cases hs4.funcs fi (List.mem_of_getElem? hfi) with
        | wasm hdt => exact hdt
        | host hdt => exact hdt
      refine ⟨s₃.funcs.length + g, s₃.tables.length + t.toNat, ti, hmiF, hmiTt, hti, hk,
        DirectizeCast.refOk_cast (by rw [hf5]; exact hfi) ?_ hTy,
        by rw [hf5]; exact (List.getElem?_eq_some_iff.mp hfi).1⟩
      rw [hmi]
      simp only
      rw [hfit]
      exact hdg
    · rw [hmiT, List.getElem?_eq_some_iff] at hta
      obtain ⟨hlt, rfl⟩ := hta
      rw [List.getElem_range', hsh.tables]
      omega
    · refine DirectizeFrozen.admsK_data (fun p hp => ?_) _ ?_
      · obtain ⟨-, hget⟩ := mem_zip_range hp
        exact List.all_eq_true.mp hdataProfile _
          (List.mem_of_getElem? (by simpa [BModule.lower] using hget))
      · intro a ha
        cases hst : m.lower.start with
        | none => rw [hst] at ha; cases ha
        | some x => rw [hst] at ha; simp at ha; exact ⟨x, ha⟩

end profile

/-- Retain the original deterministic theorem and its entry premises. -/
theorem pre_inst {o : GrowKind → Nat → Nat → Nat → Bool}
    {m : BModule} (_hprof : m.inGcProfile = true) (hfz : frozen m = true)
    (hel : elemsOk m = true) (h32 : i32Only m = true)
    (hdataProfile : m.base.data.all profileData = true) {s : Store H} {xas : List ExternAddr}
    {c c' : Config H} (hs : StoreOk s)
    (hI : Instantiate (Profile.deterministic o) closedHost s m.lower xas c)
    (hfr : c'.frame = c.frame) (hcode : c'.code = c.code)
    (hSR : DirSim.SR (siteOk m (tysOf m)) c.frame.module c.store c'.store) :
    DirSim.Pre (siteOk m (tysOf m)) c.frame.module o c c' :=
  (pre_inst_profile hfz hel h32 hdataProfile hs hI hfr hcode hSR).toPre

end DirectizeMid

end Silmaril.Wasm.Binaryen
