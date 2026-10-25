module

public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Execution.Core.Instantiation
public import Silmaril.Wasm.Execution.Core.Soundness.ConstEval
public import Silmaril.Wasm.Validation.Instructions.RangeRefs

@[expose] public section

/-! # Allocation lemmas for `Instantiate.alloc_ok`

Closed forms of the `$alloc*s` functions (`allocMany` of each allocator), the
inversion of `allocModule?`, and the per-allocator facts: each allocation
appends to one store component, so it preserves the typing of the old
instances and extends the store; the new addresses are typed against the
module context field by field (`Moduleinst_ok`, §4.2 `*inst_ok`).
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## Closed forms of `allocMany` -/

theorem allocMany_tag_eq (s : Store H) (ds : List DefType) :
    allocMany allocTag s ds =
      ({ s with tags := s.tags ++ ds.map TagInst.mk }, List.range' s.tags.length ds.length) := by
  induction ds generalizing s with
  | nil => simp [allocMany]
  | cons d ds ih =>
    simp only [allocMany, ih]
    simp [allocTag, List.range'_succ]

theorem allocMany_global_eq (s : Store H) (ps : List (CGlobalType × Val)) :
    allocMany (fun s (p : CGlobalType × Val) => allocGlobal s p.1 p.2) s ps =
      ({ s with globals := s.globals ++ ps.map fun p => ⟨p.1, p.2⟩ },
        List.range' s.globals.length ps.length) := by
  induction ps generalizing s with
  | nil => simp [allocMany]
  | cons p ps ih =>
    simp only [allocMany, ih]
    simp [allocGlobal, List.range'_succ]

theorem allocMany_mem_eq (s : Store H) (ms : List MemoryType) :
    allocMany allocMem s ms =
      ({ s with mems := s.mems ++ ms.map fun m =>
          ⟨m, ByteArray.mk (Array.replicate (m.limits.min.val * Memory.pageSize) 0)⟩ },
        List.range' s.mems.length ms.length) := by
  induction ms generalizing s with
  | nil => simp [allocMany]
  | cons p ps ih =>
    simp only [allocMany, ih]
    simp [allocMem, List.range'_succ]

theorem allocMany_table_eq (s : Store H) (ps : List (CTableType × Ref)) :
    allocMany (fun s (p : CTableType × Ref) => allocTable s p.1 p.2) s ps =
      ({ s with tables := s.tables ++ ps.map fun p => ⟨p.1, List.replicate p.1.limits.min.val p.2⟩ },
        List.range' s.tables.length ps.length) := by
  induction ps generalizing s with
  | nil => simp [allocMany]
  | cons p ps ih =>
    simp only [allocMany, ih]
    simp [allocTable, List.range'_succ]

theorem allocMany_data_eq (s : Store H) (bs : List ByteArray) :
    allocMany allocData s bs =
      ({ s with datas := s.datas ++ bs.map DataInst.mk }, List.range' s.datas.length bs.length) := by
  induction bs generalizing s with
  | nil => simp [allocMany]
  | cons p ps ih =>
    simp only [allocMany, ih]
    simp [allocData, List.range'_succ]

theorem allocMany_elem_eq (s : Store H) (ps : List (CRefType × List Ref)) :
    allocMany (fun s (p : CRefType × List Ref) => allocElem s p.1 p.2) s ps =
      ({ s with elems := s.elems ++ ps.map fun p => ⟨p.1, p.2⟩ },
        List.range' s.elems.length ps.length) := by
  induction ps generalizing s with
  | nil => simp [allocMany]
  | cons p ps ih =>
    simp only [allocMany, ih]
    simp [allocElem, List.range'_succ]

theorem allocMany_func_eq (s : Store H) (mi : ModuleInst) (ps : List (DefType × Func)) :
    allocMany (fun s (p : DefType × Func) => allocFunc s p.1 (.wasm p.2) mi) s ps =
      ({ s with funcs := s.funcs ++ ps.map fun p => ⟨p.1, mi, .wasm p.2⟩ },
        List.range' s.funcs.length ps.length) := by
  induction ps generalizing s with
  | nil => simp [allocMany]
  | cons p ps ih =>
    simp only [allocMany, ih]
    simp [allocFunc, List.range'_succ]

/-! ## Inversion of `allocModule?` -/

/-- The explicit result of a successful `allocModule?`. -/
theorem allocModule?_inv {s s' : Store H} {m : Module} {xas : List ExternAddr} {valsG : List Val}
    {refsT : List Ref} {refsE : List (List Ref)} {mi : ModuleInst}
    (h : allocModule? s m xas valsG refsT refsE = some (s', mi)) :
    ∃ tagTypes funcTypes xi,
      m.tags.mapM (fun x => (allocTypes m.types)[x.toNat]?) = some tagTypes ∧
      m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) = some funcTypes ∧
      m.exports.mapM (allocExport?
        { tags := ExternAddr.tags xas ++ List.range' s.tags.length tagTypes.length,
          globals := ExternAddr.globals xas ++ List.range' s.globals.length
            (min m.globals.length valsG.length),
          mems := ExternAddr.mems xas ++ List.range' s.mems.length m.memories.length,
          tables := ExternAddr.tables xas ++ List.range' s.tables.length
            (min m.tables.length refsT.length),
          funcs := ExternAddr.funcs xas ++
            (List.range m.funcs.length).map (s.funcs.length + ·) }) = some xi ∧
      mi = { types := allocTypes m.types,
             tags := ExternAddr.tags xas ++ List.range' s.tags.length tagTypes.length,
             globals := ExternAddr.globals xas ++ List.range' s.globals.length
              (min m.globals.length valsG.length),
             mems := ExternAddr.mems xas ++ List.range' s.mems.length m.memories.length,
             tables := ExternAddr.tables xas ++ List.range' s.tables.length
              (min m.tables.length refsT.length),
             funcs := ExternAddr.funcs xas ++
              (List.range m.funcs.length).map (s.funcs.length + ·),
             datas := List.range' s.datas.length m.data.length,
             elems := List.range' s.elems.length (min m.elems.length refsE.length),
             exports := xi } ∧
      s' = { s with
        tags := s.tags ++ tagTypes.map TagInst.mk,
        globals := s.globals ++
          ((m.globals.map fun g => (⟨g.type.mutability,
            (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩ : CGlobalType)).zip
            valsG).map (fun p => ⟨p.1, p.2⟩),
        mems := s.mems ++ m.memories.map fun m =>
          ⟨m, ByteArray.mk (Array.replicate (m.limits.min.val * Memory.pageSize) 0)⟩,
        tables := s.tables ++
          ((m.tables.map fun t => (⟨t.type.address, t.type.limits,
            (liftRef t.type.element).substAll ((allocTypes m.types).map .dt)⟩ : CTableType)).zip
            refsT).map (fun p => ⟨p.1, List.replicate p.1.limits.min.val p.2⟩),
        datas := s.datas ++ (m.data.map Data.bytes).map DataInst.mk,
        elems := s.elems ++
          ((m.elems.map fun e => (liftRef e.type).substAll ((allocTypes m.types).map .dt)).zip
            refsE).map (fun p => ⟨p.1, p.2⟩),
        funcs := s.funcs ++ (funcTypes.zip m.funcs).map fun p => ⟨p.1, mi, .wasm p.2⟩ } := by
  unfold allocModule? at h
  simp only [Option.bind_eq_bind] at h
  cases ht : m.tags.mapM (fun x => (allocTypes m.types)[x.toNat]?) with
  | none => simp [ht] at h
  | some tagTypes =>
  cases hf : m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) with
  | none => simp [ht, hf] at h
  | some funcTypes =>
  simp only [ht, hf, Option.bind_some, allocMany_tag_eq, allocMany_global_eq, allocMany_mem_eq,
    allocMany_table_eq, allocMany_data_eq, allocMany_elem_eq] at h
  cases hx : m.exports.mapM (allocExport?
        { tags := ExternAddr.tags xas ++ List.range' s.tags.length tagTypes.length,
          globals := ExternAddr.globals xas ++ List.range' s.globals.length
            (min m.globals.length valsG.length),
          mems := ExternAddr.mems xas ++ List.range' s.mems.length m.memories.length,
          tables := ExternAddr.tables xas ++ List.range' s.tables.length
            (min m.tables.length refsT.length),
          funcs := ExternAddr.funcs xas ++
            (List.range m.funcs.length).map (s.funcs.length + ·) }) with
  | none => simp [hx] at h
  | some xi =>
  simp [hx, allocMany_func_eq] at h
  obtain ⟨h1, h2⟩ := h
  subst h1 h2
  refine ⟨tagTypes, funcTypes, xi, rfl, rfl, hx, rfl, ?_⟩
  simp [Function.comp_def]

/-! ## `Func_ok` under `REFS` weakening -/

theorem localOk_rangeRefs {C : Context} {t : ValType} {lt : LocalType} (h : LocalOk C t lt) :
    LocalOk C.rangeRefs t lt := by
  cases h with
  | set h hd => exact .set h hd
  | unset h hd => exact .unset h hd

theorem funcOk_rangeRefs {C : Context} {f : Func} {d : DefType} (h : FuncOk C f d) :
    FuncOk C.rangeRefs f d := by
  cases h with
  | mk hd he hl hb =>
    refine .mk hd he (hl.imp fun _ _ h => localOk_rangeRefs h) ?_
    exact Validation.InstrsOk.rangeRefs hb

/-! ## Exports -/

theorem allocExport?_spec {mi : ModuleInst} {e : Export} {x : ExportInst}
    (h : allocExport? mi e = some x) :
    x.name = e.name ∧ x.addr ∈ mi.tags.map .tag ++ mi.globals.map .global ++
      mi.mems.map .mem ++ mi.tables.map .table ++ mi.funcs.map .func := by
  unfold allocExport? at h
  cases hi : e.index with
  | tag y =>
    rw [hi] at h
    simp only [Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp [List.mem_of_getElem? ha]
  | global y =>
    rw [hi] at h
    simp only [Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp [List.mem_of_getElem? ha]
  | memory y =>
    rw [hi] at h
    simp only [Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp [List.mem_of_getElem? ha]
  | table y =>
    rw [hi] at h
    simp only [Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp [List.mem_of_getElem? ha]
  | func y =>
    rw [hi] at h
    simp only [Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp [List.mem_of_getElem? ha]

/-! ## The allocation theorem -/

/-- `Instantiate.alloc_ok`, proved here. -/
theorem Instantiate.alloc_ok_aux {P : Profile} {host : HostSemantics H} {s : Store H} {m : Module}
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
    (helems : List.Forall₂ (ElemOk C) m.elems rts)
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
    StoreOk s₄ ∧ ModuleInstOk s₄ mi { C with refs := List.range C.funcs.length } := by
  obtain ⟨hsh, htyped⟩ := initEval_ok hs htypes himports hC' hC htags hglobals htables hfuncs helems
    hxas hg ht he
  obtain ⟨tagTypes, funcTypes, xi, htt, hft, hxi, hmi, hs₄⟩ := allocModule?_inv ha
  have hdts : allocTypes m.types = dts := allocTypes_eq htypes
  have hC'T : C'.types = dts := by subst hC'; rfl
  have hCT : C.types = dts := by subst hC hC'; rfl
  have htagT : tagTypes = jts := by
    refine mapM_eq_of_forall₂ htt (htags.imp fun x d h => ?_)
    rw [hdts, ← hC'T]; exact h.1
  have hfunT : funcTypes = fdts := by
    refine mapM_eq_of_forall₂ hft (hfuncs.imp fun fn d h => ?_)
    cases h with
    | mk hd _ _ _ => rw [hdts, ← hCT]; exact hd
  subst tagTypes funcTypes
  rw [hdts] at hs₄ hmi
  rw [GlobalsOk.types_eq hC'T hglobals, tables_types_eq hC'T htables,
    elems_types_eq hCT helems] at hs₄
  -- the components of the final store
  have eTags : s₄.tags = s.tags ++ jts.map TagInst.mk := by rw [hs₄, hsh.tags]
  have eGlobals : s₄.globals = s₃.globals ++ (gts.zip valsG).map (fun p => ⟨p.1, p.2⟩) := by
    rw [hs₄]
  have eMems : s₄.mems = s.mems ++ m.memories.map fun m =>
      ⟨m, ByteArray.mk (Array.replicate (m.limits.min.val * Memory.pageSize) 0)⟩ := by
    rw [hs₄, hsh.mems]
  have eTables : s₄.tables = s.tables ++
      (tts.zip refsT).map (fun p => ⟨p.1, List.replicate p.1.limits.min.val p.2⟩) := by
    rw [hs₄, hsh.tables]
  have eDatas : s₄.datas = s.datas ++ (m.data.map Data.bytes).map DataInst.mk := by
    rw [hs₄, hsh.datas]
  have eElems : s₄.elems = s.elems ++ (rts.zip refsE).map (fun p => ⟨p.1, p.2⟩) := by
    rw [hs₄, hsh.elems]
  have eFuncs : s₄.funcs = s.funcs ++ (fdts.zip m.funcs).map fun p => ⟨p.1, mi, .wasm p.2⟩ := by
    rw [hs₄, hsh.funcs]
  have eStructs : s₄.structs = s₃.structs := by rw [hs₄]
  have eArrays : s₄.arrays = s₃.arrays := by rw [hs₄]
  have eExns : s₄.exns = s.exns := by rw [hs₄, hsh.exns]
  have hflen : m.funcs.length = fdts.length := hfuncs.length_eq
  have hfuncsS : ∀ i fd, fdts[i]? = some fd →
      ∃ fi, s₄.funcs[s.funcs.length + i]? = some fi ∧ fi.type = fd := by
    intro i fd hi
    have hlen : i < m.funcs.length := hflen ▸ (List.getElem?_eq_some_iff.mp hi).1
    refine ⟨⟨fd, mi, .wasm m.funcs[i]⟩, ?_, rfl⟩
    rw [eFuncs, List.getElem?_append_right (by omega)]
    simp [List.getElem?_zip_eq_some, hi]
  have hext : Extend s s₄ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ExtendsList.of_prefix (by rw [eTags]; exact List.prefix_append _ _)
        fun _ _ => rfl
    · exact ExtendsList.of_prefix (hsh.globals.trans (by rw [eGlobals]; exact List.prefix_append _ _))
        fun _ _ => ⟨rfl, .inr rfl⟩
    · exact ExtendsList.of_prefix (by rw [eMems]; exact List.prefix_append _ _)
        fun _ _ => ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
    · exact ExtendsList.of_prefix (by rw [eTables]; exact List.prefix_append _ _)
        fun _ _ => ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
    · exact ExtendsList.of_prefix (by rw [eFuncs]; exact List.prefix_append _ _)
        fun _ _ => ⟨rfl, rfl, fun _ h => h, fun _ h => h⟩
    · exact ExtendsList.of_prefix (by rw [eDatas]; exact List.prefix_append _ _)
        fun _ _ => .inl rfl
    · exact ExtendsList.of_prefix (by rw [eElems]; exact List.prefix_append _ _)
        fun _ _ => ⟨rfl, .inl rfl⟩
    · refine ExtendsList.of_prefix (by rw [eStructs]; exact hsh.structs) fun si hsi => ?_
      obtain ⟨fs, he, hf⟩ := hs.structs si hsi
      exact ⟨rfl, fs, he, rfl, by simpa using hf.length_eq, fun _ _ h => .inr h⟩
    · refine ExtendsList.of_prefix (by rw [eArrays]; exact hsh.arrays) fun ai hai => ?_
      obtain ⟨ft, he, _⟩ := hs.arrays ai hai
      match ft, he with
      | .field m z, he => exact ⟨rfl, m, z, he, rfl, .inr rfl⟩
    · exact ExtendsList.of_prefix (by rw [eExns]) fun _ _ => rfl
  have hty := htyped s₄ (by rw [eGlobals]; exact List.prefix_append _ _)
    (by rw [eStructs]) (by rw [eArrays])
    hext hfuncsS
  -- lengths
  have hGlen : m.globals.length = gts.length := GlobalsOk.length_eq hglobals
  have hTlen : m.tables.length = tts.length := htables.length_eq
  have hElen : m.elems.length = rts.length := helems.length_eq
  have hvG : valsG.length = gts.length := hty.valsG.length_eq
  have hrT : refsT.length = tts.length := hty.refsT.length_eq
  have hrE : refsE.length = rts.length := hty.refsE.length_eq
  have hGmin : min m.globals.length valsG.length = gts.length := by omega
  have hTmin : min m.tables.length refsT.length = tts.length := by omega
  have hEmin : min m.elems.length refsE.length = rts.length := by omega
  simp only [hGmin, hTmin, hEmin, hsh.tags, hsh.mems, hsh.tables, hsh.funcs, hsh.datas,
    hsh.elems, ← List.range'_eq_map_range] at hmi hxi
  have hdtsOk : ∀ d ∈ dts, TyOk {} d := TypesOk.tyOk_empty htypes
  -- the typed addresses of the new module instance
  have hTagsOk : List.Forall₂ (fun a t => ExternAddrOk s₄ (.tag a) (.tag t))
      (ExternAddr.tags xas ++ List.range' s.tags.length jts.length)
      (CExternType.tags xtI ++ jts) :=
    List.rel_append ((ExternAddrOk.forall₂_tags hxas).imp fun _ _ h => h.extend hs hext)
      (forall₂_range' _ fun i d hi => by
        have := ExternAddrOk.tag (s := s₄) (a := s.tags.length + i) (ti := ⟨d⟩)
          (by rw [eTags, List.getElem?_append_right (by omega)]; simp [hi])
        exact this)
  have hGlobalsOk : List.Forall₂ (fun a g => ExternAddrOk s₄ (.global a) (.global g))
      (ExternAddr.globals xas ++ List.range' s₃.globals.length gts.length)
      (CExternType.globals xtI ++ gts) :=
    List.rel_append ((ExternAddrOk.forall₂_globals hxas).imp fun _ _ h => h.extend hs hext)
      (forall₂_range' _ fun i g hi => by
        have hi' : i < valsG.length := by rw [hvG]; exact (List.getElem?_eq_some_iff.mp hi).1
        have := ExternAddrOk.global (s := s₄) (a := s₃.globals.length + i)
          (gi := ⟨g, valsG[i]⟩)
          (by rw [eGlobals, List.getElem?_append_right (by omega)]
              simp [List.getElem?_zip_eq_some, hi])
        exact this)
  have hMemsOk : List.Forall₂ (fun a mt => ExternAddrOk s₄ (.mem a) (.mem mt))
      (ExternAddr.mems xas ++ List.range' s.mems.length m.memories.length)
      (CExternType.mems xtI ++ m.memories) :=
    List.rel_append ((ExternAddrOk.forall₂_mems hxas).imp fun _ _ h => h.extend hs hext)
      (forall₂_range' _ fun i mt hi => by
        have := ExternAddrOk.mem (s := s₄) (a := s.mems.length + i)
          (mi := ⟨mt, ByteArray.mk (Array.replicate (mt.limits.min.val * Memory.pageSize) 0)⟩)
          (by rw [eMems, List.getElem?_append_right (by omega)]; simp [hi])
        exact this)
  have hTablesOk : List.Forall₂ (fun a tt => ExternAddrOk s₄ (.table a) (.table tt))
      (ExternAddr.tables xas ++ List.range' s.tables.length tts.length)
      (CExternType.tables xtI ++ tts) :=
    List.rel_append ((ExternAddrOk.forall₂_tables hxas).imp fun _ _ h => h.extend hs hext)
      (forall₂_range' _ fun i tt hi => by
        have hi' : i < refsT.length := by rw [hrT]; exact (List.getElem?_eq_some_iff.mp hi).1
        have := ExternAddrOk.table (s := s₄) (a := s.tables.length + i)
          (ti := ⟨tt, List.replicate tt.limits.min.val refsT[i]⟩)
          (by rw [eTables, List.getElem?_append_right (by omega)]
              simp [List.getElem?_zip_eq_some, hi, hi'])
        exact this)
  have hFuncsOk : List.Forall₂ (fun a d => ExternAddrOk s₄ (.func a) (.func d))
      (ExternAddr.funcs xas ++ List.range' s.funcs.length m.funcs.length)
      (CExternType.funcs xtI ++ fdts) :=
    List.rel_append ((ExternAddrOk.forall₂_funcs hxas).imp fun _ _ h => h.extend hs hext)
      (by
        rw [hflen]
        exact forall₂_range' _ fun i d hi => by
          obtain ⟨fi, hfi, rfl⟩ := hfuncsS i d hi
          exact ExternAddrOk.func hfi)
  have hrtsOk : ∀ rt ∈ rts, TyOk {} rt := by
    intro rt hrt
    obtain ⟨e, he⟩ := forall₂_exists_right helems rt hrt
    have h2 := he.2.1
    rw [he.1] at h2 ⊢
    simp only [Context.closeRef, hCT] at h2 ⊢
    exact TyOk.closeRef_empty hdtsOk hCT h2
  have hElemsOk : List.Forall₂ (fun a rt => ∃ ei, s₄.elems[a]? = some ei ∧ ElemInstOk s₄ ei ∧
      ei.type = rt) (List.range' s.elems.length rts.length) rts :=
    forall₂_range' _ fun i rt hi => by
      have hi' : i < refsE.length := by rw [hrE]; exact (List.getElem?_eq_some_iff.mp hi).1
      refine ⟨⟨rt, refsE[i]⟩, ?_, ⟨hrtsOk rt (List.mem_of_getElem? hi), fun r hr => ?_⟩, rfl⟩
      · rw [eElems, List.getElem?_append_right (by omega)]
        simp [List.getElem?_zip_eq_some, hi, hi']
      · exact forall₂_getElem hty.refsE (List.getElem?_eq_getElem hi') hi r hr
  have hMI : ModuleInstOk s₄ mi { C with refs := List.range C.funcs.length } := by
    have hk : C.funcs.length = mi.funcs.length := by
      rw [hmi, hC, hC']
      simp [(ExternAddrOk.forall₂_funcs hxas).length_eq, hflen]
    have hctx : { C with refs := List.range C.funcs.length } =
        { types := mi.types, recs := [], tags := CExternType.tags xtI ++ jts,
          globals := CExternType.globals xtI ++ gts, mems := CExternType.mems xtI ++ m.memories,
          tables := CExternType.tables xtI ++ tts, funcs := CExternType.funcs xtI ++ fdts,
          datas := mi.datas.map fun _ => (), elems := rts,
          refs := List.range C.funcs.length } := by
      rw [hmi]; subst hC hC'; simp
    rw [hctx]
    have hexp := forall₂_of_mapM hxi
    have haddrs : ∀ xa ∈ mi.tags.map ExternAddr.tag ++ mi.globals.map .global ++
        mi.mems.map .mem ++ mi.tables.map .table ++ mi.funcs.map .func,
        ∃ xt, ExternAddrOk s₄ xa xt := by
      intro xa hxa
      rw [hmi] at hxa
      simp only [List.mem_append, List.mem_map] at hxa
      rcases hxa with (((⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩) |
        ⟨a, ha, rfl⟩
      · obtain ⟨t, ht⟩ := forall₂_exists_left hTagsOk a (List.mem_append.mpr ha); exact ⟨_, ht⟩
      · obtain ⟨t, ht⟩ := forall₂_exists_left hGlobalsOk a (List.mem_append.mpr ha); exact ⟨_, ht⟩
      · obtain ⟨t, ht⟩ := forall₂_exists_left hMemsOk a (List.mem_append.mpr ha); exact ⟨_, ht⟩
      · obtain ⟨t, ht⟩ := forall₂_exists_left hTablesOk a (List.mem_append.mpr ha); exact ⟨_, ht⟩
      · obtain ⟨t, ht⟩ := forall₂_exists_left hFuncsOk a (List.mem_append.mpr ha); exact ⟨_, ht⟩
    have hxiAddr : ∀ x ∈ xi, x.addr ∈ mi.tags.map ExternAddr.tag ++ mi.globals.map .global ++
        mi.mems.map .mem ++ mi.tables.map .table ++ mi.funcs.map .func := by
      intro x hx
      obtain ⟨e, he⟩ := forall₂_exists_right hexp x hx
      have := (allocExport?_spec he).2
      rw [hmi]; exact this
    have hnames : xi.map ExportInst.name = m.exports.map Export.name := by
      have : ∀ {mi0 : ModuleInst} {es : List Export} {xs : List ExportInst},
          List.Forall₂ (fun e x => allocExport? mi0 e = some x) es xs →
          xs.map ExportInst.name = es.map Export.name := by
        intro mi0 es xs h
        induction h with
        | nil => rfl
        | cons h _ ih => simp [ih, (allocExport?_spec h).1]
      exact this hexp
    refine ModuleInstOk.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (Nat.le_of_eq hk)
    · rw [hmi]; exact hdtsOk
    · rw [hmi]; exact hTagsOk
    · rw [hmi]; exact hGlobalsOk
    · rw [hmi]; exact hFuncsOk
    · rw [hmi]; exact hMemsOk
    · rw [hmi]; exact hTablesOk
    · intro a ha
      rw [hmi] at ha
      obtain ⟨j, hj, rfl⟩ := List.mem_range'.mp ha
      rw [eDatas, List.getElem?_append_right (by omega)]
      simp [hj]
    · rw [hmi]; exact hElemsOk
    · intro x hx
      exact haddrs x.addr (hxiAddr x (by rw [hmi] at hx; exact hx))
    · rw [hmi]; simp only; rw [hnames]; exact hdisjoint
    · intro x hx
      exact hxiAddr x (by rw [hmi] at hx; exact hx)
  -- validity of the new instances' types
  have hjtsOk : ∀ d ∈ jts, TagTypeOk {} d := by
    intro d hd
    obtain ⟨x, hx⟩ := forall₂_exists_right htags d hd
    have h1 : C'.types[x.toNat]? = some d := hx.1
    rw [hC'T] at h1
    exact ⟨hdtsOk d (List.mem_of_getElem? h1), hx.2.2⟩
  have hgtsOk : ∀ gt ∈ gts, GlobalTypeOk {} gt := by
    have key : ∀ {C₀ : Context} {gs : List Global} {gts : List CGlobalType}, C₀.types = dts →
        GlobalsOk C₀ gs gts → ∀ gt ∈ gts, GlobalTypeOk {} gt := by
      intro C₀ gs gts hT h
      induction h with
      | nil => intro gt hgt; cases hgt
      | @cons C₁ g gs gt gts hg _ ih =>
        intro gt' hgt'
        rcases List.mem_cons.mp hgt' with rfl | hgt'
        · have h2 : TyOk C₁.toTypeCtx gt'.type := hg.2.1
          rw [hg.1] at h2 ⊢
          simp only [Context.closeGlobalType, Context.closeVal, GlobalTypeOk, hT] at h2 ⊢
          exact TyOk.closeVal_empty hdtsOk (Δ := C₁.toTypeCtx) hT h2
        · exact ih hT gt' hgt'
    exact key hC'T hglobals
  have httsOk : ∀ tt ∈ tts, TableTypeOk {} tt := by
    intro tt htt
    obtain ⟨t, ht⟩ := forall₂_exists_right htables tt htt
    have h2 := ht.2.1
    refine ⟨h2.1, ?_⟩
    have h3 := h2.2
    rw [ht.1] at h3 ⊢
    simp only [Context.closeTableType, Context.closeRef, hC'T] at h3 ⊢
    exact TyOk.closeRef_empty hdtsOk hC'T h3
  have hfdtsOk : ∀ d ∈ fdts, TyOk {} d := by
    intro d hd
    obtain ⟨fn, hfn⟩ := forall₂_exists_right hfuncs d hd
    cases hfn with
    | mk hd' _ _ _ =>
      have h1 : C.types[fn.type.toNat]? = some d := hd'
      rw [hCT] at h1
      exact hdtsOk d (List.mem_of_getElem? h1)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hMI⟩
  · -- tags
    intro ti hti
    rw [eTags] at hti
    rcases List.mem_append.mp hti with h | h
    · exact hs.tags ti h
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
      exact hjtsOk d hd
  · -- globals
    intro gi hgi
    rw [eGlobals] at hgi
    rcases List.mem_append.mp hgi with h | h
    · exact hty.globals gi h
    · obtain ⟨⟨gt, v⟩, hp, rfl⟩ := List.mem_map.mp h
      exact ⟨hgtsOk gt (List.of_mem_zip hp).1, forall₂_mem_zip hty.valsG hp⟩
  · -- memories
    intro mi' hmi'
    rw [eMems] at hmi'
    rcases List.mem_append.mp hmi' with h | h
    · exact hs.mems mi' h
    · obtain ⟨mt, hmt, rfl⟩ := List.mem_map.mp h
      exact ⟨hmems mt hmt, by simp [ByteArray.size]⟩
  · -- tables
    intro ti hti
    rw [eTables] at hti
    rcases List.mem_append.mp hti with h | h
    · obtain ⟨h1, h2, h3⟩ := hs.tables ti h
      exact ⟨h1, h2, fun r hr => (h3 r hr).extend hext⟩
    · obtain ⟨⟨tt, r⟩, hp, rfl⟩ := List.mem_map.mp h
      refine ⟨httsOk tt (List.of_mem_zip hp).1, by simp, fun r' hr' => ?_⟩
      obtain ⟨-, rfl⟩ := List.mem_replicate.mp hr'
      exact forall₂_mem_zip hty.refsT hp
  · -- functions
    intro fi hfi
    rw [eFuncs] at hfi
    rcases List.mem_append.mp hfi with h | h
    · cases hs.funcs fi h with
      | wasm hdt hm hcode hf hsub => exact .wasm hdt (hm.extend hs hext) hcode hf hsub
      | host hdt he hcode => exact .host hdt he hcode
    · obtain ⟨⟨d, fn⟩, hp, rfl⟩ := List.mem_map.mp h
      have hfd : FuncOk C fn d := forall₂_mem_zip hfuncs hp
      exact .wasm (hfdtsOk d (List.of_mem_zip hp).1) hMI rfl (funcOk_rangeRefs hfd)
        (Sub.refl _ (k := .def) trivial d)
  · -- element segments
    intro ei hei
    rw [eElems] at hei
    rcases List.mem_append.mp hei with h | h
    · obtain ⟨h1, h2⟩ := hs.elems ei h
      exact ⟨h1, fun r hr => (h2 r hr).extend hext⟩
    · obtain ⟨⟨rt, rs⟩, hp, rfl⟩ := List.mem_map.mp h
      exact ⟨hrtsOk rt (List.of_mem_zip hp).1, forall₂_mem_zip hty.refsE hp⟩
  · -- structures
    intro si hsi
    rw [eStructs] at hsi
    exact hty.structs si hsi
  · -- arrays
    intro ai hai
    rw [eArrays] at hai
    exact hty.arrays ai hai
  · -- exceptions
    intro e he
    rw [eExns] at he
    obtain ⟨ti, ts, hti, hexp, hvs⟩ := hs.exns e he
    obtain ⟨ti', hti', hx⟩ := hext.tags.get hti
    cases hx
    exact ⟨ti, ts, hti', hexp, ValOk.forall₂_extend hext hvs⟩
  · intro a ha hr
    have hex : s₄.exns = s₃.exns := by rw [hs₄]
    exact hty.acyclic.1 a (by rwa [← eStructs])
      (TM.immutReachable_transfer eStructs eArrays hex hr)
  · intro a ha hr
    have hex : s₄.exns = s₃.exns := by rw [hs₄]
    exact hty.acyclic.2.1 a (by rwa [← eArrays])
      (TM.immutReachable_transfer eStructs eArrays hex hr)
  · intro a ha hr
    have hex : s₄.exns = s₃.exns := by rw [hs₄]
    exact hty.acyclic.2.2 a (by rwa [← hex])
      (TM.immutReachable_transfer eStructs eArrays hex hr)
  · intro si hsi
    rw [eStructs] at hsi
    exact hty.structsClosed si hsi
  · intro ai hai
    rw [eArrays] at hai
    exact hty.arraysClosed ai hai

end Silmaril.Wasm.Execution.Core
