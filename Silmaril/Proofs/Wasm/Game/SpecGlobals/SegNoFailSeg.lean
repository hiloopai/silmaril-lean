module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.SegNoFailConst
public import Silmaril.Proofs.Wasm.Game.SpecGlobals.SegNoFailLoop

/-!
# One segment of a validated module never fails

In a frame typed against a context `C` over a well-typed store, a validated element segment
(`ElemOk C e rt`, `C.elems[k] = rt`) or data segment (`DataOk C d`, `k < |C.datas|`) is
initialised directly or traps, never fails (`elemSeg_not_fail`, `dataSeg_not_fail`): its offset
evaluates to an address (`offset_eval`), the table/memory and the segment are found through the
frame (`ModuleInstOk`), and in bounds the loops succeed. After a successful segment the store is
still well typed and the frame still typed (`elemSeg_inv`, `dataSeg_inv`, by preservation along
silmaril-lean's `initElemSeg?_steps`/`initDataSeg?_steps`).

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.SingleThreaded

/-! ## Lookups through a typed frame -/

theorem externAddrOk_table {s : Store Nat} {a : Nat} {xt : CExternType}
    (h : ExternAddrOk s (.table a) xt) : ∃ ti, s.tables[a]? = some ti := by
  generalize hx : ExternAddr.table a = xa at h
  induction h with
  | table hl => cases hx; exact ⟨_, hl⟩
  | sub _ _ _ ih => exact ih hx
  | _ => cases hx

theorem externAddrOk_mem {s : Store Nat} {a : Nat} {xt : CExternType}
    (h : ExternAddrOk s (.mem a) xt) : ∃ mi, s.mems[a]? = some mi := by
  generalize hx : ExternAddr.mem a = xa at h
  induction h with
  | mem hl => cases hx; exact ⟨_, hl⟩
  | sub _ _ _ ih => exact ih hx
  | _ => cases hx

theorem frame_table {s : Store Nat} {f : Frame} {C : Context} (hf : FrameOk s f C) {x : TableIdx}
    {tt : CTableType} (hx : C.tables[x.toNat]? = some tt) :
    ∃ ta ti, s.table? f x = some (ta, ti) := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := hf
  cases hm with
  | mk _ _ _ _ _ htables =>
    obtain ⟨a, ha, hok⟩ := forall₂_getElem?_right htables hx
    obtain ⟨ti, hti⟩ := externAddrOk_table hok
    exact ⟨a, ti, by simp only [Store.table?, ha, hti, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]⟩

theorem frame_mem {s : Store Nat} {f : Frame} {C : Context} (hf : FrameOk s f C) {x : MemIdx}
    {mt : MemoryType} (hx : C.mems[x.toNat]? = some mt) :
    ∃ ma mi, s.mem? f x = some (ma, mi) := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := hf
  cases hm with
  | mk _ _ _ _ hmems =>
    obtain ⟨a, ha, hok⟩ := forall₂_getElem?_right hmems hx
    obtain ⟨mi, hmi⟩ := externAddrOk_mem hok
    exact ⟨a, mi, by simp only [Store.mem?, ha, hmi, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]⟩

theorem frame_elem {s : Store Nat} {f : Frame} {C : Context} (hf : FrameOk s f C) {y : ElemIdx}
    {rt : CRefType} (hy : C.elems[y.toNat]? = some rt) :
    ∃ ea ei, s.elem? f y = some (ea, ei) := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := hf
  cases hm with
  | mk _ _ _ _ _ _ _ helems =>
    obtain ⟨a, ha, ei, hei, -⟩ := forall₂_getElem?_right helems hy
    exact ⟨a, ei, by simp only [Store.elem?, ha, hei, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]⟩

theorem frame_data {s : Store Nat} {f : Frame} {C : Context} (hf : FrameOk s f C) {y : DataIdx}
    (hy : y.toNat < C.datas.length) : ∃ da di, s.data? f y = some (da, di) := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := hf
  cases hm with
  | mk _ _ _ _ _ _ hdatas =>
    simp only [List.length_map] at hy
    have ha : f.module.datas[y.toNat]? = some f.module.datas[y.toNat] :=
      List.getElem?_eq_getElem hy
    obtain ⟨di, hdi⟩ := hdatas _ (List.getElem_mem hy)
    exact ⟨f.module.datas[y.toNat], di, by simp only [Store.data?, ha, hdi, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]⟩

theorem idx_ofNat {k : Nat} (hk : k < 2 ^ 32) : (Fin.ofNat (2 ^ 32) k).val = k := by
  simp only [Fin.val_ofNat]
  exact Nat.mod_eq_of_lt hk

theorem addr?_int (a : AddrType) (i : BitVec a.intType.width) :
    (Val.num ⟨.int a.intType, i⟩).addr? = some ⟨a, i⟩ := by
  cases a <;> rfl

theorem elem?_of_elems {s s' : Store Nat} (h : s'.elems = s.elems) (f : Frame) (y : ElemIdx) :
    s'.elem? f y = s.elem? f y := by
  simp only [Store.elem?, h]

theorem data?_of_datas {s s' : Store Nat} (h : s'.datas = s.datas) (f : Frame) (y : DataIdx) :
    s'.data? f y = s.data? f y := by
  simp only [Store.data?, h]

/-! ## Element segments -/

variable {s : Store Nat} {f : Frame} {C : Context}

/-- An active element segment initialises or traps. -/
theorem elem_active {k : Nat} {e : Elem} {rt : CRefType} {y : TableIdx} {off : Expr}
    (hs : StoreOk s) (hf : FrameOk s f C)
    (hCe : C.elems[(⟨Fin.ofNat (2 ^ 32) k⟩ : ElemIdx).toNat]? = some rt)
    (hm : e.mode = .active y off) (hmode : ElemModeOk C (.active y off) rt) :
    (∃ s', initElemSeg? evalConst? s f k e = some s') ∨
      ∃ s₁, elemSegTrap? evalConst? s f k e = some s₁ := by
  obtain ⟨a, l, rt', htab, ho⟩ : ∃ a l rt', C.tables[y.toNat]? = some ⟨a, l, rt'⟩ ∧
      ExprOkConst C off a.valType := by
    cases hmode with
    | active htab _ ho => exact ⟨_, _, _, htab, ho⟩
  obtain ⟨s₁, i, hev, hs₁, he₁⟩ := offset_eval hs hf ho
  have hf₁ : FrameOk s₁ f C := FrameOk.extend hs he₁ hf
  obtain ⟨ta, ti, ht⟩ := frame_table hf₁ htab
  obtain ⟨ea, ei, hel⟩ := frame_elem hf₁ hCe
  by_cases hb : i.toNat + (BitVec.ofNat 32 e.init.length).toNat ≤ ti.refs.length ∧
      (0 : BitVec 32).toNat + (BitVec.ofNat 32 e.init.length).toNat ≤ ei.refs.length
  · obtain ⟨s₂, hl, hel₂⟩ := tableInitLoop_some _ s₁ i 0 _ rfl ta ti ea ei ht hel hb.1 hb.2
    have hel' : s₂.elem? f ⟨Fin.ofNat (2 ^ 32) k⟩ = some (ea, ei) := by
      rw [elem?_of_elems hel₂]
      exact hel
    refine .inl ⟨s₂.setElem ea [], ?_⟩
    simp only [initElemSeg?, hm, hev]
    cases a <;> simp only [Val.addr?, AddrType.intType, hl, elemDrop?, hel', Option.map_some]
  · show (∃ s', initElemSeg? evalConst? s f k e = some s') ∨
      ∃ s₁, elemSegTrap? evalConst? s f k e = some s₁
    refine .inr ⟨s₁, ?_⟩
    have hoob : tableInitOob? s₁ f y ⟨Fin.ofNat (2 ^ 32) k⟩ a i 0
        (BitVec.ofNat 32 e.init.length) = true := by
      simp only [tableInitOob?, ht, hel, decide_eq_true_eq]
      rcases Decidable.not_and_iff_or_not.1 hb with h | h
      · exact .inl (Nat.lt_of_not_le h)
      · exact .inr (Nat.lt_of_not_le h)
    simp only [elemSegTrap?, hm, hev]
    cases a <;> simp only [Val.addr?, AddrType.intType, hoob, ite_true]

/-- **A validated element segment initialises or traps.** -/
theorem elemSeg_some_or_trap {k : Nat} {e : Elem} {rt : CRefType} (hs : StoreOk s)
    (hf : FrameOk s f C) (hk : k < 2 ^ 32) (hCe : C.elems[k]? = some rt) (he : ElemOk C e rt) :
    (∃ s', initElemSeg? evalConst? s f k e = some s') ∨
      ∃ s₁, elemSegTrap? evalConst? s f k e = some s₁ := by
  have hCe' : C.elems[(⟨Fin.ofNat (2 ^ 32) k⟩ : ElemIdx).toNat]? = some rt := by
    simp only [Idx.toNat, idx_ofNat hk]
    exact hCe
  obtain ⟨-, -, -, hmode⟩ := he
  cases hm : e.mode with
  | passive => exact .inl ⟨s, by simp only [initElemSeg?, hm]⟩
  | declarative =>
    obtain ⟨ea, ei, hel⟩ := frame_elem hf hCe'
    exact .inl ⟨s.setElem ea [], by simp only [initElemSeg?, hm, elemDrop?, hel, Option.map_some]⟩
  | active y off => exact elem_active hs hf hCe' hm (hm ▸ hmode)

/-- After a successful element segment the store and the frame stay typed. -/
theorem elemSeg_inv {k : Nat} {e : Elem} {rt : CRefType} (hs : StoreOk s) (hf : FrameOk s f C)
    (hk : k < 2 ^ 32) (hCe : C.elems[k]? = some rt) (he : ElemOk C e rt) {s' : Store Nat}
    (h : initElemSeg? evalConst? s f k e = some s') : StoreOk s' ∧ FrameOk s' f C := by
  have hrun := initElemSeg?_steps (P := profile neverFail) (host := divHost) evalConst?_evalSound h
  have hc : ConfigOk ⟨s, f, expression (runElem k e)⟩ [] :=
    ⟨C, ⟨hs, hf⟩, AdminsOk.of_instrsOk (runElem_ok hk hCe he)⟩
  obtain ⟨hc', hext⟩ := steps_typed hc hrun
  exact ⟨SingleThreaded.ConfigOk.storeOk hc', FrameOk.extend hs hext hf⟩

/-! ## Data segments -/

/-- An active data segment initialises or traps. -/
theorem data_active {k : Nat} {d : Data} {y : MemIdx} {off : Expr} (hs : StoreOk s)
    (hf : FrameOk s f C) (hCd : (⟨Fin.ofNat (2 ^ 32) k⟩ : DataIdx).toNat < C.datas.length)
    (hm : d.mode = .active y off) (hmode : DataModeOk C (.active y off)) :
    (∃ s', initDataSeg? evalConst? s f k d = some s') ∨
      ∃ s₁, dataSegTrap? evalConst? s f k d = some s₁ := by
  obtain ⟨a, l, hmem, ho⟩ : ∃ a l, C.mems[y.toNat]? = some ⟨a, l⟩ ∧
      ExprOkConst C off a.valType := by
    cases hmode with
    | active hmem ho => exact ⟨_, _, hmem, ho⟩
  obtain ⟨s₁, i, hev, hs₁, he₁⟩ := offset_eval hs hf ho
  have hf₁ : FrameOk s₁ f C := FrameOk.extend hs he₁ hf
  obtain ⟨ma, mi, hmi⟩ := frame_mem hf₁ hmem
  obtain ⟨da, di, hdi⟩ := frame_data hf₁ hCd
  by_cases hb : i.toNat + (BitVec.ofNat 32 d.bytes.size).toNat ≤ mi.bytes.size ∧
      (0 : BitVec 32).toNat + (BitVec.ofNat 32 d.bytes.size).toNat ≤ di.bytes.size
  · obtain ⟨s₂, hl, hd₂⟩ := memoryInitLoop_some _ s₁ i 0 _ rfl ma mi da di hmi hdi hb.1 hb.2
    have hdi' : s₂.data? f ⟨Fin.ofNat (2 ^ 32) k⟩ = some (da, di) := by
      rw [data?_of_datas hd₂]
      exact hdi
    refine .inl ⟨s₂.setData da ByteArray.empty, ?_⟩
    simp only [initDataSeg?, hm, hev]
    cases a <;> simp only [Val.addr?, AddrType.intType, hl, dataDrop?, hdi', Option.map_some]
  · show (∃ s', initDataSeg? evalConst? s f k d = some s') ∨
      ∃ s₁, dataSegTrap? evalConst? s f k d = some s₁
    refine .inr ⟨s₁, ?_⟩
    have hoob : memoryInitOob? s₁ f y ⟨Fin.ofNat (2 ^ 32) k⟩ a i 0
        (BitVec.ofNat 32 d.bytes.size) = true := by
      simp only [memoryInitOob?, hmi, hdi, decide_eq_true_eq]
      rcases Decidable.not_and_iff_or_not.1 hb with h | h
      · exact .inl (Nat.lt_of_not_le h)
      · exact .inr (Nat.lt_of_not_le h)
    simp only [dataSegTrap?, hm, hev]
    cases a <;> simp only [Val.addr?, AddrType.intType, hoob, ite_true]

theorem datas_idx {k : Nat} (hk : k < 2 ^ 32) (hCd : k < C.datas.length) :
    (⟨Fin.ofNat (2 ^ 32) k⟩ : DataIdx).toNat < C.datas.length := by
  simp only [Idx.toNat, idx_ofNat hk]
  exact hCd

/-- **A validated data segment initialises or traps.** -/
theorem dataSeg_some_or_trap {k : Nat} {d : Data} (hs : StoreOk s) (hf : FrameOk s f C)
    (hk : k < 2 ^ 32) (hCd : k < C.datas.length) (hd : DataOk C d) :
    (∃ s', initDataSeg? evalConst? s f k d = some s') ∨
      ∃ s₁, dataSegTrap? evalConst? s f k d = some s₁ := by
  cases hm : d.mode with
  | passive => exact .inl ⟨s, by simp only [initDataSeg?, hm]⟩
  | active y off =>
    have hmode : DataModeOk C (.active y off) := hm ▸ hd
    exact data_active hs hf (datas_idx hk hCd) hm hmode

/-- After a successful data segment the store and the frame stay typed. -/
theorem dataSeg_inv {k : Nat} {d : Data} (hs : StoreOk s) (hf : FrameOk s f C)
    (hCd : k < C.datas.length) (hd : DataOk C d) {s' : Store Nat}
    (h : initDataSeg? evalConst? s f k d = some s') : StoreOk s' ∧ FrameOk s' f C := by
  have hrun := initDataSeg?_steps (P := profile neverFail) (host := divHost) evalConst?_evalSound h
  have hc : ConfigOk ⟨s, f, expression (runData k d)⟩ [] :=
    ⟨C, ⟨hs, hf⟩, AdminsOk.of_instrsOk (runData_ok hCd hd)⟩
  obtain ⟨hc', hext⟩ := steps_typed hc hrun
  exact ⟨SingleThreaded.ConfigOk.storeOk hc', FrameOk.extend hs hext hf⟩

end Silmaril.Proofs.Wasm.Game.SpecGlobals
