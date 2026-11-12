module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.StoreValid10

/-!
# `ResOkL10` from Core typing

`GoodV1`'s first field, `ResOkL10`, asks every instruction of a V1 configuration, at any depth of
labels and frames and read in its own frame, to name resources that exist: locals, globals (and a
mutable one for `global.set`), functions, types, the table and the memory. Round 4 derived
`GSetOk` and round 5 `SelOk` from validation read through Core 3.0 (`CoreTyped10`); this module
does the same for `ResOkL10`, so `GoodV1` follows from `CoreTyped10` and V1's `StoreOk10`.

* `resOkL10_of_activeF`: `ResOkL10` is the statement that every instruction reached by
  `ActiveF` names existing resources (a combinatorial lemma on V1 code).
* `CtxSame`: a Core context agrees with the frame's context `Cf` on everything but the status of
  the locals, the labels and the return type. Infixes (`infix_typed'`), labels and the switch to a
  frame's own context keep it.
* `instrRes_core`: a V1 instruction whose Core image is typed in such a context names existing
  resources. Each kind reads the context (`InstrOk` inversions), then the module instance
  (`ModuleInstOk`, through the frame erasure), then the store (`ExternAddrOk`, through the store
  erasure). `global.set` also reads the mutability of the stored global.
* **`resOkL10_of_coreTyped10`**, **`goodV1_of_coreTyped10`**, **`goodV1_steps'`**: so `GoodV1`
  holds at every `CoreTyped10` configuration with `StoreOk10`, and along V1 runs from one whose
  store has no host function.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Valid

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## `ResOkL10` from instructions reached by `ActiveF` -/

section Active

open Silmaril.Wasm.SpecTec.Sim10 (ActiveF ResOkA10 ResOkL10 InstrResOk10)

/-- `ActiveF` from a tail of the code. -/
theorem activeF_cons {f f' : Execution.Runtime.Frame} {a : V1.Execution.Admin}
    {l w : List V1.Execution.Admin} (h : ActiveF f l f' w) : ActiveF f (a :: l) f' w := by
  cases h with
  | piece =>
    rename_i l₁ l₂
    have e : a :: (l₁ ++ w ++ l₂) = (a :: l₁) ++ w ++ l₂ := by simp
    rw [e]
    exact .piece
  | label hm h' => exact .label (List.mem_cons_of_mem _ hm) h'
  | frame hm h' => exact .frame (List.mem_cons_of_mem _ hm) h'

/-- The hypothesis of `resOkL10_of_activeF`. -/
def ResAt (s : V1.Execution.Store H) (f : Execution.Runtime.Frame)
    (code : List V1.Execution.Admin) : Prop :=
  ∀ f' i, ActiveF f code f' [.source i] → InstrResOk10 s f' i

mutual
theorem resOkA_of_resAt (s : V1.Execution.Store H) :
    ∀ (f : Execution.Runtime.Frame) (a : V1.Execution.Admin) (l : List V1.Execution.Admin),
      ResAt s f (a :: l) → ResOkA10 s f a
  | f, .source i, l, h => h f i (by simpa using (ActiveF.piece (l₁ := []) (w := [.source i]) (l₂ := l) (f := f)))
  | f, .label n cont b, l, h => by
    show ResOkL10 s f b
    exact resOkL_of_resAt s f b fun f' i hb => h f' i (.label (List.mem_cons_self ..) hb)
  | f, .frame n fi b, l, h => by
    show ResOkL10 s fi b
    exact resOkL_of_resAt s fi b fun f' i hb => h f' i (.frame (List.mem_cons_self ..) hb)
  | _, .invoke _, _, _ => trivial
  | _, .trap, _, _ => trivial

theorem resOkL_of_resAt (s : V1.Execution.Store H) :
    ∀ (f : Execution.Runtime.Frame) (l : List V1.Execution.Admin), ResAt s f l → ResOkL10 s f l
  | _, [], _ => trivial
  | f, a :: l, h => ⟨resOkA_of_resAt s f a l h,
      resOkL_of_resAt s f l fun f' i hl => h f' i (activeF_cons hl)⟩
end

/-- **`ResOkL10` from the instructions `ActiveF` reaches.** -/
theorem resOkL10_of_activeF {s : V1.Execution.Store H} {f : Execution.Runtime.Frame}
    {code : List V1.Execution.Admin} (h : ResAt s f code) : ResOkL10 s f code :=
  resOkL_of_resAt s f code h

end Active

/-! ## Contexts that agree with the frame's -/

/-- **A context that agrees with the frame's context `Cf`** on functions, globals, memories,
tables and types, and on which locals exist. -/
structure CtxSame (C Cf : Context) : Prop where
  funcs : C.funcs = Cf.funcs
  globals : C.globals = Cf.globals
  mems : C.mems = Cf.mems
  tables : C.tables = Cf.tables
  types : C.types = Cf.types
  locals : ∀ y : Nat, (C.locals[y]?).isSome = (Cf.locals[y]?).isSome

theorem CtxSame.refl (C : Context) : CtxSame C C := ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem CtxSame.initLocals {C Cf : Context} (h : CtxSame C Cf) (xs : List Nat) :
    CtxSame (C.initLocals xs) Cf := by
  obtain ⟨L, hL, hy⟩ := C.initLocals_spec xs
  rw [hL]
  refine ⟨h.funcs, h.globals, h.mems, h.tables, h.types, fun y => ?_⟩
  show (L[y]?).isSome = _
  rw [hy y, ← h.locals y]
  split <;> simp

theorem CtxSame.withLabel {C Cf : Context} (h : CtxSame C Cf) (ts : List CValType) :
    CtxSame (C.withLabel ts) Cf :=
  ⟨h.funcs, h.globals, h.mems, h.tables, h.types, h.locals⟩

/-- A typed sequence types each of its non-empty infixes, after initialising some locals. -/
theorem infix_typed' {s : Store H} {C : Context} {L₁ w L₂ : List Admin} {it : InstrType}
    (h : AdminsOk s C (L₁ ++ w ++ L₂) it) (hw : w ≠ []) (hC : C.Wf) :
    ∃ xs it', AdminsOk s (C.initLocals xs) w it' := by
  rw [List.append_assoc] at h
  obtain ⟨xs, it₁, h₁⟩ := suffix_typed h (by simp [hw]) hC
  obtain ⟨it', h'⟩ := prefix_typed h₁ (hC.initLocals xs)
  exact ⟨xs, it', h'⟩

/-- A typed sequence with a single element in its middle types that element. -/
theorem single_typed' {s : Store H} {C : Context} {L₁ L₂ : List Admin} {z : Admin}
    {it : InstrType} (h : AdminsOk s C (L₁ ++ [z] ++ L₂) it) (hC : C.Wf) :
    ∃ xs it', AdminOk s (C.initLocals xs) z it' ∧ (C.initLocals xs).Wf := by
  obtain ⟨xs, it', h'⟩ := infix_typed' h (by simp) hC
  obtain ⟨_, it₀, ha, -⟩ := AdminsOk.single_aux' h' z rfl (hC.initLocals xs).types
  exact ⟨xs, it₀, ha, hC.initLocals xs⟩

/-! ## What the context names -/

theorem call_ctx {C : Context} {x : FuncIdx} {it : InstrType} (h : InstrOk C (.call x) it) :
    ∃ d, C.funcs[x.toNat]? = some d := by
  cases h <;> (try (rename_i h'; cases h'))
  exact ⟨_, ‹_›⟩

theorem callIndirect_ctx {C : Context} {x : TableIdx} {y : TypeIdx} {it : InstrType}
    (h : InstrOk C (.callIndirect x y) it) :
    (∃ tt, C.tables[x.toNat]? = some tt) ∧ ∃ d, C.types[y.toNat]? = some d := by
  cases h <;> (try (rename_i h'; cases h'))
  exact ⟨⟨_, ‹_›⟩, _, ‹_›⟩

theorem intLoad_ctx {C : Context} {t : IntType} {q : Option (PackSize × Signedness)}
    {x : MemIdx} {arg : MemArg} {it : InstrType} (h : InstrOk C (.intLoad t q x arg) it) :
    ∃ mt, C.mems[x.toNat]? = some mt := by
  cases h <;> (try (rename_i h'; cases h')) <;> exact ⟨_, ‹_›⟩

theorem floatLoad_ctx {C : Context} {t : FloatType} {x : MemIdx} {arg : MemArg}
    {it : InstrType} (h : InstrOk C (.floatLoad t x arg) it) :
    ∃ mt, C.mems[x.toNat]? = some mt := by
  cases h <;> (try (rename_i h'; cases h'))
  exact ⟨_, ‹_›⟩

theorem intStore_ctx {C : Context} {t : IntType} {q : Option PackSize} {x : MemIdx}
    {arg : MemArg} {it : InstrType} (h : InstrOk C (.intStore t q x arg) it) :
    ∃ mt, C.mems[x.toNat]? = some mt := by
  cases h <;> (try (rename_i h'; cases h')) <;> exact ⟨_, ‹_›⟩

theorem floatStore_ctx {C : Context} {t : FloatType} {x : MemIdx} {arg : MemArg}
    {it : InstrType} (h : InstrOk C (.floatStore t x arg) it) :
    ∃ mt, C.mems[x.toNat]? = some mt := by
  cases h <;> (try (rename_i h'; cases h'))
  exact ⟨_, ‹_›⟩

theorem memorySize_ctx {C : Context} {x : MemIdx} {it : InstrType}
    (h : InstrOk C (.memorySize x) it) : ∃ mt, C.mems[x.toNat]? = some mt := by
  cases h <;> (try (rename_i h'; cases h'))
  exact ⟨_, ‹_›⟩

theorem memoryGrow_ctx {C : Context} {x : MemIdx} {it : InstrType}
    (h : InstrOk C (.memoryGrow x) it) : ∃ mt, C.mems[x.toNat]? = some mt := by
  cases h <;> (try (rename_i h'; cases h'))
  exact ⟨_, ‹_›⟩

/-! ## From the frame's context to the V1 frame and store -/

/-- The fields of a Core frame whose erasure is the image of a V1 frame. -/
theorem frame_erase_fields {fC : Frame} {f : Execution.Runtime.Frame}
    (hfe : Lime1.Execution.ToCore.Frame.erase fC = f.toCore) :
    fC.module.funcs = f.module.funcs.map Execution.Runtime.Addr.value ∧
      fC.module.tables = f.module.tables.map Execution.Runtime.Addr.value ∧
      fC.module.mems = f.module.memories.map Execution.Runtime.Addr.value ∧
      fC.module.globals = f.module.globals.map Execution.Runtime.Addr.value ∧
      fC.module.types = f.module.types.map V1.FuncType.toDefType ∧
      fC.locals = f.locals.map (some ∘ Execution.Runtime.Value.toCore) := by
  have e := congrArg (fun g => (g.module.funcs, g.module.tables, g.module.mems, g.module.globals,
    g.module.types, g.locals)) hfe
  simpa [Lime1.Execution.ToCore.Frame.erase, Lime1.Execution.ToCore.ModuleInst.erase,
    Execution.Runtime.Frame.toCore, Execution.Runtime.ModuleInst.toCore] using e

/-- The tables, memories and globals of a Core store whose erasure is the image of a V1 store. -/
theorem store_erase_fields {sC : Store H} {s : V1.Execution.Store H}
    (hsS : Lime1.Execution.ToCore.Store.erase sC = (s.mapCode V1.Func.toLime).toCore) :
    sC.tables.length = s.tables.length ∧ sC.mems.length = s.memories.length ∧
      sC.globals.map Lime1.Execution.ToCore.GlobalInst.erase =
        s.globals.map Execution.Runtime.GlobalInst.toCore := by
  have et : (s.mapCode V1.Func.toLime).tables = s.tables := rfl
  have em : (s.mapCode V1.Func.toLime).memories = s.memories := rfl
  have eg : (s.mapCode V1.Func.toLime).globals = s.globals := rfl
  have e := congrArg (fun t => (t.tables.length, t.mems.length, t.globals)) hsS
  simpa [Lime1.Execution.ToCore.Store.erase, Execution.Runtime.Store.toCore, et, em, eg] using e

theorem externAddrOk_mem {sC : Store H} {a : Nat} {xt : CExternType}
    (h : ExternAddrOk sC (.mem a) xt) : ∃ mi, sC.mems[a]? = some mi := by
  generalize e : ExternAddr.mem a = xa at h
  induction h with
  | mem h => cases e; exact ⟨_, h⟩
  | sub _ _ _ ih => exact ih e
  | _ => cases e

theorem externAddrOk_table {sC : Store H} {a : Nat} {xt : CExternType}
    (h : ExternAddrOk sC (.table a) xt) : ∃ ti, sC.tables[a]? = some ti := by
  generalize e : ExternAddr.table a = xa at h
  induction h with
  | table h => cases e; exact ⟨_, h⟩
  | sub _ _ _ ih => exact ih e
  | _ => cases e

/-- A Core index in a list of the V1 addresses' values. -/
theorem addr_of_map {α : Execution.Runtime.AddrKind} {l : List (Execution.Runtime.Addr α)} {k a : Nat}
    (h : (l.map Execution.Runtime.Addr.value)[k]? = some a) : ∃ a', l[k]? = some a' ∧ a'.value = a := by
  rw [List.getElem?_map] at h
  cases hk : l[k]? with
  | none => rw [hk] at h; cases h
  | some a' => rw [hk] at h; exact ⟨a', rfl, Option.some.inj h⟩

/-- An index below the length of the Core list is one of the V1 list. -/
theorem getElem?_isSome_of_length {α β : Type} {l : List α} {m : List β} (hl : l.length = m.length)
    {k : Nat} {x : α} (h : l[k]? = some x) : (m[k]?).isSome := by
  have hk : k < l.length := (List.getElem?_eq_some_iff.1 h).1
  rw [hl] at hk
  simp [hk]

section Frame

variable {s : V1.Execution.Store H} {sC : Store H} {f : Execution.Runtime.Frame} {fC : Frame}
  {Cf : Context}

theorem funcs_res (hfe : Lime1.Execution.ToCore.Frame.erase fC = f.toCore)
    (hf : FrameOk sC fC Cf) {k : Nat} {d : DefType} (hx : Cf.funcs[k]? = some d) :
    (f.module.funcs[k]?).isSome := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := hf
  cases hm with
  | mk _ _ _ hfuncs =>
    obtain ⟨a, ha, -⟩ := forall₂_getElem?_right hfuncs hx
    rw [(frame_erase_fields hfe).1] at ha
    obtain ⟨a', ha', -⟩ := addr_of_map ha
    simp [ha']

theorem types_res (hfe : Lime1.Execution.ToCore.Frame.erase fC = f.toCore)
    (hf : FrameOk sC fC Cf) {k : Nat} {d : DefType} (hx : Cf.types[k]? = some d) :
    (f.module.types[k]?).isSome := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := hf
  have ht : C₀.types = fC.module.types := hm.ctx_fields.2.2.2
  have hx' : fC.module.types[k]? = some d := by rw [← ht]; exact hx
  rw [(frame_erase_fields hfe).2.2.2.2.1, List.getElem?_map] at hx'
  cases hk : f.module.types[k]? with
  | none => rw [hk] at hx'; cases hx'
  | some _ => rfl

theorem table_res (hfe : Lime1.Execution.ToCore.Frame.erase fC = f.toCore)
    (hsS : Lime1.Execution.ToCore.Store.erase sC = (s.mapCode V1.Func.toLime).toCore)
    (hf : FrameOk sC fC Cf) {tt : CTableType} (hx : Cf.tables[0]? = some tt) :
    (V1.Execution.frameTable s f).isSome := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := hf
  cases hm with
  | mk _ _ _ _ _ htables =>
    obtain ⟨a, ha, hxa⟩ := forall₂_getElem?_right htables hx
    rw [(frame_erase_fields hfe).2.1] at ha
    obtain ⟨a', ha', rfl⟩ := addr_of_map ha
    obtain ⟨ti, hti⟩ := externAddrOk_table hxa
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1
      (getElem?_isSome_of_length (store_erase_fields hsS).1 hti)
    simp [V1.Execution.frameTable, ha', ht]

theorem mem_res (hfe : Lime1.Execution.ToCore.Frame.erase fC = f.toCore)
    (hsS : Lime1.Execution.ToCore.Store.erase sC = (s.mapCode V1.Func.toLime).toCore)
    (hf : FrameOk sC fC Cf) {mt : MemoryType} (hx : Cf.mems[0]? = some mt) :
    (V1.Execution.frameMemory s f).isSome := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := hf
  cases hm with
  | mk _ _ _ _ hmems =>
    obtain ⟨a, ha, hxa⟩ := forall₂_getElem?_right hmems hx
    rw [(frame_erase_fields hfe).2.2.1] at ha
    obtain ⟨a', ha', rfl⟩ := addr_of_map ha
    obtain ⟨mi, hmi⟩ := externAddrOk_mem hxa
    obtain ⟨m, hm'⟩ := Option.isSome_iff_exists.1
      (getElem?_isSome_of_length (store_erase_fields hsS).2.1 hmi)
    simp [V1.Execution.frameMemory, ha', hm']

theorem local_res (hfe : Lime1.Execution.ToCore.Frame.erase fC = f.toCore)
    (hf : FrameOk sC fC Cf) {k : Nat} (hx : (Cf.locals[k]?).isSome) : k < f.locals.length := by
  obtain ⟨C₀, lts, hm, hl, rfl⟩ := hf
  have h0 : C₀.locals = [] := hm.ctx_fields.1
  have hx' : (lts[k]?).isSome := by simpa [h0] using hx
  obtain ⟨lt, hlt⟩ := Option.isSome_iff_exists.1 hx'
  obtain ⟨v, hv, -⟩ := forall₂_getElem?_right hl hlt
  rw [(frame_erase_fields hfe).2.2.2.2.2] at hv
  have hk := (List.getElem?_eq_some_iff.1 hv).1
  simpa using hk

/-- The V1 global a Core global's erasure images. -/
theorem global_of_eraseIdx (hsS : Lime1.Execution.ToCore.Store.erase sC =
    (s.mapCode V1.Func.toLime).toCore) {a : Nat} {gi : GlobalInst} (hgi : sC.globals[a]? = some gi) :
    ∃ g, s.globals[a]? = some g ∧ g.mutability = gi.type.mutability := by
  have e := congrArg (fun l => l[a]?) (store_erase_fields hsS).2.2
  simp only [List.getElem?_map, hgi, Option.map_some] at e
  cases hg : s.globals[a]? with
  | none => rw [hg] at e; cases e
  | some g =>
    rw [hg] at e
    refine ⟨g, rfl, ?_⟩
    have e' := congrArg (fun x => x.type.mutability) (Option.some.inj e)
    simp only [Execution.Runtime.GlobalInst.toCore] at e'
    rw [← e']
    unfold Lime1.Execution.ToCore.GlobalInst.erase
    split <;> rfl

theorem global_res (hs : StoreOk sC) (hfe : Lime1.Execution.ToCore.Frame.erase fC = f.toCore)
    (hsS : Lime1.Execution.ToCore.Store.erase sC = (s.mapCode V1.Func.toLime).toCore)
    (hf : FrameOk sC fC Cf) {x : GlobalIdx} {gt : CGlobalType} (hx : Cf.globals[x.toNat]? = some gt) :
    ∃ (a : Execution.Runtime.GlobalAddr) (g : Execution.Runtime.GlobalInst),
      f.module.globals[x.toNat]? = some a ∧ s.globals[a.value]? = some g ∧
        g.mutability = gt.mutability := by
  obtain ⟨a, ha, hxa⟩ := hf.globalVar hx
  obtain ⟨gi, hgi, -, hmut, -⟩ := hxa.global_invVar hs a _ rfl rfl
  rw [(frame_erase_fields hfe).2.2.2.1] at ha
  obtain ⟨a', ha', rfl⟩ := addr_of_map ha
  obtain ⟨g, hg, hgm⟩ := global_of_eraseIdx hsS hgi
  exact ⟨a', g, ha', hg, hgm.trans hmut⟩

end Frame

/-! ## One instruction -/

/-- **A V1 instruction whose Core image is typed in a context that agrees with its frame's names
existing resources.** -/
theorem instrRes_core {s : V1.Execution.Store H} {sC : Store H} (hs : StoreOk sC)
    (hsS : Lime1.Execution.ToCore.Store.erase sC = (s.mapCode V1.Func.toLime).toCore)
    {f : Execution.Runtime.Frame} {fC : Frame}
    (hfe : Lime1.Execution.ToCore.Frame.erase fC = f.toCore) {Cf C : Context}
    (hf : FrameOk sC fC Cf) (hcs : CtxSame C Cf) {i : V1.Instr} {it : InstrType}
    (hi : InstrOk C (V1.Instr.toCore i) it) : Silmaril.Wasm.SpecTec.Sim10.InstrResOk10 s f i := by
  have hloc : ∀ {k : Nat} {lt : LocalType}, C.locals[k]? = some lt → k < f.locals.length :=
    fun hk => local_res hfe hf (by rw [← hcs.locals]; simp [hk])
  cases i with
  | call x =>
    obtain ⟨d, hd⟩ := call_ctx hi
    exact funcs_res hfe hf (hcs.funcs ▸ hd)
  | callIndirect y =>
    obtain ⟨⟨tt, ht⟩, d, hd⟩ := callIndirect_ctx hi
    exact ⟨table_res hfe hsS hf (hcs.tables ▸ ht), types_res hfe hf (hcs.types ▸ hd)⟩
  | localGet x =>
    obtain ⟨t, ht, -⟩ := InstrOk.localGet_inv hi
    exact hloc ht
  | localSet x =>
    obtain ⟨_, t, ht, -⟩ := InstrOk.localSet_inv hi
    exact hloc ht
  | localTee x =>
    obtain ⟨_, t, ht, -⟩ := InstrOk.localTee_inv hi
    exact hloc ht
  | globalGet x =>
    obtain ⟨m, t, ht, -⟩ := Execution.Core.InstrOk.globalGet_inv hi
    obtain ⟨a, g, ha, hg, -⟩ := global_res hs hfe hsS hf (hcs.globals ▸ ht)
    exact ⟨a, g, ha, hg⟩
  | globalSet x =>
    obtain ⟨t, ht, -⟩ := InstrOk.globalSet_inv hi
    obtain ⟨a, g, ha, hg, hm⟩ := global_res hs hfe hsS hf (hcs.globals ▸ ht)
    exact ⟨a, g, ha, hg, hm⟩
  | intLoad t p a =>
    obtain ⟨mt, hm⟩ := intLoad_ctx hi
    exact mem_res hfe hsS hf (hcs.mems ▸ hm)
  | floatLoad t a =>
    obtain ⟨mt, hm⟩ := floatLoad_ctx hi
    exact mem_res hfe hsS hf (hcs.mems ▸ hm)
  | intStore t p a =>
    obtain ⟨mt, hm⟩ := intStore_ctx hi
    exact mem_res hfe hsS hf (hcs.mems ▸ hm)
  | floatStore t a =>
    obtain ⟨mt, hm⟩ := floatStore_ctx hi
    exact mem_res hfe hsS hf (hcs.mems ▸ hm)
  | memorySize =>
    obtain ⟨mt, hm⟩ := memorySize_ctx hi
    exact mem_res hfe hsS hf (hcs.mems ▸ hm)
  | memoryGrow =>
    obtain ⟨mt, hm⟩ := memoryGrow_ctx hi
    exact mem_res hfe hsS hf (hcs.mems ▸ hm)
  | _ => trivial

theorem listToCore_source (s : V1.Execution.Store H) (i : V1.Instr) :
    Lime1.Execution.Admin.listToCore (s.mapCode V1.Func.toLime)
      (V1.Execution.codeToLime [.source i]) = [.plain (V1.Instr.toCore i)] := by
  simp [Execution.Runtime.AdminInstr.map, Lime1.Execution.Admin.toCore]

/-! ## Through the simulation relation -/

open Silmaril.Wasm.Lime1.Execution.ToCore (Rigid map_norm_eq_of_rigid norm_eq_label norm_eq_frame)

/-- The statement of the `ActiveF` induction. -/
def ResCoreP (s : V1.Execution.Store H) (sC : Store H) (f : Execution.Runtime.Frame)
    (code : List V1.Execution.Admin) (f' : Execution.Runtime.Frame)
    (w : List V1.Execution.Admin) : Prop :=
  ∀ (i : V1.Instr), w = [.source i] →
    ∀ (fC : Frame) (L : List Admin) (Cf C : Context) (it : InstrType),
      Lime1.Execution.ToCore.Frame.erase fC = f.toCore →
      L.map (Lime1.Execution.ToCore.Admin.norm fC.module) =
        Lime1.Execution.Admin.listToCore (s.mapCode V1.Func.toLime) (V1.Execution.codeToLime code) →
      FrameOk sC fC Cf → CtxSame C Cf → C.Wf → AdminsOk sC C L it →
      Silmaril.Wasm.SpecTec.Sim10.InstrResOk10 s f' i

/-- The Core image of a V1 instruction is never a `call_ref`, so normalisation fixes it. -/
theorem rigid_toCore (i : V1.Instr) : Rigid (.plain (V1.Instr.toCore i)) := by
  refine ⟨fun x h => ?_, fun x h => ?_⟩ <;> cases i <;> simp [V1.Instr.toCore] at h

/-- The Core image of a V1 instruction is not `throw_ref`. -/
theorem toCore_ne_throwRef (i : V1.Instr) : V1.Instr.toCore i ≠ .throwRef := by
  cases i <;> simp [V1.Instr.toCore]

/-- The piece case. -/
theorem resCoreP_piece {s : V1.Execution.Store H} {sC : Store H} (hs : StoreOk sC)
    (hsS : Lime1.Execution.ToCore.Store.erase sC = (s.mapCode V1.Func.toLime).toCore)
    {f : Execution.Runtime.Frame} {l₁ w l₂ : List V1.Execution.Admin} :
    ResCoreP s sC f (l₁ ++ w ++ l₂) f w := by
  intro i hw fC L Cf C it hfe hL hf hcs hC hty
  subst hw
  simp only [V1.Execution.codeToLime_append, Lime1.Execution.listToCore_append,
    listToCore_source] at hL
  obtain ⟨L₁, M, L₂, rfl, hM⟩ := map_norm_split hL
  have hM' : M = [.plain (V1.Instr.toCore i)] :=
    map_norm_eq_of_rigid (fun y hy => by
      rw [List.mem_singleton.1 hy]; exact rigid_toCore i) hM
  subst hM'
  obtain ⟨xs, it', ha, -⟩ := single_typed' hty hC
  exact instrRes_core hs hsS hfe hf (hcs.initLocals xs)
    (AdminOk.plain_inv ha (toCore_ne_throwRef i))

/-- The label case. -/
theorem resCoreP_label {s : V1.Execution.Store H} {sC : Store H}
    {f f' : Execution.Runtime.Frame} {code w body : List V1.Execution.Admin} {n : Nat}
    {cont : V1.Expr} (hm : .label n cont body ∈ code) (ih : ResCoreP s sC f body f' w) :
    ResCoreP s sC f code f' w := by
  intro i hw fC L Cf C it hfe hL hf hcs hC hty
  obtain ⟨l₁, l₂, rfl⟩ := split_mem hm
  simp only [V1.Execution.codeToLime_append, Lime1.Execution.listToCore_append] at hL
  obtain ⟨L₁, M, L₂, rfl, hM⟩ := map_norm_split hL
  simp only [V1.Execution.codeToLime_cons, V1.Execution.codeToLime_nil,
    Execution.Runtime.AdminInstr.map, Lime1.Execution.listToCore_cons,
    Lime1.Execution.listToCore_nil, List.append_nil] at hM
  obtain ⟨z, rfl, hz⟩ := List.map_eq_singleton_iff.mp hM
  obtain ⟨b', rfl, hb'⟩ := norm_eq_label hz
  obtain ⟨xs, it', ha', hC'⟩ := single_typed' hty hC
  cases ha' with
  | label hn hc hb =>
    have hr := (AdminsOk.params_ok hC' hc).1
    exact ih i hw fC b' Cf _ _ hfe hb' hf ((hcs.initLocals xs).withLabel _) (hC'.withLabel hr) hb

/-- The frame case: the body is read in the frame's own context. -/
theorem resCoreP_frame {s : V1.Execution.Store H} {sC : Store H} (hs : StoreOk sC)
    (hts : StoreTypesOk sC) {f fi f' : Execution.Runtime.Frame}
    {code w body : List V1.Execution.Admin} {n : Nat}
    (hm : .frame n fi body ∈ code) (ih : ResCoreP s sC fi body f' w) :
    ResCoreP s sC f code f' w := by
  intro i hw fC L Cf C it hfe hL hf hcs hC hty
  obtain ⟨l₁, l₂, rfl⟩ := split_mem hm
  simp only [V1.Execution.codeToLime_append, Lime1.Execution.listToCore_append] at hL
  obtain ⟨L₁, M, L₂, rfl, hM⟩ := map_norm_split hL
  simp only [V1.Execution.codeToLime_cons, V1.Execution.codeToLime_nil,
    Execution.Runtime.AdminInstr.map, Lime1.Execution.listToCore_cons,
    Lime1.Execution.listToCore_nil, List.append_nil] at hM
  obtain ⟨z, rfl, hz⟩ := List.map_eq_singleton_iff.mp hM
  obtain ⟨fz, b', rfl, hfz, hb'⟩ := norm_eq_frame hz
  obtain ⟨xs, it', ha', -⟩ := single_typed' hty hC
  cases ha' with
  | frame hf' hn hb hok =>
    rename_i C'' ts
    have hwf : ({ C'' with return_ := some ts } : Context).Wf :=
      (FrameOk.ctxWf hs hts hf').withReturn fun t h => TyOk.of_empty _ (hok t h)
    exact ih i hw fz b' C'' { C'' with return_ := some ts } _ hfz hb' hf'
      ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩ hwf hb

/-- **The `ActiveF` induction.** -/
theorem resCoreP_of_active {s : V1.Execution.Store H} {sC : Store H} (hs : StoreOk sC)
    (hts : StoreTypesOk sC)
    (hsS : Lime1.Execution.ToCore.Store.erase sC = (s.mapCode V1.Func.toLime).toCore)
    {f f' : Execution.Runtime.Frame} {code w : List V1.Execution.Admin}
    (h : Silmaril.Wasm.SpecTec.Sim10.ActiveF f code f' w) : ResCoreP s sC f code f' w := by
  induction h with
  | piece => exact resCoreP_piece hs hsS
  | label hm _ ih => exact resCoreP_label hm ih
  | frame hm _ ih => exact resCoreP_frame hs hts hm ih

/-- **A V1 configuration related to a typed Core configuration satisfies `ResOkL10`.** -/
theorem resOkL10_of_core {c : V1.Execution.Config H} {cc : Config H} {ts : List CValType}
    (hsim : Lime1.Execution.Sim c.toLime cc) (hok : ConfigOk cc ts) :
    Silmaril.Wasm.SpecTec.Sim10.ResOkL10 c.store c.frame c.code := by
  obtain ⟨C, ⟨hs, hf⟩, hty⟩ := hok
  have hts : StoreTypesOk cc.store := ⟨hs.structsClosed, hs.arraysClosed⟩
  have hn := hsim.1
  rcases cc with ⟨sC, fC, L⟩
  obtain ⟨hsS, hfe, hL⟩ := Lime1.Execution.ToCore.Config.norm_eq_toCore_iff.mp hn
  refine resOkL10_of_activeF fun f' i hact => ?_
  exact resCoreP_of_active hs hts hsS hact i rfl fC L C C _ hfe hL hf (CtxSame.refl C)
    (FrameOk.ctxWf hs hts hf) hty

/-- **`ResOkL10` at a `CoreTyped10` configuration.** -/
theorem resOkL10_of_coreTyped10 {c : V1.Execution.Config H} (hc : CoreTyped10 c) :
    Silmaril.Wasm.SpecTec.Sim10.ResOkL10 c.store c.frame c.code := by
  obtain ⟨_, _, hsim, hok⟩ := hc
  exact resOkL10_of_core hsim hok

/-- **`GoodV1` at a `CoreTyped10` configuration with `StoreOk10`**: round 5's `goodV1_of_valid`
without its `ResOkL10` hypothesis. -/
theorem goodV1_of_coreTyped10 {c : V1.Execution.Config H} (hs : StoreOk10 c.store)
    (hc : CoreTyped10 c) : Silmaril.Wasm.SpecTec.Sim10.GoodV1 c :=
  goodV1_of_valid (resOkL10_of_coreTyped10 hc) hs hc

/-- **`GoodV1` along a V1 run** from a `CoreTyped10` configuration whose store has no host
function and satisfies `StoreOk10`. -/
theorem goodV1_steps' {host : V1.Execution.HostSemantics H} {c d : V1.Execution.Config H}
    (h : V1.Execution.Steps host c d) (hnh : Whole.NoHost10 c.store) (hs : StoreOk10 c.store)
    (hc : CoreTyped10 c) : Silmaril.Wasm.SpecTec.Sim10.GoodV1 d :=
  goodV1_steps h hnh hs hc (resOkL10_of_coreTyped10 (coreTyped10_steps h hnh hc).2)

end Silmaril.Wasm.SpecTec.Sim10.Valid
