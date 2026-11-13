module

public import Silmaril.Wasm.Binaryen.CodeSimModule
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce
public import Silmaril.Wasm.Validation.Check.ValidateFinal
public import Silmaril.Wasm.FnInst.Ground.Link.Defs

@[expose] public section

/-! # Computed instances of modules with related bodies

`instOf` (wasm-check's computed instance) runs `instantiateOnce?`: `$evalglobals`
(`evalGlobals?`), then the spec's allocation `prepare?` of the global-free residue and its
segment initialisation `initSegments?`. None of these reads function code, and none changes the
function list after `allocModule?` has built it:

* `constInstr?_wf` … `initSegments?_wf`: running on a store whose function list is replaced
  (`InlS.withFuncs`) is running on the original store and replacing the list afterwards;
* `prepare?_bodiesRel`: allocation of modules with related bodies gives the same frame and
  code and `StoreRel (FuncRel BI)`-related stores (from silmaril's `allocModule?_bodiesRel`);
* `instantiateOnce?_bodiesRel`: the same for single allocation, through the residue;
* `instRel_of_bodiesRel`: **`ModuleBodiesRel BI m m'` and validity of both modules give
  `InstRel BI m m'`**, the hypothesis of the `checkInst` link (`Ground.Link`).
-/

namespace Silmaril.Wasm.FnInst.Ground.Inst

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Validation

variable {H : Type}

/-- Replace the function list of a store. -/
abbrev wf (s : Store H) (X : List (FuncInst H)) : Store H := InlS.withFuncs s X

/-- Replace the function list of the store of a result. -/
abbrev wfP {α : Type} (X : List (FuncInst H)) (p : Store H × α) : Store H × α := (wf p.1 X, p.2)

theorem wf_wf (s : Store H) (X : List (FuncInst H)) : wf (wf s X) s.funcs = s := rfl

/-! ## Lookups and updates ignore the function list -/

theorem wf_global? (s : Store H) (X) (f : Frame) (x : GlobalIdx) :
    (wf s X).global? f x = s.global? f x := rfl
theorem wf_table? (s : Store H) (X) (f : Frame) (x : TableIdx) :
    (wf s X).table? f x = s.table? f x := rfl
theorem wf_elem? (s : Store H) (X) (f : Frame) (x : ElemIdx) :
    (wf s X).elem? f x = s.elem? f x := rfl
theorem wf_mem? (s : Store H) (X) (f : Frame) (x : MemIdx) :
    (wf s X).mem? f x = s.mem? f x := rfl
theorem wf_data? (s : Store H) (X) (f : Frame) (x : DataIdx) :
    (wf s X).data? f x = s.data? f x := rfl
theorem wf_setTable (s : Store H) (X) (a : Nat) (t : TableInst) :
    (wf s X).setTable a t = wf (s.setTable a t) X := rfl
theorem wf_setMem (s : Store H) (X) (a : Nat) (t : MemInst) :
    (wf s X).setMem a t = wf (s.setMem a t) X := rfl
theorem wf_setElem (s : Store H) (X) (a : Nat) (t : List Ref) :
    (wf s X).setElem a t = wf (s.setElem a t) X := rfl
theorem wf_setData (s : Store H) (X) (a : Nat) (t : ByteArray) :
    (wf s X).setData a t = wf (s.setData a t) X := rfl
theorem wf_addStruct (s : Store H) (X) (t : StructInst) :
    (wf s X).addStruct t = wf (s.addStruct t) X := rfl
theorem wf_addArray (s : Store H) (X) (t : ArrayInst) :
    (wf s X).addArray t = wf (s.addArray t) X := rfl
theorem wf_structs (s : Store H) (X) : (wf s X).structs = s.structs := rfl
theorem wf_arrays (s : Store H) (X) : (wf s X).arrays = s.arrays := rfl

/-! ## Constant evaluation -/

theorem structNew?_wf (s : Store H) (X) (f : Frame) (vs : List Val) (x : TypeIdx) :
    structNew? (wf s X) f vs x = (structNew? s f vs x).map (wfP X) := by
  unfold structNew?
  cases f.type? x <;> simp only [Option.bind_eq_bind, Option.bind_none, Option.map_none,
    Option.bind_some, wf_structs, wf_addStruct]
  rename_i d
  cases expandStruct? d <;> simp only [Option.bind_none, Option.map_none, Option.bind_some]
  rename_i fs
  cases popN? vs fs.length <;> simp only [Option.bind_none, Option.map_none, Option.bind_some]
  split_ifs <;> rfl

theorem arrayNewFixed?_wf (s : Store H) (X) (f : Frame) (vs : List Val) (x : TypeIdx)
    (n : Fin (2 ^ 32)) :
    arrayNewFixed? (wf s X) f vs x n = (arrayNewFixed? s f vs x n).map (wfP X) := by
  unfold arrayNewFixed?
  cases f.type? x <;> simp only [Option.bind_eq_bind, Option.bind_none, Option.map_none,
    Option.bind_some, wf_arrays, wf_addArray]
  rename_i d
  cases expandArray? d <;> simp only [Option.bind_none, Option.map_none, Option.bind_some]
  rename_i ft
  cases popN? vs n.val <;> simp only [Option.bind_none, Option.map_none, Option.bind_some]
  split_ifs <;> rfl

theorem bind_congr' {α β : Type} {o : Option α} {g g' : α → Option β} (h : ∀ a, g a = g' a) :
    o.bind g = o.bind g' := by
  rw [funext h]

theorem constInstr?_wf (s : Store H) (X) (f : Frame) (vs : List Val) (i : Instr) :
    constInstr? (wf s X) f vs i = (constInstr? s f vs i).map (wfP X) := by
  cases i <;> simp [constInstr?, structNew?_wf, arrayNewFixed?_wf, wf_global?, Option.map_bind]
  case externConvertAny =>
    refine bind_congr' fun ⟨pre, v⟩ => ?_
    cases v <;> try rfl
    dsimp only
    split_ifs <;> rfl
  case anyConvertExtern =>
    refine bind_congr' fun ⟨pre, v⟩ => ?_
    cases v <;> try rfl
    rename_i r
    cases r <;> rfl
  case intBinOp t op =>
    split_ifs
    · simp only [Option.map_bind, Function.comp_def]
      refine bind_congr' fun p => bind_congr' fun x => bind_congr' fun y => ?_
      split <;> rfl
    · rfl

theorem foldl_constInstr?_wf (X : List (FuncInst H)) (f : Frame) : ∀ (e : Expr)
    (st : Store H × List Val),
    e.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 f st.2 i) (wfP X st) =
      (e.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 f st.2 i) st).map (wfP X)
  | [], _ => rfl
  | i :: e, st => by
    simp only [List.foldlM_cons, constInstr?_wf]
    cases constInstr? st.1 f st.2 i with
    | none => rfl
    | some p => exact foldl_constInstr?_wf X f e p

theorem constExpr?_wf (s : Store H) (X) (f : Frame) (e : Expr) :
    constExpr? (wf s X) f e = (constExpr? s f e).map (wfP X) :=
  foldl_constInstr?_wf X f e (s, [])

theorem evalConst?_wf (s : Store H) (X) (f : Frame) (e : Expr) :
    evalConst? (wf s X) f e = (evalConst? s f e).map (wfP X) := by
  unfold evalConst?
  rw [constExpr?_wf]
  rcases constExpr? s f e with _ | ⟨s', _ | ⟨v, _ | _⟩⟩ <;> rfl

/-! ## Segment initialisation -/

theorem tableInitLoop_wf (X : List (FuncInst H)) (x : TableIdx) (y : ElemIdx) (a : AddrType) :
    ∀ (k : Nat) (n : BitVec 32), n.toNat = k → ∀ (s : Store H) (f : Frame)
      (i : BitVec a.intType.width) (j : BitVec 32),
      tableInitLoop (wf s X) f x y a i j n = (tableInitLoop s f x y a i j n).map (wf · X) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro n hn s f i j
  rw [tableInitLoop, tableInitLoop, wf_table?, wf_elem?]
  rcases s.table? f x with _ | ⟨ta, ti⟩ <;> rcases s.elem? f y with _ | ⟨ea, ei⟩ <;> try rfl
  dsimp only
  split_ifs with hb hz
  · rfl
  · cases ei.refs[j.toNat]? with
    | none => rfl
    | some r =>
      dsimp only
      rw [wf_setTable]
      exact ih _ (hn ▸ bv32_sub_one_lt hz) _ rfl _ _ _ _
  · rfl

theorem memoryInitLoop_wf (X : List (FuncInst H)) (x : MemIdx) (y : DataIdx) (a : AddrType) :
    ∀ (k : Nat) (n : BitVec 32), n.toNat = k → ∀ (s : Store H) (f : Frame)
      (i : BitVec a.intType.width) (j : BitVec 32),
      memoryInitLoop (wf s X) f x y a i j n = (memoryInitLoop s f x y a i j n).map (wf · X) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro n hn s f i j
  rw [memoryInitLoop, memoryInitLoop, wf_mem?, wf_data?]
  rcases s.mem? f x with _ | ⟨ma, mi⟩ <;> rcases s.data? f y with _ | ⟨da, di⟩ <;> try rfl
  dsimp only
  split_ifs with hb hz
  · rfl
  · cases di.bytes.data[j.toNat]? with
    | none => rfl
    | some byte =>
      dsimp only
      split
      · rw [wf_setMem]
        exact ih _ (hn ▸ bv32_sub_one_lt hz) _ rfl _ _ _ _
      · rfl
  · rfl

theorem initElemSeg?_wf (s : Store H) (X) (f : Frame) (k : Nat) (e : Elem) :
    initElemSeg? evalConst? (wf s X) f k e = (initElemSeg? evalConst? s f k e).map (wf · X) := by
  unfold initElemSeg? elemDrop?
  split
  · rfl
  · simp only [wf_elem?, Option.map_map]
    rfl
  · rw [evalConst?_wf]
    rcases evalConst? s f _ with _ | ⟨s₁, v⟩
    · rfl
    · simp only [Option.map_some, wfP]
      rcases v.addr? with _ | ⟨a, i⟩
      · rfl
      · dsimp only
        rw [tableInitLoop_wf X _ _ a _ _ rfl]
        rcases tableInitLoop s₁ f _ _ a i 0 _ with _ | s₂
        · rfl
        · simp only [Option.map_some, wf_elem?, Option.map_map]
          rfl

theorem initDataSeg?_wf (s : Store H) (X) (f : Frame) (k : Nat) (d : Data) :
    initDataSeg? evalConst? (wf s X) f k d = (initDataSeg? evalConst? s f k d).map (wf · X) := by
  unfold initDataSeg? dataDrop?
  split
  · rfl
  · rw [evalConst?_wf]
    rcases evalConst? s f _ with _ | ⟨s₁, v⟩
    · rfl
    · simp only [Option.map_some, wfP]
      rcases v.addr? with _ | ⟨a, i⟩
      · rfl
      · dsimp only
        rw [memoryInitLoop_wf X _ _ a _ _ rfl]
        rcases memoryInitLoop s₁ f _ _ a i 0 _ with _ | s₂
        · rfl
        · simp only [Option.map_some, wf_data?, Option.map_map]
          rfl

theorem initElemList?_wf (X : List (FuncInst H)) (f : Frame) :
    ∀ (es : List (Nat × Elem)) (s : Store H),
      initElemList? evalConst? (wf s X) f es = (initElemList? evalConst? s f es).map (wf · X)
  | [], _ => rfl
  | (k, e) :: es, s => by
    simp only [initElemList?, initElemSeg?_wf]
    cases initElemSeg? evalConst? s f k e with
    | none => rfl
    | some s₁ => exact initElemList?_wf X f es s₁

theorem initDataList?_wf (X : List (FuncInst H)) (f : Frame) :
    ∀ (ds : List (Nat × Data)) (s : Store H),
      initDataList? evalConst? (wf s X) f ds = (initDataList? evalConst? s f ds).map (wf · X)
  | [], _ => rfl
  | (k, d) :: ds, s => by
    simp only [initDataList?, initDataSeg?_wf]
    cases initDataSeg? evalConst? s f k d with
    | none => rfl
    | some s₁ => exact initDataList?_wf X f ds s₁

/-- **Segment initialisation ignores the function list.** -/
theorem initSegments?_wf (s : Store H) (X) (f : Frame) (m : Module) :
    initSegments? evalConst? (wf s X) f m = (initSegments? evalConst? s f m).map (wfP X) := by
  unfold initSegments? initElem? initData?
  rw [initElemList?_wf]
  cases initElemList? evalConst? s f _ with
  | none => rfl
  | some s₁ =>
    simp only [Option.map_some, initDataList?_wf]
    cases initDataList? evalConst? s₁ f _ <;> rfl

/-- Segment initialisation keeps the function list. -/
theorem initSegments?_funcs {s s' : Store H} {f f' : Frame} {m : Module}
    (h : initSegments? evalConst? s f m = some (s', f')) : s'.funcs = s.funcs := by
  have h' : initSegments? evalConst? (wf s s.funcs) f m = some (wf s' s.funcs, f') := by
    rw [initSegments?_wf, h]
    rfl
  have he : wf s s.funcs = s := rfl
  rw [he, h] at h'
  have : s' = wf s' s.funcs := congrArg Prod.fst (Option.some.inj h')
  rw [this]
  rfl

/-! ## Allocation of modules with related bodies -/

/-- The function relation of `ModuleBodiesRel`. -/
abbrev FQ (BI : List Instr → List Instr → Prop) (f g : Func) : Prop :=
  f.type = g.type ∧ f.locals = g.locals ∧ InstrsRel BI f.body g.body

theorem initial_withFuncs (s : Store H) (m : Module) {gs : List Func} (xas : List ExternAddr)
    (h : gs.length = m.funcs.length) :
    ModuleInst.initial s { m with funcs := gs } xas = ModuleInst.initial s m xas := by
  simp only [ModuleInst.initial, h]

/-- The last step of `prepare?`: allocation, with the segment code. -/
theorem prepare?_alloc {BI : List Instr → List Instr → Prop} {m : Module} {gs : List Func}
    (hfs : List.Forall₂ (FQ BI) m.funcs gs) {s₃ : Store H} {xas : List ExternAddr}
    {vG : List Val} {rT : List Ref} {rE : List (List Ref)} {code : List Admin}
    {sx : Option FuncIdx} {c : Config H} {st : Option FuncIdx}
    (h : (match allocModule? s₃ m xas vG rT rE with
      | none => none
      | some (s₄, mi) => some ((⟨s₄, { module := mi }, code⟩ : Config H), sx)) = some (c, st)) :
    ∃ c' : Config H, (match allocModule? s₃ { m with funcs := gs } xas vG rT rE with
      | none => none
      | some (s₄, mi) => some ((⟨s₄, { module := mi }, code⟩ : Config H), sx)) = some (c', st) ∧
      c'.frame = c.frame ∧ c'.code = c.code ∧ StoreRel (FuncRel BI) c.store c'.store := by
  rcases hA : allocModule? s₃ m xas vG rT rE with _ | ⟨s₄, mi⟩
  · simp only [hA, reduceCtorEq] at h
  · obtain ⟨s₄', hA', hst⟩ := allocModule?_bodiesRel hfs hA
    have hc : ((⟨s₄, { module := mi }, code⟩ : Config H), sx) = (c, st) := by
      simpa only [hA, Option.some.injEq] using h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
    exact ⟨⟨s₄', { module := mi }, code⟩, by rw [hA'], rfl, rfl, hst⟩

/-- **Allocation of modules with related bodies**: the same frame and code, and related
stores. -/
theorem prepare?_bodiesRel {ev : Store H → Frame → Expr → Option (Store H × Val)}
    {BI : List Instr → List Instr → Prop} {m : Module} {gs : List Func}
    (hfs : List.Forall₂ (FQ BI) m.funcs gs) {s : Store H} {xas : List ExternAddr}
    {c : Config H} {st : Option FuncIdx} (h : prepare? ev s m xas = some (c, st)) :
    ∃ c', prepare? ev s { m with funcs := gs } xas = some (c', st) ∧ c'.frame = c.frame ∧
      c'.code = c.code ∧ StoreRel (FuncRel BI) c.store c'.store := by
  unfold prepare? at h ⊢
  rw [initial_withFuncs _ _ _ hfs.length_eq.symm]
  dsimp only
  split at h
  · rename_i hc
    split
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · exact prepare?_alloc hfs h
    · exact absurd hc ‹_›
  · cases h

/-- A store whose function list is replaced by a related one is related. -/
theorem storeRel_wf {BI : List Instr → List Instr → Prop} {s t s₁ : Store H}
    (hst : StoreRel (FuncRel BI) s t) (hf : s₁.funcs = s.funcs) :
    StoreRel (FuncRel BI) s₁ (wf s₁ t.funcs) :=
  ⟨by rw [hf]; exact hst.types, rfl, by rw [hf]; exact hst.funcs⟩

/-- Segment initialisation of a module with related bodies, on a related store. -/
theorem initSegments?_rel {BI : List Instr → List Instr → Prop} {m : Module} {gs : List Func}
    {c c' : Config H} (hfr : c'.frame = c.frame) (hst : StoreRel (FuncRel BI) c.store c'.store)
    {s₁ : Store H} {f₁ : Frame} (hi : initSegments? evalConst? c.store c.frame m = some (s₁, f₁)) :
    initSegments? evalConst? c'.store c'.frame { m with funcs := gs } =
      some (wf s₁ c'.store.funcs, f₁) := by
  have hc' : c'.store = wf c.store c'.store.funcs := (storeRel_eq_withFuncs hst).symm
  have hseg : initSegments? evalConst? (wf c.store c'.store.funcs) c.frame m =
      some (wf s₁ c'.store.funcs, f₁) := by
    rw [initSegments?_wf, hi]
    rfl
  rw [hfr, hc']
  exact hseg

/-- **Direct instantiation of modules with related bodies.** -/
theorem instantiateDirect?_bodiesRel {BI : List Instr → List Instr → Prop} {m : Module}
    {gs : List Func} (hfs : List.Forall₂ (FQ BI) m.funcs gs) {s s' : Store H}
    {xas : List ExternAddr} {f' : Frame} {st : Option FuncIdx}
    (h : instantiateDirect? s m xas = some (s', f', st)) :
    ∃ s'', instantiateDirect? s { m with funcs := gs } xas = some (s'', f', st) ∧
      StoreRel (FuncRel BI) s' s'' := by
  unfold instantiateDirect? prepareDirect? at h ⊢
  split at h
  · cases h
  · rename_i c st₀ hp
    obtain ⟨c', hp', hfr, -, hst⟩ := prepare?_bodiesRel hfs hp
    rw [hp']
    split at h
    · cases h
    · rename_i s₁ f₁ hi
      have he : (s₁, f₁, st₀) = (s', f', st) := Option.some.inj h
      obtain ⟨rfl, rfl, rfl⟩ : s₁ = s' ∧ f₁ = f' ∧ st₀ = st := by simpa only [Prod.mk.injEq] using he
      refine ⟨wf s₁ c'.store.funcs, ?_, storeRel_wf hst (initSegments?_funcs hi)⟩
      show (match initSegments? evalConst? c'.store c'.frame { m with funcs := gs } with
        | none => none | some (s', f') => some (s', f', st₀)) = _
      rw [initSegments?_rel hfr hst hi]

/-- **Single allocation of modules with related bodies**: the same frame and start function,
and related stores. -/
theorem instantiateOnce?_bodiesRel {BI : List Instr → List Instr → Prop} {m m' : Module}
    (hrel : ModuleBodiesRel BI m m') {s s' : Store H} {xas : List ExternAddr} {f' : Frame}
    {st : Option FuncIdx} (h : instantiateOnce? s m xas = some (s', f', st)) :
    ∃ s'', instantiateOnce? s m' xas = some (s'', f', st) ∧ StoreRel (FuncRel BI) s' s'' := by
  have hm' : m' = { m with funcs := m'.funcs } := hrel.eq_withFuncs
  have hfs : List.Forall₂ (FQ BI) m.globalResidue.funcs m'.funcs := hrel.funcs
  rw [hm']
  unfold instantiateOnce? at h ⊢
  rw [initial_withFuncs _ _ _ hrel.funcs.length_eq.symm]
  split at h
  · cases h
  · rename_i s₁ f₁ vs hG
    have hG' := hG
    simp only [Module.closedGlobalTypes] at hG' ⊢
    rw [hG']
    exact instantiateDirect?_bodiesRel hfs h

theorem instantiateOnce?_none {BI : List Instr → List Instr → Prop} {m m' : Module}
    (hrel : ModuleBodiesRel BI m m') {s : Store H} {xas : List ExternAddr}
    (h : instantiateOnce? s m xas = none) : instantiateOnce? s m' xas = none := by
  rcases h' : instantiateOnce? s m' xas with _ | ⟨s₁, f₁, st⟩
  · rfl
  · obtain ⟨s₂, h₂, -⟩ := instantiateOnce?_bodiesRel hrel.flip h'
    rw [h] at h₂
    cases h₂

/-! ## The computed instance -/

open Silmaril.Wasm.Verify (instOf instance? instImps instFrom)
open Silmaril.Wasm.Game (ScalarInstance FnType exportFuncAddrs)

/-- Related stores have the same function types at every address. -/
theorem type_bind_of_storeRel {BI : List Instr → List Instr → Prop} {s t : Store Nat}
    (hst : StoreRel (FuncRel BI) s t) (a : Nat) :
    (s.funcs[a]?.bind fun fi => FnType.ofDefType? fi.type) =
      t.funcs[a]?.bind fun fi => FnType.ofDefType? fi.type := by
  have ht : (s.funcs.map FuncInst.type)[a]? = (t.funcs.map FuncInst.type)[a]? := by
    rw [hst.types]
  simp only [List.getElem?_map] at ht
  cases hs : s.funcs[a]? <;> cases htt : t.funcs[a]? <;> simp_all

/-- The instance read off related stores. -/
theorem instFrom_storeRel {BI : List Instr → List Instr → Prop} {s t : Store Nat}
    (hst : StoreRel (FuncRel BI) s t) (mt : CModuleType) (imps : List FnType) (f : Frame) :
    instFrom mt imps t f = (instFrom mt imps s f).map fun p => (p.1, { p.2 with store := t }) := by
  unfold instFrom
  simp only [type_bind_of_storeRel hst, Option.map_map]
  rfl

/-- The instance of an optional result (an empty instance when there is none), as in `instOf`. -/
def instD (r : Option (CModuleType × ScalarInstance)) : ScalarInstance :=
  (r.map (·.2)).getD ⟨[], [], [], {}⟩

/-- Two optional instances whose stores are related and whose export addresses agree. -/
def ORel (BI : List Instr → List Instr → Prop) (r r' : Option (CModuleType × ScalarInstance)) :
    Prop :=
  StoreRel (FuncRel BI) (instD r).store (instD r').store ∧ (instD r).addrs = (instD r').addrs

theorem oRel_none (BI : List Instr → List Instr → Prop) : ORel BI none none :=
  ⟨StoreRel.refl (fun f => FuncRel.refl f) _, rfl⟩

theorem oRel_instFrom {BI : List Instr → List Instr → Prop} {s t : Store Nat}
    (hst : StoreRel (FuncRel BI) s t) (mt : CModuleType) (imps : List FnType) (f : Frame) :
    ORel BI (instFrom mt imps s f) (instFrom mt imps t f) := by
  unfold instFrom
  simp only [type_bind_of_storeRel hst]
  cases (exportFuncAddrs f.module).mapM fun a => t.funcs[a]?.bind fun fi =>
      FnType.ofDefType? fi.type with
  | none => exact oRel_none BI
  | some p => exact ⟨hst, rfl⟩

/-- The instances of modules with related bodies, against one import list. -/
theorem oRel_instImps {BI : List Instr → List Instr → Prop} {m m' : Module}
    (hrel : ModuleBodiesRel BI m m') (mt : CModuleType) (imps : List FnType) :
    ORel BI (instImps m mt imps) (instImps m' mt imps) := by
  unfold instImps
  rcases h : instantiateOnce? (Silmaril.Wasm.Game.importStore (CExternType.funcs mt.imports)) m
      ((List.range mt.imports.length).map ExternAddr.func) with _ | ⟨s₁, f, st⟩
  · rw [instantiateOnce?_none hrel h]
    exact oRel_none BI
  · obtain ⟨s₂, h₂, hst⟩ := instantiateOnce?_bodiesRel hrel h
    rw [h₂]
    cases st with
    | none => exact oRel_instFrom hst mt imps f
    | some _ => exact oRel_none BI

/-- **The computed instances of valid modules with related bodies are related**: the
hypotheses of `ExportEquiv`'s transfer (`exportRefines_of_bodiesRel`) give `InstRel`. -/
theorem instRel_of_bodiesRel {BI : List Instr → List Instr → Prop} {m m' : Module}
    (hrel : ModuleBodiesRel BI m m') (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    Check.InstRel BI m m' := by
  obtain ⟨mt, hmt⟩ := hm
  obtain ⟨mt', hmt'⟩ := hm'
  have he : mt = mt' := hrel.moduleOk_type hmt hmt'
  have hv : validate? m = some mt := validate?_complete hmt
  have hv' : validate? m' = some mt := he ▸ validate?_complete hmt'
  have ho : ORel BI (instance? m) (instance? m') := by
    unfold instance?
    rw [hv, hv']
    dsimp only [Option.bind_some]
    split
    · cases ((CExternType.funcs mt.imports).mapM FnType.ofDefType?) with
      | none => exact oRel_none BI
      | some imps => exact oRel_instImps hrel mt imps
    · exact oRel_none BI
  unfold Check.InstRel instOf
  exact ho

end Silmaril.Wasm.FnInst.Ground.Inst
