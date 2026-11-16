module

public import Silmaril.Wasm.Execution.MemRep.Sim.Thms
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce
public import Silmaril.Wasm.Execution.Core.Exec.ExternAddrCheck
public import Silmaril.Wasm.SingleThreaded.Interface

/-! Proofs for `Silmaril.Wasm.Execution.MemRep.Inst.Thms`. The structure follows the host-type
change `instantiateOnce?_mapH` (`Proofs.Wasm.Component.Reference.HostMap`): every function of
the chain is pushed through `Store.toBytes`, which changes only the memories. -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Execution.MemRepInst

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution (MemRep LawfulMemRep)

variable {H R : Type} [MemRep R]

/-- Read the store of an optional result through `toBytes`. -/
def mapS {α : Type} : Option (Store H R × α) → Option (Store H × α) :=
  Option.map fun p => (p.1.toBytes, p.2)

@[simp] theorem mapS_some {α} (s : Store H R) (a : α) :
    mapS (some (s, a)) = some (s.toBytes, a) := rfl
@[simp] theorem mapS_none {α} : mapS (α := α) (none : Option (Store H R × α)) = none := rfl
@[simp] theorem toBytes_globals (s : Store H R) : s.toBytes.globals = s.globals := rfl
@[simp] theorem toBytes_funcs (s : Store H R) : s.toBytes.funcs = s.funcs := rfl
@[simp] theorem toBytes_structs (s : Store H R) : s.toBytes.structs = s.structs := rfl
@[simp] theorem toBytes_arrays (s : Store H R) : s.toBytes.arrays = s.arrays := rfl
@[simp] theorem global?_toBytes (s : Store H R) f x : s.toBytes.global? f x = s.global? f x := rfl
@[simp] theorem addStruct_toBytes (s : Store H R) si :
    s.toBytes.addStruct si = (s.addStruct si).toBytes := rfl
@[simp] theorem addArray_toBytes (s : Store H R) ai :
    s.toBytes.addArray ai = (s.addArray ai).toBytes := rfl

@[simp] theorem mapS_bind {α β} (o : Option β) (k : β → Option (Store H R × α)) :
    mapS (o.bind k) = o.bind fun b => mapS (k b) := by cases o <;> rfl
@[simp] theorem mapS_ite {α} (c : Prop) [Decidable c] (a b : Option (Store H R × α)) :
    mapS (if c then a else b) = if c then mapS a else mapS b := by split <;> rfl

/-! ## Constant evaluation -/

theorem structNew?_toBytes (s : Store H R) f vs x :
    structNew? s.toBytes f vs x = mapS (structNew? s f vs x) := by
  simp [structNew?]

theorem arrayNewFixed?_toBytes (s : Store H R) f vs x n :
    arrayNewFixed? s.toBytes f vs x n = mapS (arrayNewFixed? s f vs x n) := by
  simp [arrayNewFixed?]

theorem constInstr?_toBytes (s : Store H R) f vs i :
    constInstr? s.toBytes f vs i = mapS (constInstr? s f vs i) := by
  cases i <;> simp only [constInstr?, structNew?_toBytes, arrayNewFixed?_toBytes, mapS_bind,
    mapS_some, mapS_none, mapS_ite, global?_toBytes, Option.bind_eq_bind] <;>
    first
      | (congr 1; funext p; split <;> (try split_ifs) <;> rfl)
      | (split_ifs <;> first | rfl |
          (congr 1; funext p; congr 1; funext x; congr 1; funext y; split <;> rfl))

theorem constExpr?_toBytes (s : Store H R) f e :
    constExpr? s.toBytes f e = mapS (constExpr? s f e) := by
  unfold constExpr?
  generalize ([] : List Val) = vs
  induction e generalizing s vs with
  | nil => rfl
  | cons i e ih =>
    simp only [List.foldlM_cons, constInstr?_toBytes]
    cases constInstr? s f vs i with
    | none => rfl
    | some p => exact ih p.1 p.2

theorem evalConst?_toBytes (s : Store H R) f e :
    evalConst? s.toBytes f e = mapS (evalConst? s f e) := by
  unfold evalConst?
  rw [constExpr?_toBytes]
  cases constExpr? s f e with
  | none => rfl
  | some p =>
    obtain ⟨s', vs⟩ := p
    match vs with
    | [] => rfl
    | [v] => rfl
    | _ :: _ :: _ => rfl

theorem evalGlobals?_toBytes (s : Store H R) f gs es :
    evalGlobals? evalConst? s.toBytes f gs es = mapS (evalGlobals? evalConst? s f gs es) := by
  induction gs generalizing s f es with
  | nil => cases es <;> rfl
  | cons gt gs ih =>
    cases es with
    | nil => rfl
    | cons e es =>
      simp only [evalGlobals?, evalConst?_toBytes]
      rcases evalConst? s f e with _ | ⟨s', v⟩
      · rfl
      · dsimp only [mapS_some]
        rw [show allocGlobal s'.toBytes gt v =
          ((allocGlobal s' gt v).1.toBytes, (allocGlobal s' gt v).2) from rfl]
        dsimp only
        rw [ih]
        split <;> split <;> simp_all [mapS]

theorem evalExprs?_toBytes (s : Store H R) f es :
    evalExprs? evalConst? s.toBytes f es = mapS (evalExprs? evalConst? s f es) := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    simp only [evalExprs?, evalConst?_toBytes]
    rcases evalConst? s f e with _ | ⟨s', _ | _ | r⟩ <;> try rfl
    simp only [mapS_some, ih]
    rcases evalExprs? evalConst? s' f es with _ | ⟨s'', f'', rs⟩ <;> rfl

theorem evalExprss?_toBytes (s : Store H R) f ess :
    evalExprss? evalConst? s.toBytes f ess = mapS (evalExprss? evalConst? s f ess) := by
  induction ess generalizing s f with
  | nil => rfl
  | cons es ess ih =>
    simp only [evalExprss?, evalExprs?_toBytes]
    rcases evalExprs? evalConst? s f es with _ | ⟨s', f', rs⟩ <;> try rfl
    simp only [mapS_some, ih]
    rcases evalExprss? evalConst? s' f' ess with _ | ⟨s'', f'', rss⟩ <;> rfl

/-! ## Allocation -/

theorem allocMany_toBytes {α : Type} (alloc : Store H R → α → Store H R × Nat)
    (alloc' : Store H → α → Store H × Nat)
    (h : ∀ (s : Store H R) x, alloc' s.toBytes x = ((alloc s x).1.toBytes, (alloc s x).2))
    (s : Store H R) (xs : List α) :
    allocMany alloc' s.toBytes xs =
      ((allocMany alloc s xs).1.toBytes, (allocMany alloc s xs).2) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [allocMany, h, ih]

theorem allocFunc_toBytes (s : Store H R) d (code : FuncCode H) mi :
    allocFunc s.toBytes d code mi =
      ((allocFunc s d code mi).1.toBytes, (allocFunc s d code mi).2) :=
  rfl

omit [MemRep R] in
theorem toBytes_zeros [MemRep R] [LawfulMemRep R] (n : Nat) :
    MemRep.toBytes (MemRep.zeros (R := R) n) = ByteArray.mk (Array.replicate n 0) := by
  have h := LawfulMemRep.zeros_eq (R := R) n
  cases hb : MemRep.toBytes (MemRep.zeros (R := R) n) with
  | mk a =>
    rw [hb] at h
    congr 1
    exact Array.ext' (by simpa using h)

theorem allocMem_toBytes [LawfulMemRep R] (s : Store H R) (m : MemoryType) :
    allocMem s.toBytes m = ((allocMem s m).1.toBytes, (allocMem s m).2) := by
  simp only [allocMem, Store.toBytes, List.map_append, List.map_cons, List.map_nil,
    List.length_map, MemInst.toBytes, toBytes_zeros, MemRep.zeros_byteArray]

theorem allocModule?_toBytes [LawfulMemRep R] (s : Store H R) m xas valsG refsT refsE :
    allocModule? s.toBytes m xas valsG refsT refsE =
      mapS (allocModule? s m xas valsG refsT refsE) := by
  simp only [allocModule?, toBytes_funcs,
    allocMany_toBytes (allocTag (H := H) (R := R)) allocTag (fun _ _ => rfl),
    allocMany_toBytes (fun (s : Store H R) (p : CGlobalType × Val) => allocGlobal s p.1 p.2)
      (fun (s : Store H) (p : CGlobalType × Val) => allocGlobal s p.1 p.2) (fun _ _ => rfl),
    allocMany_toBytes (allocMem (H := H) (R := R)) allocMem allocMem_toBytes,
    allocMany_toBytes (fun (s : Store H R) (p : CTableType × Ref) => allocTable s p.1 p.2)
      (fun (s : Store H) (p : CTableType × Ref) => allocTable s p.1 p.2) (fun _ _ => rfl),
    allocMany_toBytes (allocData (H := H) (R := R)) allocData (fun _ _ => rfl),
    allocMany_toBytes (fun (s : Store H R) (p : CRefType × List Ref) => allocElem s p.1 p.2)
      (fun (s : Store H) (p : CRefType × List Ref) => allocElem s p.1 p.2) (fun _ _ => rfl),
    Option.bind_eq_bind, mapS_bind]
  congr 1; funext tagTypes; congr 1; funext funcTypes; congr 1; funext xi
  rw [allocMany_toBytes (fun (s : Store H R) (p : DefType × Func) => allocFunc s p.1 (.wasm p.2) _)
    (fun (s : Store H) (p : DefType × Func) => allocFunc s p.1 (.wasm p.2) _)
    (fun _ _ => allocFunc_toBytes _ _ _ _)]
  rfl

theorem initial_toBytes (s : Store H R) m xas :
    ModuleInst.initial s.toBytes m xas = ModuleInst.initial s m xas := rfl

/-! ## Segment initialisation -/

theorem tableInitLoop_toBytes (s : Store H R) f x y a i j n :
    tableInitLoop s.toBytes f x y a i j n = (tableInitLoop s f x y a i j n).map Store.toBytes := by
  induction hn : n.toNat using Nat.strong_induction_on generalizing s i j n with
  | _ k ih =>
    rw [tableInitLoop, tableInitLoop]
    show (match s.table? f x, s.elem? f y with
      | some (ta, ti), some (_, ei) => _ | _, _ => none) = _
    rcases s.table? f x with _ | ⟨ta, ti⟩ <;> rcases s.elem? f y with _ | ⟨_, ei⟩ <;>
      try rfl
    dsimp only
    split_ifs with h₁ h₂
    · rfl
    · rcases ei.refs[j.toNat]? with _ | r
      · rfl
      · exact ih _ (hn ▸ bv32_sub_one_lt h₂) (s.setTable ta _) _ _ _ rfl
    · rfl

theorem memoryInitLoop_toBytes [LawfulMemRep R] (s : Store H R) f x y a i j n :
    memoryInitLoop s.toBytes f x y a i j n =
      (memoryInitLoop s f x y a i j n).map Store.toBytes := by
  induction hn : n.toNat using Nat.strong_induction_on generalizing s i j n with
  | _ k ih =>
    rw [memoryInitLoop, memoryInitLoop, Silmaril.Wasm.Execution.Core.Store.mem?_toBytes,
      show s.toBytes.data? f y = s.data? f y from rfl]
    rcases s.mem? f x with _ | ⟨ma, mi⟩ <;> rcases s.data? f y with _ | ⟨_, di⟩ <;> try rfl
    dsimp only [Option.map_some]
    rw [show MemRep.size (R := ByteArray) mi.toBytes.bytes = MemRep.size mi.bytes from
      (LawfulMemRep.size_eq _).symm]
    split_ifs with h₁ h₂
    · rfl
    · rcases di.bytes.data[j.toNat]? with _ | byte
      · rfl
      · dsimp only
        have hst := LawfulMemRep.store_eq mi.bytes (effAddr i.toNat memarg0)
          (count := PackSize.i8.width / 8) ((BitVec.ofNat 32 byte.toNat).setWidth _)
        simp only [MemInst.toBytes, MemRep.store_byteArray] at hst ⊢
        rw [← hst]
        rcases MemRep.store mi.bytes (effAddr i.toNat memarg0) (count := PackSize.i8.width / 8)
          ((BitVec.ofNat 32 byte.toNat).setWidth _) with _ | b
        · rfl
        · have := ih _ (hn ▸ bv32_sub_one_lt h₂) (s.setMem ma { mi with bytes := b })
            (i + 1) (j + 1) (n - 1) rfl
          rw [Silmaril.Wasm.Execution.Core.Store.setMem_toBytes] at this
          exact this
    · rfl

theorem initElemSeg?_toBytes (s : Store H R) f k e :
    initElemSeg? evalConst? s.toBytes f k e =
      (initElemSeg? evalConst? s f k e).map Store.toBytes := by
  unfold initElemSeg?
  split
  · rfl
  · simp only [elemDrop?, Option.map_map]; rfl
  · rw [evalConst?_toBytes]
    rcases evalConst? s f _ with _ | ⟨s₁, v⟩
    · rfl
    · dsimp only [mapS_some]
      rcases v.addr? with _ | ⟨a, i⟩
      · rfl
      · dsimp only
        rw [tableInitLoop_toBytes]
        rcases tableInitLoop s₁ f _ _ a i 0 _ with _ | s₂
        · rfl
        · simp only [Option.map_some, elemDrop?, Option.map_map]; rfl

theorem initDataSeg?_toBytes [LawfulMemRep R] (s : Store H R) f k d :
    initDataSeg? evalConst? s.toBytes f k d =
      (initDataSeg? evalConst? s f k d).map Store.toBytes := by
  unfold initDataSeg?
  split
  · rfl
  · rw [evalConst?_toBytes]
    rcases evalConst? s f _ with _ | ⟨s₁, v⟩
    · rfl
    · dsimp only [mapS_some]
      rcases v.addr? with _ | ⟨a, i⟩
      · rfl
      · dsimp only
        rw [memoryInitLoop_toBytes]
        rcases memoryInitLoop s₁ f _ _ a i 0 _ with _ | s₂
        · rfl
        · simp only [Option.map_some, dataDrop?, Option.map_map]; rfl

theorem initElemList?_toBytes (s : Store H R) f es :
    initElemList? evalConst? s.toBytes f es =
      (initElemList? evalConst? s f es).map Store.toBytes := by
  induction es generalizing s with
  | nil => rfl
  | cons p es ih =>
    obtain ⟨k, e⟩ := p
    simp only [initElemList?, initElemSeg?_toBytes]
    rcases initElemSeg? evalConst? s f k e with _ | s₁
    · rfl
    · exact ih s₁

theorem initDataList?_toBytes [LawfulMemRep R] (s : Store H R) f ds :
    initDataList? evalConst? s.toBytes f ds =
      (initDataList? evalConst? s f ds).map Store.toBytes := by
  induction ds generalizing s with
  | nil => rfl
  | cons p ds ih =>
    obtain ⟨k, d⟩ := p
    simp only [initDataList?, initDataSeg?_toBytes]
    rcases initDataSeg? evalConst? s f k d with _ | s₁
    · rfl
    · exact ih s₁

theorem initSegments?_toBytes [LawfulMemRep R] (s : Store H R) f m :
    initSegments? evalConst? s.toBytes f m = mapS (initSegments? evalConst? s f m) := by
  simp only [initSegments?, initElem?, initData?, initElemList?_toBytes]
  rcases initElemList? evalConst? s f _ with _ | s₁
  · rfl
  · simp only [Option.map_some, initDataList?_toBytes]
    rcases initDataList? evalConst? s₁ f _ with _ | s₂ <;> rfl

/-! ## Instantiation -/

/-- `mapS` on configurations. -/
def mapC {α : Type} : Option (Config H R × α) → Option (Config H × α) :=
  Option.map fun p => (p.1.toBytes, p.2)

theorem prepare?_toBytes [LawfulMemRep R] (s : Store H R) m xas :
    prepare? evalConst? s.toBytes m xas = mapC (prepare? evalConst? s m xas) := by
  unfold prepare?
  split_ifs
  · rw [initial_toBytes, evalGlobals?_toBytes]
    rcases evalGlobals? evalConst? s _ _ _ with _ | ⟨s₁, f₁, valsG⟩
    · rfl
    · dsimp only [mapS_some]
      rw [evalExprs?_toBytes]
      rcases evalExprs? evalConst? s₁ f₁ _ with _ | ⟨s₂, f₂, refsT⟩
      · rfl
      · dsimp only [mapS_some]
        rw [evalExprss?_toBytes]
        rcases evalExprss? evalConst? s₂ f₂ _ with _ | ⟨s₃, f₃, refsE⟩
        · rfl
        · dsimp only [mapS_some]
          rw [allocModule?_toBytes]
          rcases allocModule? s₃ m xas valsG refsT refsE with _ | ⟨s₄, mi⟩ <;> rfl
  · rfl

theorem instantiateDirect?_toBytes [LawfulMemRep R] (s : Store H R) m xas :
    instantiateDirect? s.toBytes m xas = mapS (instantiateDirect? s m xas) := by
  simp only [instantiateDirect?, prepareDirect?, prepare?_toBytes]
  rcases prepare? evalConst? s m xas with _ | ⟨c, st⟩
  · rfl
  · dsimp only [mapC, Option.map_some, Config.toBytes]
    rw [initSegments?_toBytes]
    split <;> split <;> simp_all [mapS]

theorem instantiateOnce?_toBytes [LawfulMemRep R] (s : Store H R) m xas :
    instantiateOnce? s.toBytes m xas = mapS (instantiateOnce? s m xas) := by
  unfold instantiateOnce?
  rw [initial_toBytes, evalGlobals?_toBytes]
  rcases evalGlobals? evalConst? s _ _ _ with _ | ⟨s₁, f₁, vs⟩
  · rfl
  · exact instantiateDirect?_toBytes s₁ _ _

/-! ## External addresses -/

omit [MemRep R] in
theorem externAddrType?_toBytes [MemRep R] (s : Store H R) (xa : ExternAddr) :
    externAddrType? s.toBytes xa = externAddrType? s xa := by
  cases xa <;> simp only [externAddrType?, Store.toBytes, List.getElem?_map, Option.map_map,
    Function.comp_def, MemInst.toBytes]

omit [MemRep R] in
theorem externAddrsOk?_toBytes [MemRep R] (s : Store H R) :
    ∀ (xas : List ExternAddr) (xts : List CExternType),
      externAddrsOk? s.toBytes xas xts = externAddrsOk? s xas xts
  | [], [] => rfl
  | xa :: xas, xt :: xts => by
    simp only [externAddrsOk?, externAddrOk?, externAddrType?_toBytes,
      externAddrsOk?_toBytes s xas xts]
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

/-! ## The component-facing accessors -/

open Silmaril.Wasm.SingleThreaded

theorem allocHost_toBytes (s : Store H R) ft (h : H) :
    allocHost s.toBytes ft h = ((allocHost s ft h).1.toBytes, (allocHost s ft h).2) := rfl

theorem memAddrType?_toBytes (s : Store H R) (a : Nat) :
    memAddrType? s.toBytes a = memAddrType? s a := by
  simp only [memAddrType?, Store.toBytes, List.getElem?_map, Option.map_map, Function.comp_def,
    MemInst.toBytes]

theorem tableAddrType?_toBytes (s : Store H R) (a : Nat) :
    tableAddrType? s.toBytes a = tableAddrType? s a := rfl

theorem tableFunc?_toBytes (s : Store H R) (t i : Nat) :
    tableFunc? s.toBytes t i = tableFunc? s t i := rfl

theorem memSize?_toBytes [LawfulMemRep R] (s : Store H R) (a : Nat) :
    memSize? s.toBytes a = memSize? s a := by
  simp only [memSize?, Store.toBytes, List.getElem?_map, Option.map_map, Function.comp_def,
    MemInst.toBytes, LawfulMemRep.size_eq, MemRep.toBytes_byteArray]

theorem memRead?_toBytes [LawfulMemRep R] (s : Store H R) (a start len : Nat) :
    memRead? s.toBytes a start len = memRead? s a start len := by
  simp only [memRead?, Store.toBytes, List.getElem?_map, Option.bind_eq_bind]
  cases s.mems[a]? <;> simp [MemInst.toBytes, LawfulMemRep.readBytes_eq]

theorem memWrite?_toBytes [LawfulMemRep R] (s : Store H R) (a start : Nat) (bs : ByteArray) :
    memWrite? s.toBytes a start bs = (memWrite? s a start bs).map Store.toBytes := by
  unfold memWrite?
  rw [show s.toBytes.mems[a]? = s.mems[a]?.map MemInst.toBytes by
    simp only [Store.toBytes, List.getElem?_map]]
  cases s.mems[a]? with
  | none => rfl
  | some mi =>
    have hw := LawfulMemRep.writeBytes_eq mi.bytes start bs
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, MemInst.toBytes,
      MemRep.writeBytes_byteArray, ← hw]
    cases MemRep.writeBytes mi.bytes start bs with
    | none => rfl
    | some b =>
      simp only [Option.map_some, Option.bind_some, Option.pure_def, Store.setMem_toBytes]
      rfl

end Silmaril.Proofs.Wasm.Execution.MemRepInst
