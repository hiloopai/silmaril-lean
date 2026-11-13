module

public import Silmaril.Proofs.Wasm.Component.Lime1Eng.ConstBack
public import Silmaril.Proofs.Wasm.Component.Lime1Eng.Alloc
public import Silmaril.Proofs.Wasm.Component.Lime1Inst.Retract
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# Core 3.0 segment initialisation resolves the Lime1 segments

Lime1's `prepare?` resolves every element and data segment (offset, target, bounds) in the
allocated store before writing any of them; Core 3.0's executable `initSegments?` runs the segment
programs one after the other. A Core write changes neither the globals nor the size of a table
or memory (`Same`), so every Core segment check is made against the sizes of the allocated store.
Hence, when the allocated Core store and module instance are related to the Lime1 ones (`Rel`),
a successful Core segment initialisation of the image segments resolves every Lime1 segment:

* `elemSeg_back`, `dataSeg_back`: one segment;
* **`elemList_back`**, **`dataList_back`**: all of them.

The offsets are evaluated backwards (`evalConst_back`) and are `i32` by Lime1 typing with globals
(`constExpr?_typeG`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1Eng

open Silmaril.Wasm Silmaril.Wasm.Lime1 Silmaril.Wasm.Lime1.Validation
open Silmaril.Wasm.Execution.Runtime (Value ModuleInst GlobalInst)
open Silmaril.Wasm.Execution.Core (initElemSeg? initDataSeg? initElemList? initDataList?
  tableInitLoop memoryInitLoop elemDrop? dataDrop? evalConst?)

variable {H : Type}


/-! ## Writes keep the shape of a store -/

/-- `T` has the globals and the table and memory sizes of `S`. -/
structure Same (S T : Silmaril.Wasm.Execution.Core.Store H) : Prop where
  globals : T.globals = S.globals
  tables : T.tables.map (·.refs.length) = S.tables.map (·.refs.length)
  mems : T.mems.map (·.bytes.size) = S.mems.map (·.bytes.size)

theorem Same.refl (S : Silmaril.Wasm.Execution.Core.Store H) : Same S S := ⟨rfl, rfl, rfl⟩

theorem Same.trans {S T U : Silmaril.Wasm.Execution.Core.Store H} (h₁ : Same S T) (h₂ : Same T U) : Same S U :=
  ⟨h₂.globals.trans h₁.globals, h₂.tables.trans h₁.tables, h₂.mems.trans h₁.mems⟩

theorem map_set_same {α β : Type _} {f : α → β} {l : List α} {i : Nat} {a b : α}
    (hi : l[i]? = some a) (hab : f b = f a) : (l.set i b).map f = l.map f := by
  rw [List.map_set, hab]
  exact Silmaril.Wasm.Lime1.Execution.list_set_self (by simp [hi])

theorem same_setTable {S : Silmaril.Wasm.Execution.Core.Store H} {ta : Nat} {ti : Silmaril.Wasm.Execution.Core.TableInst}
    (hti : S.tables[ta]? = some ti) {i : Nat} {r : Silmaril.Wasm.Execution.Core.Ref} :
    Same S (S.setTable ta { ti with refs := ti.refs.set i r }) :=
  ⟨rfl, map_set_same hti (by simp), rfl⟩

theorem same_setMem {S : Silmaril.Wasm.Execution.Core.Store H} {ma : Nat} {mi : Silmaril.Wasm.Execution.Core.MemInst}
    (hmi : S.mems[ma]? = some mi) {b : ByteArray} (hb : b.size = mi.bytes.size) :
    Same S (S.setMem ma { mi with bytes := b }) :=
  ⟨rfl, rfl, map_set_same hmi hb⟩

theorem same_elemDrop {S S' : Silmaril.Wasm.Execution.Core.Store H} {F : Silmaril.Wasm.Execution.Core.Frame} {y : ElemIdx} (h : elemDrop? S F y = some S') :
    Same S S' := by
  obtain ⟨⟨ea, _⟩, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨rfl, rfl, rfl⟩

theorem same_dataDrop {S S' : Silmaril.Wasm.Execution.Core.Store H} {F : Silmaril.Wasm.Execution.Core.Frame} {y : DataIdx} (h : dataDrop? S F y = some S') :
    Same S S' := by
  obtain ⟨⟨da, _⟩, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨rfl, rfl, rfl⟩

/-- The `table.init` loop keeps the shape. -/
theorem tableInitLoop_same {F : Silmaril.Wasm.Execution.Core.Frame} {x : TableIdx} {y : ElemIdx} {a : AddrType} :
    ∀ (S : Silmaril.Wasm.Execution.Core.Store H) (i : BitVec a.intType.width) (j n : BitVec 32) {S' : Silmaril.Wasm.Execution.Core.Store H},
      tableInitLoop S F x y a i j n = some S' → Same S S'
  | S, i, j, n, S', h => by
    rw [tableInitLoop] at h
    split at h
    · rename_i ta ti _ ei hta _
      split_ifs at h with hb hn
      · cases h; exact Same.refl S
      · split at h
        · have hrest := tableInitLoop_same _ _ _ _ h
          exact (same_setTable (Silmaril.Wasm.Lime1.Execution.table?_inv hta).2).trans hrest
        · cases h
    · cases h
termination_by _ _ _ n => n.toNat
decreasing_by exact Silmaril.Wasm.Execution.Core.bv32_sub_one_lt hn

/-- The `memory.init` loop keeps the shape. -/
theorem memoryInitLoop_same {F : Silmaril.Wasm.Execution.Core.Frame} {x : MemIdx} {y : DataIdx} {a : AddrType} :
    ∀ (S : Silmaril.Wasm.Execution.Core.Store H) (i : BitVec a.intType.width) (j n : BitVec 32) {S' : Silmaril.Wasm.Execution.Core.Store H},
      memoryInitLoop S F x y a i j n = some S' → Same S S'
  | S, i, j, n, S', h => by
    rw [memoryInitLoop] at h
    split at h
    · rename_i ma mi _ di hma _
      split_ifs at h with hb hn
      · cases h; exact Same.refl S
      · split at h
        · split at h
          · rename_i b hst
            have hrest := memoryInitLoop_same _ _ _ _ h
            have hsz : b.size = mi.bytes.size :=
              Silmaril.Wasm.Execution.Memory.writeBytes_size _ _ _ _ hst
            exact (same_setMem (Silmaril.Wasm.Lime1.Execution.mem?_inv hma).2 hsz).trans hrest
          · cases h
        · cases h
    · cases h
termination_by _ _ _ n => n.toNat
decreasing_by exact Silmaril.Wasm.Execution.Core.bv32_sub_one_lt hn

/-- The first check of the `table.init` loop. -/
theorem tableInitLoop_check {F : Silmaril.Wasm.Execution.Core.Frame} {x : TableIdx} {y : ElemIdx} {a : AddrType}
    {S S' : Silmaril.Wasm.Execution.Core.Store H} {i : BitVec a.intType.width} {j n : BitVec 32}
    (h : tableInitLoop S F x y a i j n = some S') :
    ∃ ta ti, S.table? F x = some (ta, ti) ∧ i.toNat + n.toNat ≤ ti.refs.length := by
  rw [tableInitLoop] at h
  split at h
  · rename_i ta ti _ ei hta _
    split_ifs at h with hb
    all_goals exact ⟨ta, ti, hta, hb.1⟩
  · cases h

/-- The first check of the `memory.init` loop. -/
theorem memoryInitLoop_check {F : Silmaril.Wasm.Execution.Core.Frame} {x : MemIdx} {y : DataIdx} {a : AddrType}
    {S S' : Silmaril.Wasm.Execution.Core.Store H} {i : BitVec a.intType.width} {j n : BitVec 32}
    (h : memoryInitLoop S F x y a i j n = some S') :
    ∃ ma mi, S.mem? F x = some (ma, mi) ∧ i.toNat + n.toNat ≤ mi.bytes.size := by
  rw [memoryInitLoop] at h
  split at h
  · rename_i ma mi _ di hma _
    split_ifs at h with hb
    all_goals exact ⟨ma, mi, hma, hb.1⟩
  · cases h

/-! ## The relation of the allocated stores -/

/-- The allocated Core store and frame are the images of the allocated Lime1 store and module
instance, on globals, tables and memories. -/
structure Rel (Sa : Silmaril.Wasm.Execution.Core.Store H) (F : Silmaril.Wasm.Execution.Core.Frame) (A : Silmaril.Wasm.Lime1.Execution.Store H) (mod : ModuleInst) : Prop where
  globals : Sa.globals = A.globals.map GlobalInst.toCore
  tables : Sa.tables = A.tables.map Silmaril.Wasm.Execution.Runtime.TableInst.toCore
  mems : Sa.mems = A.memories.map Silmaril.Wasm.Execution.Runtime.MemInst.toCore
  fglobals : F.module.globals = mod.globals.map (·.value)
  ftables : F.module.tables = mod.tables.map (·.value)
  fmems : F.module.mems = mod.memories.map (·.value)

theorem gAgree {Sa S : Silmaril.Wasm.Execution.Core.Store H} {F : Silmaril.Wasm.Execution.Core.Frame} {A : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst}
    (R : Rel Sa F A mod) (hS : Same Sa S) (x : GlobalIdx) : GAgreeAt S F A mod x := by
  have hg : S.globals = A.globals.map GlobalInst.toCore := hS.globals.trans R.globals
  show (S.global? F x).map (fun p => p.2.value) = (lread A mod x).map Value.toCore
  simp only [Silmaril.Wasm.Execution.Core.Store.global?, lread, R.fglobals, hg,
    List.getElem?_map, Option.bind_eq_bind]
  rcases mod.globals[x.toNat]? with _ | a
  · rfl
  · rcases hga : A.globals[a.value]? with _ | g
    · simp [hga]
    · simp [hga]; rfl

/-- An `i32` image value is an address of the same number. -/
theorem addr?_i32 {b : BitVec 32} {a : AddrType} {i : BitVec a.intType.width}
    (h : (Value.toCore ⟨.int .i32, b⟩).addr? = some ⟨a, i⟩) : i.toNat = b.toNat := by
  simp only [Value.toCore, Silmaril.Wasm.Execution.Core.Val.addr?, Option.some.injEq] at h
  cases h
  rfl

/-- A typed offset evaluates to an `i32`. -/
theorem offset_of_typed {A : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst} {e : Lime1.Expr} {v : Value}
    (hv : Silmaril.Wasm.Lime1.Execution.constExpr? A mod e = some v) (ht : v.type = .int .i32) :
    ∃ b : BitVec 32, v = ⟨.int .i32, b⟩ ∧
      Silmaril.Wasm.Lime1.Execution.offset? A mod e = some b.toNat := by
  rcases v with ⟨ty, b⟩
  simp only at ht
  subst ht
  exact ⟨b, rfl, by simp [Silmaril.Wasm.Lime1.Execution.offset?, hv]; rfl⟩

/-- The Lime1 table at the Core table's address, with the same length. -/
theorem table_back {Sa S : Silmaril.Wasm.Execution.Core.Store H} {F : Silmaril.Wasm.Execution.Core.Frame} {A : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst}
    (R : Rel Sa F A mod) (hS : Same Sa S) {y : TableIdx} {ta : Nat}
    {ti : Silmaril.Wasm.Execution.Core.TableInst} (h : S.table? F y = some (ta, ti)) :
    ∃ a t, mod.tables[y.toNat]? = some a ∧ A.tables[a.value]? = some t ∧
      t.refs.length = ti.refs.length := by
  obtain ⟨hf, hs⟩ := Silmaril.Wasm.Lime1.Execution.table?_inv h
  rw [R.ftables, List.getElem?_map] at hf
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hf
  have hl : (S.tables.map (·.refs.length))[a.value]? = some ti.refs.length := by
    simp [List.getElem?_map, hs]
  rw [hS.tables, R.tables, List.map_map, List.getElem?_map] at hl
  obtain ⟨t, ht, htl⟩ := Option.map_eq_some_iff.mp hl
  refine ⟨a, t, ha, ht, ?_⟩
  simpa [Silmaril.Wasm.Execution.Runtime.TableInst.toCore] using htl

/-- The Lime1 memory at the Core memory's address, with the same size. -/
theorem mem_back {Sa S : Silmaril.Wasm.Execution.Core.Store H} {F : Silmaril.Wasm.Execution.Core.Frame} {A : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst}
    (R : Rel Sa F A mod) (hS : Same Sa S) {y : MemIdx} {ma : Nat}
    {mi : Silmaril.Wasm.Execution.Core.MemInst} (h : S.mem? F y = some (ma, mi)) :
    ∃ a m, mod.memories[y.toNat]? = some a ∧ A.memories[a.value]? = some m ∧
      m.data.size = mi.bytes.size := by
  obtain ⟨hf, hs⟩ := Silmaril.Wasm.Lime1.Execution.mem?_inv h
  rw [R.fmems, List.getElem?_map] at hf
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hf
  have hl : (S.mems.map (·.bytes.size))[a.value]? = some mi.bytes.size := by
    simp [List.getElem?_map, hs]
  rw [hS.mems, R.mems, List.map_map, List.getElem?_map] at hl
  obtain ⟨m, hm, hml⟩ := Option.map_eq_some_iff.mp hl
  exact ⟨a, m, ha, hm, by simpa [Silmaril.Wasm.Execution.Runtime.MemInst.toCore] using hml⟩

/-! ## Inverting one segment run -/

/-- The parts of a successful run of an active element segment. -/
theorem initElemSeg_inv {S S' : Silmaril.Wasm.Execution.Core.Store H}
    {F : Silmaril.Wasm.Execution.Core.Frame} {k : Nat} {e : Silmaril.Wasm.Elem} {y : TableIdx}
    {off : Silmaril.Wasm.Expr} (hmode : e.mode = .active y off)
    (h : initElemSeg? evalConst? S F k e = some S') :
    ∃ S₁ v, evalConst? S F off = some (S₁, v) ∧ ∃ a i, v.addr? = some ⟨a, i⟩ ∧ ∃ S₂,
      tableInitLoop S₁ F y ⟨Fin.ofNat _ k⟩ a i 0 (BitVec.ofNat 32 e.init.length) = some S₂ ∧
      elemDrop? S₂ F ⟨Fin.ofNat _ k⟩ = some S' := by
  simp only [initElemSeg?, hmode] at h
  split at h
  · cases h
  · rename_i S₁ v hev
    split at h
    · cases h
    · rename_i a i hai
      split at h
      · cases h
      · rename_i S₂ hS₂
        exact ⟨S₁, v, hev, a, i, hai, S₂, hS₂, h⟩

/-- The parts of a successful run of the image of a Lime1 data segment. -/
theorem initDataSeg_inv {S S' : Silmaril.Wasm.Execution.Core.Store H}
    {F : Silmaril.Wasm.Execution.Core.Frame} {k : Nat} {d : Lime1.Data}
    (h : initDataSeg? evalConst? S F k d.toCore = some S') :
    ∃ S₁ v, evalConst? S F (Lime1.Expr.toCore d.offset) = some (S₁, v) ∧
      ∃ a i, v.addr? = some ⟨a, i⟩ ∧ ∃ S₂, memoryInitLoop S₁ F d.memory ⟨Fin.ofNat _ k⟩ a i 0
        (BitVec.ofNat 32 d.bytes.size) = some S₂ ∧ dataDrop? S₂ F ⟨Fin.ofNat _ k⟩ = some S' := by
  simp only [initDataSeg?, Lime1.Data.toCore] at h
  split at h
  · cases h
  · rename_i S₁ v hev
    split at h
    · cases h
    · rename_i a i hai
      split at h
      · cases h
      · rename_i S₂ hS₂
        exact ⟨S₁, v, hev, a, i, hai, S₂, hS₂, h⟩

/-- Lime1 resolves an element segment whose parts resolve and fit. -/
theorem resolveElem_of {A : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst}
    {e : Lime1.Elem} {off : Nat} {ad : Silmaril.Wasm.Execution.Runtime.TableAddr}
    {t : Silmaril.Wasm.Execution.Runtime.TableInst} {refs : List Silmaril.Wasm.Execution.Runtime.FuncAddr}
    (hoff : Silmaril.Wasm.Lime1.Execution.offset? A mod e.offset = some off)
    (had : mod.tables[e.table.toNat]? = some ad) (ht : A.tables[ad.value]? = some t)
    (hrefs : e.init.mapM (fun i => mod.funcs[i.toNat]?) = some refs)
    (hfit : off + refs.length ≤ t.refs.length) :
    Silmaril.Wasm.Lime1.Execution.resolveElem? A mod e = some ⟨ad, off, refs⟩ := by
  simp only [Silmaril.Wasm.Lime1.Execution.resolveElem?, hoff, had, ht, hrefs,
    Option.bind_eq_bind, Option.bind_some, hfit, ite_true]
  rfl

/-- Lime1 resolves a data segment whose parts resolve and fit. -/
theorem resolveData_of {A : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst}
    {d : Lime1.Data} {off : Nat} {ad : Silmaril.Wasm.Execution.Runtime.MemAddr}
    {m : Silmaril.Wasm.Execution.Runtime.MemInst}
    (hoff : Silmaril.Wasm.Lime1.Execution.offset? A mod d.offset = some off)
    (had : mod.memories[d.memory.toNat]? = some ad) (hm : A.memories[ad.value]? = some m)
    (hfit : off + d.bytes.size ≤ m.data.size) :
    Silmaril.Wasm.Lime1.Execution.resolveData? A mod d = some ⟨ad, off, d.bytes⟩ := by
  simp only [Silmaril.Wasm.Lime1.Execution.resolveData?, hoff, had, hm,
    Option.bind_eq_bind, Option.bind_some, hfit, ite_true]
  rfl

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem initElemList_cons {S S' : Silmaril.Wasm.Execution.Core.Store H}
    {F : Silmaril.Wasm.Execution.Core.Frame} {k : Nat} {e : Silmaril.Wasm.Elem}
    {es : List Silmaril.Wasm.Elem}
    (h : initElemList? evalConst? S F ((List.range' k (e :: es).length).zip (e :: es)) = some S') :
    ∃ S₁, initElemSeg? evalConst? S F k e = some S₁ ∧
      initElemList? evalConst? S₁ F ((List.range' (k + 1) es.length).zip es) = some S' := by
  rw [List.length_cons, List.range'_succ, List.zip_cons_cons] at h
  simp only [initElemList?] at h
  split at h
  · cases h
  · rename_i S₁ h₁
    exact ⟨S₁, h₁, h⟩

theorem initDataList_cons {S S' : Silmaril.Wasm.Execution.Core.Store H}
    {F : Silmaril.Wasm.Execution.Core.Frame} {k : Nat} {d : Lime1.Data} {ds : List Lime1.Data}
    (h : initDataList? evalConst? S F ((List.range' k (d :: ds).length).zip
      ((d :: ds).map Lime1.Data.toCore)) = some S') :
    ∃ S₁, initDataSeg? evalConst? S F k d.toCore = some S₁ ∧
      initDataList? evalConst? S₁ F ((List.range' (k + 1) ds.length).zip
        (ds.map Lime1.Data.toCore)) = some S' := by
  rw [List.length_cons, List.range'_succ, List.map_cons, List.zip_cons_cons] at h
  simp only [initDataList?] at h
  split at h
  · cases h
  · rename_i S₁ h₁
    exact ⟨S₁, h₁, h⟩

/-! ## One segment -/

section Seg

variable {Sa : Silmaril.Wasm.Execution.Core.Store H} {F : Silmaril.Wasm.Execution.Core.Frame} {A : Silmaril.Wasm.Lime1.Execution.Store H} {mod : ModuleInst} {C : Context}
  (R : Rel Sa F A mod) (hT : GTyped A mod C)

include R hT in
/-- A Core offset evaluation of the image of a valid Lime1 offset, backwards. -/
theorem offset_back {S S₁ : Silmaril.Wasm.Execution.Core.Store H} (hS : Same Sa S) {e : Lime1.Expr}
    (he : ConstExprType C e .i32) {v : Silmaril.Wasm.Execution.Core.Val}
    (h : evalConst? S F (Lime1.Expr.toCore e) = some (S₁, v)) :
    S₁ = S ∧ ∃ b : BitVec 32, v = Value.toCore ⟨.int .i32, b⟩ ∧
      Silmaril.Wasm.Lime1.Execution.offset? A mod e = some b.toNat := by
  obtain ⟨hS₁, v', hv', rfl⟩ := evalConst_back he.constant (fun x _ => gAgree R hS x) h
  have ht : v'.type = .int .i32 := constExpr?_typeG hT he.typed hv'
  obtain ⟨b, rfl, hoff⟩ := offset_of_typed hv' ht
  exact ⟨hS₁, b, rfl, hoff⟩

include R hT in
/-- **One element segment, backwards.** -/
theorem elemSeg_back
    (hfuncs : ∀ i : FuncIdx, (∃ ft, C.funcs[i.toNat]? = some ft) → ∃ a, mod.funcs[i.toNat]? = some a)
    {S S' : Silmaril.Wasm.Execution.Core.Store H} (hS : Same Sa S) {k : Nat} {eL : Lime1.Elem} {eC : Silmaril.Wasm.Elem}
    (heC : Silmaril.Proofs.Wasm.Component.Lime1Inst.funcrefElem eC = eL.toCore)
    (hv : ElemValid C eL) (hlen : eC.init.length < 2 ^ 32)
    (h : initElemSeg? evalConst? S F k eC = some S') :
    Same Sa S' ∧ ∃ w, Silmaril.Wasm.Lime1.Execution.resolveElem? A mod eL = some w := by
  have hmode : eC.mode = .active eL.table (Lime1.Expr.toCore eL.offset) :=
    congrArg Silmaril.Wasm.Elem.mode heC
  have hinit : eC.init.length = eL.init.length := by
    simpa [Silmaril.Proofs.Wasm.Component.Lime1Inst.funcrefElem, Lime1.Elem.toCore] using
      congrArg (fun e => e.init.length) heC
  obtain ⟨S₁, v, hev, a, i, hai, S₂, hS₂, hdrop⟩ := initElemSeg_inv hmode h
  obtain ⟨rfl, b, rfl, hoff⟩ := offset_back R hT hS hv.offset hev
  have hib : i.toNat = b.toNat := addr?_i32 hai
  obtain ⟨ta, ti, hta, hbnd⟩ := tableInitLoop_check hS₂
  have hS' : Same Sa S' := (hS.trans (tableInitLoop_same _ _ _ _ hS₂)).trans (same_elemDrop hdrop)
  obtain ⟨ad, t, had, ht, htl⟩ := table_back R hS hta
  obtain ⟨refs, hrefs⟩ := mapM_some (xs := eL.init) (f := fun i => mod.funcs[i.toNat]?)
    (fun i hi => hfuncs i (hv.functions i hi))
  have hrl : refs.length = eL.init.length := Silmaril.Wasm.Lime1.Execution.mapM_length_eq hrefs
  have hfit : b.toNat + refs.length ≤ t.refs.length := by
    rw [hrl, htl, ← hinit, ← hib, ← toNat_ofNat32 hlen]; exact hbnd
  exact ⟨hS', _, resolveElem_of hoff had ht hrefs hfit⟩

include R hT in
/-- **One data segment, backwards.** -/
theorem dataSeg_back {S S' : Silmaril.Wasm.Execution.Core.Store H} (hS : Same Sa S) {k : Nat} {dL : Lime1.Data}
    (hv : DataValid C dL) (hlen : dL.bytes.size < 2 ^ 32)
    (h : initDataSeg? evalConst? S F k dL.toCore = some S') :
    Same Sa S' ∧ ∃ w, Silmaril.Wasm.Lime1.Execution.resolveData? A mod dL = some w := by
  obtain ⟨S₁, v, hev, a, i, hai, S₂, hS₂, hdrop⟩ := initDataSeg_inv h
  obtain ⟨rfl, b, rfl, hoff⟩ := offset_back R hT hS hv.offset hev
  have hib : i.toNat = b.toNat := addr?_i32 hai
  obtain ⟨ma, mi, hma, hbnd⟩ := memoryInitLoop_check hS₂
  have hS' : Same Sa S' := (hS.trans (memoryInitLoop_same _ _ _ _ hS₂)).trans (same_dataDrop hdrop)
  obtain ⟨ad, m, had, hm, hml⟩ := mem_back R hS hma
  have hfit : b.toNat + dL.bytes.size ≤ m.data.size := by
    rw [hml, ← hib, ← toNat_ofNat32 hlen]; exact hbnd
  exact ⟨hS', _, resolveData_of hoff had hm hfit⟩

include R hT in
/-- **All element segments, backwards.** -/
theorem elemList_back
    (hfuncs : ∀ i : FuncIdx, (∃ ft, C.funcs[i.toNat]? = some ft) → ∃ a, mod.funcs[i.toNat]? = some a) :
    ∀ (esL : List Lime1.Elem) (esC : List Silmaril.Wasm.Elem) (k : Nat)
      (S S' : Silmaril.Wasm.Execution.Core.Store H),
      List.Forall₂ (fun eL eC => Silmaril.Proofs.Wasm.Component.Lime1Inst.funcrefElem eC = eL.toCore)
        esL esC →
      (∀ e ∈ esL, ElemValid C e) → (∀ e ∈ esC, e.init.length < 2 ^ 32) → Same Sa S →
      initElemList? evalConst? S F ((List.range' k esC.length).zip esC) = some S' →
      Same Sa S' ∧ ∀ e ∈ esL, ∃ w, Silmaril.Wasm.Lime1.Execution.resolveElem? A mod e = some w
  | [], [], _, S, S', .nil, _, _, hS, h => by
    have hS' : S = S' := by simpa [initElemList?] using h
    exact ⟨hS' ▸ hS, fun e he => by simp at he⟩
  | eL :: esL, eC :: esC, k, S, S', .cons he hes, hv, hl, hS, h => by
    obtain ⟨S₁, h₁, h₂⟩ := initElemList_cons h
    obtain ⟨hS₁, w, hw⟩ := elemSeg_back R hT hfuncs hS he (hv eL (by simp)) (hl eC (by simp)) h₁
    obtain ⟨hS', hrest⟩ := elemList_back hfuncs esL esC (k + 1) S₁ S' hes
      (fun e he => hv e (by simp [he])) (fun e he => hl e (by simp [he])) hS₁ h₂
    exact ⟨hS', List.forall_mem_cons.mpr ⟨⟨w, hw⟩, hrest⟩⟩

include R hT in
/-- **All data segments, backwards.** -/
theorem dataList_back :
    ∀ (ds : List Lime1.Data) (k : Nat) (S S' : Silmaril.Wasm.Execution.Core.Store H),
      (∀ d ∈ ds, DataValid C d) → (∀ d ∈ ds, d.bytes.size < 2 ^ 32) → Same Sa S →
      initDataList? evalConst? S F ((List.range' k ds.length).zip (ds.map Lime1.Data.toCore)) =
        some S' →
      Same Sa S' ∧ ∀ d ∈ ds, ∃ w, Silmaril.Wasm.Lime1.Execution.resolveData? A mod d = some w
  | [], _, S, S', _, _, hS, h => by
    have hS' : S = S' := by simpa [initDataList?] using h
    exact ⟨hS' ▸ hS, fun d hd => by simp at hd⟩
  | d :: ds, k, S, S', hv, hl, hS, h => by
    obtain ⟨S₁, h₁, h₂⟩ := initDataList_cons h
    obtain ⟨hS₁, w, hw⟩ := dataSeg_back R hT hS (hv d (by simp)) (hl d (by simp)) h₁
    obtain ⟨hS', hrest⟩ := dataList_back ds (k + 1) S₁ S'
      (fun e he => hv e (by simp [he])) (fun e he => hl e (by simp [he])) hS₁ h₂
    exact ⟨hS', List.forall_mem_cons.mpr ⟨⟨w, hw⟩, hrest⟩⟩

end Seg

end Silmaril.Proofs.Wasm.Component.Lime1Eng
