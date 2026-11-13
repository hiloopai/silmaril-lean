module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkCode
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkTInit

/-!
# The base steps with the memory bulk instructions, the cover lemma, and what a step keeps

* `MemFillFwd`, `MemCopyFwd`, `MemInitFwd`, `TableFillFwd`: V2's `memory.fill`,
  `memory.copy`, `memory.init` and `table.fill` rules (`Step_read` 37–46 and 12–14 of the
  script); `TableSetFwd`: V2's `table.set` (`Step` 6, 7).
* `TableCopyFwd`, `TableInitFwd` (`Step_read` 15–21) and `DropFwd` (`Step` 10,
  21: `elem.drop`, `data.drop`).
* `BaseB P`: round 5's `StoreFn.BaseF P`, plus these.
* **`cover20B`**: every V2 step from plain-tail code that is `okB` in the frame's module, over a
  `StoreOkB` store, is a step of `Nest20 (BaseB P)`.
* **`okB_step`**: such a step keeps the code `okB`, the store's functions, the frame's module,
  and memories, data segments, tables and element segments below `2 ^ 32` bytes or entries
  (`StoreSmall`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreBulk

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim20.Whole (ctrlOk Nest20 StoreTop20 Tail20)
open Silmaril.Wasm.SpecTec.Sim20 (vecOp20)
open Silmaril.Wasm.SpecTec.Sim20.StoreGood (storeOkI)
open Silmaril.Wasm.SpecTec.Sim20.CallIndGood (ctrlOkI)
open Silmaril.Wasm.SpecTec.Sim20.GoodMerge (ctrlOkM)
open Silmaril.Wasm.SpecTec.Sim20.StoreDeep (ctrlOkD okD)
open Silmaril.Wasm.SpecTec.Sim20.StoreFn (BaseF)

variable {H : Type}

/-! ## The base -/

/-- **V2's three `memory.fill` rules.** -/
inductive MemFillFwd : Config H → Config H → Prop where
  | trap {s : Store H} {f : Frame} {i n : BitVec 32} {v : Val} {mi : MemInst}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi) (h : mi.bytes.size < i.toNat + n.toNat) :
      MemFillFwd ⟨s, f, [constI32 i, v.toAdmin, constI32 n, .plain .memoryFill]⟩ ⟨s, f, [.trap]⟩
  | zero {s : Store H} {f : Frame} {i : BitVec 32} {v : Val} {mi : MemInst}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi) (h : i.toNat ≤ mi.bytes.size) :
      MemFillFwd ⟨s, f, [constI32 i, v.toAdmin, constI32 0, .plain .memoryFill]⟩ ⟨s, f, []⟩
  | succ {s : Store H} {f : Frame} {i n : BitVec 32} {v : Val} {mi : MemInst}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi) (h : i.toNat + n.toNat ≤ mi.bytes.size)
      (hn : n ≠ 0) :
      MemFillFwd ⟨s, f, [constI32 i, v.toAdmin, constI32 n, .plain .memoryFill]⟩
        ⟨s, f, [constI32 i, v.toAdmin, store8, constI32 (i + 1), v.toAdmin, constI32 (n - 1),
          .plain .memoryFill]⟩

theorem MemFillFwd.readStep {c c' : Config H} (h : MemFillFwd c c') :
    c'.store = c.store ∧ c'.frame = c.frame ∧ ReadStep c.store c.frame c.code c'.code := by
  cases h with
  | trap hm h => exact ⟨rfl, rfl, .memoryFillTrap hm h⟩
  | zero hm h => exact ⟨rfl, rfl, .memoryFillZero hm h⟩
  | succ hm h hn => exact ⟨rfl, rfl, .memoryFillSucc hm h hn⟩

theorem MemFillFwd.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : MemFillFwd c c') : Step P host c c' := by
  cases h with
  | trap hm h => exact .read (.memoryFillTrap hm h)
  | zero hm h => exact .read (.memoryFillZero hm h)
  | succ hm h hn => exact .read (.memoryFillSucc hm h hn)

/-- **V2's four `memory.copy` rules.** -/
inductive MemCopyFwd : Config H → Config H → Prop where
  | trap {s : Store H} {f : Frame} {j i n : BitVec 32} {mi : MemInst}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (h : mi.bytes.size < i.toNat + n.toNat ∨ mi.bytes.size < j.toNat + n.toNat) :
      MemCopyFwd ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain .memoryCopy]⟩ ⟨s, f, [.trap]⟩
  | zero {s : Store H} {f : Frame} {j i : BitVec 32} {mi : MemInst}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (h : i.toNat ≤ mi.bytes.size ∧ j.toNat ≤ mi.bytes.size) :
      MemCopyFwd ⟨s, f, [constI32 j, constI32 i, constI32 0, .plain .memoryCopy]⟩ ⟨s, f, []⟩
  | le {s : Store H} {f : Frame} {j i n : BitVec 32} {mi : MemInst}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (h : i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size)
      (hn : n ≠ 0) (hle : j.toNat ≤ i.toNat) :
      MemCopyFwd ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain .memoryCopy]⟩
        ⟨s, f, [constI32 j, constI32 i, load8u, store8, constI32 (j + 1), constI32 (i + 1),
          constI32 (n - 1), .plain .memoryCopy]⟩
  | gt {s : Store H} {f : Frame} {j i n : BitVec 32} {mi : MemInst}
      (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (h : i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size)
      (hn : n ≠ 0) (hgt : i.toNat < j.toNat) :
      MemCopyFwd ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain .memoryCopy]⟩
        ⟨s, f, [constI32 (j + n - 1), constI32 (i + n - 1), load8u, store8, constI32 j,
          constI32 i, constI32 (n - 1), .plain .memoryCopy]⟩

theorem MemCopyFwd.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : MemCopyFwd c c') : Step P host c c' := by
  cases h with
  | trap hm h => exact .read (.memoryCopyTrap hm h)
  | zero hm h => exact .read (.memoryCopyZero hm h)
  | le hm h hn hle => exact .read (.memoryCopyLe hm h hn hle)
  | gt hm h hn hgt => exact .read (.memoryCopyGt hm h hn hgt)

/-- **V2's three `memory.init` rules.** -/
inductive MemInitFwd : Config H → Config H → Prop where
  | trap {s : Store H} {f : Frame} {x : DataIdx} {j i n : BitVec 32} {mi : MemInst}
      {di : DataInst} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (hd : (⟨s, f⟩ : State H).data? x = some di)
      (h : di.bytes.size < i.toNat + n.toNat ∨ mi.bytes.size < j.toNat + n.toNat) :
      MemInitFwd ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain (.memoryInit x)]⟩
        ⟨s, f, [.trap]⟩
  | zero {s : Store H} {f : Frame} {x : DataIdx} {j i : BitVec 32} {mi : MemInst}
      {di : DataInst} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (hd : (⟨s, f⟩ : State H).data? x = some di)
      (h : i.toNat ≤ di.bytes.size ∧ j.toNat ≤ mi.bytes.size) :
      MemInitFwd ⟨s, f, [constI32 j, constI32 i, constI32 0, .plain (.memoryInit x)]⟩
        ⟨s, f, []⟩
  | succ {s : Store H} {f : Frame} {x : DataIdx} {j i n : BitVec 32} {mi : MemInst}
      {di : DataInst} {b : UInt8} (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi)
      (hd : (⟨s, f⟩ : State H).data? x = some di)
      (h : i.toNat + n.toNat ≤ di.bytes.size ∧ j.toNat + n.toNat ≤ mi.bytes.size)
      (hn : n ≠ 0) (hb : di.bytes.data[i.toNat]? = some b) :
      MemInitFwd ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain (.memoryInit x)]⟩
        ⟨s, f, [constI32 j, constI32 (BitVec.ofNat 32 b.toNat), store8, constI32 (j + 1),
          constI32 (i + 1), constI32 (n - 1), .plain (.memoryInit x)]⟩

theorem MemInitFwd.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : MemInitFwd c c') : Step P host c c' := by
  cases h with
  | trap hm hd h => exact .read (.memoryInitTrap hm hd h)
  | zero hm hd h => exact .read (.memoryInitZero hm hd h)
  | succ hm hd h hn hb => exact .read (.memoryInitSucc hm hd h hn hb)

/-- **V2's two `table.set` rules** (`Step`). -/
inductive TableSetFwd : Config H → Config H → Prop where
  | trap {s : Store H} {f : Frame} {x : TableIdx} {i : BitVec 32} {r : Ref} {a : TableAddr}
      {ti : TableInst} (ha : f.module.tableAddr? x = some a) (ht : s.tableInst? a = some ti)
      (h : ti.refs.length ≤ i.toNat) :
      TableSetFwd ⟨s, f, [constI32 i, aref r, .plain (.tableSet x)]⟩ ⟨s, f, [.trap]⟩
  | val {s : Store H} {f : Frame} {x : TableIdx} {i : BitVec 32} {r : Ref} {a : TableAddr}
      {ti : TableInst} (ha : f.module.tableAddr? x = some a) (ht : s.tableInst? a = some ti)
      (h : i.toNat < ti.refs.length) :
      TableSetFwd ⟨s, f, [constI32 i, aref r, .plain (.tableSet x)]⟩
        ⟨s.setTableInst a (ti.setRef i.toNat r), f, []⟩

theorem TableSetFwd.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : TableSetFwd c c') : Step P host c c' := by
  cases h with
  | trap ha ht h => exact .tableSetTrap ha ht h
  | val ha ht h => exact .tableSetVal ha ht h

/-- **V2's three `table.fill` rules.** -/
inductive TableFillFwd : Config H → Config H → Prop where
  | trap {s : Store H} {f : Frame} {x : TableIdx} {i n : BitVec 32} {v : Val} {ti : TableInst}
      (ht : (⟨s, f⟩ : State H).table? x = some ti) (h : ti.refs.length < i.toNat + n.toNat) :
      TableFillFwd ⟨s, f, [constI32 i, v.toAdmin, constI32 n, .plain (.tableFill x)]⟩
        ⟨s, f, [.trap]⟩
  | zero {s : Store H} {f : Frame} {x : TableIdx} {i : BitVec 32} {v : Val} {ti : TableInst}
      (ht : (⟨s, f⟩ : State H).table? x = some ti) (h : i.toNat ≤ ti.refs.length) :
      TableFillFwd ⟨s, f, [constI32 i, v.toAdmin, constI32 0, .plain (.tableFill x)]⟩
        ⟨s, f, []⟩
  | succ {s : Store H} {f : Frame} {x : TableIdx} {i n : BitVec 32} {v : Val} {ti : TableInst}
      (ht : (⟨s, f⟩ : State H).table? x = some ti) (h : i.toNat + n.toNat ≤ ti.refs.length)
      (hn : n ≠ 0) :
      TableFillFwd ⟨s, f, [constI32 i, v.toAdmin, constI32 n, .plain (.tableFill x)]⟩
        ⟨s, f, [constI32 i, v.toAdmin, .plain (.tableSet x), constI32 (i + 1), v.toAdmin,
          constI32 (n - 1), .plain (.tableFill x)]⟩

theorem TableFillFwd.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : TableFillFwd c c') : Step P host c c' := by
  cases h with
  | trap ht h => exact .read (.tableFillTrap ht h)
  | zero ht h => exact .read (.tableFillZero ht h)
  | succ ht h hn => exact .read (.tableFillSucc ht h hn)

/-- **V2's four `table.copy` rules.** -/
inductive TableCopyFwd : Config H → Config H → Prop where
  | trap {s : Store H} {f : Frame} {x y : TableIdx} {j i n : BitVec 32} {tx ty : TableInst}
      (hx : (⟨s, f⟩ : State H).table? x = some tx) (hy : (⟨s, f⟩ : State H).table? y = some ty)
      (h : ty.refs.length < i.toNat + n.toNat ∨ tx.refs.length < j.toNat + n.toNat) :
      TableCopyFwd ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain (.tableCopy x y)]⟩
        ⟨s, f, [.trap]⟩
  | zero {s : Store H} {f : Frame} {x y : TableIdx} {j i : BitVec 32} {tx ty : TableInst}
      (hx : (⟨s, f⟩ : State H).table? x = some tx) (hy : (⟨s, f⟩ : State H).table? y = some ty)
      (h : i.toNat ≤ ty.refs.length ∧ j.toNat ≤ tx.refs.length) :
      TableCopyFwd ⟨s, f, [constI32 j, constI32 i, constI32 0, .plain (.tableCopy x y)]⟩
        ⟨s, f, []⟩
  | le {s : Store H} {f : Frame} {x y : TableIdx} {j i n : BitVec 32} {tx ty : TableInst}
      (hx : (⟨s, f⟩ : State H).table? x = some tx) (hy : (⟨s, f⟩ : State H).table? y = some ty)
      (h : i.toNat + n.toNat ≤ ty.refs.length ∧ j.toNat + n.toNat ≤ tx.refs.length)
      (hn : n ≠ 0) (hle : j.toNat ≤ i.toNat) :
      TableCopyFwd ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain (.tableCopy x y)]⟩
        ⟨s, f, [constI32 j, constI32 i, .plain (.tableGet y), .plain (.tableSet x),
          constI32 (j + 1), constI32 (i + 1), constI32 (n - 1), .plain (.tableCopy x y)]⟩
  | gt {s : Store H} {f : Frame} {x y : TableIdx} {j i n : BitVec 32} {tx ty : TableInst}
      (hx : (⟨s, f⟩ : State H).table? x = some tx) (hy : (⟨s, f⟩ : State H).table? y = some ty)
      (h : i.toNat + n.toNat ≤ ty.refs.length ∧ j.toNat + n.toNat ≤ tx.refs.length)
      (hn : n ≠ 0) (hgt : i.toNat < j.toNat) :
      TableCopyFwd ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain (.tableCopy x y)]⟩
        ⟨s, f, [constI32 (j + n - 1), constI32 (i + n - 1), .plain (.tableGet y),
          .plain (.tableSet x), constI32 j, constI32 i, constI32 (n - 1),
          .plain (.tableCopy x y)]⟩

theorem TableCopyFwd.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : TableCopyFwd c c') : Step P host c c' := by
  cases h with
  | trap hx hy h => exact .read (.tableCopyTrap hx hy h)
  | zero hx hy h => exact .read (.tableCopyZero hx hy h)
  | le hx hy h hn hle => exact .read (.tableCopyLe hx hy h hn hle)
  | gt hx hy h hn hgt => exact .read (.tableCopyGt hx hy h hn hgt)

/-- **V2's three `table.init` rules.** -/
inductive TableInitFwd : Config H → Config H → Prop where
  | trap {s : Store H} {f : Frame} {x : TableIdx} {y : ElemIdx} {j i n : BitVec 32}
      {ti : TableInst} {ei : ElemInst} (ht : (⟨s, f⟩ : State H).table? x = some ti)
      (he : (⟨s, f⟩ : State H).elem? y = some ei)
      (h : ei.refs.length < i.toNat + n.toNat ∨ ti.refs.length < j.toNat + n.toNat) :
      TableInitFwd ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain (.tableInit x y)]⟩
        ⟨s, f, [.trap]⟩
  | zero {s : Store H} {f : Frame} {x : TableIdx} {y : ElemIdx} {j i : BitVec 32}
      {ti : TableInst} {ei : ElemInst} (ht : (⟨s, f⟩ : State H).table? x = some ti)
      (he : (⟨s, f⟩ : State H).elem? y = some ei)
      (h : i.toNat ≤ ei.refs.length ∧ j.toNat ≤ ti.refs.length) :
      TableInitFwd ⟨s, f, [constI32 j, constI32 i, constI32 0, .plain (.tableInit x y)]⟩
        ⟨s, f, []⟩
  | succ {s : Store H} {f : Frame} {x : TableIdx} {y : ElemIdx} {j i n : BitVec 32}
      {ti : TableInst} {ei : ElemInst} {r : Ref} (ht : (⟨s, f⟩ : State H).table? x = some ti)
      (he : (⟨s, f⟩ : State H).elem? y = some ei)
      (h : i.toNat + n.toNat ≤ ei.refs.length ∧ j.toNat + n.toNat ≤ ti.refs.length)
      (hn : n ≠ 0) (hr : ei.refs[i.toNat]? = some r) :
      TableInitFwd ⟨s, f, [constI32 j, constI32 i, constI32 n, .plain (.tableInit x y)]⟩
        ⟨s, f, [constI32 j, aref r, .plain (.tableSet x), constI32 (j + 1), constI32 (i + 1),
          constI32 (n - 1), .plain (.tableInit x y)]⟩

theorem TableInitFwd.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : TableInitFwd c c') : Step P host c c' := by
  cases h with
  | trap ht he h => exact .read (.tableInitTrap ht he h)
  | zero ht he h => exact .read (.tableInitZero ht he h)
  | succ ht he h hn hr => exact .read (.tableInitSucc ht he h hn hr)

/-- **V2's `elem.drop` and `data.drop`** (`Step`). -/
inductive DropFwd : Config H → Config H → Prop where
  | elem {s : Store H} {f : Frame} {x : ElemIdx} {a : ElemAddr} {ei : ElemInst}
      (ha : f.module.elemAddr? x = some a) (he : s.elemInst? a = some ei) :
      DropFwd ⟨s, f, [.plain (.elemDrop x)]⟩ ⟨s.setElemInst a { ei with refs := [] }, f, []⟩
  | data {s : Store H} {f : Frame} {x : DataIdx} {a : DataAddr} {di : DataInst}
      (ha : f.module.dataAddr? x = some a) (hd : s.dataInst? a = some di) :
      DropFwd ⟨s, f, [.plain (.dataDrop x)]⟩ ⟨s.setDataInst a ⟨ByteArray.empty⟩, f, []⟩

theorem DropFwd.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : DropFwd c c') : Step P host c c' := by
  cases h with
  | elem ha he => exact .elemDrop ha he
  | data ha hd => exact .dataDrop ha hd

/-- **The base steps with the memory bulk instructions, `table.fill` and `table.set`**, and
`table.copy`, `table.init`, `elem.drop`, `data.drop`. -/
inductive BaseB (P : Profile) : Config H → Config H → Prop where
  | old {c c' : Config H} (h : BaseF P c c') : BaseB P c c'
  | fill {c c' : Config H} (h : MemFillFwd c c') : BaseB P c c'
  | copy {c c' : Config H} (h : MemCopyFwd c c') : BaseB P c c'
  | init {c c' : Config H} (h : MemInitFwd c c') : BaseB P c c'
  | tset {c c' : Config H} (h : TableSetFwd c c') : BaseB P c c'
  | tfill {c c' : Config H} (h : TableFillFwd c c') : BaseB P c c'
  | tcopy {c c' : Config H} (h : TableCopyFwd c c') : BaseB P c c'
  | tinit {c c' : Config H} (h : TableInitFwd c c') : BaseB P c c'
  | drop {c c' : Config H} (h : DropFwd c c') : BaseB P c c'

/-- Every base step is a V2 step. -/
theorem BaseB.step {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : BaseB P c c') :
    Step P host c c' := by
  cases h with
  | old h => exact h.step
  | fill h => exact h.step
  | copy h => exact h.step
  | init h => exact h.step
  | tset h => exact h.step
  | tfill h => exact h.step
  | tcopy h => exact h.step
  | tinit h => exact h.step
  | drop h => exact h.step

/-! ## The cover lemma -/

/-- `PureRest20N` has an instruction that is not covered. -/
theorem not_pureRest20N_okB {m : ModuleInst} {is : List Admin} (h : Whole.PureRest20N is)
    (hok : is.all (okB m) = true) : False := by
  cases h with
  | @vec is i hm hv =>
    have hi : okB m (.plain i) = true := List.all_eq_true.1 hok _ hm
    have hc : ctrlOkB m i = false := by
      cases i <;> simp_all [vecOp20, ctrlOkB, bulkOkI, ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk,
        storeOkI]
    rw [okB_plain, hc] at hi
    exact absurd hi (by decide)
  | unOpInvalid h => simp_all [ctrlOkB, bulkOkI, ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI]
  | cvtUndefined h => simp_all [ctrlOkB, bulkOkI, ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI]

/-- The pure steps. -/
theorem cover20B_pure {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (hp : PureStep P is is') (ht : Tail20 s f is) (hok : is.all (okB f.module) = true) :
    BaseB P ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  rcases Whole.pureStep_cover_tail hp ht with h | h | h
  · exact .old (.pureA h)
  · exact .old (.pureB (.mk h))
  · exact (not_pureRest20N_okB h hok).elim

/-- **The read steps from covered code.** -/
theorem cover20B_read {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (hr : ReadStep s f is is') (hok : is.all (okB f.module) = true) :
    BaseB P ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  cases hr with
  | block hbt hk => exact .old (.block (.block hbt hk))
  | loop hbt hk => exact .old (.block (.loop hbt hk))
  | call hx => exact .old (.call (.call (by simpa [ModuleInst.funcAddr?] using hx)))
  | callAddr hf hcode hk => exact .old (.callAddr (.mk hf hcode hk))
  | loadIntTrap hm h => exact .old (.load (.intTrap hm h))
  | loadIntVal hm hb => exact .old (.load (.intVal hm hb))
  | loadFloatTrap hm h => exact .old (.load (.floatTrap hm h))
  | loadFloatVal hm hb => exact .old (.load (.floatVal hm hb))
  | loadPackTrap hm h => exact .old (.pack (.trap hm h))
  | @loadPackVal t sz sx ao i mi c hm hb => cases sx <;> exact .old (.pack (.val hm hb))
  | localGet h => exact .old (.read (.localGet (by simpa [State.local?, Frame.local?] using h)))
  | globalGet h =>
    obtain ⟨a, ha, hg⟩ := Whole.global?_some h
    exact .old (.read (.globalGet ha hg))
  | refFunc hx => exact .old (.read (.refFunc (by simpa [ModuleInst.funcAddr?] using hx)))
  | callIndirectCall ht hr hf hy => exact .old (.callInd (.mk ht hr hf hy))
  | tableSize ht hn => exact .old (.size (.table ht hn))
  | memorySize hm hn => exact .old (.size (.memory hm hn))
  | tableGetTrap ht h => exact .old (.tget (.trap ht h))
  | tableGetVal ht hr => exact .old (.tget (.val ht hr))
  | @callIndirectTrap x y i ti ht h =>
    have hy : (f.module.type? y).isSome = true := by
      simpa [ctrlOkB, bulkOkI, ctrlOkD, ctrlOkM, ctrlOkI, storeOkI] using
        (by simpa [ctrlOkB, bulkOkI, ctrlOkD, ctrlOkM, ctrlOkI, storeOkI] using hok : _ ∧ _).2
    obtain ⟨ft, hft⟩ := Option.isSome_iff_exists.1 hy
    exact .old (.callIndTrap (.mk ht (ft := ft) hft h))
  | memoryFillTrap hm h => exact .fill (.trap hm h)
  | memoryFillZero hm h => exact .fill (.zero hm h)
  | memoryFillSucc hm h hn => exact .fill (.succ hm h hn)
  | memoryCopyTrap hm h => exact .copy (.trap hm h)
  | memoryCopyZero hm h => exact .copy (.zero hm h)
  | memoryCopyLe hm h hn hle => exact .copy (.le hm h hn hle)
  | memoryCopyGt hm h hn hgt => exact .copy (.gt hm h hn hgt)
  | memoryInitTrap hm hd h => exact .init (.trap hm hd h)
  | memoryInitZero hm hd h => exact .init (.zero hm hd h)
  | memoryInitSucc hm hd h hn hb => exact .init (.succ hm hd h hn hb)
  | tableFillTrap ht h => exact .tfill (.trap ht h)
  | tableFillZero ht h => exact .tfill (.zero ht h)
  | tableFillSucc ht h hn => exact .tfill (.succ ht h hn)
  | tableCopyTrap hx hy h => exact .tcopy (.trap hx hy h)
  | tableCopyZero hx hy h => exact .tcopy (.zero hx hy h)
  | tableCopyLe hx hy h hn hle => exact .tcopy (.le hx hy h hn hle)
  | tableCopyGt hx hy h hn hgt => exact .tcopy (.gt hx hy h hn hgt)
  | tableInitTrap ht he h => exact .tinit (.trap ht he h)
  | tableInitZero ht he h => exact .tinit (.zero ht he h)
  | tableInitSucc ht he h hn hr => exact .tinit (.succ ht he h hn hr)
  | _ => simp [ctrlOkB, bulkOkI, ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI] at hok

theorem okB_ctx_inner {m : ModuleInst} {vs : List Val} {is rest : List Admin}
    (h : (vals vs ++ is ++ rest).all (okB m) = true) : is.all (okB m) = true := by
  simp only [List.all_append, Bool.and_eq_true] at h
  exact h.1.2

theorem okB_label_parts {m : ModuleInst} {n : Nat} {cont : List V2.Instr} {body : List Admin}
    (h : [Admin.label n cont body].all (okB m) = true) :
    cont.all (ctrlOkB m) = true ∧ body.all (okB m) = true := by
  simpa using h

theorem okB_frame_body {m : ModuleInst} {n : Nat} {fr : Frame} {body : List Admin}
    (h : [Admin.frame n fr body].all (okB m) = true) : body.all (okB fr.module) = true := by
  simpa using h

/-- **Every V2 step from plain-tail covered code over a `StoreOkB` store is in the nested
fragment `BaseB`.** -/
theorem cover20B {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : Step P host c c')
    (ht : Tail20 c.store c.frame c.code) (hok : c.code.all (okB c.frame.module) = true)
    (hs : StoreOkB c.store) : Nest20 (BaseB P) c c' := by
  induction h with
  | pure hp => exact .base (cover20B_pure hp ht hok)
  | read hr => exact .base (cover20B_read hr hok)
  | ctxtInstrs hstep hne ih =>
    exact .ctx (ih (Whole.tail20_ctx hstep.not_allVals ht) (okB_ctx_inner hok) hs) hne
  | ctxtLabel _ ih => exact .label (ih (Whole.tail20_label ht).tail (okB_label_parts hok).2 hs)
  | ctxtFrame _ ih => exact .frame (ih (Whole.tail20_frame ht).tail (okB_frame_body hok) hs)
  | callAddrHost hf hcode => exact (hs.not_host hf hcode).elim
  | callAddrHostDiv hf hcode => exact (hs.not_host hf hcode).elim
  | localSet hx => exact .base (.old (.localSet hx))
  | globalSet ha hg => exact .base (.old (.globalSet ha hg))
  | storeIntTrap ha hm h => exact .base (.old (.store (.intTrap ha hm h)))
  | storeIntVal ha hm hw => exact .base (.old (.store (.intVal ha hm hw)))
  | storeFloatTrap ha hm h => exact .base (.old (.store (.floatTrap ha hm h)))
  | storeFloatVal ha hm hw => exact .base (.old (.store (.floatVal ha hm hw)))
  | storePackTrap ha hm h => exact .base (.old (.store (.packTrap ha hm h)))
  | storePackVal ha hm hw => exact .base (.old (.store (.packVal ha hm hw)))
  | tableSetTrap ha ht' h => exact .base (.tset (.trap ha ht' h))
  | tableSetVal ha ht' h => exact .base (.tset (.val ha ht' h))
  | elemDrop ha he => exact .base (.drop (.elem ha he))
  | dataDrop ha hd => exact .base (.drop (.data ha hd))
  | _ => exact absurd hok (by simp [ctrlOkB, bulkOkI, ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI])

/-! ## What a step keeps -/

/-- **Every memory and every data segment of the store has fewer than `2 ^ 32` bytes, every
table and every element segment fewer than `2 ^ 32` entries.** -/
structure StoreSmall (s : Store H) : Prop where
  mems : ∀ mi ∈ s.mems, mi.bytes.size < 2 ^ 32
  datas : ∀ di ∈ s.datas, di.bytes.size < 2 ^ 32
  tables : ∀ ti ∈ s.tables, ti.refs.length < 2 ^ 32
  elems : ∀ ei ∈ s.elems, ei.refs.length < 2 ^ 32

theorem StoreSmall.setMemInst {s : Store H} {a : MemAddr} {mi mi' : MemInst}
    (hw : StoreSmall s) (hm : s.memInst? a = some mi) (hs : mi'.bytes.size = mi.bytes.size) :
    StoreSmall (s.setMemInst a mi') := by
  refine ⟨fun m hmem => ?_, hw.datas, hw.tables, hw.elems⟩
  rcases List.mem_or_eq_of_mem_set hmem with h | rfl
  · exact hw.mems m h
  · have hmi : s.mems[a]? = some mi := by simpa [Store.memInst?] using hm
    rw [hs]
    exact hw.mems mi (List.mem_of_getElem? hmi)

theorem StoreSmall.lt {s : Store H} {f : Frame} {mi : MemInst} (hw : StoreSmall s)
    (hm : (⟨s, f⟩ : State H).mem? memIdx0 = some mi) : mi.bytes.size < 2 ^ 32 := by
  obtain ⟨a, -, hm'⟩ := Whole.mem?_some hm
  exact hw.mems mi (List.mem_of_getElem? (by simpa [Store.memInst?] using hm'))

theorem StoreSmall.ltData {s : Store H} {a : Nat} {di : DataInst} (hw : StoreSmall s)
    (hd : s.datas[a]? = some di) : di.bytes.size < 2 ^ 32 :=
  hw.datas di (List.mem_of_getElem? hd)

theorem StoreSmall.setGlobalInst {s : Store H} {a : GlobalAddr} {gi : GlobalInst}
    (hw : StoreSmall s) : StoreSmall (s.setGlobalInst a gi) :=
  ⟨hw.mems, hw.datas, hw.tables, hw.elems⟩

theorem StoreSmall.setTableInst {s : Store H} {a : TableAddr} {ti : TableInst} {k : Nat}
    {r : Ref} (hw : StoreSmall s) (ht : s.tableInst? a = some ti) :
    StoreSmall (s.setTableInst a (ti.setRef k r)) := by
  refine ⟨hw.mems, hw.datas, fun t hmem => ?_, hw.elems⟩
  rcases List.mem_or_eq_of_mem_set hmem with h | rfl
  · exact hw.tables t h
  · have hti : s.tables[a]? = some ti := by simpa [Store.tableInst?] using ht
    simpa [TableInst.setRef] using hw.tables ti (List.mem_of_getElem? hti)

theorem StoreSmall.ltTable {s : Store H} {f : Frame} {x : TableIdx} {ti : TableInst}
    (hw : StoreSmall s) (ht : (⟨s, f⟩ : State H).table? x = some ti) :
    ti.refs.length < 2 ^ 32 := by
  obtain ⟨a, -, ht'⟩ := table?_some ht
  exact hw.tables ti (List.mem_of_getElem? ht')

theorem StoreSmall.ltElem {s : Store H} {f : Frame} {y : ElemIdx} {ei : ElemInst}
    (hw : StoreSmall s) (he : (⟨s, f⟩ : State H).elem? y = some ei) :
    ei.refs.length < 2 ^ 32 := by
  simp only [State.elem?, ModuleInst.elemAddr?, Store.elemInst?, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at he
  obtain ⟨a, -, he'⟩ := he
  exact hw.elems ei (List.mem_of_getElem? he')

theorem StoreSmall.setElemInst {s : Store H} {a : ElemAddr} {ei : ElemInst} (hw : StoreSmall s) :
    StoreSmall (s.setElemInst a { ei with refs := [] }) := by
  refine ⟨hw.mems, hw.datas, hw.tables, fun e hmem => ?_⟩
  rcases List.mem_or_eq_of_mem_set hmem with h | rfl
  · exact hw.elems e h
  · simp

theorem StoreSmall.setDataInst {s : Store H} {a : DataAddr} (hw : StoreSmall s) :
    StoreSmall (s.setDataInst a ⟨ByteArray.empty⟩) := by
  refine ⟨hw.mems, fun d hmem => ?_, hw.tables, hw.elems⟩
  rcases List.mem_or_eq_of_mem_set hmem with h | rfl
  · exact hw.datas d h
  · simp

/-- What a step from covered code keeps. -/
def KeepsB (c c' : Config H) : Prop :=
  c'.code.all (okB c'.frame.module) = true ∧ c'.store.funcs = c.store.funcs ∧
    (StoreSmall c.store → StoreSmall c'.store) ∧ c'.frame.module = c.frame.module

theorem keepsB_same {s : Store H} {f f' : Frame} {is is' : List Admin}
    (h : is'.all (okB f'.module) = true) (hm : f'.module = f.module) :
    KeepsB ⟨s, f, is⟩ ⟨s, f', is'⟩ := ⟨h, rfl, id, hm⟩

/-- **Every pure step keeps covered code covered** in the same module. -/
theorem okB_pureStep {P : Profile} {m : ModuleInst} {is is' : List Admin}
    (h : PureStep P is is') (hok : is.all (okB m) = true) : is'.all (okB m) = true := by
  cases h <;> simp_all [ctrlOkB, bulkOkI, ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI,
    List.all_append]

/-- **Every read step keeps covered code covered**, over a `StoreOkB` store. -/
theorem okB_readStep {s : Store H} {f : Frame} {is is' : List Admin}
    (h : ReadStep s f is is') (hok : is.all (okB f.module) = true) (hs : StoreOkB s) :
    is'.all (okB f.module) = true := by
  cases h with
  | @callAddr a vs fi fn hf hcode hk =>
    obtain ⟨fn', hc', hb⟩ := hs a fi hf
    rw [hcode] at hc'
    cases hc'
    simpa using hb
  | _ => simp_all [ctrlOkB, bulkOkI, ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI, store8, load8u,
    PackSize.width, IntType.width,
    List.all_append]

/-- The six store steps keep the functions and small memories. -/
theorem keepsB_storeTop {c c' : Config H} (h : StoreTop20 c c') : KeepsB c c' := by
  cases h with
  | intTrap _ _ _ | floatTrap _ _ _ | packTrap _ _ _ => exact keepsB_same rfl rfl
  | intVal _ hm hw | floatVal _ hm hw | packVal _ hm hw =>
    exact ⟨rfl, rfl, fun hp => hp.setMemInst hm (StoreGood.writeBytes?_size hw), rfl⟩

/-- **Every V2 step from covered code over a `StoreOkB` store keeps the code covered, the store's
functions, small memories and the frame's module.** -/
theorem okB_step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hok : c.code.all (okB c.frame.module) = true)
    (hs : StoreOkB c.store) : KeepsB c c' := by
  induction h with
  | pure hp => exact keepsB_same (okB_pureStep hp hok) rfl
  | read hr => exact keepsB_same (okB_readStep hr hok hs) rfl
  | ctxtInstrs _ _ ih =>
    simp only [List.all_append, Bool.and_eq_true] at hok
    obtain ⟨hi, hm, hw, hmod⟩ := ih hok.1.2 hs
    have hi' : _ = true := hmod ▸ hi
    refine ⟨?_, hm, hw, hmod⟩
    rw [hmod]
    simp [List.all_append, hi', hok.2]
  | @ctxtLabel s s' f f' n cont is is' _ ih =>
    have hb : cont.all (ctrlOkB f.module) = true ∧ is.all (okB f.module) = true := by
      simpa using hok
    obtain ⟨hi, hm, hw, hmod⟩ := ih hb.2 hs
    have hi' : _ = true := hmod ▸ hi
    refine ⟨?_, hm, hw, hmod⟩
    rw [hmod]
    simp [hb.1, hi']
  | ctxtFrame _ ih =>
    obtain ⟨hi, hm, hw, -⟩ := ih (by simpa using hok) hs
    exact ⟨by simpa using hi, hm, hw, rfl⟩
  | callAddrHost hf hcode => exact (hs.not_host hf hcode).elim
  | callAddrHostDiv hf hcode => exact (hs.not_host hf hcode).elim
  | localSet => exact ⟨rfl, rfl, id, rfl⟩
  | globalSet => exact ⟨rfl, rfl, fun hp => hp.setGlobalInst, rfl⟩
  | storeIntTrap ha hm h => exact keepsB_storeTop (.intTrap ha hm h)
  | storeIntVal ha hm hw => exact keepsB_storeTop (.intVal ha hm hw)
  | storeFloatTrap ha hm h => exact keepsB_storeTop (.floatTrap ha hm h)
  | storeFloatVal ha hm hw => exact keepsB_storeTop (.floatVal ha hm hw)
  | storePackTrap ha hm h => exact keepsB_storeTop (.packTrap ha hm h)
  | storePackVal ha hm hw => exact keepsB_storeTop (.packVal ha hm hw)
  | tableSetTrap => exact ⟨rfl, rfl, id, rfl⟩
  | tableSetVal _ ht _ => exact ⟨rfl, rfl, fun hp => hp.setTableInst ht, rfl⟩
  | elemDrop => exact ⟨rfl, rfl, fun hp => hp.setElemInst, rfl⟩
  | dataDrop => exact ⟨rfl, rfl, fun hp => hp.setDataInst, rfl⟩
  | _ => simp_all [ctrlOkB, bulkOkI, ctrlOkD, ctrlOkM, ctrlOkI, ctrlOk, storeOkI]

end Silmaril.Wasm.SpecTec.Sim20.StoreBulk
