module

public import Silmaril.Proofs.Wasm.Logic.V1.Sound.Single

/-!
# Soundness of the memory-management proof rules

Figure 8 of Watt et al. These are the rules where the two-stage interpretation
of heap assertions does real work: an abstract heap owning a byte range is
reified by a linear memory agreeing with it on those bytes, and a store must
leave the frame's bytes alone.

Ownership of `size(τ)` is permission to call `memory.grow`, and growing confers
ownership of the new, zeroed, addresses. Our `Execution.Memory.Grow` may also
fail because of a declared maximum, which the `size` resource does not track;
that only narrows the success case, and the rule's postcondition already covers
failure, so the rule stays sound.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1.Execution

variable {H : Type*} {host : HostSemantics H} {n : Nat} {F : List FuncDef}
variable {L : List Assert} {R : Option Assert}

/-! ## Byte arrays, as lists

`ByteArray.toList` is defined by a tail-recursive loop; the list lemma library
is much richer than the `ByteArray` one, so every argument below runs over
`b.data.toList`. -/

private theorem toList_loop_eq (b : Memory.Bytes) (i : Nat) (r : List Memory.Byte) :
    ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
  fun_induction ByteArray.toList.loop b i r with
  | case1 i r hlt ih =>
    have hi : i < b.data.toList.length := by simpa using hlt
    rw [ih, List.drop_eq_getElem_cons hi]
    have hget : b.get! i = b.data.toList[i] := by
      simp [ByteArray.get!, getElem!_pos, hlt]
    simp [hget]
  | case2 i r hlt =>
    have hle : b.data.toList.length ≤ i := by simpa using Nat.le_of_not_lt hlt
    simp [List.drop_eq_nil_of_le hle]

private theorem toList_eq (b : Memory.Bytes) : b.toList = b.data.toList := by
  simp [ByteArray.toList, toList_loop_eq]

private theorem getElem?_eq (b : Memory.Bytes) (i : Nat) : b[i]? = b.data.toList[i]? := by
  simp only [Array.getElem?_toList]; rfl

private theorem length_toList (b : Memory.Bytes) : b.data.toList.length = b.size := by simp

/-! ## Byte segments of an abstract heap -/

private theorem ofBytes_cells_add (A : Nat) (bs : List Memory.Byte) (j : Nat) :
    (AHeap.ofBytes A bs).cells (A + j) = bs[j]? := by
  simp [AHeap.ofBytes]

private theorem ofBytes_cells_none {A : Nat} {bs : List Memory.Byte} {i : Nat}
    (h : i < A ∨ A + bs.length ≤ i) : (AHeap.ofBytes A bs).cells i = none := by
  simp only [AHeap.ofBytes]
  rcases h with h | h
  · simp [Nat.not_le.mpr h]
  · rw [ite_eq_left (show A ≤ i by omega), List.getElem?_eq_none (by omega)]

private theorem ofBytes_out_of_cells_none {A : Nat} {bs : List Memory.Byte} {i : Nat}
    (h : (AHeap.ofBytes A bs).cells i = none) : i < A ∨ A + bs.length ≤ i := by
  by_cases h₁ : i < A
  · exact Or.inl h₁
  by_cases h₂ : A + bs.length ≤ i
  · exact Or.inr h₂
  exfalso
  rw [show i = A + (i - A) by omega, ofBytes_cells_add, List.getElem?_eq_none_iff] at h
  omega

private theorem ofBytes_cells_none_congr {A : Nat} {bs bs' : List Memory.Byte}
    (hlen : bs.length = bs'.length) {i : Nat} (h : (AHeap.ofBytes A bs).cells i = none) :
    (AHeap.ofBytes A bs').cells i = none :=
  ofBytes_cells_none (hlen ▸ ofBytes_out_of_cells_none h)

private theorem ofBytes_size (A : Nat) (bs : List Memory.Byte) :
    (AHeap.ofBytes A bs).size = none := rfl

/-! ## Owned bytes are the bytes the memory holds -/

private theorem pow_eight (count : Nat) : (256 : Nat) ^ count = 2 ^ (8 * count) := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]

private theorem readBytes_of_agree {mem enc : Memory.Bytes} {A : Nat} (pos : 0 < enc.size)
    (agree : ∀ i b, (AHeap.ofBytes A enc.data.toList).cells i = some b → mem[i]? = some b) :
    Memory.readBytes mem A enc.size = some enc := by
  have key : ∀ j, j < enc.size → mem.data.toList[A + j]? = enc.data.toList[j]? := by
    intro j hj
    have hj' : j < enc.data.toList.length := by rw [length_toList]; exact hj
    rw [List.getElem?_eq_getElem hj', ← getElem?_eq]
    exact agree _ _ (by rw [ofBytes_cells_add, List.getElem?_eq_getElem hj'])
  have hlast : mem.data.toList[A + (enc.size - 1)]? = enc.data.toList[enc.size - 1]? :=
    key (enc.size - 1) (by omega)
  have hbound : A + enc.size ≤ mem.size := by
    have hne : enc.data.toList[enc.size - 1]? ≠ none := by
      simp only [ne_eq, List.getElem?_eq_none_iff, length_toList]; omega
    have hne' : mem.data.toList[A + (enc.size - 1)]? ≠ none := hlast.symm ▸ hne
    have hlt : ¬ mem.data.toList.length ≤ A + (enc.size - 1) := by
      simpa only [ne_eq, List.getElem?_eq_none_iff] using hne'
    have hlen : mem.data.toList.length = mem.size := length_toList mem
    omega
  rw [Memory.readBytes_eq_some_iff]
  refine ⟨hbound, ByteArray.ext ?_⟩
  show enc.data = (mem.extract A (A + enc.size)).data
  rw [← Array.toList_inj, ByteArray.data_extract, Array.toList_extract,
    List.extract_eq_take_drop]
  refine (List.ext_getElem? fun i => ?_).symm
  show (List.take (A + enc.size - A) (List.drop A mem.data.toList))[i]? = enc.data.toList[i]?
  rw [List.getElem?_take, List.getElem?_drop, Nat.add_sub_cancel_left]
  by_cases hi : i < enc.size
  · rw [ite_eq_left hi]; exact key i hi
  · rw [ite_eq_right hi, List.getElem?_eq_none (by rw [length_toList]; omega)]

private theorem load_of_agree {mem : Memory.Bytes} {A count x : Nat} (pos : 0 < count)
    (hx : x < 2 ^ (8 * count))
    (agree : ∀ i b, (AHeap.ofBytes A (Memory.encodeLE count x).data.toList).cells i = some b →
      mem[i]? = some b) :
    Memory.load mem A count = some (BitVec.ofNat (8 * count) x) := by
  have hread := readBytes_of_agree (by rw [Memory.encodeLE_size]; exact pos) agree
  rw [Memory.encodeLE_size] at hread
  rw [Memory.load, hread, Option.map_some, Memory.decodeLE_encodeLE, pow_eight,
    Nat.mod_eq_of_lt hx]

private theorem setWidth_ofNat_toNat {c w : Nat} (hw : 8 * c = w) (y : BitVec w) :
    (BitVec.ofNat (8 * c) y.toNat).setWidth w = y := by
  subst hw; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.setWidth_eq]

/-! ## Reification against the frame's linear memory -/

private theorem frameMemory_eq {H : Type*} {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    (hm : frameMemory s f = some (a, m)) :
    f.module.memories[0]? = some a ∧ s.memories[a.value]? = some m := by
  unfold frameMemory at hm
  cases h₁ : f.module.memories[0]? with
  | none => rw [h₁] at hm; simp at hm
  | some a₁ =>
    rw [h₁] at hm
    simp at hm
    cases h₂ : s.memories[a₁.value]? with
    | none => rw [h₂] at hm; simp at hm
    | some m₁ =>
      rw [h₂] at hm
      simp at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact ⟨rfl, h₂⟩

private theorem reifiesMem_agree {H : Type*} {s : Store H} {f : Frame} {h : AHeap}
    {a : MemAddr} {m : MemInst} (reify : ReifiesMem s f.module h)
    (hm : frameMemory s f = some (a, m)) :
    (∀ i b, h.cells i = some b → m.data[i]? = some b) ∧
      ∀ p, h.size = some p → Memory.size m.data = p := by
  obtain ⟨hidx, hfound⟩ := frameMemory_eq hm
  obtain ⟨a', m', ha', hm', hcells, hsize⟩ := reify
  rw [hidx, Option.some.injEq] at ha'
  subst ha'
  rw [hfound, Option.some.injEq] at hm'
  subst hm'
  exact ⟨hcells, hsize⟩

private theorem reifies_setMemory {H : Type*} {F : List FuncDef} {s : Store H} {f : Frame}
    {ρ : Sto} {h h' : AHeap} {a : MemAddr} {m m' : MemInst}
    (reify : Reifies F s f ρ h) (hm : frameMemory s f = some (a, m))
    (cells : ∀ i b, h'.cells i = some b → m'.data[i]? = some b)
    (size : ∀ p, h'.size = some p → Memory.size m'.data = p) :
    Reifies F (setMemory s a m') f ρ h' := by
  obtain ⟨hidx, hfound⟩ := frameMemory_eq hm
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hfound
  exact ⟨reify.funcs, reify.locals, ⟨reify.globals.nodup, reify.globals.agree⟩,
    ⟨a, m', hidx, List.getElem?_set_self hlt, cells, size⟩⟩

private theorem Value_int_inj {t : IntType} {x y : BitVec t.width}
    (h : Value.int t x = Value.int t y) : x = y := by
  rw [Value.int, Value.int] at h; injection h

private theorem Value_float_inj {t : FloatType} {x y : BitVec t.width}
    (h : Value.float t x = Value.float t y) : x = y := by
  rw [Value.float, Value.float] at h; injection h

private theorem cellNum_ofBytes {t : NumType} {A : Term Nat} {x : Term (BitVec t.width)}
    {ρ : Sto} {h : AHeap} (hp : HAssert.cellNum t A x ρ h) :
    h = AHeap.ofBytes (A ρ) (Memory.encodeLE (t.width / 8) (x ρ).toNat).data.toList := by
  rw [HAssert.cellNum, HAssert.seg, toList_eq] at hp; exact hp

private theorem cellNum_of_ofBytes {t : NumType} {A : Term Nat} {x : Term (BitVec t.width)}
    {ρ : Sto} {h : AHeap}
    (hp : h = AHeap.ofBytes (A ρ) (Memory.encodeLE (t.width / 8) (x ρ).toNat).data.toList) :
    HAssert.cellNum t A x ρ h := by
  rw [HAssert.cellNum, HAssert.seg, toList_eq]; exact hp

private theorem cellNum_agree {H : Type*} {s : Store H} {f : Frame} {ρ : Sto} {h hf : AHeap}
    {tp : NumType} {A : Term Nat} {x : Term (BitVec tp.width)} {addr : MemAddr} {m : MemInst}
    (hp : HAssert.cellNum tp A x ρ h) (reify : Reifies F s f ρ (h ∪ hf))
    (hmem : frameMemory s f = some (addr, m)) :
    ∀ i b, (AHeap.ofBytes (A ρ)
        (Memory.encodeLE (tp.width / 8) (x ρ).toNat).data.toList).cells i = some b →
      m.data[i]? = some b := by
  rw [HAssert.cellNum, HAssert.seg, toList_eq] at hp
  intro i b hi
  obtain ⟨hcells, -⟩ := reifiesMem_agree reify.mem hmem
  exact hcells i b (by rw [AHeap.union_cells, hp, hi, Option.some_or])

private theorem ofBytes_cells_isSome {A : Nat} {bs : List Memory.Byte} {i : Nat}
    {b : Memory.Byte} (h : (AHeap.ofBytes A bs).cells i = some b) :
    A ≤ i ∧ i - A < bs.length ∧ bs[i - A]? = some b := by
  by_cases hA : A ≤ i
  · rw [show i = A + (i - A) by omega, ofBytes_cells_add] at h
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp h
    exact ⟨hA, hlt, h⟩
  · simp [AHeap.ofBytes, hA] at h

private theorem bound_of_agree {mem enc : Memory.Bytes} {A : Nat} (pos : 0 < enc.size)
    (agree : ∀ i b, (AHeap.ofBytes A enc.data.toList).cells i = some b → mem[i]? = some b) :
    A + enc.size ≤ mem.size :=
  ((Memory.readBytes_eq_some_iff mem enc A enc.size).mp (readBytes_of_agree pos agree)).1

/-! ## Writes -/

private theorem writeBytes_toList {b enc b' : Memory.Bytes} {A : Nat}
    (hw : Memory.writeBytes b A enc = some b') :
    A + enc.size ≤ b.size ∧
      b'.data.toList = b.data.toList.take A ++ enc.data.toList ++
        b.data.toList.drop (A + enc.size) := by
  obtain ⟨hle, rfl⟩ := (Memory.writeBytes_eq_some_iff b enc b' A).mp hw
  refine ⟨hle, ?_⟩
  simp only [ByteArray.toList_data_append, ByteArray.data_extract, Array.toList_extract,
    List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero]
  rw [List.take_of_length_le (l := List.drop (A + enc.size) b.data.toList)
    (by simp only [List.length_drop, length_toList]; omega)]

private theorem writeBytes_getElem?_inside {b enc b' : Memory.Bytes} {A j : Nat}
    (hw : Memory.writeBytes b A enc = some b') (hj : j < enc.size) :
    b'[A + j]? = enc[j]? := by
  obtain ⟨hle, hlist⟩ := writeBytes_toList hw
  have hT : (b.data.toList.take A).length = A := by
    rw [List.length_take, length_toList]; omega
  rw [getElem?_eq, getElem?_eq, hlist, List.append_assoc,
    List.getElem?_append_right (by omega), hT, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by rw [length_toList]; exact hj)]

private theorem writeBytes_getElem?_outside {b enc b' : Memory.Bytes} {A i : Nat}
    (hw : Memory.writeBytes b A enc = some b') (hi : i < A ∨ A + enc.size ≤ i) :
    b'[i]? = b[i]? := by
  obtain ⟨hle, hlist⟩ := writeBytes_toList hw
  have hT : (b.data.toList.take A).length = A := by
    rw [List.length_take, length_toList]; omega
  rw [getElem?_eq, getElem?_eq, hlist, List.append_assoc]
  rcases hi with hi | hi
  · rw [List.getElem?_append_left (by omega), List.getElem?_take, ite_eq_left hi]
  · rw [List.getElem?_append_right (by omega), hT,
      List.getElem?_append_right (by rw [length_toList]; omega), length_toList,
      List.getElem?_drop]
    congr 1
    omega

private theorem writeBytes_of_bound {mem bs : Memory.Bytes} {A : Nat}
    (hb : A + bs.size ≤ mem.size) :
    Memory.writeBytes mem A bs =
      some (mem.extract 0 A ++ bs ++ mem.extract (A + bs.size) mem.size) :=
  (Memory.writeBytes_eq_some_iff mem bs _ A).mpr ⟨hb, rfl⟩

/-! ## Loads -/

private theorem loadInt_of_agree {t : IntType} {mem : Memory.Bytes} {A : Nat}
    {x : BitVec t.width}
    (agree : ∀ i b,
      (AHeap.ofBytes A (Memory.encodeLE (t.width / 8) x.toNat).data.toList).cells i = some b →
      mem[i]? = some b) :
    loadInt t none mem A = some (Value.int t x) := by
  have hw : 8 * (t.width / 8) = t.width := by cases t <;> rfl
  have hpos : 0 < t.width / 8 := by cases t <;> decide
  have hx : x.toNat < 2 ^ (8 * (t.width / 8)) := by rw [hw]; exact x.isLt
  simp only [loadInt, load_of_agree hpos hx agree, Option.map_some,
    setWidth_ofNat_toNat hw]

private theorem loadFloat_of_agree {t : FloatType} {mem : Memory.Bytes} {A : Nat}
    {x : BitVec t.width}
    (agree : ∀ i b,
      (AHeap.ofBytes A (Memory.encodeLE (t.width / 8) x.toNat).data.toList).cells i = some b →
      mem[i]? = some b) :
    loadFloat t mem A = some (Value.float t x) := by
  have hw : 8 * (t.width / 8) = t.width := by cases t <;> rfl
  have hpos : 0 < t.width / 8 := by cases t <;> decide
  have hx : x.toNat < 2 ^ (8 * (t.width / 8)) := by rw [hw]; exact x.isLt
  simp only [loadFloat, load_of_agree hpos hx agree, Option.map_some,
    setWidth_ofNat_toNat hw]

/-! ## Stores -/

private theorem storeInt_eq_writeBytes {t : IntType} {mem : Memory.Bytes} {A : Nat}
    (x : BitVec t.width) :
    storeInt t none mem A x =
      Memory.writeBytes mem A (Memory.encodeLE (t.width / 8) x.toNat) := by
  have hw : 8 * (t.width / 8) = t.width := by cases t <;> rfl
  have hx : (BitVec.setWidth (8 * (t.width / 8)) x).toNat = x.toNat := by
    rw [BitVec.toNat_setWidth, hw, Nat.mod_eq_of_lt x.isLt]
  simp only [storeInt, Memory.store, Option.map_none, Option.getD_none, hx]

private theorem storeFloat_eq_writeBytes {t : FloatType} {mem : Memory.Bytes} {A : Nat}
    (x : BitVec t.width) :
    storeFloat t mem A x =
      Memory.writeBytes mem A (Memory.encodeLE (t.width / 8) x.toNat) := by
  have hw : 8 * (t.width / 8) = t.width := by cases t <;> rfl
  have hx : (BitVec.setWidth (8 * (t.width / 8)) x).toNat = x.toNat := by
    rw [BitVec.toNat_setWidth, hw, Nat.mod_eq_of_lt x.isLt]
  simp only [storeFloat, Memory.store, hx]

/-- The heart of the store rules: the frame's bytes lie outside the written
range, because the precondition owns exactly that range and is disjoint from
the frame, so the written memory still reifies the frame. -/
private theorem store_effect {H : Type*} {s : Store H} {f : Frame} {ρ : Sto} {h hf : AHeap}
    {addr : MemAddr} {m : MemInst} {A : Nat} {old enc bytes : Memory.Bytes}
    (hh : h = AHeap.ofBytes A old.data.toList) (hlen : old.size = enc.size)
    (hdisj : AHeap.Disj h hf) (reify : Reifies F s f ρ (h ∪ hf))
    (hmem : frameMemory s f = some (addr, m))
    (hwrite : Memory.writeBytes m.data A enc = some bytes) :
    AHeap.Disj (AHeap.ofBytes A enc.data.toList) hf ∧
      Reifies F (setMemory s addr { m with data := bytes }) f ρ
        (AHeap.ofBytes A enc.data.toList ∪ hf) := by
  subst hh
  obtain ⟨hcells, hsz⟩ := reifiesMem_agree reify.mem hmem
  have hlen' : old.data.toList.length = enc.data.toList.length := by
    rw [length_toList, length_toList, hlen]
  have hd : AHeap.Disj (AHeap.ofBytes A enc.data.toList) hf := by
    refine ⟨fun i => ?_, Or.inl rfl⟩
    rcases hdisj.1 i with hi | hi
    · exact Or.inl (ofBytes_cells_none_congr hlen' hi)
    · exact Or.inr hi
  refine ⟨hd, reifies_setMemory reify hmem (fun i b hi => ?_) (fun q hq => ?_)⟩
  · rw [AHeap.union_cells] at hi
    show bytes[i]? = some b
    cases hc : (AHeap.ofBytes A enc.data.toList).cells i with
    | some b' =>
      rw [hc, Option.some_or, Option.some.injEq] at hi
      obtain ⟨hA, hlt, hget⟩ := ofBytes_cells_isSome hc
      have hj : i - A < enc.size := by rw [← length_toList]; exact hlt
      have hin := writeBytes_getElem?_inside hwrite hj
      rw [show A + (i - A) = i by omega] at hin
      rw [hin, getElem?_eq, hget, hi]
    | none =>
      rw [hc, Option.none_or] at hi
      have hout : i < A ∨ A + enc.size ≤ i := by
        have := ofBytes_out_of_cells_none hc
        rw [length_toList] at this
        exact this
      rw [writeBytes_getElem?_outside hwrite hout]
      refine hcells i b ?_
      rw [AHeap.union_cells, ofBytes_cells_none_congr hlen'.symm hc, Option.none_or]
      exact hi
  · rw [AHeap.union_size, ofBytes_size, Option.none_or] at hq
    have hsame : Memory.size bytes = Memory.size m.data := by
      unfold Memory.size
      rw [Memory.writeBytes_size m.data enc bytes A hwrite]
    refine hsame.trans (hsz q ?_)
    rw [AHeap.union_size, ofBytes_size, Option.none_or]
    exact hq

/-! ## Zero-filled segments and the iterated star -/

private theorem ofBytes_nil (A : Nat) : AHeap.ofBytes A [] = AHeap.emp :=
  AHeap.ext (fun i => by simp [AHeap.ofBytes, AHeap.emp]) rfl

private theorem ofBytes_cons (A : Nat) (b : Memory.Byte) (bs : List Memory.Byte) :
    AHeap.ofBytes A (b :: bs) = AHeap.single A b ∪ AHeap.ofBytes (A + 1) bs := by
  refine AHeap.ext (fun i => ?_) rfl
  simp only [AHeap.ofBytes, AHeap.single, AHeap.union_cells]
  rcases Nat.lt_trichotomy i A with hi | rfl | hi
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    rfl
  · rw [ite_eq_left (by omega), ite_eq_left rfl, ite_eq_right (by omega), Nat.sub_self]
    rfl
  · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      Option.none_or, show i - A = (i - (A + 1)) + 1 by omega, List.getElem?_cons_succ]

private theorem disj_single_ofBytes (A : Nat) (b : Memory.Byte) (bs : List Memory.Byte) :
    AHeap.Disj (AHeap.single A b) (AHeap.ofBytes (A + 1) bs) := by
  refine ⟨fun i => ?_, Or.inl rfl⟩
  by_cases hi : i = A
  · exact Or.inr (by simp [AHeap.ofBytes, hi])
  · exact Or.inl (by simp [AHeap.single, hi])

/-- The abstract heap owning `k` zero bytes from `A` on: what `memory.grow`
hands back, and the value of the `[memory.grow]` rule's iterated star. -/
private def zeroSeg (A k : Nat) : AHeap := AHeap.ofBytes A (List.replicate k 0)

private theorem zeroSeg_size (A k : Nat) : (zeroSeg A k).size = none := rfl

private theorem zeroSeg_cells_none {A k i : Nat} (h : i < A ∨ A + k ≤ i) :
    (zeroSeg A k).cells i = none :=
  ofBytes_cells_none (by rwa [List.length_replicate])

/-- The iterated star of `i ↦ 0` over `[A, A + k)` is the zero-filled segment. -/
private theorem iterRange_zeros (k A : Nat) (ρ : Sto) :
    HAssert.iterRange A (A + k) (fun i => HAssert.cell (fun _ => i) (fun _ => 0)) ρ
      (zeroSeg A k) := by
  show HAssert.iterRange A (A + k) _ ρ (AHeap.ofBytes A (List.replicate k 0))
  induction k generalizing A with
  | zero =>
    rw [HAssert.iterRange, Nat.add_sub_cancel_left, List.range'_zero, List.foldr_nil]
    exact ofBytes_nil A
  | succ k ih =>
    rw [HAssert.iterRange, Nat.add_sub_cancel_left, List.range'_succ, List.foldr_cons]
    refine ⟨AHeap.single A 0, AHeap.ofBytes (A + 1) (List.replicate k 0),
      disj_single_ofBytes .., by rw [List.replicate_succ, ofBytes_cons], rfl, ?_⟩
    have hih := ih (A + 1)
    rwa [HAssert.iterRange, Nat.add_sub_cancel_left] at hih

/-! ## Growth -/

private theorem zeroSeg_cells {A k i : Nat} {b : Memory.Byte}
    (hi : (zeroSeg A k).cells i = some b) : A ≤ i ∧ i - A < k ∧ b = 0 := by
  obtain ⟨hA, hlt, hget⟩ := ofBytes_cells_isSome hi
  rw [List.length_replicate] at hlt
  rw [List.getElem?_replicate, ite_eq_left hlt, Option.some.injEq] at hget
  exact ⟨hA, hlt, hget.symm⟩

private theorem append_zeros_left {mem after : Memory.Bytes} {k i : Nat}
    (hl : after.data.toList = mem.data.toList ++ List.replicate k 0) (hi : i < mem.size) :
    after[i]? = mem[i]? := by
  rw [getElem?_eq, getElem?_eq, hl,
    List.getElem?_append_left (by rw [length_toList]; exact hi)]

private theorem append_zeros_right {mem after : Memory.Bytes} {k i : Nat}
    (hl : after.data.toList = mem.data.toList ++ List.replicate k 0)
    (hi : mem.size ≤ i) (hi' : i < mem.size + k) : after[i]? = some 0 := by
  rw [getElem?_eq, hl, List.getElem?_append_right (by rw [length_toList]; exact hi),
    length_toList, List.getElem?_replicate, ite_eq_left (by omega)]

private theorem grow?_spec {mem after : Memory.Bytes} {mx : Option Nat} {delta : Nat}
    (hg : Memory.grow? mem mx delta = some after) :
    mem.size % Memory.pageSize = 0 ∧ Memory.size mem + delta ≤ Memory.maxPages ∧
      after.data.toList = mem.data.toList ++ List.replicate (delta * Memory.pageSize) 0 := by
  rw [Memory.grow?] at hg
  split at hg
  · rename_i hc
    obtain rfl := Option.some_inj.mp hg
    exact ⟨hc.1, hc.2.1, by
      simp [ByteArray.data_append, Array.toList_append, Array.toList_replicate]⟩
  · exact absurd hg (by simp)

/-! ### Inverting the memory instructions

The operands are kept as a variable `args`: with a concrete operand list the
dependent pattern matcher cannot discard the `convert` rule, whose operand type is
computed from the conversion. -/

private theorem plain_intLoad_inv {s s' : Store H} {f f' : Frame} {args : List Value}
    {t : IntType} {p : Option (Silmaril.Wasm.V1.PackSize × Signedness)} {arg : Silmaril.Wasm.V1.MemArg} {rets : List Value}
    (step : Plain s f args (.intLoad t p arg) s' f' rets) :
    s = s' ∧ f = f' ∧ ∃ c addr m w, args = [.int .i32 c] ∧ frameMemory s f = some (addr, m) ∧
      loadInt t p m.data (effectiveAddress c arg) = some w ∧ [w] = rets :=
  match step with
  | .intLoad _ _ _ _ _ c addr m w hmem hloaded => ⟨rfl, rfl, c, addr, m, w, rfl, hmem, hloaded, rfl⟩

private theorem trap_intLoad_inv {s : Store H} {f : Frame} {args : List Value} {t : IntType}
    {p : Option (Silmaril.Wasm.V1.PackSize × Signedness)} {arg : Silmaril.Wasm.V1.MemArg}
    (htrap : PlainTrap s f args (.intLoad t p arg)) :
    ∃ c addr m, args = [.int .i32 c] ∧ frameMemory s f = some (addr, m) ∧
      loadInt t p m.data (effectiveAddress c arg) = none :=
  match htrap with
  | .intLoad _ _ _ _ _ c addr m hmem hloaded => ⟨c, addr, m, rfl, hmem, hloaded⟩

private theorem plain_floatLoad_inv {s s' : Store H} {f f' : Frame} {args : List Value}
    {t : FloatType} {arg : Silmaril.Wasm.V1.MemArg} {rets : List Value}
    (step : Plain s f args (.floatLoad t arg) s' f' rets) :
    s = s' ∧ f = f' ∧ ∃ c addr m w, args = [.int .i32 c] ∧ frameMemory s f = some (addr, m) ∧
      loadFloat t m.data (effectiveAddress c arg) = some w ∧ [w] = rets :=
  match step with
  | .floatLoad _ _ _ _ c addr m w hmem hloaded => ⟨rfl, rfl, c, addr, m, w, rfl, hmem, hloaded, rfl⟩

private theorem trap_floatLoad_inv {s : Store H} {f : Frame} {args : List Value} {t : FloatType}
    {arg : Silmaril.Wasm.V1.MemArg} (htrap : PlainTrap s f args (.floatLoad t arg)) :
    ∃ c addr m, args = [.int .i32 c] ∧ frameMemory s f = some (addr, m) ∧
      loadFloat t m.data (effectiveAddress c arg) = none :=
  match htrap with
  | .floatLoad _ _ _ _ c addr m hmem hloaded => ⟨c, addr, m, rfl, hmem, hloaded⟩

private theorem plain_intStore_inv {s s' : Store H} {f f' : Frame} {args : List Value}
    {t : IntType} {p : Option Silmaril.Wasm.V1.PackSize} {arg : Silmaril.Wasm.V1.MemArg} {rets : List Value}
    (step : Plain s f args (.intStore t p arg) s' f' rets) :
    f = f' ∧ [] = rets ∧ ∃ c x addr m bytes, args = [.int .i32 c, .int t x] ∧
      frameMemory s f = some (addr, m) ∧
      storeInt t p m.data (effectiveAddress c arg) x = some bytes ∧
      setMemory s addr {m with data := bytes} = s' :=
  match step with
  | .intStore _ _ _ _ _ c x addr m bytes hmem hstored =>
    ⟨rfl, rfl, c, x, addr, m, bytes, rfl, hmem, hstored, rfl⟩

private theorem trap_intStore_inv {s : Store H} {f : Frame} {args : List Value} {t : IntType}
    {p : Option Silmaril.Wasm.V1.PackSize} {arg : Silmaril.Wasm.V1.MemArg} (htrap : PlainTrap s f args (.intStore t p arg)) :
    ∃ c x addr m, args = [.int .i32 c, .int t x] ∧ frameMemory s f = some (addr, m) ∧
      storeInt t p m.data (effectiveAddress c arg) x = none :=
  match htrap with
  | .intStore _ _ _ _ _ c x addr m hmem hstored => ⟨c, x, addr, m, rfl, hmem, hstored⟩

private theorem plain_floatStore_inv {s s' : Store H} {f f' : Frame} {args : List Value}
    {t : FloatType} {arg : Silmaril.Wasm.V1.MemArg} {rets : List Value}
    (step : Plain s f args (.floatStore t arg) s' f' rets) :
    f = f' ∧ [] = rets ∧ ∃ c x addr m bytes, args = [.int .i32 c, .float t x] ∧
      frameMemory s f = some (addr, m) ∧
      storeFloat t m.data (effectiveAddress c arg) x = some bytes ∧
      setMemory s addr {m with data := bytes} = s' :=
  match step with
  | .floatStore _ _ _ _ c x addr m bytes hmem hstored =>
    ⟨rfl, rfl, c, x, addr, m, bytes, rfl, hmem, hstored, rfl⟩

private theorem trap_floatStore_inv {s : Store H} {f : Frame} {args : List Value} {t : FloatType}
    {arg : Silmaril.Wasm.V1.MemArg} (htrap : PlainTrap s f args (.floatStore t arg)) :
    ∃ c x addr m, args = [.int .i32 c, .float t x] ∧ frameMemory s f = some (addr, m) ∧
      storeFloat t m.data (effectiveAddress c arg) x = none :=
  match htrap with
  | .floatStore _ _ _ _ c x addr m hmem hstored => ⟨c, x, addr, m, rfl, hmem, hstored⟩

/-- The address operand of a memory instruction, read off its operand list. -/
private theorem addr_eq {c : BitVec 32} {rest rest' : List Value} {a : BitVec 32}
    (h : Value.int .i32 a :: rest = Value.int .i32 c :: rest') : a = c :=
  Value_int_inj (List.cons.inj h).1

/-- The stored integer operand of a store, read off its operand list. -/
private theorem int_operand_eq {t : IntType} {a c : BitVec 32} {x y : BitVec t.width}
    (h : [Value.int .i32 a, Value.int t y] = [Value.int .i32 c, Value.int t x]) :
    a = c ∧ y = x :=
  ⟨addr_eq h, Value_int_inj (List.cons.inj (List.cons.inj h).2).1⟩

/-- The stored float operand of a store, read off its operand list. -/
private theorem float_operand_eq {t : FloatType} {a c : BitVec 32} {x y : BitVec t.width}
    (h : [Value.int .i32 a, Value.float t y] = [Value.int .i32 c, Value.float t x]) :
    a = c ∧ y = x :=
  ⟨addr_eq h, Value_float_inj (List.cons.inj (List.cons.inj h).2).1⟩

/-- An owned cell is in bounds: writing over it succeeds. -/
private theorem write_of_cellNum {s : Store H} {f : Frame} {ρ : Sto} {h hf : AHeap}
    {tp : NumType} {A : Term Nat} {x₀ : Term (BitVec tp.width)} {addr : MemAddr} {m : MemInst}
    (hx₀ : HAssert.cellNum tp A x₀ ρ h) (reify : Reifies F s f ρ (h ∪ hf))
    (hmem : frameMemory s f = some (addr, m)) (pos : 0 < tp.width / 8) (n : Nat) :
    Memory.writeBytes m.data (A ρ) (Memory.encodeLE (tp.width / 8) n) ≠ none := by
  have hb : A ρ + (tp.width / 8) ≤ m.data.size := by
    simpa only [Memory.encodeLE_size] using
      bound_of_agree (enc := Memory.encodeLE (tp.width / 8) (x₀ ρ).toNat)
        (by rw [Memory.encodeLE_size]; exact pos) (cellNum_agree hx₀ reify hmem)
  rw [writeBytes_of_bound (by rw [Memory.encodeLE_size]; exact hb)]
  exact Option.some_ne_none _

theorem valid_intLoad (t : IntType) (arg : Silmaril.Wasm.V1.MemArg) (a : Term (BitVec 32))
    (v : Term (BitVec t.width)) :
    Valid host n F L R
      (Assert.mk [Term.i32 a] (HAssert.cellNum (.int t) (memAddr arg a) v))
      [.intLoad t none arg]
      (Assert.mk [Term.int t v] (HAssert.cellNum (.int t) (memAddr arg a) v)) := by
  refine valid_single trivial (fun s s' f f' args rets step => by cases step; rfl)
    (fun s f args step => by cases step; rfl) ?_ ?_
  · intro s f ρ h hf hp hdisj reify htrap
    obtain ⟨c, addr, m, hargs, hmem, hloaded⟩ := trap_intLoad_inv htrap
    obtain rfl : a ρ = c := addr_eq hargs
    exact absurd ((loadInt_of_agree (x := v ρ) (cellNum_agree hp reify hmem)).symm.trans hloaded)
      (Option.some_ne_none _)
  · intro s s' f f' ρ h hf rets hp hdisj reify step
    obtain ⟨rfl, rfl, c, addr, m, w, hargs, hmem, hloaded, rfl⟩ := plain_intLoad_inv step
    obtain rfl : a ρ = c := addr_eq hargs
    have hw : Value.int t (v ρ) = w :=
      Option.some.inj ((loadInt_of_agree (cellNum_agree hp reify hmem)).symm.trans hloaded)
    exact ⟨h, ρ, hdisj, reify, fun _ _ => rfl, by rw [← hw]; rfl, hp⟩

theorem valid_floatLoad (t : FloatType) (arg : Silmaril.Wasm.V1.MemArg) (a : Term (BitVec 32))
    (v : Term (BitVec t.width)) :
    Valid host n F L R
      (Assert.mk [Term.i32 a] (HAssert.cellNum (.float t) (memAddr arg a) v))
      [.floatLoad t arg]
      (Assert.mk [Term.float t v] (HAssert.cellNum (.float t) (memAddr arg a) v)) := by
  refine valid_single trivial (fun s s' f f' args rets step => by cases step; rfl)
    (fun s f args step => by cases step; rfl) ?_ ?_
  · intro s f ρ h hf hp hdisj reify htrap
    obtain ⟨c, addr, m, hargs, hmem, hloaded⟩ := trap_floatLoad_inv htrap
    obtain rfl : a ρ = c := addr_eq hargs
    exact absurd ((loadFloat_of_agree (x := v ρ) (cellNum_agree hp reify hmem)).symm.trans
      hloaded) (Option.some_ne_none _)
  · intro s s' f f' ρ h hf rets hp hdisj reify step
    obtain ⟨rfl, rfl, c, addr, m, w, hargs, hmem, hloaded, rfl⟩ := plain_floatLoad_inv step
    obtain rfl : a ρ = c := addr_eq hargs
    have hw : Value.float t (v ρ) = w :=
      Option.some.inj ((loadFloat_of_agree (cellNum_agree hp reify hmem)).symm.trans hloaded)
    exact ⟨h, ρ, hdisj, reify, fun _ _ => rfl, by rw [← hw]; rfl, hp⟩

theorem valid_intStore (t : IntType) (arg : Silmaril.Wasm.V1.MemArg) (a : Term (BitVec 32))
    (v : Term (BitVec t.width)) :
    Valid host n F L R
      (Assert.mk [Term.i32 a, Term.int t v] (HAssert.cellNumAny (.int t) (memAddr arg a)))
      [.intStore t none arg]
      (Assert.mk [] (HAssert.cellNum (.int t) (memAddr arg a) v)) := by
  refine valid_single trivial (fun s s' f f' args rets step => by cases step; rfl)
    (fun s f args step => by cases step; rfl) ?_ ?_
  · intro s f ρ h hf hp hdisj reify htrap
    obtain ⟨x₀, hx₀⟩ := hp
    obtain ⟨c, x, addr, m, hargs, hmem, hstored⟩ := trap_intStore_inv htrap
    obtain ⟨rfl, rfl⟩ : a ρ = c ∧ v ρ = x := int_operand_eq hargs
    exact write_of_cellNum hx₀ reify hmem (by cases t <;> decide) (v ρ).toNat
      ((storeInt_eq_writeBytes (v ρ)).symm.trans hstored)
  · intro s s' f f' ρ h hf rets hp hdisj reify step
    obtain ⟨x₀, hx₀⟩ := hp
    obtain ⟨rfl, rfl, c, x, addr, m, bytes, hargs, hmem, hstored, rfl⟩ := plain_intStore_inv step
    obtain ⟨rfl, rfl⟩ : a ρ = c ∧ v ρ = x := int_operand_eq hargs
    obtain ⟨hd, hr⟩ := store_effect (old := Memory.encodeLE (t.width / 8) x₀.toNat)
      (enc := Memory.encodeLE (t.width / 8) (v ρ).toNat) (cellNum_ofBytes hx₀)
      (by rw [Memory.encodeLE_size, Memory.encodeLE_size]) hdisj reify hmem
      ((storeInt_eq_writeBytes (v ρ)).symm.trans hstored)
    exact ⟨_, ρ, hd, hr, fun _ _ => rfl, rfl, cellNum_of_ofBytes rfl⟩

theorem valid_floatStore (t : FloatType) (arg : Silmaril.Wasm.V1.MemArg) (a : Term (BitVec 32))
    (v : Term (BitVec t.width)) :
    Valid host n F L R
      (Assert.mk [Term.i32 a, Term.float t v] (HAssert.cellNumAny (.float t) (memAddr arg a)))
      [.floatStore t arg]
      (Assert.mk [] (HAssert.cellNum (.float t) (memAddr arg a) v)) := by
  refine valid_single trivial (fun s s' f f' args rets step => by cases step; rfl)
    (fun s f args step => by cases step; rfl) ?_ ?_
  · intro s f ρ h hf hp hdisj reify htrap
    obtain ⟨x₀, hx₀⟩ := hp
    obtain ⟨c, x, addr, m, hargs, hmem, hstored⟩ := trap_floatStore_inv htrap
    obtain ⟨rfl, rfl⟩ : a ρ = c ∧ v ρ = x := float_operand_eq hargs
    exact write_of_cellNum hx₀ reify hmem (by cases t <;> decide) (v ρ).toNat
      ((storeFloat_eq_writeBytes (v ρ)).symm.trans hstored)
  · intro s s' f f' ρ h hf rets hp hdisj reify step
    obtain ⟨x₀, hx₀⟩ := hp
    obtain ⟨rfl, rfl, c, x, addr, m, bytes, hargs, hmem, hstored, rfl⟩ :=
      plain_floatStore_inv step
    obtain ⟨rfl, rfl⟩ : a ρ = c ∧ v ρ = x := float_operand_eq hargs
    obtain ⟨hd, hr⟩ := store_effect (old := Memory.encodeLE (t.width / 8) x₀.toNat)
      (enc := Memory.encodeLE (t.width / 8) (v ρ).toNat) (cellNum_ofBytes hx₀)
      (by rw [Memory.encodeLE_size, Memory.encodeLE_size]) hdisj reify hmem
      ((storeFloat_eq_writeBytes (v ρ)).symm.trans hstored)
    exact ⟨_, ρ, hd, hr, fun _ _ => rfl, rfl, cellNum_of_ofBytes rfl⟩

theorem valid_memorySize (p : Term Nat) :
    Valid host n F L R (Assert.mk [] (HAssert.size p)) [.memorySize]
      (Assert.mk [Term.i32 fun ρ => BitVec.ofNat 32 (p ρ)] (HAssert.size p)) := by
  refine valid_single trivial (fun s s' f f' args rets step => by cases step; rfl)
    (fun s f args step => by cases step) (fun s f ρ h hf _ _ _ htrap => by cases htrap) ?_
  intro s s' f f' ρ h hf rets hp hdisj reify step
  cases step
  rename_i addr m hmem
  have hsize : Memory.size m.data = p ρ :=
    (reifiesMem_agree reify.mem hmem).2 (p ρ) (by rw [AHeap.union_size, hp]; rfl)
  exact ⟨h, ρ, hdisj, reify, fun _ _ => rfl, by rw [hsize]; rfl, hp⟩

/-! ### `memory.grow` -/

private theorem plain_memoryGrow_inv {s s' : Store H} {f f' : Frame} {args rets : List Value}
    (step : Plain s f args .memoryGrow s' f' rets) :
    f = f' ∧ ∃ c addr m r bytes, args = [.int .i32 c] ∧ frameMemory s f = some (addr, m) ∧
      Memory.Grow m.data m.max c.toNat bytes r ∧
      setMemory s addr {m with data := bytes} = s' ∧ [.int .i32 r] = rets :=
  match step with
  | .memoryGrow _ _ addr m c r bytes hmem hgrown =>
    ⟨rfl, c, addr, m, r, bytes, rfl, hmem, hgrown, rfl, rfl⟩

/-- Owning the page count, the frame owns no page count of its own. -/
private theorem frame_size_none {p : Nat} {hf : AHeap} (hdisj : AHeap.Disj (AHeap.pages p) hf) :
    hf.size = none := by
  rcases hdisj.2 with hz | hz
  · exact absurd hz (by simp [AHeap.pages])
  · exact hz

/-- Every cell the frame owns is inside the memory. -/
private theorem frame_cells_lt {p : Nat} {hf : AHeap} {mem : Memory.Bytes}
    (hcells : ∀ i b, (AHeap.pages p ∪ hf).cells i = some b → mem[i]? = some b) :
    ∀ i b, hf.cells i = some b → i < mem.size := by
  intro i b hb
  have hi : mem.data.toList[i]? = some b := by
    rw [← getElem?_eq]; exact hcells i b (by rw [AHeap.union_cells, hb]; rfl)
  have hlt : i < mem.data.toList.length := (List.getElem?_eq_some_iff.mp hi).1
  simpa only [length_toList] using hlt

/-- The sizes of the memory before and after growing by `δ` pages. -/
private theorem grow_sizes {mem bytes : Memory.Bytes} {p δ : Nat} (hsz : Memory.size mem = p)
    (hmod : mem.size % Memory.pageSize = 0)
    (hlist : bytes.data.toList = mem.data.toList ++ List.replicate (δ * Memory.pageSize) 0) :
    mem.size = p * Memory.pageSize ∧ Memory.size bytes = p + δ := by
  have hsz' : mem.size / Memory.pageSize = p := hsz
  have hdata : mem.size = p * Memory.pageSize := by
    have h1 : Memory.pageSize * (mem.size / Memory.pageSize) + mem.size % Memory.pageSize =
        mem.size := Nat.div_add_mod _ _
    rw [hsz', hmod, Nat.add_zero] at h1
    rw [← h1, Nat.mul_comm]
  have hafter : bytes.size = (p + δ) * Memory.pageSize := by
    have h1 : bytes.data.toList.length = mem.data.toList.length + δ * Memory.pageSize := by
      rw [hlist, List.length_append, List.length_replicate]
    rw [length_toList, length_toList] at h1
    rw [h1, hdata, Nat.add_mul]
  refine ⟨hdata, ?_⟩
  show bytes.size / Memory.pageSize = _
  rw [hafter]
  exact Nat.mul_div_cancel _ (by decide)

/-- The grown memory agrees with the new zero cells, the new page count and the
frame's cells. -/
private theorem grow_cells {mem bytes : Memory.Bytes} {p δ : Nat} {hf : AHeap}
    (hdata : mem.size = p * Memory.pageSize)
    (hlist : bytes.data.toList = mem.data.toList ++ List.replicate (δ * Memory.pageSize) 0)
    (hcells : ∀ i b, (AHeap.pages p ∪ hf).cells i = some b → mem[i]? = some b)
    (hfcells : ∀ i b, hf.cells i = some b → i < mem.size) (i : Nat) (b : Memory.Byte)
    (hb : (zeroSeg (p * Memory.pageSize) (δ * Memory.pageSize) ∪ AHeap.pages (p + δ) ∪ hf).cells i
      = some b) :
    bytes[i]? = some b := by
  cases hc : (zeroSeg (p * Memory.pageSize) (δ * Memory.pageSize)).cells i with
  | some b' =>
    have hbb : b' = b := by
      simpa only [AHeap.union_cells, hc, Option.some_or, Option.some.injEq] using hb
    obtain ⟨hA, hlt, rfl⟩ : p * Memory.pageSize ≤ i ∧ i - p * Memory.pageSize <
        δ * Memory.pageSize ∧ b' = 0 := zeroSeg_cells hc
    exact hbb ▸ append_zeros_right hlist (by omega) (by omega)
  | none =>
    have hb' : hf.cells i = some b := by
      simpa only [AHeap.union_cells, hc, Option.none_or, AHeap.pages] using hb
    rw [append_zeros_left hlist (hfcells i b hb')]
    exact hcells i b (by rw [AHeap.union_cells, hb']; rfl)

/-- The new pages of a grow by `δ` pages, as the iterated star of zero cells. -/
private theorem zeroSeg_iter (p δ : Nat) (ρ : Sto) :
    HAssert.iterRange (p * Memory.pageSize) ((p + δ) * Memory.pageSize)
      (fun i => HAssert.cell (fun _ => i) (fun _ => 0)) ρ
      (zeroSeg (p * Memory.pageSize) (δ * Memory.pageSize)) := by
  rw [Nat.add_mul]; exact iterRange_zeros _ _ ρ

/-- A successful `memory.grow`: the new pages are owned as zero cells. -/
private theorem grow_success {s : Store H} {f : Frame} {ρ : Sto} {hf : AHeap} {addr : MemAddr}
    {m : MemInst} {bytes : Memory.Bytes} {p δ : Nat}
    (reify : Reifies F s f ρ (AHeap.pages p ∪ hf)) (hmem : frameMemory s f = some (addr, m))
    (hsz : Memory.size m.data = p) (hfsize : hf.size = none)
    (hcells : ∀ i b, (AHeap.pages p ∪ hf).cells i = some b → m.data[i]? = some b)
    (hfcells : ∀ i b, hf.cells i = some b → i < m.data.size)
    (hg : Memory.grow? m.data m.max δ = some bytes) :
    AHeap.Disj (zeroSeg (p * Memory.pageSize) (δ * Memory.pageSize) ∪ AHeap.pages (p + δ)) hf ∧
      Reifies F (setMemory s addr {m with data := bytes}) f ρ
        (zeroSeg (p * Memory.pageSize) (δ * Memory.pageSize) ∪ AHeap.pages (p + δ) ∪ hf) ∧
      p + δ ≤ Memory.maxPages := by
  obtain ⟨hmod, hmax, hlist⟩ := grow?_spec hg
  obtain ⟨hdata, hsizeAfter⟩ : m.data.size = p * Memory.pageSize ∧ Memory.size bytes = p + δ :=
    grow_sizes hsz hmod hlist
  have hzf : AHeap.Disj (zeroSeg (p * Memory.pageSize) (δ * Memory.pageSize)) hf := by
    refine ⟨fun i => ?_, Or.inl rfl⟩
    cases hb : hf.cells i with
    | none => exact Or.inr rfl
    | some b => exact Or.inl (zeroSeg_cells_none (Or.inl (by have := hfcells i b hb; omega)))
  have hpf : AHeap.Disj (AHeap.pages (p + δ)) hf := ⟨fun _ => Or.inl rfl, Or.inr hfsize⟩
  refine ⟨AHeap.disj_union hzf hpf, reifies_setMemory reify hmem
    (grow_cells hdata hlist hcells hfcells) (fun q hq => ?_), by rw [← hsz]; exact hmax⟩
  have hq' : p + δ = q := by
    simpa only [AHeap.union_size, zeroSeg_size, AHeap.pages, Option.none_or, Option.some_or,
      Option.some.injEq] using hq
  exact hq' ▸ hsizeAfter

theorem valid_memoryGrow (d : Term (BitVec 32)) (p : Term Nat) :
    Valid host n F L R (Assert.mk [Term.i32 d] (HAssert.size p)) [.memoryGrow]
      (Assert.ex fun r : BitVec 32 => Assert.mk [Term.i32 fun _ => r]
        (HAssert.or
          (HAssert.and
            (HAssert.star
              (HAssert.iter (fun ρ => p ρ * Memory.pageSize)
                (fun ρ => (p ρ + (d ρ).toNat) * Memory.pageSize)
                (fun i => HAssert.cell (fun _ => i) (fun _ => 0)))
              (HAssert.size fun ρ => p ρ + (d ρ).toNat))
            (HAssert.pure fun ρ =>
              r = BitVec.ofNat 32 (p ρ) ∧ p ρ + (d ρ).toNat ≤ Memory.maxPages))
          (HAssert.and (HAssert.size p) (HAssert.pure fun _ => r = -1)))) := by
  refine valid_single trivial (fun s s' f f' args rets step => by cases step; rfl)
    (fun s f args step => (not_plainTrap step).elim)
    (fun s f ρ h hf _ _ _ htrap => not_plainTrap htrap) ?_
  intro s s' f f' ρ h hf rets hp hdisj reify step
  obtain ⟨rfl, c, addr, m, r, bytes, hargs, hmem, hgrown, rfl, rfl⟩ := plain_memoryGrow_inv step
  obtain rfl : d ρ = c := addr_eq hargs
  obtain rfl : h = AHeap.pages (p ρ) := hp
  obtain ⟨hcells, hsizes⟩ := reifiesMem_agree reify.mem hmem
  have hsz : Memory.size m.data = p ρ := hsizes (p ρ) rfl
  cases hgrown with
  | failure =>
    exact ⟨AHeap.pages (p ρ), ρ, hdisj, reifies_setMemory reify hmem hcells hsizes,
      fun _ _ => rfl, -1, rfl, Or.inr ⟨rfl, rfl⟩⟩
  | success _ hg =>
    obtain ⟨hdisj', hreify, hmax⟩ := grow_success reify hmem hsz (frame_size_none hdisj) hcells
      (frame_cells_lt hcells) hg
    exact ⟨_, ρ, hdisj', hreify, fun _ _ => rfl, BitVec.ofNat 32 (p ρ), by rw [hsz]; rfl,
      Or.inl ⟨⟨_, _, ⟨fun _ => Or.inr rfl, Or.inl rfl⟩, rfl, zeroSeg_iter _ _ ρ, rfl⟩, rfl, hmax⟩⟩

end Silmaril.Wasm.Logic.V1
