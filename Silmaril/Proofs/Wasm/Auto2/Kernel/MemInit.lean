module

public import Silmaril.Wasm.Auto2.Kernel.Defs
public import Silmaril.Wasm.Verify.Kernel.Thms

/-!
# `memoryInitLoop` in closed form

`memoryInitLoop_fast`: on the fast path (both ranges in bounds, no address wraps) the byte loop
of `memory.init` writes the whole segment at once; `memoryInitLoopK_eq` follows.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto2.Kernel

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Verify.Kernel
open Silmaril.Wasm.Auto2.Kernel

variable {H : Type}

theorem mem?_setMem {s : Store H} {f : Frame} {x : MemIdx} {ma : Nat} {mi : MemInst}
    (h : s.mem? f x = some (ma, mi)) (mi' : MemInst) :
    (s.setMem ma mi').mem? f x = some (ma, mi') := by
  simp only [Store.mem?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, he⟩ := h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hlt : a < s.mems.length := (List.getElem?_eq_some_iff.mp hb).1
  simp [Store.mem?, Store.setMem, ha, hlt]

theorem data?_setMem (s : Store H) (f : Frame) (y : DataIdx) (ma : Nat) (mi : MemInst) :
    (s.setMem ma mi).data? f y = s.data? f y := rfl

theorem setMem_setMem (s : Store H) (a : Nat) (m₁ m₂ : MemInst) :
    (s.setMem a m₁).setMem a m₂ = s.setMem a m₂ := by
  simp [Store.setMem]

/-- One byte stored by `Memory.store` (the step of `memoryInitLoop`) is a `writeL`. -/
theorem store_byte (B : ByteArray) (i : Nat) (b : UInt8) (h : i + 1 ≤ B.size) :
    Memory.store B i (count := 1) ((BitVec.ofNat 32 b.toNat).setWidth 8) =
      some ⟨⟨writeL B.data.toList i [b]⟩⟩ := by
  rw [← fstore_eq]
  have hl : lenGe B.data.toList (i + 1) = true := by
    rw [lenGe_eq]
    exact decide_eq_true h
  have hb : (Memory.encodeLE 1 ((BitVec.ofNat 32 b.toNat).setWidth 8).toNat).data.toList =
      [b] := by
    simp [Memory.encodeLE]
  simp only [fstore, hl, ite_true, hb]

theorem overL_nil {α : Type} (l : List α) : overL l [] = l := by
  cases l <;> rfl

theorem writeL_zero {α : Type} (l bs : List α) : writeL l 0 bs = overL l bs := by
  cases l <;> rfl

/-- Two consecutive writes are one. -/
theorem writeL_cons {α : Type} (l : List α) (i : Nat) (b : α) (r : List α) :
    writeL (writeL l i [b]) (i + 1) r = writeL l i (b :: r) := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih =>
    cases i with
    | zero =>
      show writeL (b :: overL l []) 1 r = b :: overL l r
      rw [overL_nil]
      show b :: writeL l 0 r = b :: overL l r
      rw [writeL_zero]
    | succ i =>
      show a :: writeL (writeL l i [b]) (i + 1) r = a :: writeL l i (b :: r)
      rw [ih]

theorem size_writeL (B : ByteArray) (i : Nat) (bs : List UInt8) (h : i + bs.length ≤ B.size) :
    (⟨⟨writeL B.data.toList i bs⟩⟩ : ByteArray).size = B.size := by
  show (writeL B.data.toList i bs).length = B.data.toList.length
  rw [writeL_eq _ _ _ (by simpa using h)]
  simp only [List.length_append, List.length_take, List.length_drop]
  have : B.data.toList.length = B.size := rfl
  omega

theorem toNat_add_one {w : Nat} (i : BitVec w) (h : i.toNat + 1 < 2 ^ w) :
    (i + 1).toNat = i.toNat + 1 := by
  rw [BitVec.toNat_add]
  show (i.toNat + 1 % 2 ^ w) % 2 ^ w = i.toNat + 1
  rw [Nat.mod_eq_of_lt (by omega : 1 < 2 ^ w)]
  exact Nat.mod_eq_of_lt h

theorem drop_take_succ (l : List UInt8) (j k : Nat) (h : j < l.length) :
    (l.drop j).take (k + 1) = l[j] :: (l.drop (j + 1)).take k := by
  rw [List.drop_eq_getElem_cons h]
  rfl

/-- **`memoryInitLoop` on the fast path**: the whole segment written at once. -/
theorem memoryInitLoop_fast {f : Frame} {x : MemIdx} {y : DataIdx} {a : AddrType} {ma da : Nat}
    {di : DataInst} : ∀ (k : Nat) (s : Store H) (mi : MemInst) (i : BitVec a.intType.width)
      (j n : BitVec 32), n.toNat = k → s.mem? f x = some (ma, mi) →
      s.data? f y = some (da, di) → i.toNat + k ≤ mi.bytes.size → j.toNat + k ≤ di.bytes.size →
      i.toNat + k < 2 ^ a.intType.width → j.toNat + k < 2 ^ 32 →
      memoryInitLoop s f x y a i j n =
        if k = 0 then some s
        else some (s.setMem ma
          ⟨mi.type, writeSeg mi i.toNat ((di.bytes.data.toList.drop j.toNat).take k)⟩)
  | 0, s, mi, i, j, n, hn, hm, hd, hi, hj, _, _ => by
    have hn0 : n = 0 := BitVec.eq_of_toNat_eq (by simpa using hn)
    subst hn0
    rw [memoryInitLoop]
    simp only [hm, hd]
    simp [show i.toNat ≤ mi.bytes.size by omega, show j.toNat ≤ di.bytes.size by omega]
  | k + 1, s, mi, i, j, n, hn, hm, hd, hi, hj, hiw, hjw => by
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at hn
    have hjl : j.toNat < di.bytes.data.size := by
      have : di.bytes.data.size = di.bytes.size := rfl
      omega
    have hb : di.bytes.data[j.toNat]? = some di.bytes.data[j.toNat] :=
      Array.getElem?_eq_getElem hjl
    have hst : Memory.store mi.bytes (effAddr i.toNat memarg0) (count := PackSize.i8.width / 8)
        ((BitVec.ofNat 32 di.bytes.data[j.toNat].toNat).setWidth _) =
        some ⟨⟨writeL mi.bytes.data.toList i.toNat [di.bytes.data[j.toNat]]⟩⟩ :=
      store_byte mi.bytes i.toNat _ (by omega)
    have hsz := size_writeL mi.bytes i.toNat [di.bytes.data[j.toNat]] (by simp; omega)
    have hk : (n - 1).toNat = k := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
      simp
      omega
    have hi1 := toNat_add_one i (by omega)
    have hj1 := toNat_add_one j (by omega)
    rw [memoryInitLoop]
    simp only [hm, hd]
    have hc : i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ di.bytes.size :=
      ⟨by omega, by omega⟩
    simp only [hc, hn0, ↓reduceDIte, hb, hst]
    rw [memoryInitLoop_fast k _ { mi with bytes := _ } (i + 1) (j + 1) (n - 1) hk
      (mem?_setMem hm _) (by rw [data?_setMem]; exact hd) (by rw [hsz, hi1]; omega)
      (by rw [hj1]; omega) (by rw [hi1]; omega) (by rw [hj1]; omega)]
    have hl : di.bytes.data.toList.length = di.bytes.data.size := Array.length_toList
    simp only [Nat.succ_ne_zero k, ↓reduceIte]
    rw [drop_take_succ _ _ _ (by omega)]
    simp only [Array.getElem_toList]
    by_cases hk0 : k = 0
    · subst hk0
      simp only [↓reduceIte, List.take_zero]
      rfl
    · simp only [hk0, ↓reduceIte]
      rw [setMem_setMem, hi1, hj1]
      simp only [writeSeg, and_self, ↓reduceIte]
      rw [writeL_cons]

/-- **`memoryInitLoopK = memoryInitLoop`.** -/
theorem memoryInitLoopK_eq : @memoryInitLoopK H = @memoryInitLoop H := by
  funext s f x y a i j n
  unfold memoryInitLoopK
  split
  · rename_i ma mi da di hm hd
    split
    · rename_i hfast
      simp only [initFast, Bool.and_eq_true, lenGe_eq, decide_eq_true_eq] at hfast
      obtain ⟨⟨⟨hi, hj⟩, hiw⟩, hjw⟩ := hfast
      rw [memoryInitLoop_fast n.toNat s mi i j n rfl hm hd hi hj hiw hjw]
    · rfl
  · rfl

end Silmaril.Proofs.Wasm.Auto2.Kernel
