module

public import Silmaril.Machine.X86.Lir.Machine.Defs

/-!
# The linear memory on the machine

`MemRel S lm mem`: the Lir linear memory `lm` has `S.memSize` bytes and byte
`a` of it is the machine byte at `S.memBase + a`. This file relates Lir's
little-endian `readLE`/`writeLE` to the machine's `loadN`/`storeN` on that
region.
-/

@[expose] public section

namespace Silmaril.X86.Backend

open Silmaril.Process (Memory)
open Silmaril.X86 (State Word Byte Reg)
open Silmaril.Machine

/-- The machine memory represents the Lir linear memory at `S.memBase`. -/
def MemRel (S : Space) (lm : Lir.Memory) (mem : Memory) : Prop :=
  lm.size = S.memSize ∧ ∀ a < lm.size, mem.bytes.get? (S.memBase + a) = some (lm.bytes a)

theorem MemRel.congr {S : Space} {lm : Lir.Memory} {m m' : Memory} (h : MemRel S lm m)
    (hb : ∀ a, S.InMem a → m'.bytes.get? a = m.bytes.get? a) : MemRel S lm m' := by
  refine ⟨h.1, fun a ha => ?_⟩
  rw [hb _ ⟨by omega, by have := h.1; omega⟩]
  exact h.2 a ha

/-! ## Little-endian values -/

private theorem and_shift_zero (b : Byte) (r : Word) :
    b.setWidth 64 &&& (r <<< 8) = 0#64 := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_setWidth, BitVec.getElem_shiftLeft,
    BitVec.getElem_zero]
  by_cases h : i < 8
  · simp [h]
  · simp [BitVec.getLsbD_of_ge b i (by omega)]

theorem readLE_toNat (bytes : Nat → Byte) :
    ∀ (k a : Nat), k ≤ 8 →
      (Lir.readLE bytes a k).toNat = Ext.leValue (List.ofFn fun i : Fin k => bytes (a + i))
  | 0, a, _ => by simp [Lir.readLE, Ext.leValue]
  | k + 1, a, hk => by
    have ih := readLE_toNat bytes k (a + 1) (by omega)
    have hlt : Ext.leValue (List.ofFn fun i : Fin k => bytes (a + 1 + i)) < 2 ^ (8 * k) := by
      rw [← ih]
      have : Lir.readLE bytes (a + 1) k = BitVec.ofNat 64 (Lir.readLE bytes (a + 1) k).toNat := by simp
      clear ih
      induction k generalizing a with
      | zero => simp [Lir.readLE]
      | succ k ih2 =>
        have := ih2 (a + 1) (by omega) (by simp)
        rw [Lir.readLE, ← BitVec.add_eq_or_of_and_eq_zero _ _ (and_shift_zero _ _)]
        rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft]
        have hb := (bytes (a + 1)).isLt
        have h56 : 2 ^ (8 * k) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.mod_eq_of_lt (a := (bytes (a + 1)).toNat) (by omega), Nat.shiftLeft_eq,
          Nat.mod_eq_of_lt (a := _ * 2 ^ 8) (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [show 8 * (k + 1) = 8 + 8 * k by omega, Nat.pow_add]
        omega
    rw [Lir.readLE, ← BitVec.add_eq_or_of_and_eq_zero _ _ (and_shift_zero _ _)]
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, ih]
    have hb := (bytes a).isLt
    have h56 : 2 ^ (8 * k) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.mod_eq_of_lt (a := (bytes a).toNat) (by omega), Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (a := _ * 2 ^ 8) (by omega), Nat.mod_eq_of_lt (by omega)]
    simp only [List.ofFn_succ, Ext.leValue, Fin.val_zero, Nat.add_zero, Fin.val_succ]
    have e : (fun i : Fin k => bytes (a + (i.val + 1))) = fun i : Fin k => bytes (a + 1 + i) := by
      funext i; congr 1; omega
    rw [e]
    omega

theorem leValue_lt : ∀ (l : List Byte), Ext.leValue l < 2 ^ (8 * l.length)
  | [] => by simp [Ext.leValue]
  | b :: l => by
    have := leValue_lt l
    have := b.isLt
    simp only [Ext.leValue, List.length_cons]
    rw [show 8 * (l.length + 1) = 8 + 8 * l.length by omega, Nat.pow_add]
    omega

/-- The linear-memory bytes of an in-bounds access, read from the machine. -/
theorem readBytes_lin {S : Space} {n : Nat} (hv : S.Valid n) {lm : Lir.Memory} {m : Memory}
    (hreg : m.regions = S.regions n) (h : MemRel S lm m) {a k : Nat} (hin : a + k ≤ lm.size) :
    m.readBytes (S.memBase + a) k = some (List.ofFn fun i : Fin k => lm.bytes (a + i)) := by
  have := Memory.readWith_eq m .read (S.memBase + a) (List.ofFn fun i : Fin k => lm.bytes (a + i))
    (by
      rw [List.length_ofFn]
      exact permitted_mem hreg hv .read (by decide) (by omega) (by have := h.1; omega))
    (fun i hi => by
      rw [List.getElem_ofFn, Nat.add_assoc]
      exact h.2 _ (by rw [List.length_ofFn] at hi; omega))
  rw [List.length_ofFn] at this
  exact this

theorem loadN_lin {S : Space} {n : Nat} (hv : S.Valid n) {lm : Lir.Memory} {m : Memory}
    (hreg : m.regions = S.regions n) (h : MemRel S lm m) {a k : Nat} (hk : k ≤ 8)
    (hin : a + k ≤ lm.size) :
    Ext.loadN m (BitVec.ofNat 64 (S.memBase + a)) k = some (Lir.readLE lm.bytes a k) := by
  have hb : S.memBase + a < 2 ^ 64 := by have := hv.mem_end; have := h.1; omega
  simp only [Ext.loadN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, readBytes_lin hv hreg h hin,
    Option.map_some, Option.some.injEq]
  apply BitVec.eq_of_toNat_eq
  rw [readLE_toNat _ _ _ hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := leValue_lt (List.ofFn fun i : Fin k => lm.bytes (a + i))
  rw [List.length_ofFn] at this
  have : 2 ^ (8 * k) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem readLE_lt (bytes : Nat → Byte) {k : Nat} (hk : k ≤ 8) (a : Nat) :
    (Lir.readLE bytes a k).toNat < 2 ^ (8 * k) := by
  rw [readLE_toNat _ _ _ hk]
  have := leValue_lt (List.ofFn fun i : Fin k => bytes (a + i))
  rwa [List.length_ofFn] at this

/-! ## Stores -/

/-- A store of the low `k` bytes of `v` to the linear memory at offset `a`
represents the Lir store, when the stored bytes agree. -/
theorem memRel_store {S : Space} {n : Nat} (hv : S.Valid n) {lm : Lir.Memory} {m m' : Memory}
    (h : MemRel S lm m) {a k : Nat} (hin : a + k ≤ lm.size) {v v' : Word}
    (hs : Ext.storeN m (BitVec.ofNat 64 (S.memBase + a)) k v' = some m')
    (hbytes : ∀ j < k, Machine.LittleEndian.wordByte v' j = Machine.LittleEndian.wordByte v j) :
    MemRel S { lm with bytes := Lir.writeLE lm.bytes a k v } m' := by
  have hb : S.memBase + a < 2 ^ 64 := by have := hv.mem_end; have := h.1; omega
  have wo := storeN_writesOnly' hb hs
  refine ⟨h.1, fun x hx => ?_⟩
  simp only [Lir.writeLE]
  by_cases hr : a ≤ x ∧ x < a + k
  · rw [ite_eq_left hr]
    have := storeN_get hb hs (x - a) (by omega)
    rw [show S.memBase + a + (x - a) = S.memBase + x by omega] at this
    rw [this, hbytes _ (by omega)]
  · rw [ite_eq_right hr, wo.2 _ (by omega)]
    exact h.2 x hx

/-- A store to the linear memory changes no byte outside it. -/
theorem store_outside {S : Space} {lm : Lir.Memory} {m m' : Memory} (h : MemRel S lm m)
    {a k : Nat} (hin : a + k ≤ lm.size) (hb : S.memBase + a < 2 ^ 64) {v' : Word}
    (hs : Ext.storeN m (BitVec.ofNat 64 (S.memBase + a)) k v' = some m') :
    ∀ x, ¬ S.InMem x → m'.bytes.get? x = m.bytes.get? x := by
  have wo := storeN_writesOnly' hb hs
  intro x hx
  apply wo.2
  simp only [Space.InMem] at hx
  have := h.1
  omega

theorem storeN_lin_some {S : Space} {n : Nat} (hv : S.Valid n) {lm : Lir.Memory} {m : Memory}
    (hreg : m.regions = S.regions n) (h : MemRel S lm m) {a k : Nat} (hin : a + k ≤ lm.size)
    (v : Word) : ∃ m', Ext.storeN m (BitVec.ofNat 64 (S.memBase + a)) k v = some m' := by
  have hb : S.memBase + a < 2 ^ 64 := by have := hv.mem_end; have := h.1; omega
  exact storeN_some hb v (permitted_mem hreg hv .write (by decide) (by omega)
    (by have := h.1; omega))

end Silmaril.X86.Backend
