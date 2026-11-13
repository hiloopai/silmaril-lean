module

public import Silmaril.Machine.RiscV.Ext.Instr.Defs
public import Silmaril.Process.Memory
public import Silmaril.Machine.LittleEndian

/-!
# Little-endian data accesses for the extended RV64 model

`leBytes n v` are the low `n` bytes of `v`, least significant first; `leValue`
reads a byte list back as a natural number. Loads interpret `op.width` bytes
with `LoadOp.value` (sign- or zero-extension to 64 bits) and stores write
`leBytes op.width` of the source register. `LoadOp.value_leBytes` is the
store/load round trip at equal widths.

The `Process.Memory` lemmas here are about permission-checked spans: reading
back after a write, and reads that avoid a written interval. They are stated
for this model and are independent of any hardware memory representation.
-/

@[expose] public section

namespace Silmaril.RiscV.Ext

open Silmaril.Process (Memory Byte)

/-! ## Little-endian bytes -/

/-- The low `n` bytes of a register value, least significant first. -/
def leBytes : Nat → Word → List Byte
  | 0, _ => []
  | n + 1, v => v.setWidth 8 :: leBytes n (v >>> 8)

/-- The natural number denoted by little-endian bytes. -/
def leValue : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leValue bs

@[simp] theorem leBytes_length (n : Nat) (v : Word) : (leBytes n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [leBytes, ih]

theorem leValue_leBytes (n : Nat) (v : Word) : leValue (leBytes n v) = v.toNat % 2 ^ (8 * n) := by
  induction n generalizing v with
  | zero => simp [leBytes, leValue, Nat.mod_one]
  | succ n ih =>
    simp only [leBytes, leValue, ih, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
    rw [show 8 * (n + 1) = 8 + 8 * n by omega, Nat.pow_add, Nat.mod_mul]

theorem leValue_lt (bytes : List Byte) : leValue bytes < 2 ^ (8 * bytes.length) := by
  induction bytes with
  | nil => simp [leValue]
  | cons b bs ih =>
    simp only [leValue, List.length_cons]
    have hb := b.isLt
    rw [show 8 * (bs.length + 1) = 8 + 8 * bs.length by omega, Nat.pow_add]
    have : 256 * leValue bs + 256 ≤ 256 * 2 ^ (8 * bs.length) := by
      have := Nat.mul_le_mul_left 256 (Nat.succ_le_of_lt ih)
      simpa [Nat.mul_succ] using this
    simp only [Nat.reducePow] at hb ⊢
    omega

/-- Byte `index` of `leBytes` is the shared little-endian byte of the value. -/
theorem leBytes_getElem (n : Nat) (v : Word) (index : Nat) (bound : index < (leBytes n v).length) :
    (leBytes n v)[index] = Machine.LittleEndian.wordByte v index := by
  induction n generalizing v index with
  | zero => simp at bound
  | succ n ih =>
    cases index with
    | zero => simp [leBytes, Machine.LittleEndian.wordByte]
    | succ index =>
      simp only [leBytes, List.getElem_cons_succ]
      rw [ih (v >>> 8) index (by simpa [leBytes] using bound)]
      simp only [Machine.LittleEndian.wordByte, ← BitVec.shiftRight_add]
      congr 2
      omega

/-- Eight little-endian bytes are the shared serialization of one 64-bit word. -/
theorem leBytes_eight (v : Word) : leBytes 8 v = Machine.LittleEndian.encodeWords [v] := by
  apply List.ext_getElem
  · simp
  · intro index h1 h2
    rw [leBytes_getElem, Machine.LittleEndian.encodeWords_get]
    simp only [leBytes_length] at h1
    have hd : index / 8 = 0 := by omega
    have hm : index % 8 = index := by omega
    simp [hd, hm]

/-! ## Load results -/

/-- The loaded register value: `op.width` little-endian bytes, sign- or
zero-extended to 64 bits. -/
def LoadOp.value (op : LoadOp) (bytes : List Byte) : Word :=
  let raw : BitVec (8 * op.width) := BitVec.ofNat _ (leValue bytes)
  if op.signed then raw.signExtend 64 else raw.setWidth 64

private theorem ofNat_leValue_leBytes (n : Nat) (v : Word) :
    (BitVec.ofNat (8 * n) (leValue (leBytes n v)) : BitVec (8 * n)) = v.setWidth (8 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, leValue_leBytes, BitVec.toNat_setWidth, Nat.mod_mod]

/-- Loading the bytes of a same-width store gives the stored value truncated to
the access width and then extended. -/
theorem LoadOp.value_leBytes (op : LoadOp) (v : Word) :
    op.value (leBytes op.width v) =
      if op.signed then (v.setWidth (8 * op.width)).signExtend 64
      else (v.setWidth (8 * op.width)).setWidth 64 := by
  simp only [LoadOp.value, ofNat_leValue_leBytes]

@[simp] theorem ld_value_leBytes (v : Word) : LoadOp.ld.value (leBytes 8 v) = v := by
  have := LoadOp.value_leBytes .ld v
  simpa [LoadOp.signed, LoadOp.width] using this

@[simp] theorem lw_value_leBytes (v : Word) : LoadOp.lw.value (leBytes 4 v) = sext32 (low32 v) := by
  have := LoadOp.value_leBytes .lw v
  simpa [LoadOp.signed, LoadOp.width, sext32, low32] using this

@[simp] theorem lwu_value_leBytes (v : Word) :
    LoadOp.lwu.value (leBytes 4 v) = (low32 v).setWidth 64 := by
  have := LoadOp.value_leBytes .lwu v
  simpa [LoadOp.signed, LoadOp.width, low32] using this

@[simp] theorem lh_value_leBytes (v : Word) :
    LoadOp.lh.value (leBytes 2 v) = (v.setWidth 16).signExtend 64 := by
  have := LoadOp.value_leBytes .lh v
  simpa [LoadOp.signed, LoadOp.width] using this

@[simp] theorem lhu_value_leBytes (v : Word) :
    LoadOp.lhu.value (leBytes 2 v) = (v.setWidth 16).setWidth 64 := by
  have := LoadOp.value_leBytes .lhu v
  simpa [LoadOp.signed, LoadOp.width] using this

@[simp] theorem lb_value_leBytes (v : Word) :
    LoadOp.lb.value (leBytes 1 v) = (v.setWidth 8).signExtend 64 := by
  have := LoadOp.value_leBytes .lb v
  simpa [LoadOp.signed, LoadOp.width] using this

@[simp] theorem lbu_value_leBytes (v : Word) :
    LoadOp.lbu.value (leBytes 1 v) = (v.setWidth 8).setWidth 64 := by
  have := LoadOp.value_leBytes .lbu v
  simpa [LoadOp.signed, LoadOp.width] using this

theorem LoadOp.width_pos (op : LoadOp) : 0 < op.width := by cases op <;> decide
theorem StoreOp.width_pos (op : StoreOp) : 0 < op.width := by cases op <;> decide

/-! ## Checked spans of `Process.Memory` -/

namespace MemoryLemmas

/-- A checked access succeeds exactly when the span is permitted and backed. -/
theorem readWith_eq_some_iff {memory : Memory} {access : Process.Access} {address length : Nat}
    {bytes : List Byte} :
    memory.readWith access address length = some bytes ↔
      bytes.length = length ∧ memory.Permitted access address length ∧
        ∀ index (bound : index < bytes.length),
          memory.bytes.get? (address + index) = some (bytes[index]) := by
  constructor
  · intro h
    exact ⟨Memory.readWith_length h, Memory.readWith_permitted h,
      fun index bound => Memory.readWith_get h index bound⟩
  · rintro ⟨rfl, permitted, installed⟩
    exact Memory.readWith_eq memory access address bytes permitted installed

/-- A sub-span of a successful access succeeds with the corresponding bytes. -/
theorem readWith_slice {memory : Memory} {access : Process.Access} {address length : Nat}
    {bytes : List Byte} (h : memory.readWith access address length = some bytes)
    (offset count : Nat) (positive : 0 < count) (bound : offset + count ≤ length) :
    memory.readWith access (address + offset) count = some ((bytes.drop offset).take count) := by
  obtain ⟨hlen, permitted, installed⟩ := readWith_eq_some_iff.mp h
  rw [Memory.Permitted, Memory.checkSpan_iff] at permitted
  obtain ⟨start, limit, perm⟩ := permitted
  refine readWith_eq_some_iff.mpr ⟨by simp; omega, ?_, ?_⟩
  · rw [Memory.Permitted, Memory.checkSpan_iff]
    refine ⟨by omega, by omega, fun k hk => ?_⟩
    have := perm (offset + k) (by omega)
    rwa [Nat.add_assoc]
  · intro index hindex
    simp only [List.length_take, List.length_drop] at hindex
    have := installed (offset + index) (by omega)
    simp only [List.getElem_take, List.getElem_drop]
    rwa [Nat.add_assoc]

/-- Memory permissions depend only on the region list. -/
theorem checkSpan_congr {first second : Memory} (h : first.regions = second.regions)
    (access : Process.Access) (address length : Nat) :
    first.checkSpan access address length = second.checkSpan access address length := by
  simp [Memory.checkSpan, Memory.permits, h]

/-- A read whose span avoids a written interval is unaffected by the write. -/
theorem readWith_writesOnly {before after : Memory} {address length : Nat}
    (frame : Memory.WritesOnly before after address length)
    (access : Process.Access) (start count : Nat)
    (disjoint : start + count ≤ address ∨ address + length ≤ start) :
    after.readWith access start count = before.readWith access start count := by
  have backing : ∀ k, k ≤ count →
      Memory.readBacking after.bytes (start + (count - k)) k =
        Memory.readBacking before.bytes (start + (count - k)) k := by
    intro k
    induction k with
    | zero => intro; rfl
    | succ k ih =>
      intro hk
      have same := frame.2 (start + (count - (k + 1))) (by omega)
      have next : start + (count - (k + 1)) + 1 = start + (count - k) := by omega
      simp only [Memory.readBacking, Std.ExtHashMap.get?_eq_getElem?] at same ⊢
      rw [same, next, ih (by omega)]
  have := backing count le_rfl
  simp only [Nat.sub_self, Nat.add_zero] at this
  simp only [Memory.readWith, checkSpan_congr frame.1, this]

theorem writeBytes_eq_some_iff {memory : Memory} {address : Nat} {bytes : List Byte}
    {after : Memory} :
    memory.writeBytes address bytes = some after ↔
      memory.Permitted .write address bytes.length ∧
        after = { memory with bytes := Memory.install memory.bytes address bytes } := by
  unfold Memory.writeBytes Memory.Permitted
  split
  · rename_i h
    simp only [Option.some.injEq, h, true_and]
    exact eq_comm
  · rename_i h
    simp [h]

theorem writeBytes_eq_none_iff {memory : Memory} {address : Nat} {bytes : List Byte} :
    memory.writeBytes address bytes = none ↔ ¬ memory.Permitted .write address bytes.length := by
  unfold Memory.writeBytes Memory.Permitted
  split <;> simp_all

/-- After a write, the written bytes read back, provided the span is readable. -/
theorem readBytes_writeBytes {memory after : Memory} {address : Nat} {bytes : List Byte}
    (written : memory.writeBytes address bytes = some after)
    (readable : memory.Permitted .read address bytes.length) :
    after.readBytes address bytes.length = some bytes := by
  have frame := Memory.writeBytes_writesOnly written
  apply Memory.readWith_eq
  · simpa [Memory.Permitted, checkSpan_congr frame.1] using readable
  · exact fun index bound => Memory.writeBytes_get written index bound

/-- A write leaves reads of every disjoint span unchanged. -/
theorem readWith_writeBytes_disjoint {memory after : Memory} {address : Nat} {bytes : List Byte}
    (written : memory.writeBytes address bytes = some after) (access : Process.Access)
    (start count : Nat)
    (disjoint : start + count ≤ address ∨ address + bytes.length ≤ start) :
    after.readWith access start count = memory.readWith access start count :=
  readWith_writesOnly (Memory.writeBytes_writesOnly written) access start count disjoint

/-- A write never changes the mappings, so it preserves every permission check. -/
theorem writeBytes_regions {memory after : Memory} {address : Nat} {bytes : List Byte}
    (written : memory.writeBytes address bytes = some after) : after.regions = memory.regions :=
  (Memory.writeBytes_writesOnly written).1

end MemoryLemmas

end Silmaril.RiscV.Ext
