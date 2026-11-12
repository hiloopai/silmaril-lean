module
public import Silmaril.Compiler.C.Sem.C1LirScalarStore.Defs
public import Silmaril.Compiler.Mir.LoadForwardMemory.Defs
/-! The actual C1 unsigned64 serializer and store correspond to one actual LIR
b8 store. Both primitives succeed from initialized byte ownership; the updated
whole-memory relation, initialized ownership of the serialized bytes, actual
full-word readback, and arbitrary outside-span data/initialization frames are proved. This flat-memory result does not model pointer provenance. -/

@[expose] public section
namespace Silmaril.Compile.C.Sem.C1LirScalarEncoding
open Silmaril.Machine

private theorem wrap_word (word : Lir.Word) :
    C1.wrap 8 false (word.toNat : Int) = word.toNat := by
  have bound := word.isLt
  have range : C1.inRange 8 false (word.toNat : Int) = true := by
    simp [C1.inRange, C1.lo, C1.hi]
    omega
  unfold C1.wrap
  rw [range]
  rfl

/-- The actual C1 scalar serializer exposes exactly eight low-to-high bytes. -/
theorem serialize_word (word : Lir.Word) :
    C1.Memory.le 8 (word.toNat : Int) =
      Array.ofFn (fun i : Fin 8 => (word.toNat / 256 ^ i.val % 256).toUInt8) := by
  simp [C1.Memory.le, wrap_word, List.range'_succ]
  apply Array.ext
  · simp
  · intro i left right
    have bound : i < 8 := by simpa using right
    interval_cases i <;> simp_all [Nat.div_div_eq_div_mul]

/-- The serializer bytes are the actual LIR little-endian word bytes. -/
theorem serialized_byte (word : Lir.Word) (index : Nat) :
    ((word.toNat / 256 ^ index % 256).toUInt8).toBitVec =
      LittleEndian.wordByte word index := by
  apply BitVec.eq_of_toNat_eq
  simp [LittleEndian.wordByte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, pow_mul]

open C1LirMemory C1LirScalarStore

def encoded (word : Lir.Word) (index : Nat) : UInt8 :=
  (word.toNat / 256 ^ index % 256).toUInt8

def storeWordBytes (target : Lir.Memory) (address count : Nat) (word : Lir.Word) : Lir.Memory :=
  (List.range count).foldl (fun memory i => stored memory (address + i) (encoded word i)) target

/-- A sequence of byte writes is exactly the target's little-endian span update. -/
theorem storeWordBytes_at (target : Lir.Memory) (address count : Nat) (word : Lir.Word) (other : Nat) :
    (storeWordBytes target address count word).bytes other =
      Lir.writeLE target.bytes address count word other := by
  induction count with
  | zero => simp [storeWordBytes, Lir.writeLE]
  | succ count ih =>
    simp only [storeWordBytes, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [stored_byte]
    change (if other = address + count then (encoded word count).toBitVec else
      (storeWordBytes target address count word).bytes other) = _
    rw [ih]
    by_cases same : other = address + count
    · subst other
      rw [ite_eq_left rfl]
      simp only [encoded, serialized_byte, Lir.writeLE]
      rw [ite_eq_left (by omega)]
      congr 1
      omega
    · rw [ite_eq_right same]
      unfold Lir.writeLE
      by_cases inside : address ≤ other ∧ other < address + count
      · rw [ite_eq_left inside, ite_eq_left (by omega)]
      · rw [ite_eq_right inside, ite_eq_right (by omega)]

theorem storeWordBytes_size (target : Lir.Memory) (address count : Nat) (word : Lir.Word) :
    (storeWordBytes target address count word).size = target.size := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simpa only [storeWordBytes, List.range_succ, List.foldl_append,
      List.foldl_cons, List.foldl_nil, stored] using ih

private theorem memory_eq {left right : Lir.Memory} (size : left.size = right.size)
    (bytes : left.bytes = right.bytes) : left = right := by
  cases left
  cases right
  cases size
  cases bytes
  rfl

theorem storeWordBytes_eq (target : Lir.Memory) (address count : Nat) (word : Lir.Word) :
    storeWordBytes target address count word =
      ⟨target.size, Lir.writeLE target.bytes address count word⟩ := by
  have size := storeWordBytes_size target address count word
  have bytes : (storeWordBytes target address count word).bytes =
      Lir.writeLE target.bytes address count word := funext (storeWordBytes_at target address count word)
  exact memory_eq size bytes

private theorem fold_agrees {α β : Type} (indices : List α) (left right : β → α → β)
    (agree : ∀ i ∈ indices, ∀ acc, left acc i = right acc i) (initial : β) :
    indices.foldl left initial = indices.foldl right initial := by
  induction indices generalizing initial with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [agree i (by simp) initial]
    apply ih
    intro j member
    exact agree j (by simp [member])

theorem serialized_stores (target : Lir.Memory) (address : Nat) (word : Lir.Word)
    (lower : C1.base ≤ address) :
    (List.range (C1.Memory.le 8 (word.toNat : Int)).size).foldl
      (fun memory i => stored memory (C1.base + (address - C1.base + i))
        (C1.Memory.le 8 (word.toNat : Int))[i]!) target =
      ⟨target.size, Lir.writeLE target.bytes address 8 word⟩ := by
  rw [serialize_word]
  simp only [Array.size_ofFn]
  rw [← storeWordBytes_eq target address 8 word]
  apply fold_agrees
  intro i member acc
  have bound : i < 8 := List.mem_range.mp member
  have address_eq : C1.base + (address - C1.base + i) = address + i := by omega
  simp [address_eq, getElem!_pos, bound, encoded]

/-- Owned initialized scalar bytes justify both actual unsigned64 stores and
preserve the whole source/target memory relation after one target b8 store. -/
theorem store_owned {source : C1.Memory} {target : Lir.Memory}
    (related : Rel source target) {address : Nat} {old : Fin 8 → UInt8}
    (owned : C1LirScalarMemory.OwnedBytes source address old) (word : Lir.Word) :
    C1.store source (.int 8 false) address (word.toNat : Int) =
        .ok (written source address (C1.Memory.le 8 (word.toNat : Int))) ∧
      target.store .b8 address word =
        some ⟨target.size, Lir.writeLE target.bytes address 8 word⟩ ∧
      Rel (written source address (C1.Memory.le 8 (word.toNat : Int)))
        ⟨target.size, Lir.writeLE target.bytes address 8 word⟩ := by
  have lower : C1.base ≤ address := (owned 0).lower
  have upper : address + 8 ≤ source.sp := (owned 7).upper
  have writable : source.roTop ≤ address := (owned 0).writable
  have backing := (owned 7).bytes_bound
  change address + 7 - C1.base < source.bytes.size at backing
  have size : (C1.Memory.le 8 (word.toNat : Int)).size = 8 := by
    rw [serialize_word]
    exact Array.size_ofFn
  have valid : source.valid address (C1.Memory.le 8 (word.toNat : Int)).size = true := by
    simp only [C1.Memory.valid, size, decide_eq_true lower, decide_eq_true upper, Bool.and_self]
  have backed : address - C1.base + (C1.Memory.le 8 (word.toNat : Int)).size ≤ source.bytes.size := by
    rw [size]
    omega
  have writes := writeBytes_related related address (C1.Memory.le 8 (word.toNat : Int)) valid writable backed
  have fits := related.fits
  have inside : target.InBounds address .b8 := by
    change address + 8 ≤ target.size
    omega
  refine ⟨?_, ?_, ?_⟩
  · simpa only [C1.store, C1.width] using writes.1
  · simp only [Lir.Memory.store, inside, ↓reduceIte, Lir.Width.bytes]
  · rw [serialized_stores target address word lower] at writes
    exact writes.2

/-- A scalar store preserves every target byte outside its eight-byte span. -/
theorem store_target_frame (target : Lir.Memory) (address other : Nat) (word : Lir.Word)
    (outside : other < address ∨ address + 8 ≤ other) :
    Lir.writeLE target.bytes address 8 word other = target.bytes other := by
  unfold Lir.writeLE
  rw [ite_eq_right (by omega)]

/-- Source data and initialization outside a scalar store are both preserved. -/
theorem store_source_frame (source : C1.Memory) (address offset : Nat) (word : Lir.Word)
    (lower : C1.base ≤ address)
    (outside : C1.base + offset < address ∨ address + 8 ≤ C1.base + offset) :
    (written source address (C1.Memory.le 8 (word.toNat : Int))).bytes[offset]! =
        source.bytes[offset]! ∧
      (written source address (C1.Memory.le 8 (word.toNat : Int))).init[offset]! =
        source.init[offset]! := by
  apply writeOffsets_raw_frame
  intro i member
  have bound := List.mem_range.mp member
  have size : (C1.Memory.le 8 (word.toNat : Int)).size = 8 := by
    rw [serialize_word]
    exact Array.size_ofFn
  rw [size] at bound
  omega

/-- All source metadata and array bounds survive the finite write sequence. -/
theorem writeOffsets_shape (source : C1.Memory) (indices : List Nat)
    (offset : Nat → Nat) (value : Nat → UInt8) :
    (writeOffsets source indices offset value).bytes.size = source.bytes.size ∧
    (writeOffsets source indices offset value).init.size = source.init.size ∧
    (writeOffsets source indices offset value).roTop = source.roTop ∧
    (writeOffsets source indices offset value).sp = source.sp := by
  induction indices generalizing source with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons i rest ih =>
    simpa only [writeOffsets, List.foldl_cons, writeOffset, ByteArray.size_set!]
      using ih (writeOffset source (offset i) (value i))

private theorem writeOffsets_range_at (source : C1.Memory) (start count : Nat)
    (value : Nat → UInt8) (index : Nat) (inside : index < count)
    (bytesBound : start + count ≤ source.bytes.size) (initBound : start + count ≤ source.init.size) :
    (writeOffsets source (List.range count) (fun i => start + i) value).bytes[start + index]! = value index ∧
    (writeOffsets source (List.range count) (fun i => start + i) value).init[start + index]! = 1 := by
  induction count with
  | zero => omega
  | succ count ih =>
    simp only [writeOffsets, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    let prior := writeOffsets source (List.range count) (fun i => start + i) value
    change (writeOffset prior (start + count) (value count)).bytes[start + index]! = value index ∧
      (writeOffset prior (start + count) (value count)).init[start + index]! = 1
    have shape := writeOffsets_shape source (List.range count) (fun i => start + i) value
    by_cases last : index = count
    · subst index
      have b : start + count < prior.bytes.size := by dsimp only [prior]; rw [shape.1]; omega
      have z : start + count < prior.init.size := by dsimp only [prior]; rw [shape.2.1]; omega
      constructor
      · exact by simp only [writeOffset, ByteArray.getElem!_set! _ _ _ _ b, ↓reduceIte]
      · exact by simp only [writeOffset, ByteArray.getElem!_set! _ _ _ _ z, ↓reduceIte]
    · have previous := ih (by omega) (by omega) (by omega)
      have different : start + count ≠ start + index := by omega
      constructor
      · exact (ByteArray.getElem!_set!_ne _ _ _ _ different).trans previous.1
      · exact (ByteArray.getElem!_set!_ne _ _ _ _ different).trans previous.2

private theorem owned_offset (source : C1.Memory) (index : Nat) (value : UInt8)
    (upper : C1.base + index + 1 ≤ source.sp) (writable : source.roTop ≤ C1.base + index)
    (bytesBound : index < source.bytes.size) (initBound : index < source.init.size)
    (initialized : source.init[index]! ≠ 0) (read : source.bytes[index]! = value) :
    Silmaril.Cerberus.Assertion.ConcreteResources.OwnedByte source (C1.base + index) value := by
  refine ⟨by omega, upper, writable, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_sub_cancel_left] using bytesBound
  · simpa only [Nat.add_sub_cancel_left] using initBound
  · simpa only [Nat.add_sub_cancel_left] using initialized
  · simpa only [Nat.add_sub_cancel_left] using read

/-- Actual scalar writes establish initialized ownership of every serialized byte. -/
theorem store_owned_bytes {source : C1.Memory} {address : Nat} {old : Fin 8 → UInt8}
    (owned : C1LirScalarMemory.OwnedBytes source address old) (word : Lir.Word) :
    C1LirScalarMemory.OwnedBytes
      (written source address (C1.Memory.le 8 (word.toNat : Int))) address
      (fun i => encoded word i.val) := by
  rw [serialize_word]
  change C1LirScalarMemory.OwnedBytes
    (writeOffsets source (List.range 8) (fun j => address - C1.base + j)
      (fun j => (Array.ofFn (fun k : Fin 8 => encoded word k.val))[j]!)) address
    (fun i => encoded word i.val)
  intro i
  have lower : C1.base ≤ address := (owned 0).lower
  have endBytes := (owned 7).bytes_bound
  have endInit := (owned 7).init_bound
  change address + 7 - C1.base < source.bytes.size at endBytes
  change address + 7 - C1.base < source.init.size at endInit
  have reads := writeOffsets_range_at source (address - C1.base) 8
    (fun j => (Array.ofFn (fun k : Fin 8 => encoded word k.val))[j]!) i.val i.isLt
    (by omega) (by omega)
  have shape := writeOffsets_shape source (List.range 8) (fun j => address - C1.base + j)
    (fun j => (Array.ofFn (fun k : Fin 8 => encoded word k.val))[j]!)
  have eqAddress : C1.base + (address - C1.base + i.val) = address + i.val := by omega
  rw [← eqAddress]
  apply owned_offset
  · rw [shape.2.2.2]
    have upper := (owned i).upper
    omega
  · rw [shape.2.2.1]
    have writable := (owned i).writable
    omega
  · rw [shape.1]
    have bound := i.isLt
    omega
  · rw [shape.2.1]
    have bound := i.isLt
    omega
  · rw [reads.2]
    decide
  · rw [reads.1]
    simp [getElem!_pos, i.isLt]

/-- A write followed by actual source and target loads reads the full stored word. -/
theorem store_readback {source : C1.Memory} {target : Lir.Memory}
    (related : Rel source target) {address : Nat} {old : Fin 8 → UInt8}
    (owned : C1LirScalarMemory.OwnedBytes source address old) (word : Lir.Word) :
    C1.load (written source address (C1.Memory.le 8 (word.toNat : Int)))
        (.int 8 false) address = .ok (word.toNat : Int) ∧
      (Lir.Memory.mk target.size (Lir.writeLE target.bytes address 8 word)).load
        .b8 .zero address = some word := by
  have post := (store_owned related owned word).2.2
  have loads := C1LirScalarMemory.load_owned post (store_owned_bytes owned word)
  simpa only [Silmaril.Compile.Mir.LoadForward.readLE_writeLE8] using loads

/-- Arbitrary serialized writes preserve both backing sizes and stack metadata. -/
theorem written_shape (source : C1.Memory) (address : Nat) (bytes : Array UInt8) :
    (written source address bytes).bytes.size = source.bytes.size ∧
    (written source address bytes).init.size = source.init.size ∧
    (written source address bytes).roTop = source.roTop ∧
    (written source address bytes).sp = source.sp :=
  writeOffsets_shape source (List.range bytes.size) (fun i => address - C1.base + i)
    (fun i => bytes[i]!)

end Silmaril.Compile.C.Sem.C1LirScalarEncoding
