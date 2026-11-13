module
public import Silmaril.Compiler.C.Sem.C1LirScalarMemory.Defs
/-! Actual finite C1 byte-array writes transfer to successful LIR byte-store
updates. The relation covers all backed bytes; separate frame theorems preserve
source data/initialization outside the updated physical offsets and all target
bytes outside the written addresses. Overwritten source cells need not already
be initialized. This foundation does not yet identify C1 scalar serialization
with one LIR b8 store, nor recover source access permissions from target memory. -/

@[expose] public section
namespace Silmaril.Compile.C.Sem.C1LirScalarStore
open Silmaril.Machine Silmaril.Cerberus.Assertion.ConcreteResources
open C1LirMemory C1LirScalarMemory

def writeOffset (source : C1.Memory) (offset : Nat) (value : UInt8) : C1.Memory :=
  ⟨source.bytes.set! offset value, source.init.set! offset 1, source.roTop, source.sp⟩

def writeOffsets (source : C1.Memory) (indices : List Nat) (offset : Nat → Nat) (value : Nat → UInt8) : C1.Memory :=
  indices.foldl (fun memory index => writeOffset memory (offset index) (value index)) source

private theorem write_loop (indices : List Nat) (offset : Nat → Nat) (value : Nat → UInt8) (source : C1.Memory) :
    (forIn indices (source.bytes, source.init) fun i acc =>
      pure (ForInStep.yield (acc.1.set! (offset i) (value i), acc.2.set! (offset i) 1))) =
      (Except.ok ((writeOffsets source indices offset value).bytes,
        (writeOffsets source indices offset value).init) : Except C0.Stop (ByteArray × ByteArray)) := by
  induction indices generalizing source with
  | nil => rfl
  | cons i rest ih =>
    simpa only [List.forIn_cons, pure, Except.pure, Bind.bind, Except.bind,
      writeOffsets, List.foldl_cons, writeOffset] using ih (writeOffset source (offset i) (value i))

private theorem writeOffsets_metadata (source : C1.Memory) (indices : List Nat)
    (offset : Nat → Nat) (value : Nat → UInt8) :
    (writeOffsets source indices offset value).roTop = source.roTop ∧
      (writeOffsets source indices offset value).sp = source.sp := by
  induction indices generalizing source with
  | nil => exact ⟨rfl, rfl⟩
  | cons i rest ih => exact ih (writeOffset source (offset i) (value i))

def written (source : C1.Memory) (address : Nat) (bytes : Array UInt8) : C1.Memory :=
  writeOffsets source (List.range bytes.size) (fun i => address - C1.base + i) (fun i => bytes[i]!)

private theorem array_get (bytes : Array UInt8) (i : Nat) (bound : i < bytes.size) :
    bytes[i] = bytes[i]! := (getElem!_pos bytes i bound).symm

theorem writeBytes_actual (source : C1.Memory) (address : Nat) (bytes : Array UInt8)
    (valid : source.valid address bytes.size = true) (writable : source.roTop ≤ address) :
    source.writeBytes address bytes = .ok (written source address bytes) := by
  have metadata := writeOffsets_metadata source (List.range bytes.size)
    (fun i => address - C1.base + i) (fun i => bytes[i]!)
  have loop := write_loop (List.range bytes.size) (fun i => address - C1.base + i)
    (fun i => bytes[i]!) source
  unfold C1.Memory.writeBytes
  simp only [valid, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Nat.not_lt.mpr writable, array_get]
  simp only [forIn'_eq_forIn, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    ← List.range_eq_range']
  rw [loop]
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  unfold written
  apply congrArg Except.ok
  rw [← metadata.1, ← metadata.2]

/-- A raw byte update preserves the whole-memory relation without requiring
initialization of the overwritten byte. Bounds are the only backing condition. -/
theorem writeOffset_related {source : C1.Memory} {target : Lir.Memory}
    (related : Rel source target) (offset : Nat) (value : UInt8)
    (bound : offset < source.bytes.size) :
    Rel (writeOffset source offset value) (stored target (C1.base + offset) value) := by
  constructor
  · simpa only [writeOffset, stored, ByteArray.size_set!] using related.fits
  · intro other inside
    change other < (source.bytes.set! offset value).size at inside
    rw [ByteArray.size_set!] at inside
    change (stored target (C1.base + offset) value).bytes (C1.base + other) =
      (source.bytes.set! offset value)[other]!.toBitVec
    rw [stored_byte, ByteArray.getElem!_set! _ _ _ _ bound]
    by_cases same : offset = other
    · subst other
      simp
    · have different : C1.base + other ≠ C1.base + offset := by omega
      rw [ite_eq_right different, ite_eq_right same]
      exact related.bytes other inside

/-- Each transferred byte update is a successful real target store. -/
theorem writeOffset_target_store {source : C1.Memory} {target : Lir.Memory}
    (related : Rel source target) (offset : Nat) (value : UInt8)
    (bound : offset < source.bytes.size) :
    target.store .b1 (C1.base + offset) (word value) =
      some (stored target (C1.base + offset) value) := by
  have inside : target.InBounds (C1.base + offset) .b1 := by
    have fits := related.fits
    change C1.base + offset + 1 ≤ target.size
    omega
  simp only [Lir.Memory.store, inside, ↓reduceIte, Lir.Width.bytes, stored]

/-- Updating a list of backed byte offsets transfers to the matching sequence
of target byte writes. This is independent of source initialization metadata. -/
theorem writeOffsets_related {source : C1.Memory} {target : Lir.Memory}
    (related : Rel source target) (indices : List Nat) (offset : Nat → Nat)
    (value : Nat → UInt8) (bounds : ∀ i ∈ indices, offset i < source.bytes.size) :
    Rel (writeOffsets source indices offset value)
      (indices.foldl (fun memory i => stored memory (C1.base + offset i) (value i)) target) := by
  induction indices generalizing source target with
  | nil => exact related
  | cons i rest ih =>
    simp only [writeOffsets, List.foldl_cons]
    apply ih (writeOffset_related related (offset i) (value i) (bounds i (by simp)))
    intro j member
    simpa only [writeOffset, ByteArray.size_set!] using bounds j (by simp [member])

/-- Target bytes outside the updated addresses are preserved, including bytes
outside the source backing. -/
theorem stores_frame (target : Lir.Memory) (indices : List Nat)
    (address : Nat → Nat) (value : Nat → UInt8) (other : Nat)
    (outside : ∀ i ∈ indices, other ≠ address i) :
    (indices.foldl (fun memory i => stored memory (address i) (value i)) target).bytes other =
      target.bytes other := by
  induction indices generalizing target with
  | nil => rfl
  | cons i rest ih =>
    rw [List.foldl_cons, ih]
    · rw [stored_byte, ite_eq_right (outside i (by simp))]
    · intro j member
      exact outside j (by simp [member])

/-- Raw byte and initialization frames, with the physical array index explicit. -/
theorem writeOffsets_raw_frame (source : C1.Memory) (indices : List Nat)
    (offset : Nat → Nat) (value : Nat → UInt8) (other : Nat)
    (outside : ∀ i ∈ indices, offset i ≠ other) :
    (writeOffsets source indices offset value).bytes[other]! = source.bytes[other]! ∧
      (writeOffsets source indices offset value).init[other]! = source.init[other]! := by
  induction indices generalizing source with
  | nil => exact ⟨rfl, rfl⟩
  | cons i rest ih =>
    have next := ih (writeOffset source (offset i) (value i)) (by
      intro j member
      exact outside j (by simp [member]))
    have different := outside i (by simp)
    constructor
    · exact next.1.trans (ByteArray.getElem!_set!_ne _ _ _ _ different)
    · exact next.2.trans (ByteArray.getElem!_set!_ne _ _ _ _ different)

/-- Actual finite source writes transfer to target byte writes and preserve the
full memory relation. No successful-store premise is assumed. -/
theorem writeBytes_related {source : C1.Memory} {target : Lir.Memory}
    (related : Rel source target) (address : Nat) (bytes : Array UInt8)
    (valid : source.valid address bytes.size = true) (writable : source.roTop ≤ address)
    (backed : address - C1.base + bytes.size ≤ source.bytes.size) :
    source.writeBytes address bytes = .ok (written source address bytes) ∧
      Rel (written source address bytes)
        ((List.range bytes.size).foldl
          (fun memory i => stored memory (C1.base + (address - C1.base + i)) bytes[i]!) target) := by
  refine ⟨writeBytes_actual source address bytes valid writable, ?_⟩
  apply writeOffsets_related related
  intro i member
  have bound := List.mem_range.mp member
  omega


end Silmaril.Compile.C.Sem.C1LirScalarStore
