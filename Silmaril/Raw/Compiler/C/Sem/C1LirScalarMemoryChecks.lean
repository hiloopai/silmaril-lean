module
public import Silmaril.Compiler.C.Sem.C1LirScalarMemory.Defs
@[expose] public section
namespace Silmaril.Compile.C.Sem.C1LirScalarMemory.Checks
open Silmaril.Machine Silmaril.Cerberus.Assertion.ConcreteResources C1LirMemory

/-- Eight arbitrary scalar bytes and one arbitrary neighboring byte. -/
def memory (bytes : Fin 9 → UInt8) : C1.Memory :=
  ⟨⟨Array.ofFn bytes⟩, ⟨Array.replicate 9 1⟩, C1.base, C1.base + 9⟩

private theorem owned_offset (source : C1.Memory) (index : Nat) (value : UInt8)
    (upper : C1.base + index + 1 ≤ source.sp) (writable : source.roTop ≤ C1.base + index)
    (bytesBound : index < source.bytes.size) (initBound : index < source.init.size)
    (initialized : source.init[index]! ≠ 0) (read : source.bytes[index]! = value) :
    OwnedByte source (C1.base + index) value := by
  refine ⟨by omega, upper, writable, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_sub_cancel_left] using bytesBound
  · simpa only [Nat.add_sub_cancel_left] using initBound
  · simpa only [Nat.add_sub_cancel_left] using initialized
  · simpa only [Nat.add_sub_cancel_left] using read

theorem cell (bytes : Fin 9 → UInt8) (index : Fin 9) :
    OwnedByte (memory bytes) (C1.base + index.val) (bytes index) := by
  apply owned_offset
  · have := index.isLt
    simp only [memory]
    omega
  · simp [memory]
  · simp [memory, ByteArray.size]
  · simp [memory, ByteArray.size]
  · change (ByteArray.mk (Array.replicate 9 1))[index.val]! ≠ 0
    rw [getElem!_pos _ _ (by simp [ByteArray.size])]
    change (Array.replicate 9 (1 : UInt8))[index.val] ≠ 0
    simp
  · change (ByteArray.mk (Array.ofFn bytes))[index.val]! = bytes index
    rw [getElem!_pos _ _ (by simp [ByteArray.size])]
    change (Array.ofFn bytes)[index.val] = bytes index
    simp

theorem scalar_owned (bytes : Fin 9 → UInt8) :
    OwnedBytes (memory bytes) C1.base (fun index => bytes ⟨index.val, by omega⟩) := by
  intro index
  exact cell bytes ⟨index.val, by omega⟩

/-- All 72 input bits are admissible, with actual source and target scalar
loads and a simultaneously owned initialized neighboring frame byte. -/
theorem all_bytes (bytes : Fin 9 → UInt8) :
    ∃ word : Lir.Word,
      C1.load (memory bytes) (.int 8 false) C1.base = .ok (word.toNat : Int) ∧
      (embed (memory bytes)).load .b8 .zero C1.base = some word ∧
      C1.load (memory bytes) (.int 1 false) (C1.base + 8) = .ok ((bytes 8).toNat : Int) ∧
      (embed (memory bytes)).load .b1 .zero (C1.base + 8) = some (C1LirMemory.word (bytes 8)) := by
  have scalar := load_owned (embed_related (memory bytes)) (scalar_owned bytes)
  have frame := (embed_related (memory bytes)).load_owned (cell bytes 8)
  exact ⟨_, scalar.1, scalar.2, frame.1, frame.2⟩

/-- Both flat models also admit an unaligned scalar, with an owned frame byte
immediately before the span. This is not an alignment theorem for upstream C. -/
theorem unaligned_all_bytes (bytes : Fin 9 → UInt8) :
    ∃ word : Lir.Word,
      C1.load (memory bytes) (.int 8 false) (C1.base + 1) = .ok (word.toNat : Int) ∧
      (embed (memory bytes)).load .b8 .zero (C1.base + 1) = some word ∧
      C1.load (memory bytes) (.int 1 false) C1.base = .ok ((bytes 0).toNat : Int) := by
  have owned : OwnedBytes (memory bytes) (C1.base + 1)
      (fun index => bytes ⟨index.val + 1, by omega⟩) := by
    intro index
    change OwnedByte (memory bytes) (C1.base + 1 + index.val) (bytes ⟨index.val + 1, _⟩)
    rw [show C1.base + 1 + index.val = C1.base + (index.val + 1) by omega]
    exact cell bytes ⟨index.val + 1, by omega⟩
  have scalar := load_owned (embed_related (memory bytes)) owned
  have frame := (embed_related (memory bytes)).load_owned (cell bytes 0)
  exact ⟨_, scalar.1, scalar.2, by simpa using frame.1⟩

/-- A high bit is decoded unsigned; reversing byte order changes the value. -/
theorem endian_controls :
    Lir.readLE (fun address => if address = 7 then 128 else 0) 0 8 = 0x8000000000000000 ∧
    Lir.readLE (fun address => if address = 0 then 128 else 0) 0 8 = 128 ∧
    Lir.readLE (fun _ => 255) 0 8 = 0xffffffffffffffff := by decide

def uninitialized : C1.Memory :=
  ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩, ⟨#[0, 1, 1, 1, 1, 1, 1, 1]⟩,
    C1.base, C1.base + 8⟩

/-- Equal target bytes cannot reconstruct source initialization evidence. -/
theorem initialization_not_recovered :
    C1.load uninitialized (.int 8 false) C1.base =
      .error (.undefined "a read of uninitialised memory") ∧
    (embed uninitialized).load .b8 .zero C1.base = some 0 := by
  constructor
  · have firstInit : (ByteArray.mk #[0, 1, 1, 1, 1, 1, 1, 1])[0]! = (0 : UInt8) := by decide
    simp [C1.load, C1.width, C1.Memory.readBytes, C1.Memory.valid, uninitialized, C0.ub,
      List.range', firstInit, Bind.bind, Except.bind]
  · rfl

/-- A scalar that extends past the available span is rejected by both models. -/
theorem short_span_rejected :
    C1.load uninitialized (.int 8 false) (C1.base + 1) =
      .error (.undefined "an access out of bounds") ∧
    (embed uninitialized).load .b8 .zero (C1.base + 1) = none := by
  constructor <;> rfl

end Silmaril.Compile.C.Sem.C1LirScalarMemory.Checks
