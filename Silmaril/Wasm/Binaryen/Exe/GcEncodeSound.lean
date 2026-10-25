module

public import Silmaril.Wasm.Binaryen.Exe.GcEncode
public import Silmaril.Wasm.Binaryen.Exe.EncodeBaseSound
public import Silmaril.Wasm.Binary.Core.Instructions

@[expose] public section

/-! # Soundness of the reference and GC type encodings

Against the specification's grammar (`Forms.all`, which enables the prefixed reference
forms). -/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

theorem encAbsHeapType_sound (ht : Wasm.AbsHeapType) : Core.AbsHeapType [encAbsHeapType ht] ht := by
  cases ht <;> constructor

/-- A type index as a non-negative `s33`. -/
theorem encS_typeIdx_sound (x : TypeIdx) : S33 (encS x.toNat) x.toNat := by
  have hx := x.value.isLt
  have hx' : x.toNat = x.value.val := rfl
  exact encS_sound (N := 33) (by simp only [Nat.reduceSub, Int.reducePow]; omega)
    (by simp only [Nat.reduceSub, Int.reducePow, Nat.reducePow] at hx ⊢; omega) (by decide)

theorem encHeapType_sound (ht : Wasm.HeapType) : Core.HeapType (encHeapType ht) ht := by
  cases ht with
  | abstract ht => exact .abs (encAbsHeapType_sound ht)
  | typeIdx x => exact .idx x (encS_typeIdx_sound x)

theorem encRefType_sound (r : Wasm.RefType) : Core.RefType Forms.all (encRefType r) r := by
  rcases r with ⟨_ | _, ht⟩
  · exact .nonNull rfl (encHeapType_sound ht)
  · cases ht with
    | abstract ht => exact .abs (encAbsHeapType_sound ht)
    | typeIdx x => exact .null rfl (.idx x (encS_typeIdx_sound x))

theorem encCastOp_sound (n₁ n₂ : Bool) : Core.CastOp [encCastOp n₁ n₂] (n₁, n₂) := by
  cases n₁ <;> cases n₂ <;> constructor

theorem encPackType_sound (p : Wasm.PackType) : Core.PackType [encPackType p] p := by
  cases p <;> constructor

/-- A small `u32` opcode immediate is its own single byte. -/
theorem u32_byte (n : Nat) (h : n < 128 := by decide) : U32 [UInt8.ofNat n] n := by
  have e : (UInt8.ofNat n).toNat = n := by
    rw [UInt8.toNat_ofNat']; omega
  have := UN.byte (N := 32) (UInt8.ofNat n) (by rw [e]; omega) (by rw [e]; omega)
  rwa [e] at this

end Silmaril.Wasm.Binaryen.Exe
