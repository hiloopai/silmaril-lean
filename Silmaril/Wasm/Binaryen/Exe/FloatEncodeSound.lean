module

public import Silmaril.Wasm.Binaryen.Exe.FloatEncode
public import Silmaril.Wasm.Binaryen.Exe.EncodeBaseSound
public import Silmaril.Wasm.Binary.Core.Instructions

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

theorem encLE_length (n x : Nat) : (encLE n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [encLE, ih]

theorem littleEndian_encLE (n x : Nat) (hx : x < 256 ^ n) :
    littleEndian (encLE n x) = x := by
  induction n generalizing x with
  | zero => simp at hx; subst x; rfl
  | succ n ih =>
    have hdiv : x / 256 < 256 ^ n := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa [Nat.pow_succ, Nat.mul_comm] using hx
    simp only [encLE, littleEndian, UInt8.toNat_ofNat', Nat.reducePow, ih _ hdiv]
    omega

theorem encFloatBits_sound (t : FloatType) (b : BitVec t.width) :
    FN t.width (encFloatBits t b) b := by
  have hx : b.toNat < 256 ^ (t.width / 8) := by
    cases t <;> exact b.isLt
  have hbits : BitVec.ofNat t.width (littleEndian (encFloatBits t b)) = b := by
    simp only [encFloatBits, littleEndian_encLE _ _ hx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simpa only [hbits] using (FN.mk (N := t.width) (encFloatBits t b) (encLE_length _ _))

theorem floatUnOpcode_sound (t : FloatType) (o : FloatUnOp) :
    PlainOp (floatTypeBase t (0x8B + floatUnOff o) (0x99 + floatUnOff o)) (.floatUnOp t o) := by
  cases t <;> cases o <;> constructor

theorem floatBinOpcode_sound (t : FloatType) (o : FloatBinOp) :
    PlainOp (floatTypeBase t (0x92 + floatBinOff o) (0xA0 + floatBinOff o)) (.floatBinOp t o) := by
  cases t <;> cases o <;> constructor

theorem floatRelOpcode_sound (t : FloatType) (o : FloatRelOp) :
    PlainOp (floatTypeBase t (0x5B + floatRelOff o) (0x61 + floatRelOff o)) (.floatRelOp t o) := by
  cases t <;> cases o <;> constructor

theorem encConvert_sound {F : Forms} (o : ConvertOp) : Core.Instr F (encConvert o) (.convert o) := by
  cases o with
  | wrap => exact .plain .rxA7
  | extend s => cases s <;> exact .plain (by constructor)
  | trunc src dst s => cases src <;> cases dst <;> cases s <;> exact .plain (by constructor)
  | convert src dst s => cases src <;> cases dst <;> cases s <;> exact .plain (by constructor)
  | demote => exact .plain .rxB6
  | promote => exact .plain .rxBB
  | reinterpretInt src => cases src <;> exact .plain (by constructor)
  | reinterpretFloat src => cases src <;> exact .plain (by constructor)
  | truncSat src dst s =>
    cases src <;> cases dst <;> cases s
    all_goals first
      | exact .prefixFC .r0 (.byte 0 (by decide) (by decide))
      | exact .prefixFC .r1 (.byte 1 (by decide) (by decide))
      | exact .prefixFC .r2 (.byte 2 (by decide) (by decide))
      | exact .prefixFC .r3 (.byte 3 (by decide) (by decide))
      | exact .prefixFC .r4 (.byte 4 (by decide) (by decide))
      | exact .prefixFC .r5 (.byte 5 (by decide) (by decide))
      | exact .prefixFC .r6 (.byte 6 (by decide) (by decide))
      | exact .prefixFC .r7 (.byte 7 (by decide) (by decide))

end Silmaril.Wasm.Binaryen.Exe
