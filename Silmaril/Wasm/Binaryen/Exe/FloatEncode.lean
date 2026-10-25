module

public import Silmaril.Wasm.Binaryen.Exe.EncodeBase

@[expose] public section

/-! # Scalar floating-point encodings

Constants are encoded from their raw bits, preserving signed zero and NaN payloads.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm

def encFloatType : FloatType → UInt8
  | .f32 => 0x7D
  | .f64 => 0x7C

def floatTypeBase (t : FloatType) (b32 b64 : Nat) : UInt8 :=
  match t with
  | .f32 => UInt8.ofNat b32
  | .f64 => UInt8.ofNat b64

/-- Exactly `n` bytes, least significant first. -/
def encLE : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, x => UInt8.ofNat x :: encLE n (x / 256)

def encFloatBits (t : FloatType) (b : BitVec t.width) : List UInt8 :=
  encLE (t.width / 8) b.toNat

def floatUnOff : FloatUnOp → Nat
  | .abs => 0 | .neg => 1 | .ceil => 2 | .floor => 3
  | .trunc => 4 | .nearest => 5 | .sqrt => 6

def floatBinOff : FloatBinOp → Nat
  | .add => 0 | .sub => 1 | .mul => 2 | .div => 3
  | .min => 4 | .max => 5 | .copysign => 6

def floatRelOff : FloatRelOp → Nat
  | .eq => 0 | .ne => 1 | .lt => 2 | .gt => 3 | .le => 4 | .ge => 5

def encConvert : ConvertOp → List UInt8
  | .wrap => [0xA7]
  | .extend .signed => [0xAC]
  | .extend .unsigned => [0xAD]
  | .trunc .f32 .i32 .signed => [0xA8]
  | .trunc .f32 .i32 .unsigned => [0xA9]
  | .trunc .f64 .i32 .signed => [0xAA]
  | .trunc .f64 .i32 .unsigned => [0xAB]
  | .trunc .f32 .i64 .signed => [0xAE]
  | .trunc .f32 .i64 .unsigned => [0xAF]
  | .trunc .f64 .i64 .signed => [0xB0]
  | .trunc .f64 .i64 .unsigned => [0xB1]
  | .convert .i32 .f32 .signed => [0xB2]
  | .convert .i32 .f32 .unsigned => [0xB3]
  | .convert .i64 .f32 .signed => [0xB4]
  | .convert .i64 .f32 .unsigned => [0xB5]
  | .demote => [0xB6]
  | .convert .i32 .f64 .signed => [0xB7]
  | .convert .i32 .f64 .unsigned => [0xB8]
  | .convert .i64 .f64 .signed => [0xB9]
  | .convert .i64 .f64 .unsigned => [0xBA]
  | .promote => [0xBB]
  | .reinterpretInt .f32 => [0xBC]
  | .reinterpretInt .f64 => [0xBD]
  | .reinterpretFloat .i32 => [0xBE]
  | .reinterpretFloat .i64 => [0xBF]
  | .truncSat .f32 .i32 .signed => [0xFC, 0]
  | .truncSat .f32 .i32 .unsigned => [0xFC, 1]
  | .truncSat .f64 .i32 .signed => [0xFC, 2]
  | .truncSat .f64 .i32 .unsigned => [0xFC, 3]
  | .truncSat .f32 .i64 .signed => [0xFC, 4]
  | .truncSat .f32 .i64 .unsigned => [0xFC, 5]
  | .truncSat .f64 .i64 .signed => [0xFC, 6]
  | .truncSat .f64 .i64 .unsigned => [0xFC, 7]

end Silmaril.Wasm.Binaryen.Exe
