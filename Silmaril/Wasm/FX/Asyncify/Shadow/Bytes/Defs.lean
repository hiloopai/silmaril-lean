module

public import Silmaril.Wasm.FX.Asyncify.Shadow.Defs

/-!
# The shadow stack in a bounded byte memory

The shadow-stack strategy (`Silmaril.Wasm.FX.Asyncify.Shadow.mstep`) keeps its saved frames as a
list of abstract cells. This module lays the cells out in a **byte memory** with addresses and
widths, as a Core 3.0 linear memory would hold them, and bounds it.

* **Values** are encoded by a codec (`Codec V`): a fixed width `w` and a decoder that inverts the
  encoder (for Core `i32` values, four little-endian bytes).
* **Cells** (`cellBytes`): a number is an `i32`, four little-endian bytes (`le32`; numbers from
  `2 ^ 32` on have no layout); a stored value is a slot of `sw = 1 + max w 4` bytes: a tag byte
  (`0` a value, `1` a continuation handle), then the value or the handle (an `i32`), padded.
* **The memory** (`layout`): the cells one after the other from address `0`; `addrOf cs` is the
  byte address where cells `cs` end (`4` per number, `sw` per value).
* **Reading a record backwards** (`readRec bs e`): at end address `e`, the trailer is the three
  words before `e` (function, resume index, operand count `n`), and the operands are the `n`
  slots before the trailer. This is how a rewinding Core 3.0 function pops its data
  (`i32.load` at `sp - 4`, …).
* **The bound** (`fitsB C cap x`): the memory of `x` has a layout of at most `cap` bytes.
  **`bmstep C cap`** is `mstep` that traps when a step would leave a memory that does not fit
  (an overflow, or a number past `2 ^ 32`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Shadow

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.Models.FXAsyncPC

/-- A fixed-width byte codec of values. -/
structure Codec (V : Type) where
  w : Nat
  enc : V → List UInt8
  dec : List UInt8 → Option V
  enc_len : ∀ v, (enc v).length = w
  dec_enc : ∀ v, dec (enc v) = some v

/-- Four little-endian bytes. -/
def le32 (n : Nat) : List UInt8 := [UInt8.ofNat n, UInt8.ofNat (n / 256),
  UInt8.ofNat (n / 65536), UInt8.ofNat (n / 16777216)]

/-- The number of four little-endian bytes (`0` for another length). -/
def unle32 : List UInt8 → Nat
  | [a, b, c, d] => a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat
  | _ => 0

/-- `l` padded with zeros to `k` bytes. -/
def pad (k : Nat) (l : List UInt8) : List UInt8 := l ++ List.replicate (k - l.length) 0

variable {V : Type}

/-- The width of a value slot: a tag byte and the wider of a value and an `i32`. -/
def Codec.sw (C : Codec V) : Nat := 1 + max C.w 4

/-- The bytes of a cell (`none` for a number or handle from `2 ^ 32` on). -/
def cellBytes (C : Codec V) : Cell V → Option (List UInt8)
  | .num n => if n < 2 ^ 32 then some (le32 n) else none
  | .sv (.val v) => some (0 :: pad (max C.w 4) (C.enc v))
  | .sv (.cont k) => if k < 2 ^ 32 then some (1 :: pad (max C.w 4) (le32 k)) else none

/-- The width of a cell in bytes. -/
def cellWidth (C : Codec V) : Cell V → Nat
  | .num _ => 4
  | .sv _ => C.sw

/-- **The byte layout** of a list of cells, from address `0`. -/
def layout (C : Codec V) : List (Cell V) → Option (List UInt8)
  | [] => some []
  | c :: cs =>
    match cellBytes C c, layout C cs with
    | some b, some r => some (b ++ r)
    | _, _ => none

/-- The byte address where the cells `cs` end. -/
def addrOf (C : Codec V) (cs : List (Cell V)) : Nat := (cs.map (cellWidth C)).sum

/-- The `i32` at byte address `a`. -/
def rd32 (bs : List UInt8) (a : Nat) : Nat := unle32 ((bs.drop a).take 4)

/-- The stored value in the slot at byte address `a`. -/
def rdSV (C : Codec V) (bs : List UInt8) (a : Nat) : Option (SV V) :=
  match bs[a]? with
  | some 0 => (C.dec ((bs.drop (a + 1)).take C.w)).map .val
  | some 1 => some (.cont (rd32 bs (a + 1)))
  | _ => none

/-- `n` stored values from byte address `a` up. -/
def rdVals (C : Codec V) (bs : List UInt8) : Nat → Nat → Option (List (SV V))
  | _, 0 => some []
  | a, n + 1 =>
    match rdSV C bs a, rdVals C bs (a + C.sw) n with
    | some x, some r => some (x :: r)
    | _, _ => none

/-- **Read the record that ends at byte address `e`**: the trailer (function, resume index,
operand count `n`) in the three words before `e`, the operands in the `n` slots before it.
Returns the record and its start address. -/
def readRec (C : Codec V) (bs : List UInt8) (e : Nat) : Option (Rec V × Nat) :=
  let n := rd32 bs (e - 4)
  if 12 + C.sw * n ≤ e then
    (rdVals C bs (e - 12 - C.sw * n) n).map fun ops =>
      (⟨rd32 bs (e - 12), rd32 bs (e - 8), ops⟩, e - 12 - C.sw * n)
  else none

/-- The memory of `x` has a layout of at most `cap` bytes. -/
def fitsB (C : Codec V) (cap : Nat) (x : MCfg V) : Bool :=
  match layout C x.mem with
  | some bs => decide (bs.length ≤ cap)
  | none => false

/-- **The bounded shadow-stack step**: `mstep`, trapping when the memory after the step does not
fit in `cap` bytes. -/
def bmstep (C : Codec V) (cap : Nat) (P : Prog (AIns V)) (B : Nat → Option (List (TIns V)))
    (test : V → Bool) (x : MCfg V) : Res (MCfg V) V :=
  match mstep P B test x with
  | .next y => if fitsB C cap y then .next y else .stop .trap
  | .stop o => .stop o

/-- Every configuration reachable from `x` fits. -/
def AllFit (C : Codec V) (cap : Nat) (P : Prog (AIns V)) (B : Nat → Option (List (TIns V)))
    (test : V → Bool) (x : MCfg V) : Prop :=
  ∀ n y, runN (mstep P B test) n x = .next y → fitsB C cap y = true

theorem unle32_le32 {n : Nat} (h : n < 2 ^ 32) : unle32 (le32 n) = n := by
  simp only [le32, unle32, UInt8.toNat_ofNat']
  omega

/-- The `i32` codec: four little-endian bytes of a 32-bit word. -/
def i32Codec : Codec (BitVec 32) where
  w := 4
  enc v := le32 v.toNat
  dec l := if l.length = 4 then some (BitVec.ofNat 32 (unle32 l)) else none
  enc_len _ := rfl
  dec_enc v := by
    have hv := v.isLt
    have hl : (le32 v.toNat).length = 4 := rfl
    simp only [hl, ↓reduceIte, unle32_le32 hv, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end Silmaril.Wasm.FX.Asyncify.Shadow
