module

public import Silmaril.Wasm.Modules

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm

/-- Unsigned LEB128, minimal. -/
def encU (n : Nat) : List UInt8 :=
  if h : n < 0x80 then [UInt8.ofNat n]
  else UInt8.ofNat (n % 0x80 + 0x80) :: encU (n / 0x80)
termination_by n
decreasing_by omega

/-- Signed LEB128, minimal. -/
def encS (i : Int) : List UInt8 :=
  if h : -64 ≤ i ∧ i < 64 then [UInt8.ofNat (i % 128).toNat]
  else UInt8.ofNat (i % 128 + 128).toNat :: encS (i / 128)
termination_by i.natAbs
decreasing_by omega

/-- A `u32`: unsigned LEB128, failing on values that do not fit. -/
def encU32 (n : Nat) : Except String (List UInt8) :=
  if n < 2 ^ 32 then pure (encU n) else throw s!"encoder: {n} does not fit in u32"

/-- An index (always below `2^32`). -/
def encIdx {k : IndexKind} (x : Idx k) : List UInt8 := encU x.toNat

/-- The concatenated encodings of a list's elements. -/
def encList {α : Type} (f : α → Except String (List UInt8)) :
    List α → Except String (List UInt8)
  | [] => pure []
  | x :: xs => do pure ((← f x) ++ (← encList f xs))

/-- A vector: its length, then its elements. -/
def encVec {α : Type} (f : α → Except String (List UInt8)) (xs : List α) :
    Except String (List UInt8) := do
  pure ((← encU32 xs.length) ++ (← encList f xs))

/-- A section with id `n`; a section with no entries is omitted. -/
def encSection (n : UInt8) (count : Nat) (body : List UInt8) : Except String (List UInt8) :=
  if count = 0 then pure [] else do pure ([n] ++ (← encU32 body.length) ++ body)

/-- A name: its UTF-8 bytes as a byte vector. -/
def encName (s : String) : Except String (List UInt8) := do
  pure ((← encU32 s.toUTF8.data.toList.length) ++ s.toUTF8.data.toList)

end Silmaril.Wasm.Binaryen.Exe
