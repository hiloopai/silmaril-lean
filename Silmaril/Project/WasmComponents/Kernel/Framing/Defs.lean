module

public import Silmaril.Wasm.Wit.Binary.Embed.Defs

/-!
# Kernel decoders: the section framing of a core module on its byte list

`Wit.Binary.coreSections` and the `name` parser read a `ByteArray` by position: every `bs[i]`
and `bs.size` walks the array's list from its start, and on a 51 KB adapter module the kernel
needs about half a minute for the framing alone and times out on the custom section names.
These are the same computations on the list itself, walked once from the front:

* `uAuxL`: unsigned LEB128 (`Parse.ByteParse.uAux`) on a list, returning the value and the rest;
* `framesL`: `coreSectionsFrom` (the sections' ids and content spans) on the rest of the list;
* `nameL`: the `name` parser on a window.

The fast forms `coreSectionsFast` and `nameFast` use them and fall back to the originals when
they fail, so they are equal to the originals everywhere
(`Silmaril.Project.WasmComponents.Kernel.Framing.Thms`: only the successful runs need a proof).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

open Silmaril.Parse.ByteParse (Parser Res)
open Silmaril.Wasm.Wit.Binary

/-- The bytes `i` to `j` of `b` as a list slice, wrapped in the constructors (no pushes). -/
def sliceOf (b : ByteArray) (i j : Nat) : ByteArray := ⟨⟨(b.data.toList.drop i).take (j - i)⟩⟩

/-- Unsigned LEB128 with `budget` bits left on a list: the value and the rest of the list. -/
def uAuxL (budget shift acc : Nat) : List UInt8 → Option (Nat × List UInt8)
  | x :: r =>
    if x.toNat < 128 then
      if x.toNat < 2 ^ budget then some (acc + 2 ^ shift * x.toNat, r) else none
    else if 7 < budget then uAuxL (budget - 7) (shift + 7) (acc + 2 ^ shift * (x.toNat - 128)) r
    else none
  | [] => none

/-- `coreSectionsFrom` on `rest`, the list from position `i` on. -/
def framesL : Nat → Nat → List UInt8 → Option (List (UInt8 × Nat × Nat))
  | 0, _, _ => none
  | _ + 1, _, [] => some []
  | fuel + 1, i, x :: r =>
    match uAuxL 32 0 0 r with
    | some (n, r') =>
      if n ≤ r'.length then
        ((x, i + 1 + (r.length - r'.length), i + 1 + (r.length - r'.length) + n) :: ·) <$>
          framesL fuel (i + 1 + (r.length - r'.length) + n) (r'.drop n)
      else none
    | none => none

/-- `coreSections` on the byte list, falling back to `coreSections`. -/
def coreSectionsFast (b : ByteArray) : Except String (List (UInt8 × Nat × Nat)) :=
  if 8 ≤ b.size ∧ b.data.toList.take 8 = coreHeader then
    match framesL b.size 8 (b.data.toList.drop 8) with
    | some t => .ok t
    | none => coreSections b
  else coreSections b

/-- The `name` parser on a window `w`: the string and the bytes it took. -/
def nameL (w : List UInt8) : Option (String × Nat) :=
  match uAuxL 32 0 0 w with
  | some (n, r) =>
    if n ≤ r.length then
      (String.fromUTF8? ⟨⟨r.take n⟩⟩).map fun str => (str, w.length - r.length + n)
    else none
  | none => none

/-- `name b s i` on the window's list, falling back to `name`. -/
def nameFast (b : ByteArray) (s i : Nat) : Res String :=
  if i ≤ s ∧ s ≤ b.size then
    match nameL ((b.data.toList.drop i).take (s - i)) with
    | some (str, k) => .ok str (i + k)
    | none => Silmaril.Parse.ByteParse.name b s i
  else Silmaril.Parse.ByteParse.name b s i

end Silmaril.Project.WasmComponents.Kernel

end
