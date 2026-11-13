module

public import Silmaril.Wasm.Logic.Sep.Thms

@[expose] public section
namespace Silmaril.Wasm.Logic.Sep
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-- Native byte cells in one memory, starting at an effective byte address. -/
def Heap.bytes (m p : Nat) (bs : List UInt8) : Heap
  | .byte m' i => if m' = m ∧ p ≤ i then bs[i - p]?.map Cell.byte else none
  | _ => none

/-- Exact ownership of a byte range; an i32 word owns four distinct byte cells. -/
def bytesPts (m p : Nat) (bs : List UInt8) : Assn := fun h => h = Heap.bytes m p bs

end Silmaril.Wasm.Logic.Sep
