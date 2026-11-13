module

public import Silmaril.Wasm.FX.Asyncify.Shadow.Bytes.Defs
public import Silmaril.Wasm.Execution.Memory

/-!
# The words of the byte layout are Core 3.0 loads

`load_rd32`: in a silmaril-lean memory holding the bytes `bs`, the four-byte little-endian load
(`Execution.Memory.load`, which `i32.load` uses) at an in-bounds address `a` is the word `rd32`
reads there.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Shadow.Bytes

open Silmaril.Wasm.Execution.Memory Silmaril.Wasm.FX.Asyncify.Shadow

theorem unle32_decode (l : List UInt8) (h : l.length = 4) :
    decodeLE ⟨l.toArray⟩ = unle32 l := by
  match l, h with
  | [a, b, c, d], _ =>
    simp [decodeLE, unle32]
    omega

theorem load_rd32 (bs : List UInt8) (a : Nat) (h : a + 4 ≤ bs.length) :
    load ⟨bs.toArray⟩ a 4 = some (BitVec.ofNat 32 (rd32 bs a)) := by
  have hl : ((bs.drop a).take 4).length = 4 := by simp; omega
  have he : (ByteArray.mk bs.toArray).extract a (a + 4) = ⟨((bs.drop a).take 4).toArray⟩ := by
    ext1
    simp [List.take_drop]
  have hs : a + 4 ≤ (ByteArray.mk bs.toArray).size := by
    show a + 4 ≤ bs.toArray.size
    simpa using h
  simp [load, readBytes, hs, he, rd32, unle32_decode _ hl]

end Silmaril.Proofs.Wasm.FX.Asyncify.Shadow.Bytes
