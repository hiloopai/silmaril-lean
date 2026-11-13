module

public import Silmaril.X86.Features.Ext.Avx.Extension
public import Silmaril.X86.Features.Checks

/-!
# Checking the `avx` lane against native execution

`checkLine` reads one vector line of `Vectors.lean` (written by
`scripts/x86-features/gen_avx_vectors.py`), decodes the instruction bytes the
assembler produced with the lane's decoder (`decode` must consume exactly
them), executes the result through `ext.exec` on a state where YMM `j` holds
`pattern j` unless the line gives an input, bits 511:256 are zero, RSI points
to a 64-byte read/write buffer at `bufBase`, and compares with the hardware:
all sixteen YMM registers, bits 511:256 still zero (VEX zeroing), and the
buffer, and MXCSR (the input MXCSR is the line's).
-/

@[expose] public section

namespace Silmaril.X86.Features.Avx

open Silmaril.Process (Memory Region)
open Silmaril.X86 (Byte)

/-- The value of the YMM registers the vector does not set (as the generator). -/
def pattern (j : Nat) : BitVec 256 :=
  let q := BitVec.ofNat 64 (0x9E3779B97F4A7C15 * (j + 1))
  q ++ q ++ q ++ q

/-- The address of the buffer RSI points to. -/
def bufBase : Nat := 0x20000

def bufRegion : Region := ⟨bufBase, 64, ⟨true, true, false⟩⟩

/-- The state of a vector: the YMM inputs over `pattern`, upper bits zero. -/
def vecState (ins : List (Nat × Nat)) : State :=
  (List.finRange 16).foldl (fun s (j : Fin 16) =>
      let v : BitVec 256 := match ins.lookup j.val with
        | some v => BitVec.ofNat 256 v
        | none => pattern j.val
      s.writeZmm (j.castLE (by decide)) (v.setWidth 512))
    (State.ofCore (vcore.write .rsi (BitVec.ofNat 64 bufBase)))

/-- Decode, execute and compare one vector. -/
def checkVec (code : List Nat) (ins : List (Nat × Nat)) (memIn : Nat) (outs : List (Nat × Nat))
    (memOut mxIn mxOut : Nat) : Bool :=
  let bytes : List Byte := code.map (BitVec.ofNat 8)
  match decode bytes with
  | none => false
  | some (i, n) =>
    let s := (vecState ins).setMxcsr ⟨BitVec.ofNat 32 mxIn⟩
    let memory : Memory := ⟨[bufRegion], Memory.install ∅ bufBase (natLe 64 memIn)⟩
    n == bytes.length &&
    match exec i n s memory with
    | .retired t m =>
      (List.finRange 16).all (fun (j : Fin 16) =>
        let r := j.castLE (by decide)
        let want : BitVec 256 := match outs.lookup j.val with
          | some v => BitVec.ofNat 256 v
          | none => s.ymm r
        t.ymm r == want && (t.zmm r).extractLsb' 256 256 == 0) &&
      m.readBytes bufBase 64 == some (natLe 64 memOut) &&
      t.rip == s.rip + BitVec.ofNat 64 n && t.mxcsr.bits == BitVec.ofNat 32 mxOut
    | _ => false

/-- Read `n` (register, value) pairs. -/
def pairs : Nat → List Nat → Option (List (Nat × Nat) × List Nat)
  | 0, rest => some ([], rest)
  | n + 1, r :: v :: rest => (pairs n rest).map fun (ps, rest) => ((r, v) :: ps, rest)
  | _ + 1, _ => none

/-- A vector line: `len b0 .. nin (reg value)* memIn nout (reg value)* memOut mxIn mxOut`. -/
def checkLine : List Nat → Bool
  | len :: rest =>
    let code := rest.take len
    match rest.drop len with
    | nin :: rest =>
      match pairs nin rest with
      | some (ins, memIn :: nout :: rest) =>
        match pairs nout rest with
        | some (outs, [memOut, mxIn, mxOut]) =>
          code.length == len && checkVec code ins memIn outs memOut mxIn mxOut
        | _ => false
      | _ => false
    | _ => false
  | _ => false

end Silmaril.X86.Features.Avx
