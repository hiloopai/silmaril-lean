module

public import Silmaril.Process.CLI.Sha256Cli.SecondPaddingFrame
public import Silmaril.Process.CLI.Sha256Cli.TailPaddingReference

/-! # Canonical reference fold for the two actual long-tail blocks

The marker block and the zero/length block are the machine-facing definitions.
The existing all-remainders padding decomposition identifies their fold with
the reference hash, including the modular length serialization.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.LongTailPaddingReference

open Silmaril.X86 (Word)
open Silmaril.Crypto

theorem paddedBlocks (prefixBlocks : List (List Byte)) (tail : List Byte)
    (full : ∀ block ∈ prefixBlocks, block.length = 64)
    (long : 56 ≤ tail.length) (room : tail.length < 64) :
    Driver.paddedBlocks (prefixBlocks.flatten ++ tail) =
      prefixBlocks ++ [PaddingExtra.block tail,
        SecondPaddingFrame.block (BitVec.ofNat 64 (prefixBlocks.flatten ++ tail).length)] := by
  have notShort : ¬tail.length < 56 := by omega
  simpa only [TailPaddingReference.blocks, ite_eq_right notShort, PaddingExtra.block,
    SecondPaddingFrame.block, List.append_assoc, List.singleton_append] using
      TailPaddingReference.paddedBlocks prefixBlocks tail full room

/-- This identifies the two-compression result only after the caller supplies
the prefix fold from H0 and the whole message's modular byte count. -/
theorem fold_long (prefixBlocks : List (List Byte)) (tail : List Byte)
    (full : ∀ block ∈ prefixBlocks, block.length = 64)
    (long : 56 ≤ tail.length) (room : tail.length < 64) :
    Driver.compressBlock
      (Driver.compressBlock (prefixBlocks.foldl Driver.compressBlock SHA256.H0)
        (PaddingExtra.block tail))
      (SecondPaddingFrame.block (BitVec.ofNat 64 (prefixBlocks.flatten ++ tail).length)) =
        SHA256.hash ((prefixBlocks.flatten ++ tail).map UInt8.ofBitVec) := by
  have folded := Driver.fold_paddedBlocks (prefixBlocks.flatten ++ tail)
  rw [paddedBlocks prefixBlocks tail full long room, List.foldl_append] at folded
  simpa only [List.foldl_cons, List.foldl_nil] using folded

end Silmaril.Process.CLI.Sha256Cli.LongTailPaddingReference
