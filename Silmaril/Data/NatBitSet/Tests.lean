module

public import Silmaril.Data.NatBitSet.Thms

/-!
# Bit-mask sets: kernel-checked examples
-/

namespace Silmaril.Data.NatBitSet.Tests

open Silmaril.Data

def s : NatBitSet := NatBitSet.ofList [3, 1, 4, 1, 5, 9, 2, 6]

example : s.mem 9 = true := by decide +kernel
example : s.mem 7 = false := by decide +kernel
example : s = NatBitSet.ofList [1, 2, 3, 4, 5, 6, 9] := by decide +kernel
example : (s.erase 9).insert 9 = s := by decide +kernel
example : s.diff (NatBitSet.ofList [1, 2, 3]) = NatBitSet.ofList [4, 5, 6, 9] := by decide +kernel

/-- Multiples of 3 below 3000, built in two orders: equality is one `Nat` comparison. -/
def threes : NatBitSet := (List.range 1000).foldl (fun s i => s.insert (3 * i)) NatBitSet.empty
def threesRev : NatBitSet :=
  (List.range 1000).reverse.foldl (fun s i => s.insert (3 * i)) NatBitSet.empty

example : threes.mem 2997 = true := by decide +kernel
example : threes.mem 2998 = false := by decide +kernel
example : threes = threesRev := by decide +kernel

end Silmaril.Data.NatBitSet.Tests
