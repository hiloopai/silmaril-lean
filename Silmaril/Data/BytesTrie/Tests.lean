module

public import Silmaril.Data.BytesTrie.Thms

/-!
# Byte tries: kernel-checked examples

Every example is checked by kernel evaluation (`decide +kernel` or `rfl`).
`scripts/bench/finmap-kernel.py` measures the same operations at larger sizes.
-/

namespace Silmaril.Data.BytesMap.Tests

open Silmaril.Data

/-- `"ab"`, `"abc"`, `"b"` and the empty key. -/
def m : BytesMap Nat :=
  ((((empty.insert [0x61, 0x62] 1).insert [0x61, 0x62, 0x63] 2).insert [0x62] 3).insert [] 0)

example : m.find? [0x61, 0x62] = some 1 := by decide +kernel
example : m.find? [0x61, 0x62, 0x63] = some 2 := by decide +kernel
example : m.find? [] = some 0 := by decide +kernel
example : m.find? [0x61] = none := by decide +kernel
example : m.find? [0x63] = none := by decide +kernel
example : m.size = 4 := by decide +kernel
example : m.toList = [([], 0), ([0x61, 0x62], 1), ([0x61, 0x62, 0x63], 2), ([0x62], 3)] := by
  decide +kernel

/-- Erasing prunes: removing `"abc"` then `"ab"` leaves no `0x61` branch. -/
example : ((m.erase [0x61, 0x62, 0x63]).erase [0x61, 0x62]).1.kids =
    .node 0x62 (some 3) .nil .nil := by decide +kernel

/-- Insertion order does not matter for canonical maps: equality is structural. -/
example : m = (((empty.insert [] 0).insert [0x62] 3).insert [0x61, 0x62, 0x63] 2).insert
    [0x61, 0x62] 1 := by decide +kernel

/-- Insert then erase is the identity on canonical maps. -/
example : (m.insert [0x61, 0x7a] 9).erase [0x61, 0x7a] = m := by decide +kernel

example : m ≠ m.insert [0x61] 5 := by decide +kernel

/-- Raw tries are not canonical: a value-free leaf denotes the same map as `empty`. -/
example : (⟨none, .node 0x61 none .nil .nil⟩ : BytesTrie Nat).Equiv .empty := by
  intro ks
  rcases ks with _ | ⟨_, _ | _⟩ <;> simp [BytesTrie.find?, BytesTrie.Trie.find?, BytesTrie.empty]
example : (⟨none, .node 0x61 none .nil .nil⟩ : BytesTrie Nat) ≠ .empty := by decide +kernel

/-- A literal trie, accepted as a map by kernel evaluation of `canonB`. -/
def lit : BytesMap Nat :=
  ofCanonB ⟨none, .node 0x61 (some 1) (.node 0x62 (some 2) .nil .nil) (.node 0x63 (some 3) .nil .nil)⟩

example : lit = ofList [([0x63], 3), ([0x61, 0x62], 2), ([0x61], 1)] := by decide +kernel
example : (BytesMap.ofRaw? (⟨none, .node 0x62 (some 1) .nil (.node 0x61 (some 2) .nil .nil)⟩ :
    BytesTrie Nat)).isNone := by decide +kernel

/-- A few hundred keys: three-byte keys `[0, i / 256, i % 256]`. -/
def big : BytesMap Nat :=
  (List.range 300).foldl (fun m i => m.insert [0, UInt8.ofNat (i / 256), UInt8.ofNat i] i) empty

example : big.find? [0, 1, 0x2a] = some 298 := by decide +kernel
example : big.find? [0, 2, 0] = none := by decide +kernel

end Silmaril.Data.BytesMap.Tests
