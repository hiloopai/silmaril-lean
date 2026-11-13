module

public import Silmaril.Elf.Staged.Defs

/-! # Symbol indexes: names to entries, addresses to entries

A stripped-down, checkable form of what `nm`, `addr2line` and a debugger's symbol lookup do,
over one symbol table (`.symtab` or `.dynsym`) of a staged file:

* `SymAt F t i s`: entry `i` of the table `t` (its header and its linked string table) is the
  symbol `s`, as the specification's reader `Parse.symbol` reads it;
* `ByName`: a **forward index**, `(name, entry)` pairs sorted by name bytes, with a binary
  search `ByName.find`;
* `ByAddr`: a **reverse map**, `(value, size, entry)` triples sorted by value, with
  `ByAddr.find v` returning the entry whose `[value, value + size)` contains `v`.

An index is an untrusted certificate (an emitter computes it); `ByName.Sound F x` and
`ByAddr.Sound F x` say each of its entries is a true statement about the file, and the checks
`byNameOk`/`byAddrOk` establish them with one symbol read and one wide name read per entry
(leaves `elf.symbols.byName`, `elf.symbols.byAddr`). Lookups are then sound by construction
(`ByName.find_sound`, `ByAddr.find_sound`: a lookup re-checks the entry it returns).

**Supported**: soundness of every answer. **Not yet**: completeness (that an absent answer
means the table has no such name or address; the index is checked sorted, which is what a
completeness proof needs, but the counting argument is future work), a byte trie shared across
files, and versioned `.dynsym` names (`Silmaril.Elf.Lookup` covers ld.so's lookup).
-/

@[expose] public section

namespace Silmaril.Elf.Staged.Symbols

open Silmaril.Formats.ELF (SectionHeader NameBytes ObjectSymbol)
open Silmaril.Elf.Link.DynElf (Rd blobRead)
open Silmaril.Elf.Check (Src)
open Silmaril.X86.Link (Blob)

/-- A symbol table: its section header and the string table it links to. -/
structure Tab where
  strs : SectionHeader
  tab : SectionHeader
  deriving DecidableEq, Repr

/-- The reader of entry `i`. -/
def Tab.entry (t : Tab) (i : Nat) : Rd ObjectSymbol := Parse.symbol t.strs (t.tab.offset + 24 * i)

/-- The number of entries. -/
def Tab.count (t : Tab) : Nat := t.tab.size / 24

/-- **Entry `i` of the table `t` of `F` is `s`.** -/
def SymAt (F : Blob) (t : Tab) (i : Nat) (s : ObjectSymbol) : Prop :=
  i < t.count ∧ (t.entry i).run (blobRead F) = some s

/-- Lexicographic order on name bytes. -/
def nameCmp : NameBytes → NameBytes → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    if a.toNat < b.toNat then .lt else if b.toNat < a.toNat then .gt else nameCmp as bs

/-! ## Forward index -/

/-- **Names to entries**, sorted by name. -/
structure ByName where
  t : Tab
  entries : Array (NameBytes × Nat)
  deriving Repr

/-- Binary search for `n` in `[lo, hi)`; `fuel` bounds the halvings. -/
def ByName.go (x : ByName) (n : NameBytes) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      match x.entries[mid]? with
      | none => none
      | some (m, i) =>
        match nameCmp m n with
        | .eq => some i
        | .lt => x.go n fuel (mid + 1) hi
        | .gt => x.go n fuel lo mid
    else none

/-- The entry named `n` (binary search). -/
def ByName.find (x : ByName) (n : NameBytes) : Option Nat := x.go n 64 0 x.entries.size

/-- Strictly sorted by name. -/
def ByName.sorted (x : ByName) : Bool :=
  (x.entries.toList.zip (x.entries.toList.drop 1)).all fun (a, b) => nameCmp a.1 b.1 == .lt

/-- **Every entry of the index is true of `F`.** -/
def ByName.Sound (F : Blob) (x : ByName) : Prop :=
  ∀ e ∈ x.entries.toList, ∃ s, SymAt F x.t e.2 s ∧ s.name = e.1

/-- The check behind `elf.symbols.byName`. -/
def byNameOk (r : Src) (x : ByName) : Bool :=
  x.sorted && x.entries.toList.all fun (n, i) =>
    decide (i < x.t.count) && match (x.t.entry i).run r with
      | some s => s.name == n
      | none => false

/-! ## Reverse map -/

/-- **Addresses to entries**: `(value, size, entry)`, sorted by value. -/
structure ByAddr where
  t : Tab
  entries : Array (Nat × Nat × Nat)
  deriving Repr

/-- The last position in `[lo, hi)` whose value is `≤ v`, if any (binary search). -/
def ByAddr.go (x : ByAddr) (v : Nat) : Nat → Nat → Nat → Option Nat → Option Nat
  | 0, _, _, best => best
  | fuel + 1, lo, hi, best =>
    if lo < hi then
      let mid := (lo + hi) / 2
      match x.entries[mid]? with
      | none => best
      | some (a, _, _) => if a ≤ v then x.go v fuel (mid + 1) hi (some mid) else x.go v fuel lo mid best
    else best

/-- The entry whose `[value, value + size)` contains `v`. -/
def ByAddr.find (x : ByAddr) (v : Nat) : Option Nat :=
  match (x.go v 64 0 x.entries.size none).bind (x.entries[·]?) with
  | some (a, z, i) => if a ≤ v ∧ v < a + z then some i else none
  | none => none

/-- Sorted by value. -/
def ByAddr.sorted (x : ByAddr) : Bool :=
  (x.entries.toList.zip (x.entries.toList.drop 1)).all fun (a, b) => a.1 ≤ b.1

/-- **Every entry of the map is true of `F`.** -/
def ByAddr.Sound (F : Blob) (x : ByAddr) : Prop :=
  ∀ e ∈ x.entries.toList, ∃ s, SymAt F x.t e.2.2 s ∧ s.raw.value = e.1 ∧ s.raw.size = e.2.1

/-- The check behind `elf.symbols.byAddr`. -/
def byAddrOk (r : Src) (x : ByAddr) : Bool :=
  x.sorted && x.entries.toList.all fun (a, z, i) =>
    decide (i < x.t.count) && match (x.t.entry i).run r with
      | some s => s.raw.value == a && s.raw.size == z
      | none => false

end Silmaril.Elf.Staged.Symbols
