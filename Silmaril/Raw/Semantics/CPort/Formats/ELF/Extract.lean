module

public import Silmaril.Formats.ELF.Object

/-!
# Extracting a named function, its constants, and its relocations

`Silmaril.Formats.ELF.Object` parses a relocatable file into sections, symbols
and explicit-addend relocations. This layer selects the parts a code proof needs:

* `ObjectFile.symbolData` — the bytes a symbol denotes, namely the window
  `[value, value + size)` of its defining section. For a `.text` symbol those
  are the function's instruction bytes; for a `.rodata` symbol they are its
  constant table.
* `ObjectFile.symbolRelocations` — the relocations that land inside that same
  window, which are exactly the link-time edits a proof about the function has
  to account for.
* `words32LE` — a constant table read as little-endian 32-bit words.

Selection is total and checked: an out-of-range symbol yields `none` rather than
a truncated window. Nothing here applies a relocation or interprets an ISA; the
numeric relocation kinds are kept as data, with the x86-64 names collected in
`Silmaril.Formats.ELF.X86_64` for readability.

## References
* System V ABI, AMD64 Architecture Processor Supplement, §4.4 (relocation types).
-/

@[expose] public section

namespace Silmaril.Formats.ELF

/-- The bytes a symbol denotes: the window `[value, value + size)` of the
section that defines it. `none` if the symbol names no section of this file or
runs past the end of its section's data. -/
def ObjectFile.symbolData (file : ObjectFile) (symbol : ObjectSymbol) : Option Bytes := do
  let owner ← file.sections[symbol.raw.sectionIndex]?
  guard (symbol.raw.value + symbol.raw.size ≤ owner.data.size)
  pure ⟨(owner.data.toList.drop symbol.raw.value).take symbol.raw.size⟩

/-- The first symbol carrying exactly this name. Names are byte strings, so this
does not assume UTF-8. -/
def ObjectFile.symbolNamed? (file : ObjectFile) (name : NameBytes) : Option ObjectSymbol :=
  file.symbols.find? fun symbol => symbol.name == name

/-- A relocation applies inside a symbol when it edits the symbol's own section
at an offset within `[value, value + size)`. -/
def ObjectSymbol.covers (symbol : ObjectSymbol) (relocation : ObjectRelocation) : Bool :=
  relocation.targetSection == symbol.raw.sectionIndex &&
    symbol.raw.value ≤ relocation.offset &&
    relocation.offset < symbol.raw.value + symbol.raw.size

/-- The relocations that apply inside a symbol's extent, in file order. -/
def ObjectFile.symbolRelocations (file : ObjectFile) (symbol : ObjectSymbol) :
    List ObjectRelocation :=
  file.relocations.filter symbol.covers

/-- A byte string read as little-endian 32-bit words; a trailing partial word is
dropped. -/
def words32LE : List (BitVec 8) → List (BitVec 32)
  | b0 :: b1 :: b2 :: b3 :: rest =>
      BitVec.ofNat 32
          (b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat) ::
        words32LE rest
  | _ => []

/-- The window a symbol selects, once its section and extent are known. -/
theorem symbolData_eq {file : ObjectFile} {symbol : ObjectSymbol} {owner : ObjectSection}
    (owner_at : file.sections[symbol.raw.sectionIndex]? = some owner)
    (inside : symbol.raw.value + symbol.raw.size ≤ owner.data.size) :
    file.symbolData symbol =
      some ⟨(owner.data.toList.drop symbol.raw.value).take symbol.raw.size⟩ := by
  simp [ObjectFile.symbolData, owner_at, guard, inside]

/-- Extraction yields exactly the symbol's declared size. -/
theorem symbolData_size {file : ObjectFile} {symbol : ObjectSymbol} {bytes : Bytes}
    {owner : ObjectSection} (owner_at : file.sections[symbol.raw.sectionIndex]? = some owner)
    (read : file.symbolData symbol = some bytes) : bytes.size = symbol.raw.size := by
  by_cases inside : symbol.raw.value + symbol.raw.size ≤ owner.data.size
  · have shape : bytes =
        (⟨(owner.data.toList.drop symbol.raw.value).take symbol.raw.size⟩ : Bytes) :=
      Option.some.inj (read.symm.trans (symbolData_eq owner_at inside))
    subst shape
    have bound : symbol.raw.value + symbol.raw.size ≤ owner.data.toList.length := inside
    show ((owner.data.toList.drop symbol.raw.value).take symbol.raw.size).length = symbol.raw.size
    rw [List.length_take, List.length_drop]
    omega
  · simp [ObjectFile.symbolData, owner_at, guard, inside] at read

/-- The extracted bytes are the ones the defining section already held, shifted
by the symbol's value. -/
theorem symbolData_getElem? {file : ObjectFile} {symbol : ObjectSymbol} {bytes : Bytes}
    {owner : ObjectSection} (owner_at : file.sections[symbol.raw.sectionIndex]? = some owner)
    (read : file.symbolData symbol = some bytes) (index : Nat) (small : index < symbol.raw.size) :
    bytes.toList[index]? = owner.data.toList[symbol.raw.value + index]? := by
  by_cases inside : symbol.raw.value + symbol.raw.size ≤ owner.data.size
  · have shape : bytes =
        (⟨(owner.data.toList.drop symbol.raw.value).take symbol.raw.size⟩ : Bytes) :=
      Option.some.inj (read.symm.trans (symbolData_eq owner_at inside))
    subst shape
    show ((owner.data.toList.drop symbol.raw.value).take symbol.raw.size)[index]? = _
    simp [List.getElem?_drop, small]
  · simp [ObjectFile.symbolData, owner_at, guard, inside] at read

/-- Compare the underlying lists rather than the arrays.

`DecidableEq (Array α)` indexes, so deciding an equality of `Bytes` costs a
number of steps quadratic in their length — prohibitive in the kernel for a
function of any size. `DecidableEq (List α)` is structural and linear, so a
`decide` on the list form of the goal and this lemma together prove the array
form cheaply. -/
theorem symbolData_of_toList {file : ObjectFile} {symbol : ObjectSymbol} {bytes : Bytes}
    (lists : (file.symbolData symbol).map Array.toList = some bytes.toList) :
    file.symbolData symbol = some bytes := by
  rcases read : file.symbolData symbol with _ | selected
  · rw [read] at lists
    exact absurd lists (by simp)
  · rw [read] at lists
    simp only [Option.map_some, Option.some.injEq] at lists
    exact congrArg some (Array.ext' lists)

/-- Every relocation selected for a symbol edits that symbol's own section. -/
theorem targetSection_of_mem_symbolRelocations {file : ObjectFile} {symbol : ObjectSymbol}
    {relocation : ObjectRelocation} (mem : relocation ∈ file.symbolRelocations symbol) :
    relocation.targetSection = symbol.raw.sectionIndex := by
  simp only [ObjectFile.symbolRelocations, List.mem_filter, ObjectSymbol.covers,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at mem
  exact mem.2.1.1

/-- Every relocation selected for a symbol lies inside the symbol's extent. -/
theorem offset_mem_of_mem_symbolRelocations {file : ObjectFile} {symbol : ObjectSymbol}
    {relocation : ObjectRelocation} (mem : relocation ∈ file.symbolRelocations symbol) :
    symbol.raw.value ≤ relocation.offset ∧
      relocation.offset < symbol.raw.value + symbol.raw.size := by
  simp only [ObjectFile.symbolRelocations, List.mem_filter, ObjectSymbol.covers,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at mem
  exact ⟨mem.2.1.2, mem.2.2⟩

/-- Relocations selected for a symbol are relocations of the file. -/
theorem mem_of_mem_symbolRelocations {file : ObjectFile} {symbol : ObjectSymbol}
    {relocation : ObjectRelocation} (mem : relocation ∈ file.symbolRelocations symbol) :
    relocation ∈ file.relocations :=
  (List.mem_filter.mp mem).1

/-- Reading little-endian words consumes four bytes at a time. -/
theorem words32LE_length : ∀ bytes : List (BitVec 8),
    (words32LE bytes).length = bytes.length / 4
  | [] => by simp [words32LE]
  | [_] => by simp [words32LE]
  | [_, _] => by simp [words32LE]
  | [_, _, _] => by simp [words32LE]
  | _ :: _ :: _ :: _ :: rest => by
      simp only [words32LE, List.length_cons, words32LE_length rest]
      omega

/-! ### x86-64 numeric codes

The System V AMD64 supplement's relocation types, kept as plain numbers so the
parser stays architecture independent. -/

namespace X86_64

/-- `EM_X86_64`: the ELF machine identifier for AMD64. -/
def machine : Nat := 62

/-- `R_X86_64_PC32`: `S + A - P`, truncated to 32 bits. -/
def R_PC32 : Nat := 2

/-- `R_X86_64_PLT32`: `L + A - P`, truncated to 32 bits. -/
def R_PLT32 : Nat := 4

end X86_64

end Silmaril.Formats.ELF
