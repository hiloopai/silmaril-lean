module

public import Silmaril.Formats.ELF.Object

/-! # Architecture-independent static section linking

An explicit layout places every nonempty allocated part. Strong definitions,
local symbols, and explicitly supplied absolute symbols are resolved without
interposition. The architecture supplies only relocation patches. The common
layer checks placement, bounds, patch extents, and disjointness. Archives, weak
symbols, COMMON, COMDAT, TLS, and dynamic linking are outside this profile.
-/

@[expose] public section

namespace Silmaril.Formats.ELF.Link

structure SectionKey where
  object : Nat
  index : Nat
  deriving DecidableEq, Repr

structure Placement where
  key : SectionKey
  address : Nat
  deriving DecidableEq, Repr

abbrev Layout := List Placement
abbrev AbsoluteSymbols := List (NameBytes × Nat)

def sectionAt (objects : List ObjectFile) (key : SectionKey) : Option ObjectSection := do
  let object ← objects[key.object]?
  object.sections[key.index]?

def addressAt (layout : Layout) (key : SectionKey) : Option Nat :=
  (layout.find? (fun placement => placement.key == key)).map Placement.address

def allocated (part : ObjectSection) : Bool :=
  (part.header.flags &&& 2) != 0 && part.header.size != 0

def allocatedSections (objects : List ObjectFile) : List SectionKey :=
  objects.zipIdx.flatMap fun (object, objectIndex) =>
    object.sections.zipIdx.filterMap fun (part, sectionIndex) =>
      if allocated part then some ⟨objectIndex, sectionIndex⟩ else none

def definitionValue (objects : List ObjectFile) (layout : Layout)
    (object : Nat) (symbol : ObjectSymbol) : Option Nat := do
  if symbol.raw.sectionIndex = 0xfff1 then
    pure symbol.raw.value
  else do
    guard (symbol.raw.sectionIndex ≠ 0 ∧ symbol.raw.sectionIndex < 0xff00)
    let part ← sectionAt objects ⟨object, symbol.raw.sectionIndex⟩
    guard (symbol.raw.value + symbol.raw.size ≤ part.header.size)
    let base ← addressAt layout ⟨object, symbol.raw.sectionIndex⟩
    guard (base + symbol.raw.value < 2 ^ 64)
    pure (base + symbol.raw.value)

def globalDefinitions (objects : List ObjectFile) (name : NameBytes) : List (Nat × ObjectSymbol) :=
  objects.zipIdx.flatMap fun (object, index) =>
    (object.symbols.filter fun symbol =>
      symbol.binding == 1 && symbol.raw.sectionIndex != 0 && symbol.name == name).map (index, ·)

/-- Local names are scoped to their object; undefined strong names require one definition. -/
def resolveSymbol (objects : List ObjectFile) (layout : Layout) (absolute : AbsoluteSymbols)
    (objectIndex symbolIndex : Nat) : Option Nat := do
  let object ← objects[objectIndex]?
  let symbol ← object.symbols[symbolIndex]?
  guard (symbol.binding ≤ 1 ∧ symbol.raw.other = 0)
  if symbol.raw.sectionIndex ≠ 0 then
    definitionValue objects layout objectIndex symbol
  else do
    guard (symbol.binding = 1 ∧ symbol.name ≠ [])
    let external := absolute.filter (fun entry => entry.1 == symbol.name)
    match globalDefinitions objects symbol.name, external with
    | [(owner, definition)], [] => definitionValue objects layout owner definition
    | [], [(_, value)] => if value < 2 ^ 64 then some value else none
    | _, _ => none

structure ResolvedRelocation where
  key : SectionKey
  offset : Nat
  place : Nat
  symbolValue : Nat
  kind : Nat
  addend : Int
  deriving DecidableEq, Repr

def resolveRelocations (objects : List ObjectFile) (layout : Layout)
    (absolute : AbsoluteSymbols) : Option (List ResolvedRelocation) := do
  let groups : List (List ResolvedRelocation) ← objects.zipIdx.mapM fun (object, objectIndex) =>
    object.relocations.mapM fun relocation => do
      let key : SectionKey := ⟨objectIndex, relocation.targetSection⟩
      let part ← sectionAt objects key
      guard (allocated part)
      let base ← addressAt layout key
      guard (relocation.offset < part.header.size)
      let symbolValue ← resolveSymbol objects layout absolute objectIndex relocation.symbol
      pure { key := key
             offset := relocation.offset
             place := base + relocation.offset
             symbolValue := symbolValue
             kind := relocation.kind
             addend := relocation.addend }
  pure groups.flatten

structure Patch where
  offset : Nat
  bytes : Bytes
  deriving DecidableEq, Repr

/-- Every replacement stays within the original section; no implicit section growth. -/
def applyPatch (bytes : Bytes) (patch : Patch) : Option Bytes := do
  guard (patch.offset + patch.bytes.size ≤ bytes.size)
  pure ⟨bytes.toList.take patch.offset ++ patch.bytes.toList ++
    bytes.toList.drop (patch.offset + patch.bytes.size)⟩

def Patch.Disjoint (first second : Patch) : Prop :=
  first.offset + first.bytes.size ≤ second.offset ∨
    second.offset + second.bytes.size ≤ first.offset

instance (first second : Patch) : Decidable (first.Disjoint second) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The callback may inspect paired relocations, as required by RISC-V HI/LO pairs. -/
abbrev Relocator := List ResolvedRelocation → ResolvedRelocation → Bytes → Option Patch

structure LinkedSection where
  key : SectionKey
  address : Nat
  flags : Nat
  memorySize : Nat
  data : Bytes
  deriving DecidableEq, Repr

def LinkedSection.Disjoint (first second : LinkedSection) : Prop :=
  first.address + first.memorySize ≤ second.address ∨
    second.address + second.memorySize ≤ first.address

instance (first second : LinkedSection) : Decidable (first.Disjoint second) :=
  inferInstanceAs (Decidable (_ ∨ _))

def linkSection (objects : List ObjectFile) (relocations : List ResolvedRelocation)
    (relocate : Relocator) (placement : Placement) : Option LinkedSection := do
  let part ← sectionAt objects placement.key
  guard (allocated part)
  guard (part.header.kind = 1 ∨ part.header.kind = 8)
  guard (part.header.flags = 2 ∨ part.header.flags = 3 ∨ part.header.flags = 6)
  guard (placement.address + part.header.size ≤ 2 ^ 64)
  guard (part.header.alignment ≤ 1 ∨ placement.address % part.header.alignment = 0)
  let patches ← (relocations.filter (fun relocation => relocation.key == placement.key)).mapM
    (fun relocation => do
      let patch ← relocate relocations relocation part.data
      guard (patch.offset = relocation.offset ∧ 0 < patch.bytes.size)
      pure patch)
  guard (patches.Pairwise Patch.Disjoint)
  let data ← patches.foldlM applyPatch part.data
  guard (data.size ≤ part.header.size)
  pure { key := placement.key
         address := placement.address
         flags := part.header.flags
         memorySize := part.header.size
         data := data }

/-- Link all allocated parts with explicit absolute definitions and ISA policy.
The output is section data, not a claim about an operating-system image writer. -/
def link (acceptHeader : Header → Bool) (relocate : Relocator) (objects : List ObjectFile)
    (layout : Layout) (absolute : AbsoluteSymbols := []) : Option (List LinkedSection) := do
  guard (objects.all fun object => acceptHeader object.header &&
    object.header.fileType == 1 && object.header.version == 1 &&
    object.symbols.all (fun symbol => symbol.binding ≤ 1))
  guard ((layout.map Placement.key).Perm (allocatedSections objects))
  guard ((layout.map Placement.key).Nodup)
  guard ((absolute.map Prod.fst).Nodup)
  let defined := objects.flatMap (fun object => object.symbols.filter fun symbol =>
    symbol.binding == 1 && symbol.raw.sectionIndex != 0)
  guard ((defined.map ObjectSymbol.name).Nodup)
  guard (defined.all fun symbol => !(absolute.any fun pair => pair.1 == symbol.name))
  let relocations ← resolveRelocations objects layout absolute
  let sections ← layout.mapM (linkSection objects relocations relocate)
  guard (sections.Pairwise LinkedSection.Disjoint)
  pure sections

/-- Section offset `i` is overwritten by `patch`. -/
def Covers (patch : Patch) (i : Nat) : Prop :=
  patch.offset ≤ i ∧ i < patch.offset + patch.bytes.size

instance (patch : Patch) (i : Nat) : Decidable (Covers patch i) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Silmaril.Formats.ELF.Link
