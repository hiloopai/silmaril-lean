module

public import Silmaril.X86.Link.Abi.Defs

/-! # Translation units and their relocation-parametric images

A translation unit (TU, one `ET_REL` object) on its own, before any link:

* `Placement`: unit-local section index ↦ address;
* `Valuation`: global name ↦ address, for the names the unit leaves undefined;
* `image object slot p σ relocate`: the unit's allocated sections placed by `p`
  and relocated with locals and the unit's own global definitions resolved
  through `p`, undefined globals through `σ`. It reuses the body of the
  imported `linkSection` (`linkPart`) and the imported `Relocator`, so it is
  the TU-alone view of exactly the same byte computation. `slot` is only the
  object index written into the `SectionKey`s of the result;
* `restrict layout slot` and `globalValuation objects layout absolute`: the
  placement and valuation that one global `link` induces on one unit. The
  theorem `link_eq_units` (`Silmaril.X86.Link.Unit.Thms`) says the linked image
  restricted to a unit is that unit's image under them;
* `TU Tag Spec`: an object with a configuration key (`-D` set and a flags
  hash), ABI-tagged exports and imports that also carry an abstract `Spec`
  (to be instantiated with the separation-logic `FnSpec` later) and owned
  sections. `TU.iface` is the `Abi.Interface` that `Abi.checkAbi` checks, and
  `linkUnits` is `Abi.linkAbi` over a list of units.

The linker design calls the unit structure `Unit`; it is `TU` here because `Unit`
would shadow Lean's `Unit` inside this namespace.
-/

@[expose] public section

namespace Silmaril.X86.Link.Unit

universe u

open Silmaril.Formats.ELF
open Silmaril.Formats.ELF.Link (SectionKey Layout AbsoluteSymbols ResolvedRelocation Relocator
  LinkedSection Patch applyPatch allocated definitionValue globalDefinitions addressAt sectionAt)

/-- Unit-local placement: `(section index, address)` for the unit's sections. -/
abbrev Placement := List (Nat × Nat)

/-- The address `p` gives section `index` (the first entry for it). -/
def Placement.addr (p : Placement) (index : Nat) : Option Nat :=
  (p.find? (·.1 == index)).map Prod.snd

/-- Addresses of the global names a unit leaves undefined. -/
abbrev Valuation := NameBytes → Option Nat

/-- The placement a global layout gives object `slot`. -/
def restrict (layout : Layout) (slot : Nat) : Placement :=
  layout.filterMap fun placement =>
    if placement.key.object = slot then some (placement.key.index, placement.address) else none

/-- The one valuation of a link: an undefined global resolves to its unique
strong definition, else to its unique absolute symbol (exactly the undefined
branch of `Silmaril.Formats.ELF.Link.resolveSymbol`). -/
def globalValuation (objects : List ObjectFile) (layout : Layout) (absolute : AbsoluteSymbols) :
    Valuation := fun name =>
  match globalDefinitions objects name, absolute.filter (fun entry => entry.1 == name) with
  | [(owner, definition)], [] => definitionValue objects layout owner definition
  | [], [(_, value)] => if value < 2 ^ 64 then some value else none
  | _, _ => none

/-- `definitionValue` for a symbol defined in `object`, placed by `p`. -/
def localValue (object : ObjectFile) (p : Placement) (symbol : ObjectSymbol) : Option Nat := do
  if symbol.raw.sectionIndex = 0xfff1 then
    pure symbol.raw.value
  else do
    guard (symbol.raw.sectionIndex ≠ 0 ∧ symbol.raw.sectionIndex < 0xff00)
    let part ← object.sections[symbol.raw.sectionIndex]?
    guard (symbol.raw.value + symbol.raw.size ≤ part.header.size)
    let base ← p.addr symbol.raw.sectionIndex
    guard (base + symbol.raw.value < 2 ^ 64)
    pure (base + symbol.raw.value)

/-- `resolveSymbol` for one unit: symbols it defines (local or global) through
`p`, undefined globals through `σ`. -/
def resolveIn (object : ObjectFile) (p : Placement) (σ : Valuation) (symbolIndex : Nat) :
    Option Nat := do
  let symbol ← object.symbols[symbolIndex]?
  guard (symbol.binding ≤ 1 ∧ symbol.raw.other = 0)
  if symbol.raw.sectionIndex ≠ 0 then
    localValue object p symbol
  else do
    guard (symbol.binding = 1 ∧ symbol.name ≠ [])
    σ symbol.name

/-- The unit's resolved relocations (the `slot` group of `resolveRelocations`). -/
def relocations (object : ObjectFile) (slot : Nat) (p : Placement) (σ : Valuation) :
    Option (List ResolvedRelocation) :=
  object.relocations.mapM fun relocation => do
    let key : SectionKey := ⟨slot, relocation.targetSection⟩
    let part ← object.sections[relocation.targetSection]?
    guard (allocated part)
    let base ← p.addr relocation.targetSection
    guard (relocation.offset < part.header.size)
    let symbolValue ← resolveIn object p σ relocation.symbol
    pure { key := key
           offset := relocation.offset
           place := base + relocation.offset
           symbolValue := symbolValue
           kind := relocation.kind
           addend := relocation.addend }

/-- The body of the imported `linkSection` once the input section is known. -/
def linkPart (part : ObjectSection) (relocations : List ResolvedRelocation)
    (relocate : Relocator) (placement : Silmaril.Formats.ELF.Link.Placement) :
    Option LinkedSection := do
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

/-- The TU-alone image: every section `p` places, relocated under `p` and `σ`,
pairwise disjoint. It does not check that `p` places each allocated section
exactly once: a section missing from `p` is simply absent, and a duplicated
index is placed twice with relocations computed for its first address (see
`image_not_wellPlaced`). `link_eq_units` covers the placements `restrict` gives
after a successful link. -/
def image (object : ObjectFile) (slot : Nat) (p : Placement) (σ : Valuation)
    (relocate : Relocator) : Option (List LinkedSection) := do
  let rels ← relocations object slot p σ
  let sections ← p.mapM fun entry => do
    let part ← object.sections[entry.1]?
    linkPart part rels relocate ⟨⟨slot, entry.1⟩, entry.2⟩
  guard (sections.Pairwise LinkedSection.Disjoint)
  pure sections

/-- A relocator whose patch for `r` depends only on the relocations aimed at
`r`'s own section (true of the x86-64 profile, which ignores the list). -/
def SectionLocal (relocate : Relocator) : Prop :=
  ∀ (all all' : List ResolvedRelocation) (r : ResolvedRelocation) (bytes : Bytes),
    all.filter (·.key == r.key) = all'.filter (·.key == r.key) →
      relocate all r bytes = relocate all' r bytes

/-- Byte `b` is at address `a` in an image. -/
def Contains (img : List LinkedSection) (a : Nat) (b : BitVec 8) : Prop :=
  ∃ s ∈ img, s.address ≤ a ∧ s.data[a - s.address]? = some b

/-! ## Translation units -/

/-- The configuration a TU was compiled under: its `-D` set and a hash of the
remaining flags. Proofs about a unit are about this configuration only. -/
structure Config where
  defines : List String := []
  flagsHash : String := ""
  deriving DecidableEq, Repr

/-- An export or import: a global name, its ABI tag and its (abstract) spec. -/
structure Entry (Tag : Type) (Spec : Type u) where
  name : NameBytes
  tag : Tag
  spec : Spec

/-- A translation unit. `Tag` is the ABI vocabulary of `Silmaril.X86.Link.Abi`
(default instance `Abi.Conv`, `sysv64`); `Spec` is an abstract contract type. -/
structure TU (Tag : Type) (Spec : Type u) where
  object : ObjectFile
  config : Config := {}
  exports : List (Entry Tag Spec) := []
  imports : List (Entry Tag Spec) := []
  /-- Sections (by index) whose memory the unit owns privately (`.data`/`.bss`). -/
  owned : List Nat := []

variable {Tag : Type} {Spec : Type u}

def TU.iface (u : TU Tag Spec) : Abi.Interface Tag where
  exports := u.exports.map fun e => (e.name, e.tag)
  imports := u.imports.map fun e => (e.name, e.tag)

def TU.image (u : TU Tag Spec) (slot : Nat) (p : Placement) (σ : Valuation)
    (relocate : Relocator) : Option (List LinkedSection) :=
  Unit.image u.object slot p σ relocate

/-- The unit-local address of a global name the unit defines. -/
def TU.exportAddr (u : TU Tag Spec) (p : Placement) (name : NameBytes) : Option Nat := do
  let symbol ← u.object.symbols.find? fun symbol =>
    symbol.binding == 1 && symbol.raw.sectionIndex != 0 && symbol.name == name
  localValue u.object p symbol

/-- ABI-checked link of a list of units (`Abi.linkAbi`). -/
def linkUnits [DecidableEq Tag] (accepts : Header → Bool) (relocate : Relocator)
    (policy : Abi.Policy Tag) (units : List (TU Tag Spec)) (layout : Layout)
    (absolute : AbsoluteSymbols := []) : Option (List LinkedSection) :=
  Abi.linkAbi accepts relocate policy (units.map TU.object) (units.map TU.iface) layout absolute

end Silmaril.X86.Link.Unit
