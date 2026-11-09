module

public import Silmaril.Formats.ELF.Link.Defs

/-! # The shared static-link profile (weak symbols, mergeable sections)

The imported linker (`Silmaril.Formats.ELF.Link.link`) rejects `STB_WEAK` symbols and
allocated sections with flags other than A, AW and AX. This module is the **one** place
where parsed objects are rewritten before they are linked: the link validator
(`Silmaril.X86.Link.Validate.prepare`) uses `normalize` below, and an executable linker that
uses it too produces, by construction, links the validator speaks about.

The rewrites are total and structural:

* **Weak symbols (`resolveWeakSymbol`, gABI rule for static links).**
  - A weak *definition* that some strong definition of the same name overrides becomes an
    undefined global reference, so every reference, including one from its own object, binds
    to the strong definition. The overridden bytes stay in the image, unreferenced.
  - Otherwise the first weak definition of the name, in link order, becomes a strong
    definition, and every later one becomes an undefined global reference.
  - A weak *reference* (undefined) becomes a strong reference when some object defines the
    name (strong or weak). Otherwise it stays weak, and the imported linker rejects it: the
    default profile has no zero-valued weak undefined symbols. (`unresolvedWeak` names such
    a symbol, for diagnostics only.) The opt-in `Options.weakUndefZero` below resolves it.
* **Mergeable sections (`unmergeSection`).** `SHF_MERGE`/`SHF_STRINGS` (`0x10`/`0x20`) are
  cleared on allocated sections, so string and constant pools are linked as ordinary
  read-only sections and not merged. Merging is an optional size optimisation; C does not
  promise distinct or equal addresses for equal literals. A link whose real linker *did*
  merge pools (`ld` without `-fno-merge-constants`) still fails validation, because the
  merged output does not hold the unmerged bytes at the map-file addresses: incompleteness,
  never unsoundness.

The behaviour-preservation argument for both rewrites is informal (stated here, not
proved); what is proved is that they are structural (`normalize_*` in the header).
-/

@[expose] public section

namespace Silmaril.X86.Link.Profile

open Silmaril.Formats.ELF Silmaril.Formats.ELF.Link

/-! ## Weak symbols -/

/-- A weak definition (`STB_WEAK`, defined). -/
def isWeakDef (symbol : ObjectSymbol) : Bool :=
  symbol.binding == 2 && symbol.raw.sectionIndex != 0

/-- A weak reference (`STB_WEAK`, undefined). -/
def isWeakRef (symbol : ObjectSymbol) : Bool :=
  symbol.binding == 2 && symbol.raw.sectionIndex == 0

/-- A strong global definition (`STB_GLOBAL`, defined). -/
def isStrongDef (symbol : ObjectSymbol) : Bool :=
  symbol.binding == 1 && symbol.raw.sectionIndex != 0

/-- The same symbol with binding `STB_GLOBAL` (type, section and value unchanged). -/
def promote (symbol : ObjectSymbol) : ObjectSymbol :=
  { symbol with raw := { symbol.raw with info := 16 + symbol.raw.info % 16 } }

/-- The same name as an undefined global reference. -/
def undefine (symbol : ObjectSymbol) : ObjectSymbol :=
  { symbol with raw := { symbol.raw with
      info := 16 + symbol.raw.info % 16, sectionIndex := 0, value := 0, size := 0 } }

/-- Some object holds a strong definition of `name`. -/
def strongDefined (objects : List ObjectFile) (name : NameBytes) : Bool :=
  objects.any fun object => object.symbols.any fun symbol =>
    isStrongDef symbol && symbol.name == name

/-- Some object holds a strong or weak definition of `name`. -/
def anyDefined (objects : List ObjectFile) (name : NameBytes) : Bool :=
  objects.any fun object => object.symbols.any fun symbol =>
    (isStrongDef symbol || isWeakDef symbol) && symbol.name == name

/-- The first weak definition of `name` in link order, as (object, symbol) indices. -/
def firstWeak (objects : List ObjectFile) (name : NameBytes) : Option (Nat × Nat) :=
  (objects.zipIdx.flatMap fun (object, i) =>
    object.symbols.zipIdx.filterMap fun (symbol, j) =>
      if isWeakDef symbol && symbol.name == name then some (i, j) else none).head?

/-- **The weak rule**: symbol `j` of object `i`. -/
def resolveWeakSymbol (objects : List ObjectFile) (i j : Nat) (symbol : ObjectSymbol) :
    ObjectSymbol :=
  if isWeakDef symbol then
    if strongDefined objects symbol.name then undefine symbol
    else if firstWeak objects symbol.name == some (i, j) then promote symbol
    else undefine symbol
  else if isWeakRef symbol then
    if anyDefined objects symbol.name then promote symbol else symbol
  else symbol

/-- A weak reference that `resolveWeakSymbol` leaves weak (no definition anywhere); the
imported linker rejects it. Diagnostics only. -/
def unresolvedWeak (objects : List ObjectFile) : Option NameBytes :=
  ((objects.flatMap ObjectFile.symbols).find? fun symbol =>
    isWeakRef symbol && !anyDefined objects symbol.name).map ObjectSymbol.name

/-! ## Mergeable sections -/

/-- Clear `SHF_MERGE | SHF_STRINGS` on an allocated section. -/
def unmergeSection (part : ObjectSection) : ObjectSection :=
  if allocated part && (part.header.flags &&& 0x30) != 0 then
    { part with header := { part.header with flags := part.header.flags - (part.header.flags &&& 0x30) } }
  else part

/-! ## The profile rewrite -/

/-- Object `i` after the profile rewrite. -/
def normalizeObject (objects : List ObjectFile) (object : ObjectFile) (i : Nat) : ObjectFile :=
  { object with
    symbols := object.symbols.zipIdx.map fun (symbol, j) => resolveWeakSymbol objects i j symbol
    sections := object.sections.map unmergeSection }

/-- **The profile rewrite** used by `Validate.prepare`. -/
def normalize (objects : List ObjectFile) : List ObjectFile :=
  objects.zipIdx.map fun (object, i) => normalizeObject objects object i

/-! ## Opt-in static-executable rewrites

Two further rewrites, applied only when a witness asks for them (`Options`, default all
off), after `normalize`. Every existing fixture uses the default, so its meaning is unchanged.
They make musl's startup objects linkable (`examples/elf-zlib`, the `zinflate` P0 image):

* **`weakUndefZero`.** A weak reference that `resolveWeakSymbol` leaves weak (no object
  defines the name) resolves, as `ld` does in a static non-PIE link, to
  - the linker-provided value when the name is one of `provided` (the witness's absolute
    symbols, e.g. `PROVIDE (__init_array_start = .)` in the default linker script): the
    reference becomes a strong reference, which the imported linker resolves through
    `W.absolute`;
  - otherwise **zero**: the symbol becomes a *local* absolute symbol (`SHN_ABS`) of value 0
    (`_DYNAMIC` in musl's `crt1.o` and `__init_tls.o`). Being local, two objects may both
    hold one without clashing as duplicate global definitions.
* **`staticVisibility`.** The visibility bits of `st_other` (`STV_HIDDEN`, ...) are cleared.
  Visibility restricts what a *shared* object exports; inside one static executable a hidden
  symbol binds like a default one (gABI "Symbol Visibility"), and the imported linker rejects
  any nonzero `st_other`. Other bits of `st_other` are kept, so they are still rejected.

As with `normalize`, the behaviour-preservation argument is informal (stated here). -/

/-- Opt-in rewrites beyond `normalize`; the default changes nothing. -/
structure Options where
  /-- A weak reference that nothing defines takes its `provided` value, else zero. -/
  weakUndefZero : Bool := false
  /-- Clear `STV_*` visibility bits. -/
  staticVisibility : Bool := false
  /-- Link `SHF_MERGE | SHF_STRINGS` sections through a piece map (`unmergeStrings`). -/
  mergeStrings : Bool := false
  deriving DecidableEq, Repr

/-- All three rewrites: the profile of a static musl executable. -/
def Options.staticExe : Options :=
  { weakUndefZero := true, staticVisibility := true, mergeStrings := true }

/-- The same symbol with the visibility bits (`st_other & 3`) cleared. -/
def clearVisibility (symbol : ObjectSymbol) : ObjectSymbol :=
  { symbol with raw := { symbol.raw with other := symbol.raw.other - symbol.raw.other % 4 } }

/-- `SHN_ABS`. -/
def shnAbs : Nat := 0xfff1

/-- The weak-undefined rule: a still-weak reference becomes a strong reference to a
`provided` (linker-defined) name, or else a local absolute symbol of value zero. -/
def weakUndefSymbol (provided : List NameBytes) (symbol : ObjectSymbol) : ObjectSymbol :=
  if isWeakRef symbol then
    if provided.contains symbol.name then promote symbol
    else { symbol with raw := { symbol.raw with
      info := symbol.raw.info % 16, sectionIndex := shnAbs, value := 0, size := 0 } }
  else symbol

/-- The opt-in rewrites of one symbol. -/
def extendSymbol (opts : Options) (provided : List NameBytes) (symbol : ObjectSymbol) :
    ObjectSymbol :=
  let symbol := if opts.weakUndefZero then weakUndefSymbol provided symbol else symbol
  if opts.staticVisibility then clearVisibility symbol else symbol

/-- The opt-in rewrites of one object (symbols only; sections and relocations unchanged). -/
def extendObject (opts : Options) (provided : List NameBytes) (object : ObjectFile) :
    ObjectFile :=
  { object with symbols := object.symbols.map (extendSymbol opts provided) }

/-! ## Merged string sections (opt-in, `Options.mergeStrings`)

`ld` merges `SHF_MERGE | SHF_STRINGS` input sections (`.rodata.*.str1.*`) into a pool:
equal strings, and strings that are suffixes of others, share one copy. The pool does not
hold the input sections side by side, so they cannot be placed as ordinary sections. Instead
the witness supplies a **piece map** (`Piece`): for a string starting at offset `start` of
input section `key`, the address of its copy in the output. Then, before the shared profile
rewrite,

* every merged string section loses `SHF_ALLOC`, so it is not placed (`unmergeStringsObject`);
* every relocation whose symbol is defined in a merged string section is redirected to the
  string's output address (`unmergeRelocation`), following `ld.bfd`
  (`_bfd_elf_rela_local_sym`, `_bfd_merged_section_offset`): for a section symbol the
  offset is `st_value + r_addend` and the addend is absorbed; for another symbol the offset
  is `st_value` and the addend is kept. The relocation then refers to symbol 0, which
  becomes the absolute symbol of value 0: the gABI meaning of `STN_UNDEF` as a relocation
  symbol ("the relocation uses 0 as the symbol value");
* a relocation whose target string has no piece, or lies outside its section, is left
  unchanged; it then refers to an unplaced section and the link fails.

The validator checks every piece against the image (`Validate.pieceSection`): the string's
bytes, through its terminating NUL, are at the piece's address in a read-only segment. -/

/-- A merged-string piece: the output address of the string at offset `start` of input
section `key`. -/
structure Piece where
  key : SectionKey
  start : Nat
  address : Nat
  deriving DecidableEq, Repr

/-- An allocated `SHF_MERGE | SHF_STRINGS` `PROGBITS` section of one-byte characters. -/
def isMergedStrings (part : ObjectSection) : Bool :=
  allocated part && part.header.kind == 1 && part.header.flags &&& 0x30 == 0x30 &&
    part.header.entrySize == 1

/-- The start of the string holding offset `t`: one past the last NUL before `t`, or 0. -/
def pieceStart (data : List (BitVec 8)) (t : Nat) : Nat :=
  (data.take t).zipIdx.foldl (fun acc (b, i) => if b == 0 then i + 1 else acc) 0

/-- The string at offset `start`, through its NUL (`none` without a NUL). -/
def pieceBytes (data : List (BitVec 8)) (start : Nat) : Option (List (BitVec 8)) :=
  let rest := data.drop start
  let body := rest.takeWhile (· != 0)
  if body.length < rest.length then some (body ++ [0]) else none

/-- The piece map's address for the string at `start` of section `key`. -/
def pieceAddress (pieces : List Piece) (key : SectionKey) (start : Nat) : Option Nat :=
  (pieces.find? fun p => p.key == key && p.start == start).map Piece.address

/-- The output address of offset `t` of merged section `key`. -/
def mergedTarget (pieces : List Piece) (key : SectionKey) (data : List (BitVec 8)) (t : Nat) :
    Option Nat :=
  if t < data.length then
    let s := pieceStart data t
    (pieceAddress pieces key s).map (· + (t - s))
  else none

/-- Redirect relocation `r` of object `i` when its symbol lies in a merged string section. -/
def unmergeRelocation (pieces : List Piece) (i : Nat) (object : ObjectFile)
    (r : ObjectRelocation) : ObjectRelocation :=
  match object.symbols[r.symbol]? with
  | none => r
  | some symbol =>
    match object.sections[symbol.raw.sectionIndex]? with
    | none => r
    | some part =>
      if symbol.raw.sectionIndex != 0 && isMergedStrings part then
        let key : SectionKey := ⟨i, symbol.raw.sectionIndex⟩
        let section? := symbol.kind == 3
        let offset : Int := if section? then symbol.raw.value + r.addend else symbol.raw.value
        if offset < 0 then r else
        match mergedTarget pieces key part.data.toList offset.toNat with
        | some address =>
          { r with symbol := 0, addend := address + (if section? then 0 else r.addend) }
        | none => r
      else r

/-- Symbol 0 as the absolute symbol of value 0 (gABI `STN_UNDEF` in a relocation). -/
def absZero (symbol : ObjectSymbol) : ObjectSymbol :=
  { symbol with raw := { symbol.raw with
      info := 0, other := 0, sectionIndex := shnAbs, value := 0, size := 0 } }

/-- Merged string sections lose `SHF_ALLOC`. -/
def unallocMerged (part : ObjectSection) : ObjectSection :=
  if isMergedStrings part then
    { part with header := { part.header with flags := part.header.flags - 2 } }
  else part

/-- **The merged-string rewrite** of object `i`. -/
def unmergeStringsObject (pieces : List Piece) (object : ObjectFile) (i : Nat) : ObjectFile :=
  { object with
    sections := object.sections.map unallocMerged
    symbols := match object.symbols with
      | [] => []
      | s :: rest => absZero s :: rest
    relocations := object.relocations.map (unmergeRelocation pieces i object) }

/-- The merged-string rewrite of all objects. -/
def unmergeStrings (pieces : List Piece) (objects : List ObjectFile) : List ObjectFile :=
  objects.zipIdx.map fun (object, i) => unmergeStringsObject pieces object i

end Silmaril.X86.Link.Profile
