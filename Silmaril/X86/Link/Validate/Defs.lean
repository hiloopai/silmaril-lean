module

public import Silmaril.X86.Link.Blob.Defs
public import Silmaril.X86.Linking.Defs
public import Silmaril.X86.Link.Profile.Defs

/-! # Translation validation of a real static link (`ld.bfd`, `ld.gold`, `ld.lld`)

The `ofNormalizer` pattern with the imported abstract linker as the normaliser:
the validator recomputes `Relocation.link` on the parsed input objects at the
layout an untrusted witness proposes, parses the executable with the public
checked loader `ELFImage.parse`, and checks that every linked section sits
byte-exactly in one loaded segment whose permissions match its flags, and that
`e_entry` is the entry symbol's linked address.

The witness (`Witness`, produced by an external tool from the linker's
map file) is a hint and cannot make a wrong link pass: `validate_sound` speaks
only about `readObject`, `ELFImage.parse` and `Relocation.link`. `Validated` is
relative to two witness fields, which are therefore part of what a fixture
states: `W.dropped` (sections claimed discarded) and `W.absolute` (values for
names no object defines). `W.absolute` is not yet restricted to linker-defined
names or checked against the image; the generated fixtures all use `[]`.

Two link-time mechanisms the imported linker rejects are modelled as explicit object
rewrites (`prepare`), so that ordinary `-ffunction-sections --gc-sections` links
validate:

* `Silmaril.X86.Link.Profile.normalize`, the profile rewrite, meant to be shared with an
  executable linker: the gABI weak rule for static links
  (strong beats weak, else the first weak definition; a weak reference binds to a
  definition when one exists and is otherwise rejected) and clearing `SHF_MERGE`/
  `SHF_STRINGS` on allocated sections. See `Silmaril.X86.Link.Profile.Defs`.
* `dropSections` (`--gc-sections`): the witness lists the input sections the
  linker discarded. They lose `SHF_ALLOC` and their own relocations. A
  surviving relocation that refers to a symbol in a dropped section then fails
  to resolve (`addressAt` finds no placement), so the check that discarded code
  is unreferenced is the linker's own resolution, not a new rule.

Still rejected (incompleteness, never unsoundness): links in which the real linker merged
`SHF_MERGE` pools (the merged output does not hold the unmerged bytes; compile with
`-fno-merge-constants`, or use the opt-in piece map below), COMMON, weak undefined with
no definition (unless opted in below), TLS, IFUNC, groups, GOT/PLT synthesis and relaxation (link with `--no-relax`
when a relaxable relocation occurs), linker-synthesised sections that a
relocation references, and `R_X86_64_*` kinds outside the profile.

**Opt-in static-executable profile.** A witness may set `W.profile`
(`Silmaril.X86.Link.Profile.Options`): zero-valued or linker-provided weak undefined
symbols, cleared symbol visibility, and merged string sections through a piece map
(`W.pieces`). `validateN`/`Validated` ignore these fields and are unchanged; such a witness
is checked with `validateProfileN` and means `ValidatedProfile`, which links
`prepareProfile W parsed` and also places every piece in the image. Generic forms over the
preparation (`validateByN`, `ValidatedBy`) share the soundness proof. `W.archiveMembers` is
provenance only.

`validateN` runs on `Blob`s (one `Nat` per file), which the kernel evaluates by
arithmetic; `validate` is the same check on byte arrays.

**Section-wise structure.** `validateN` does not call
`Relocation.link` as one function. It checks the link's global guards (`linkGuards`),
resolves the relocations once, checks that the placements do not overlap
(`shapesDisjoint`, on addresses and section sizes only), and then, placement by placement,
links one section with `linkSectionFast` and looks for it in a loaded segment
(`checkSection`). `linkSectionFast` is `linkSection` with a one-pass patcher
(`applyPatches`; proved equal, `linkSectionFast_eq`), and `link_of_sections` reassembles a
successful `Relocation.link` from the parts, so `Validated` is unchanged.
`validateGlobalN` and `validateChunkN` split the same work over several kernel
evaluations; `validated_of_chunks` composes them.
-/

@[expose] public section

namespace Silmaril.X86.Link.Validate

open Silmaril.Formats.ELF Silmaril.Formats.ELF.Link
open Silmaril.Process.LPS
open Silmaril.X86.Linking

/-- Untrusted hint extracted from the linker's map file. -/
structure Witness where
  /-- Address of every kept nonempty allocated input section. -/
  layout : Layout
  /-- Input sections the linker discarded (`--gc-sections`). -/
  dropped : List SectionKey := []
  /-- Linker-defined absolute symbols that some object references. -/
  absolute : AbsoluteSymbols := []
  /-- Name of the entry symbol, normally `_start`. -/
  entry : NameBytes
  /-- Opt-in profile rewrites (`Profile.Options`). Only the `…Profile…` validators below read
  it; `validateN` and `Validated` ignore it, so a witness that sets it is checked with
  `validateProfileN` and means `ValidatedProfile`. -/
  profile : Profile.Options := {}
  /-- Which inputs were archive members: (object index, member name), from the map's
  "Archive member included" section. Provenance only; no validator reads it. The objects a
  fixture lists are what `Validated` speaks about, so member selection is an untrusted hint. -/
  archiveMembers : List (Nat × NameBytes) := []
  /-- The piece map for merged string sections (`Profile.Piece`), read when
  `profile.mergeStrings`. Each piece is checked against the image (`piecesOk`). -/
  pieces : List Profile.Piece := []
  deriving DecidableEq, Repr

/-! ## Discarded sections -/

/-- Clear `SHF_ALLOC` on the dropped sections of object `i` and remove their
relocations. -/
def dropSections (dropped : List SectionKey) (i : Nat) (object : ObjectFile) : ObjectFile :=
  { object with
    sections := object.sections.zipIdx.map fun (part, k) =>
      if dropped.contains ⟨i, k⟩ then
        { part with header := { part.header with flags := part.header.flags - (part.header.flags &&& 2) } }
      else part
    relocations := object.relocations.filter fun r => !dropped.contains ⟨i, r.targetSection⟩ }

/-- The objects the abstract linker sees. -/
def prepare (objects : List ObjectFile) (dropped : List SectionKey) : List ObjectFile :=
  (Profile.normalize objects).zipIdx.map fun (object, i) => dropSections dropped i object

/-- The objects the abstract linker sees under the witness's opt-in profile: the merged-string
rewrite with the witness's piece map (when `W.profile.mergeStrings`), then `prepare`, then
`Profile.extendObject W.profile` with the witness's absolute names as the linker-provided
names. -/
def prepareProfile (W : Witness) (objects : List ObjectFile) : List ObjectFile :=
  let objects := if W.profile.mergeStrings then Profile.unmergeStrings W.pieces objects
    else objects
  (prepare objects W.dropped).map (Profile.extendObject W.profile (W.absolute.map Prod.fst))

/-- The address of the unique global definition of `name`. -/
def entryValue (objects : List ObjectFile) (layout : Layout) (name : NameBytes) : Option Nat :=
  match globalDefinitions objects name with
  | [(owner, symbol)] => definitionValue objects layout owner symbol
  | _ => none

/-! ## Image inclusion -/

/-- What a linked section must read as: its data, then zeros up to its size. -/
def expected (s : LinkedSection) : List (BitVec 8) :=
  s.data.toList ++ List.replicate (s.memorySize - s.data.size) 0

/-- Section flags (`SHF_WRITE` = 1, `SHF_EXECINSTR` = 4) against a segment's
`"rwx"` letters: readable, writable exactly when the section is, and executable
when the section is. -/
def PermsOk (seg : Silmaril.Process.LPS.Segment) (flags : Nat) : Prop :=
  seg.readable = true ∧ (seg.writable = true ↔ flags &&& 1 ≠ 0) ∧
    (flags &&& 4 ≠ 0 → seg.executable = true)

/-- The loaded image holds `s` byte-exactly inside one segment. -/
def SectionIn (image : Silmaril.Process.LPS.Image) (s : LinkedSection) : Prop :=
  ∃ seg ∈ image.segments, seg.base ≤ s.address ∧ s.address + s.memorySize ≤ seg.base + seg.size ∧
    PermsOk seg s.flags ∧
    ∀ i < s.memorySize, seg.bytes[s.address - seg.base + i]? = (expected s)[i]?

/-- The same permission test on `PF_*` program-header flags (`PF_X` = 1,
`PF_W` = 2, `PF_R` = 4). -/
def permsOkN (phFlags flags : Nat) : Bool :=
  phFlags / 4 % 2 == 1 && ((phFlags / 2 % 2 == 1) == (flags &&& 1 != 0)) &&
    (flags &&& 4 == 0 || phFlags % 2 == 1)

/-- Byte `j` of the segment that program header `ph` loads from the blob file `n`. -/
def segByteN (n : Nat) (ph : ProgramHeader) (j : Nat) : BitVec 8 :=
  if j < ph.fileSize then Blob.byteAt n (ph.offset + j) else 0

/-- `SectionIn`'s byte comparison by arithmetic: the section's data byte by byte, then its
zero tail. The tail needs no byte reads when it starts at or after the segment's file bytes
(`.bss`), which keeps large zero-filled sections cheap under kernel evaluation (for example
the 128 KiB arena of `zinflate`). `bytesInN_spec` gives the bytewise meaning. -/
def bytesInN (n : Nat) (ph : ProgramHeader) (s : LinkedSection) : Bool :=
  let off := s.address - ph.virtualAddress
  decide (s.data.size ≤ s.memorySize) &&
    (List.range s.data.size).map (fun i => segByteN n ph (off + i)) == s.data.toList &&
    (decide (ph.fileSize ≤ off + s.data.size) ||
      (List.range (s.memorySize - s.data.size)).all fun j =>
        segByteN n ph (off + s.data.size + j) == 0)

/-- `SectionIn`, checked against one `PT_LOAD` header by arithmetic. -/
def sectionInN (n : Nat) (ph : ProgramHeader) (s : LinkedSection) : Bool :=
  ph.kind == 1 && decide (ph.virtualAddress ≤ s.address) &&
    decide (s.address + s.memorySize ≤ ph.virtualAddress + ph.memorySize) &&
    permsOkN ph.flags s.flags && bytesInN n ph s

/-! ## Kernel-fast section linking (proved equal to `linkSection`)

The imported `linkSection` applies patches with `foldlM applyPatch`, which rebuilds the
section byte list once per patch; under kernel evaluation, forcing the result costs about
the number of patches times the section size, with a large constant (seconds for a large `.text` section). `applyPatches` computes every byte once, from the patch that
covers it. `Silmaril.Proofs.X86.Link.Validate` proves `linkSectionFast_eq :
linkSectionFast = linkSection`, so it is not trusted. -/

/-- Byte `i` after the patches: the covering patch's byte, else the original. -/
def patchedByte (patches : List Patch) (i : Nat) (b : BitVec 8) : BitVec 8 :=
  match patches.find? (fun p => decide (Covers p i)) with
  | some p => p.bytes[i - p.offset]?.getD b
  | none => b

/-- All patches at once. -/
def applyAll (data : Bytes) (patches : List Patch) : Bytes :=
  ⟨data.toList.zipIdx.map fun (b, i) => patchedByte patches i b⟩

/-- The patches start at or after `pos`, in offset order, without overlap (`R_X86_64`
relocation tables from gcc/as are sorted by offset). -/
def sortedFrom : Nat → List Patch → Bool
  | _, [] => true
  | pos, p :: ps => decide (pos ≤ p.offset) && sortedFrom (p.offset + p.bytes.size) ps

/-- Patch `l` (the section bytes from offset `pos` on) with offset-sorted patches, touching
each patch once. -/
def mergePatches : List (BitVec 8) → Nat → List Patch → List (BitVec 8)
  | l, _, [] => l
  | l, pos, p :: ps => l.take (p.offset - pos) ++ p.bytes.toList ++
      mergePatches (l.drop (p.offset - pos + p.bytes.size)) (p.offset + p.bytes.size) ps

/-- `Pairwise Patch.Disjoint`, in linear time for sorted patches. -/
def pairwiseFast (patches : List Patch) : Bool :=
  sortedFrom 0 patches || decide (patches.Pairwise Patch.Disjoint)

/-- `foldlM applyPatch` for pairwise disjoint patches, in one pass: a merge for sorted
patches, otherwise `applyAll`. -/
def applyPatches (data : Bytes) (patches : List Patch) : Option Bytes :=
  if patches.all (fun p => decide (p.offset + p.bytes.size ≤ data.size)) then
    some (if sortedFrom 0 patches then ⟨mergePatches data.toList 0 patches⟩
      else applyAll data patches)
  else none

/-- `linkSection` with `applyPatches` in place of `foldlM applyPatch`. -/
def linkSectionFast (objects : List ObjectFile) (relocations : List ResolvedRelocation)
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
  guard (pairwiseFast patches = true)
  let data ← applyPatches part.data patches
  guard (data.size ≤ part.header.size)
  pure { key := placement.key
         address := placement.address
         flags := part.header.flags
         memorySize := part.header.size
         data := data }

/-! ## Section-wise link checks

`Relocation.link` is its global guards, the resolved relocations, one `linkSection` per
placement, and pairwise disjointness of the results. The disjointness depends only on
each placement's address and section size (`shapeOf`), so it is checked on the layout.
`Silmaril.Proofs.X86.Link.Validate.link_of_sections` reassembles a successful
`Relocation.link` from these parts. -/

/-- The global guards of `Relocation.link`, as one Boolean. -/
def linkGuards (objects : List ObjectFile) (layout : Layout) (absolute : AbsoluteSymbols) : Bool :=
  let defined := objects.flatMap (fun object => object.symbols.filter fun symbol =>
    symbol.binding == 1 && symbol.raw.sectionIndex != 0)
  objects.all Relocation.staticObject &&
  (objects.all fun object => Relocation.accepts object.header &&
    object.header.fileType == 1 && object.header.version == 1 &&
    object.symbols.all (fun symbol => symbol.binding ≤ 1)) &&
  decide ((layout.map Placement.key).Perm (allocatedSections objects)) &&
  decide ((layout.map Placement.key).Nodup) &&
  decide ((absolute.map Prod.fst).Nodup) &&
  decide ((defined.map ObjectSymbol.name).Nodup) &&
  (defined.all fun symbol => !(absolute.any fun pair => pair.1 == symbol.name))

/-- Where a placement puts its section: (address, size). -/
def shapeOf (objects : List ObjectFile) (pl : Placement) : Nat × Nat :=
  (pl.address, ((sectionAt objects pl.key).map (·.header.size)).getD 0)

def ShapeDisjoint (a b : Nat × Nat) : Prop := a.1 + a.2 ≤ b.1 ∨ b.1 + b.2 ≤ a.1

instance (a b : Nat × Nat) : Decidable (ShapeDisjoint a b) := inferInstanceAs (Decidable (_ ∨ _))

/-- The placed sections do not overlap (checked on the layout, before linking). -/
def shapesDisjoint (objects : List ObjectFile) (layout : Layout) : Bool :=
  decide ((layout.map (shapeOf objects)).Pairwise ShapeDisjoint)

/-! ## The validator -/

/-- One placement: it links, and the result sits in a loaded segment of `exe`. -/
def checkSection (n : Nat) (records : ELFImage.Records) (objects : List ObjectFile)
    (rels : List ResolvedRelocation) (pl : Placement) : Bool :=
  match linkSectionFast objects rels Relocation.relocate pl with
  | some s => records.programHeaders.any fun ph => sectionInN n ph s
  | none => false

/-- The checks that span sections: link guards, disjoint placements and the entry point. -/
def globalOk (objects : List ObjectFile) (records : ELFImage.Records) (W : Witness) : Bool :=
  linkGuards objects W.layout W.absolute && shapesDisjoint objects W.layout &&
    entryValue objects W.layout W.entry == some records.header.entry

/-- Validate one link run: input objects and the executable as blobs. -/
def validateN (objects : List Blob) (exe : Blob) (W : Witness) : Bool :=
  match objects.mapM (fun b => Blob.readObjectN b.n b.len),
      Blob.parseN ELFImage.x86Policy exe.n exe.len with
  | some parsed, some records =>
    let prepared := prepare parsed W.dropped
    match resolveRelocations prepared W.layout W.absolute with
    | some rels =>
      globalOk prepared records W && W.layout.all (checkSection exe.n records prepared rels)
    | none => false
  | _, _ => false

/-- **Section-wise validation, global part**: `validateN` without the per-section checks. -/
def validateGlobalN (objects : List Blob) (exe : Blob) (W : Witness) : Bool :=
  match objects.mapM (fun b => Blob.readObjectN b.n b.len),
      Blob.parseN ELFImage.x86Policy exe.n exe.len with
  | some parsed, some records =>
    let prepared := prepare parsed W.dropped
    (resolveRelocations prepared W.layout W.absolute).isSome && globalOk prepared records W
  | _, _ => false

/-- **Section-wise validation, one chunk**: the per-section checks of the placements in
`chunk` only. `validated_of_chunks` composes a global check with chunks covering the
layout. -/
def validateChunkN (objects : List Blob) (exe : Blob) (W : Witness) (chunk : List Placement) :
    Bool :=
  match objects.mapM (fun b => Blob.readObjectN b.n b.len),
      Blob.parseN ELFImage.x86Policy exe.n exe.len with
  | some parsed, some records =>
    let prepared := prepare parsed W.dropped
    match resolveRelocations prepared W.layout W.absolute with
    | some rels => chunk.all (checkSection exe.n records prepared rels)
    | none => false
  | _, _ => false

/-- The same validator on byte arrays. -/
def validate (objects : List Bytes) (exe : Bytes) (W : Witness) : Bool :=
  validateN (objects.map Blob.ofBytes) (Blob.ofBytes exe) W

/-- What an accepted link means, in terms of the public readers and the
imported linker only. -/
def Validated (objects : List Bytes) (exe : Bytes) (W : Witness) : Prop :=
  ∃ parsed records out,
    objects.mapM readObject = some parsed ∧
    ELFImage.parse ELFImage.x86Policy exe = some records ∧
    Relocation.link (prepare parsed W.dropped) W.layout W.absolute = some out ∧
    (∀ s ∈ out, SectionIn (records.image exe) s) ∧
    entryValue (prepare parsed W.dropped) W.layout W.entry = some (records.image exe).initPc

/-! ## The validator for a chosen preparation

`validateN`, `validateGlobalN`, `validateChunkN` and `Validated` above fix the preparation
to `prepare · W.dropped`; they are unchanged so that existing fixtures and their consumers
keep their meaning. The `…By…` forms below take the preparation as a parameter, and the
`…Profile…` forms instantiate it with `prepareProfile W`, which honours `W.profile`. With
`W.profile = {}` the two preparations agree (`prepareProfile_default`), so
`ValidatedProfile` gives `Validated` (`validated_of_profile_default`). -/

/-- The checks after parsing, for the preparation `prep`: resolution, the global checks and
every placement. -/
def checkAllBy (prep : List ObjectFile → List ObjectFile) (n : Nat) (records : ELFImage.Records)
    (parsed : List ObjectFile) (W : Witness) : Bool :=
  let prepared := prep parsed
  match resolveRelocations prepared W.layout W.absolute with
  | some rels =>
    globalOk prepared records W && W.layout.all (checkSection n records prepared rels)
  | none => false

/-- `validateN` for the preparation `prep`. -/
def validateByN (prep : List ObjectFile → List ObjectFile) (objects : List Blob) (exe : Blob)
    (W : Witness) : Bool :=
  match objects.mapM (fun b => Blob.readObjectN b.n b.len),
      Blob.parseN ELFImage.x86Policy exe.n exe.len with
  | some parsed, some records => checkAllBy prep exe.n records parsed W
  | _, _ => false

/-- `validateGlobalN` for the preparation `prep`. -/
def validateGlobalByN (prep : List ObjectFile → List ObjectFile) (objects : List Blob)
    (exe : Blob) (W : Witness) : Bool :=
  match objects.mapM (fun b => Blob.readObjectN b.n b.len),
      Blob.parseN ELFImage.x86Policy exe.n exe.len with
  | some parsed, some records =>
    let prepared := prep parsed
    (resolveRelocations prepared W.layout W.absolute).isSome && globalOk prepared records W
  | _, _ => false

/-- `validateChunkN` for the preparation `prep`. -/
def validateChunkByN (prep : List ObjectFile → List ObjectFile) (objects : List Blob)
    (exe : Blob) (W : Witness) (chunk : List Placement) : Bool :=
  match objects.mapM (fun b => Blob.readObjectN b.n b.len),
      Blob.parseN ELFImage.x86Policy exe.n exe.len with
  | some parsed, some records =>
    let prepared := prep parsed
    match resolveRelocations prepared W.layout W.absolute with
    | some rels => chunk.all (checkSection exe.n records prepared rels)
    | none => false
  | _, _ => false

/-- `Validated` for the preparation `prep`. -/
def ValidatedBy (prep : List ObjectFile → List ObjectFile) (objects : List Bytes) (exe : Bytes)
    (W : Witness) : Prop :=
  ∃ parsed records out,
    objects.mapM readObject = some parsed ∧
    ELFImage.parse ELFImage.x86Policy exe = some records ∧
    Relocation.link (prep parsed) W.layout W.absolute = some out ∧
    (∀ s ∈ out, SectionIn (records.image exe) s) ∧
    entryValue (prep parsed) W.layout W.entry = some (records.image exe).initPc

/-! ### Merged-string pieces -/

/-- Piece `p` as a read-only linked section: the string of the raw (parsed, not prepared)
input section at `p.start`, through its NUL, at `p.address`. -/
def pieceSection (parsed : List ObjectFile) (p : Profile.Piece) : Option LinkedSection := do
  let part ← sectionAt parsed p.key
  guard (Profile.isMergedStrings part)
  let bytes ← Profile.pieceBytes part.data.toList p.start
  pure { key := p.key, address := p.address, flags := 2, memorySize := bytes.length,
         data := bytes.toArray }

/-- Every piece sits byte-exactly in a readable, non-writable loaded segment. -/
def piecesOk (n : Nat) (records : ELFImage.Records) (parsed : List ObjectFile)
    (pieces : List Profile.Piece) : Bool :=
  pieces.all fun p => match pieceSection parsed p with
    | some s => records.programHeaders.any fun ph => sectionInN n ph s
    | none => false

/-- What an accepted piece map means. -/
def PiecesIn (objects : List Bytes) (exe : Bytes) (W : Witness) : Prop :=
  ∃ parsed records,
    objects.mapM readObject = some parsed ∧
    ELFImage.parse ELFImage.x86Policy exe = some records ∧
    ∀ p ∈ W.pieces, ∃ s, pieceSection parsed p = some s ∧ SectionIn (records.image exe) s

/-! ### The profile-aware validator -/

/-- **The profile-aware validator**: `validateN` with `prepareProfile W`, and the pieces
(one parse of the inputs). -/
def validateProfileN (objects : List Blob) (exe : Blob) (W : Witness) : Bool :=
  match objects.mapM (fun b => Blob.readObjectN b.n b.len),
      Blob.parseN ELFImage.x86Policy exe.n exe.len with
  | some parsed, some records =>
    checkAllBy (prepareProfile W) exe.n records parsed W &&
      piecesOk exe.n records parsed W.pieces
  | _, _ => false

/-- `validateGlobalN` with `prepareProfile W`, and the pieces. -/
def validateProfileGlobalN (objects : List Blob) (exe : Blob) (W : Witness) : Bool :=
  match objects.mapM (fun b => Blob.readObjectN b.n b.len),
      Blob.parseN ELFImage.x86Policy exe.n exe.len with
  | some parsed, some records =>
    let prepared := prepareProfile W parsed
    (resolveRelocations prepared W.layout W.absolute).isSome && globalOk prepared records W &&
      piecesOk exe.n records parsed W.pieces
  | _, _ => false

/-- `validateChunkN` with `prepareProfile W`. -/
def validateProfileChunkN (objects : List Blob) (exe : Blob) (W : Witness)
    (chunk : List Placement) : Bool :=
  validateChunkByN (prepareProfile W) objects exe W chunk

/-- What an accepted profile-aware link means: `Validated` with `prepareProfile W` in place of
`prepare · W.dropped`, and every merged-string piece in the image. -/
def ValidatedProfile (objects : List Bytes) (exe : Bytes) (W : Witness) : Prop :=
  ValidatedBy (prepareProfile W) objects exe W ∧ PiecesIn objects exe W

end Silmaril.X86.Link.Validate
