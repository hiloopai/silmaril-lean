module

public import Silmaril.X86.Link.Validate.Defs
public import Silmaril.X86.Link.Blob.Thms
public import Silmaril.Formats.ELF.Link.Thms
import Silmaril.Proofs.X86.Link.Validate

/-! # Translation validation of static links: theorems (header)

`Silmaril.Proofs.X86.Link.Validate` (PROVED, standard axioms):

* `validateN_sound : validateN objects exe W = true →
    Validated (objects.map Blob.bytes) exe.bytes W`;
* `validate_sound : validate objects exe W = true → Validated objects exe W`;
* `validated_of_chunks`: `validateGlobalN objects exe W = true`
  and `validateChunkN objects exe W c = true` for chunks `c` covering `W.layout` give
  `Validated (objects.map Blob.bytes) exe.bytes W`; `validated_of_parts` is the common core;
* `link_of_sections`: the global guards of `Relocation.link`, resolved relocations, one
  successful `linkSection` per placement and disjoint placements give a successful
  `Relocation.link` (section-wise linking);
* `linkSectionFast_eq : linkSectionFast … = linkSection …` and `foldlM_applyPatch_eq`
  (one-pass patching, via `mergePatches_spec` for offset-sorted patches and
  `applyAll_getElem?` otherwise), `pairwiseFast_iff`;
* `prepare_nil`, `dropSections_nil`, `link_flags`;
* `bytesInN_spec`: the bytewise meaning of the image comparison (data, then a zero tail
  that is free when it lies past the segment's file bytes);
* the opt-in profile: `validatedBy_of_parts`, `validateByN_sound`,
  `validatedBy_of_chunks` (any preparation); `validateProfileN_sound :
  validateProfileN objects exe W = true → ValidatedProfile (objects.map Blob.bytes)
  exe.bytes W`, `validatedProfile_of_chunks`, `piecesIn_of_check`; `validateProfileChunkN_of` and
  `validateProfileN_false_of_chunk` (a failing chunk rejects the whole link); and with the default
  profile, `prepareProfile_default` and `validated_of_profile_default` (`ValidatedProfile`
  gives `Validated`);
* `sectionIn_of_check`, `permsOk_of_check`, `permissions_bits`,
  `mapM_readObject_bytes`.

`Validated objects exe W` says: every object parses with `readObject`; the
executable parses with `ELFImage.parse x86Policy`; the imported x86-64 linker
`Relocation.link` succeeds on `prepare parsed W.dropped` (weak resolution and
discarded sections, see `Silmaril.X86.Link.Validate.Defs`) at `W.layout` with
`W.absolute`; every linked section is `SectionIn` the loaded image (one segment,
byte-exact data then zeros, permissions matching `SHF_WRITE`/`SHF_EXECINSTR`);
and the image's entry point is the linked address of `W.entry`.

`prepare` is the shared profile rewrite `Silmaril.X86.Link.Profile.normalize` (also used
by the executable linker) followed by `dropSections`.

`ValidatedProfile objects exe W` is `Validated` with `prepareProfile W parsed` (the
merged-string rewrite with `W.pieces`, `prepare`, then the opt-in symbol rewrites of
`W.profile`) in place of `prepare parsed W.dropped`, and `PiecesIn`: every piece's string
(through its NUL, from the parsed input section) is byte-exact in a read-only segment.

Not claimed: that the image has nothing else (other loaded bytes, such as the
ELF header or padding, are unconstrained), and anything about `ld` itself.
-/

@[expose] public section

namespace Silmaril.X86.Link.Validate

open Silmaril.Formats.ELF Silmaril.Formats.ELF.Link
open Silmaril.Process.LPS
open Silmaril.X86.Linking

theorem permissions_bits {f : Nat} (h : f < 8) :
    (ELFImage.permissions f).contains 'r' = (f / 4 % 2 == 1) ∧
      (ELFImage.permissions f).contains 'w' = (f / 2 % 2 == 1) ∧
      (ELFImage.permissions f).contains 'x' = (f % 2 == 1) :=
  Proofs.X86.Link.Validate.permissions_bits h

theorem permsOk_of_check {ph : ProgramHeader} {flags : Nat} (hf : ph.flags < 8)
    (h : permsOkN ph.flags flags = true) (file : Bytes) :
    PermsOk (ELFImage.segment file ph) flags :=
  Proofs.X86.Link.Validate.permsOk_of_check hf h file

/-- The bytewise meaning of `bytesInN`. -/
theorem bytesInN_spec {n : Nat} {ph : ProgramHeader} {s : LinkedSection}
    (h : bytesInN n ph s = true) (i : Nat) (hi : i < s.memorySize) :
    (expected s)[i]? = some (segByteN n ph (s.address - ph.virtualAddress + i)) :=
  Proofs.X86.Link.Validate.bytesInN_spec h i hi

/-- One arithmetic check against a parsed `PT_LOAD` header places a linked
section byte-exactly in the loaded image. -/
theorem sectionIn_of_check {policy : ELFImage.Policy} {n len : Nat}
    {records : ELFImage.Records} {ph : ProgramHeader} {s : LinkedSection}
    (hp : ELFImage.parse policy (Blob.bytesOf n len) = some records)
    (hph : ph ∈ records.programHeaders) (hc : sectionInN n ph s = true) :
    SectionIn (records.image (Blob.bytesOf n len)) s :=
  Proofs.X86.Link.Validate.sectionIn_of_check hp hph hc

theorem mapM_readObject_bytes (objects : List Blob) :
    (objects.map Blob.bytes).mapM readObject =
      objects.mapM (fun b => Blob.readObjectN b.n b.len) :=
  Proofs.X86.Link.Validate.mapM_readObject_bytes objects

/-- Dropping no section changes nothing. -/
theorem dropSections_nil (i : Nat) (object : ObjectFile) : dropSections [] i object = object :=
  Proofs.X86.Link.Validate.dropSections_nil i object

/-- With no discarded sections, `prepare` is the shared profile rewrite. -/
theorem prepare_nil (objects : List ObjectFile) : prepare objects [] = Profile.normalize objects :=
  Proofs.X86.Link.Validate.prepare_nil objects

theorem link_flags {objects : List ObjectFile} {layout : Layout} {absolute : AbsoluteSymbols}
    {out : List LinkedSection} (h : Relocation.link objects layout absolute = some out)
    {s : LinkedSection} (hs : s ∈ out) : s.flags = 2 ∨ s.flags = 3 ∨ s.flags = 6 :=
  Proofs.X86.Link.Validate.link_flags h hs

theorem applyAll_getElem? (d : Bytes) (patches : List Patch) (i : Nat) :
    (applyAll d patches)[i]? = d[i]?.map (patchedByte patches i) :=
  Proofs.X86.Link.Validate.applyAll_getElem? d patches i

theorem mergePatches_spec : ∀ {ps : List Patch} {l : List (BitVec 8)} {pos : Nat},
    sortedFrom pos ps = true → (∀ q ∈ ps, q.offset + q.bytes.size ≤ pos + l.length) →
    (mergePatches l pos ps).length = l.length ∧
    ∀ j, (mergePatches l pos ps)[j]? =
      match ps.find? (fun q => decide (Covers q (pos + j))) with
      | some q => q.bytes[pos + j - q.offset]?
      | none => l[j]? :=
  Proofs.X86.Link.Validate.mergePatches_spec

theorem pairwiseFast_iff (patches : List Patch) :
    pairwiseFast patches = true ↔ patches.Pairwise Patch.Disjoint :=
  Proofs.X86.Link.Validate.pairwiseFast_iff patches

/-- **One-pass patching is `foldlM applyPatch`** for pairwise disjoint patches. -/
theorem foldlM_applyPatch_eq {patches : List Patch} {d : Bytes}
    (hpw : patches.Pairwise Patch.Disjoint) :
    patches.foldlM applyPatch d = applyPatches d patches :=
  Proofs.X86.Link.Validate.foldlM_applyPatch_eq hpw

theorem linkSectionFast_eq (objects : List ObjectFile) (relocations : List ResolvedRelocation)
    (relocate : Relocator) (placement : Placement) :
    linkSectionFast objects relocations relocate placement =
      linkSection objects relocations relocate placement :=
  Proofs.X86.Link.Validate.linkSectionFast_eq objects relocations relocate placement

/-- **Section-wise linking.** The global guards, the resolved relocations, one successful
`linkSection` per placement and disjoint placements give a successful `Relocation.link`,
each of whose sections is the `linkSection` of a placement. -/
theorem link_of_sections {objects : List ObjectFile} {layout : Layout}
    {absolute : AbsoluteSymbols} {rels : List ResolvedRelocation}
    (hg : linkGuards objects layout absolute = true)
    (hr : resolveRelocations objects layout absolute = some rels)
    (hs : ∀ pl ∈ layout, ∃ s, linkSection objects rels Relocation.relocate pl = some s)
    (hd : shapesDisjoint objects layout = true) :
    ∃ out, Relocation.link objects layout absolute = some out ∧
      ∀ s ∈ out, ∃ pl ∈ layout, linkSection objects rels Relocation.relocate pl = some s :=
  Proofs.X86.Link.Validate.link_of_sections hg hr hs hd

/-- **Composition of section-wise checks**, for any preparation `prep`. Parsed inputs,
resolved relocations, the global checks, and the per-section check for every placement give
`ValidatedBy prep`. -/
theorem validatedBy_of_parts {prep : List ObjectFile → List ObjectFile}
    {objects : List Blob} {exe : Blob} {W : Witness}
    {parsed : List ObjectFile} {records : ELFImage.Records} {rels : List ResolvedRelocation}
    (hobj : objects.mapM (fun b => Blob.readObjectN b.n b.len) = some parsed)
    (hexe : Blob.parseN ELFImage.x86Policy exe.n exe.len = some records)
    (hrels : resolveRelocations (prep parsed) W.layout W.absolute = some rels)
    (hg : globalOk (prep parsed) records W = true)
    (hs : ∀ pl ∈ W.layout, checkSection exe.n records (prep parsed) rels pl = true) :
    ValidatedBy prep (objects.map Blob.bytes) exe.bytes W :=
  Proofs.X86.Link.Validate.validatedBy_of_parts hobj hexe hrels hg hs

/-- **Composition of section-wise checks.** Parsed inputs, resolved relocations, the
global checks, and the per-section check for every placement give `Validated`. -/
theorem validated_of_parts {objects : List Blob} {exe : Blob} {W : Witness}
    {parsed : List ObjectFile} {records : ELFImage.Records} {rels : List ResolvedRelocation}
    (hobj : objects.mapM (fun b => Blob.readObjectN b.n b.len) = some parsed)
    (hexe : Blob.parseN ELFImage.x86Policy exe.n exe.len = some records)
    (hrels : resolveRelocations (prepare parsed W.dropped) W.layout W.absolute = some rels)
    (hg : globalOk (prepare parsed W.dropped) records W = true)
    (hs : ∀ pl ∈ W.layout, checkSection exe.n records (prepare parsed W.dropped) rels pl = true) :
    Validated (objects.map Blob.bytes) exe.bytes W :=
  Proofs.X86.Link.Validate.validated_of_parts hobj hexe hrels hg hs

/-- Soundness of the blob validator, for any preparation. -/
theorem validateByN_sound {prep : List ObjectFile → List ObjectFile}
    {objects : List Blob} {exe : Blob} {W : Witness}
    (h : validateByN prep objects exe W = true) :
    ValidatedBy prep (objects.map Blob.bytes) exe.bytes W :=
  Proofs.X86.Link.Validate.validateByN_sound h

/-- Soundness of the blob validator. -/
theorem validateN_sound {objects : List Blob} {exe : Blob} {W : Witness}
    (h : validateN objects exe W = true) :
    Validated (objects.map Blob.bytes) exe.bytes W :=
  Proofs.X86.Link.Validate.validateN_sound h

/-- Section-wise validation for any preparation. -/
theorem validatedBy_of_chunks {prep : List ObjectFile → List ObjectFile}
    {objects : List Blob} {exe : Blob} {W : Witness}
    (chunks : List (List Placement)) (hg : validateGlobalByN prep objects exe W = true)
    (hc : ∀ c ∈ chunks, validateChunkByN prep objects exe W c = true)
    (hcover : ∀ pl ∈ W.layout, ∃ c ∈ chunks, pl ∈ c) :
    ValidatedBy prep (objects.map Blob.bytes) exe.bytes W :=
  Proofs.X86.Link.Validate.validatedBy_of_chunks chunks hg hc hcover

/-- **Section-wise validation**: a global check and per-chunk section checks
whose chunks cover the layout give `Validated`. Each chunk is a separate kernel
evaluation, so no single `decide` has to link the whole image. -/
theorem validated_of_chunks {objects : List Blob} {exe : Blob} {W : Witness}
    (chunks : List (List Placement)) (hg : validateGlobalN objects exe W = true)
    (hc : ∀ c ∈ chunks, validateChunkN objects exe W c = true)
    (hcover : ∀ pl ∈ W.layout, ∃ c ∈ chunks, pl ∈ c) :
    Validated (objects.map Blob.bytes) exe.bytes W :=
  Proofs.X86.Link.Validate.validated_of_chunks chunks hg hc hcover

/-- Soundness of the validator on byte arrays. -/
theorem validate_sound {objects : List Bytes} {exe : Bytes} {W : Witness}
    (h : validate objects exe W = true) : Validated objects exe W :=
  Proofs.X86.Link.Validate.validate_sound h

/-- The piece check gives `PiecesIn`. -/
theorem piecesIn_of_check {objects : List Blob} {exe : Blob} {W : Witness}
    {parsed : List ObjectFile} {records : ELFImage.Records}
    (hobj : objects.mapM (fun b => Blob.readObjectN b.n b.len) = some parsed)
    (hexe : Blob.parseN ELFImage.x86Policy exe.n exe.len = some records)
    (h : piecesOk exe.n records parsed W.pieces = true) :
    PiecesIn (objects.map Blob.bytes) exe.bytes W :=
  Proofs.X86.Link.Validate.piecesIn_of_check hobj hexe h

/-- Soundness of the profile-aware validator. -/
theorem validateProfileN_sound {objects : List Blob} {exe : Blob} {W : Witness}
    (h : validateProfileN objects exe W = true) :
    ValidatedProfile (objects.map Blob.bytes) exe.bytes W :=
  Proofs.X86.Link.Validate.validateProfileN_sound h

/-- Section-wise validation with the profile-aware validator. -/
theorem validatedProfile_of_chunks {objects : List Blob} {exe : Blob} {W : Witness}
    (chunks : List (List Placement)) (hg : validateProfileGlobalN objects exe W = true)
    (hc : ∀ c ∈ chunks, validateProfileChunkN objects exe W c = true)
    (hcover : ∀ pl ∈ W.layout, ∃ c ∈ chunks, pl ∈ c) :
    ValidatedProfile (objects.map Blob.bytes) exe.bytes W :=
  Proofs.X86.Link.Validate.validatedProfile_of_chunks chunks hg hc hcover

/-- A chunk of the layout passes when the whole profile-aware validation does. -/
theorem validateProfileChunkN_of {objects : List Blob} {exe : Blob} {W : Witness}
    {chunk : List Placement} (h : validateProfileN objects exe W = true)
    (hsub : ∀ pl ∈ chunk, pl ∈ W.layout) : validateProfileChunkN objects exe W chunk = true :=
  Proofs.X86.Link.Validate.validateProfileChunkN_of h hsub

/-- **Rejection from one chunk**: if a chunk of the layout fails, the whole profile-aware
validation fails. -/
theorem validateProfileN_false_of_chunk {objects : List Blob} {exe : Blob} {W : Witness}
    {chunk : List Placement} (hsub : ∀ pl ∈ chunk, pl ∈ W.layout)
    (h : validateProfileChunkN objects exe W chunk = false) :
    validateProfileN objects exe W = false :=
  Proofs.X86.Link.Validate.validateProfileN_false_of_chunk hsub h

/-- With the default profile, `prepareProfile` is `prepare`. -/
theorem prepareProfile_default {W : Witness} (h : W.profile = {}) (objects : List ObjectFile) :
    prepareProfile W objects = prepare objects W.dropped :=
  Proofs.X86.Link.Validate.prepareProfile_default h objects

/-- With the default profile, the profile-aware meaning is `Validated`. -/
theorem validated_of_profile_default {objects : List Bytes} {exe : Bytes} {W : Witness}
    (h : W.profile = {}) (hv : ValidatedProfile objects exe W) : Validated objects exe W :=
  Proofs.X86.Link.Validate.validated_of_profile_default h hv

end Silmaril.X86.Link.Validate
