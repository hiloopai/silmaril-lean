module

public import Silmaril.Machine.Link.Validate.Defs
public import Silmaril.Machine.Link.Blob.Thms
public import Silmaril.Proofs.Machine.Link.Validate

/-! # Translation validation of static links: theorems (header)

`Silmaril.Proofs.Machine.Link.Validate` (PROVED, standard axioms):

* `validateN_sound : validateN objects exe W = true →
    Validated (objects.map Blob.bytes) exe.bytes W`;
* `validate_sound : validate objects exe W = true → Validated objects exe W`;
* `validated_of_chunks` (F3; REVIEW M13): `validateGlobalN objects exe W = true`
  and `validateChunkN objects exe W c = true` for chunks `c` covering `W.layout` give
  `Validated (objects.map Blob.bytes) exe.bytes W`; `validated_of_parts` is the common core;
* `link_of_sections`: the global guards of `Relocation.link`, resolved relocations, one
  successful `linkSection` per placement and disjoint placements give a successful
  `Relocation.link` (section-wise linking);
* `linkSectionFast_eq : linkSectionFast … = linkSection …` and `foldlM_applyPatch_eq`
  (one-pass patching, via `mergePatches_spec` for offset-sorted patches and
  `applyAll_getElem?` otherwise), `pairwiseFast_iff`;
* `prepare_nil`, `dropSections_nil`, `link_flags` (used by `Exe.run_validated`);
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
discarded sections, see `Silmaril.Machine.Link.Validate.Defs`) at `W.layout` with
`W.absolute`; every linked section is `SectionIn` the loaded image (one segment,
byte-exact data then zeros, permissions matching `SHF_WRITE`/`SHF_EXECINSTR`);
and the image's entry point is the linked address of `W.entry`.

`prepare` is the shared profile rewrite `Silmaril.Machine.Link.Profile.normalize` (also used
by the executable linker) followed by `dropSections`.

`ValidatedProfile objects exe W` is `Validated` with `prepareProfile W parsed` (the
merged-string rewrite with `W.pieces`, `prepare`, then the opt-in symbol rewrites of
`W.profile`) in place of `prepare parsed W.dropped`, and `PiecesIn`: every piece's string
(through its NUL, from the parsed input section) is byte-exact in a read-only segment.

Not claimed: that the image has nothing else (other loaded bytes, such as the
ELF header or padding, are unconstrained), and anything about `ld` itself.
Generated fixtures: `Silmaril.Machine.Link.Fixtures.*`.
-/
