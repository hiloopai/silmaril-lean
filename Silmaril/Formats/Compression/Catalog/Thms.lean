module

public import Silmaril.Formats.Compression.Catalog.Defs
public import Silmaril.Formats.Compression.Format.Thms
public import Silmaril.Formats.Compression.Transform.Thms
public import Silmaril.Formats.Compression.Gzip.Thms
public import Silmaril.Formats.Compression.Zlib.Thms
import Silmaril.Proofs.Formats.Compression.Catalog

/-!
# The catalogue of compressed formats: certificates

Proved (standard axioms):

* the catalogue reuses the existing decoders: `deflate_decode_nil`
  (`deflate.decode [] = Deflate.decoder`), `zlib_decode_none`
  (`= Zlib.decoder`), `zlib_decode_some` (`= Zlib.takeWithDictionary`),
  `gzipMember_decode` (`= Gzip.decoder`), `gzipFile_decompress`
  (`Gzip.decompress` is `gzipFile`), `zlib_decompress` (`Zlib.decompress` is
  `Transform.whole zlib` without a dictionary);
* `zlib_decode`: a zlib member is `(zlibFraming dictionary).wrapDep deflate.decode`,
  the header choosing the DEFLATE history;
* `deflate_all`, `zlib_all`, `gzip_all`, `identity_all`: every listed claim
  holds, hence the certificates `deflateCertified`, `zlibCertified`,
  `gzipCertified`, `identityCertified`;
* `identity_not_local`: the identity format is not self-delimiting, which is
  why its certificate omits `local` and member round trips;
* `gzipFile_inverts`, `gzipFile_linear`, `gzip_gzip_inverts`, `gzip_gzip_linear`:
  a gzip file round-trips and is bounded, and so is the chain of two gzip
  codings (`Content-Encoding: gzip, gzip`), with bound `2064 * 2064`.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Catalog

/-! ## The formats are the existing decoders -/

theorem deflate_decode_nil : deflate.decode [] = Deflate.decoder :=
  Proofs.Formats.Compression.Catalog.deflate_decode_nil

theorem zlib_decode (dictionary : Option (List UInt8)) :
    zlib.decode dictionary = (zlibFraming dictionary).wrapDep deflate.decode :=
  Proofs.Formats.Compression.Catalog.zlib_decode dictionary

theorem zlib_decode_none : zlib.decode none = Zlib.decoder :=
  Proofs.Formats.Compression.Catalog.zlib_decode_none

theorem zlib_decode_some (dictionary : List UInt8) :
    zlib.decode (some dictionary) = Zlib.takeWithDictionary dictionary :=
  Proofs.Formats.Compression.Catalog.zlib_decode_some dictionary

theorem gzipMember_decode (p : gzipMember.Params) : gzipMember.decode p = Gzip.decoder :=
  Proofs.Formats.Compression.Catalog.gzipMember_decode p

theorem gzipFile_run (bytes : List UInt8) : gzipFile.run () bytes = Gzip.decoder.members bytes :=
  Proofs.Formats.Compression.Catalog.gzipFile_run bytes

theorem gzipFile_decompress (bytes : ByteArray) :
    Gzip.decompress bytes = (gzipFile.run () bytes.data.toList).map (fun out => ⟨out.toArray⟩) := by
  rw [gzipFile_run, Gzip.decompress_eq]

theorem zlib_decompress (bytes : ByteArray) :
    Zlib.decompress bytes =
      ((Transform.whole zlib).run none bytes.data.toList).map (fun out => ⟨out.toArray⟩) := by
  rw [Zlib.decompress_eq]; exact congrArg _ (congrArg (Decoder.whole · _) zlib_decode_none.symm)

/-! ## Certificates -/

theorem deflate_all : Capability.All deflateClaims := Proofs.Formats.Compression.Catalog.deflate_all

theorem zlib_all : Capability.All zlibClaims := Proofs.Formats.Compression.Catalog.zlib_all

theorem gzip_all : Capability.All gzipClaims := Proofs.Formats.Compression.Catalog.gzip_all

theorem identity_all : Capability.All identityClaims :=
  Proofs.Formats.Compression.Catalog.identity_all

def deflateCertified : Certified deflate := .of deflateClaims deflate_all deflateSecurity

def zlibCertified : Certified zlib := .of zlibClaims zlib_all zlibSecurity

def gzipCertified : Certified gzipMember := .of gzipClaims gzip_all gzipSecurity

def identityCertified : Certified identity := .of identityClaims identity_all identitySecurity

/-- The identity format is not self-delimiting: appended bytes join its member. -/
theorem identity_not_local : ¬ (identity.decode ()).Local :=
  Proofs.Formats.Compression.Catalog.identity_not_local

/-! ## Whole files and chains -/

theorem gzipFile_inverts : gzipFile.Inverts () Gzip.encoder := fun data => by
  rw [gzipFile_run]; exact Gzip.roundTrip.members_single data

theorem gzipFile_linear : gzipFile.LinearAt () 2064 := fun _ _ h => by
  rw [gzipFile_run] at h; exact Gzip.members_output_le h

/-- `Content-Encoding: gzip, gzip` decodes back. -/
theorem gzip_gzip_inverts :
    (gzipFile.andThen gzipFile).Inverts ((), ()) (fun data => Gzip.encoder (Gzip.encoder data)) :=
  Transform.inverts_andThen gzipFile_inverts gzipFile_inverts

theorem gzip_gzip_linear : (gzipFile.andThen gzipFile).LinearAt ((), ()) (2064 * 2064) :=
  Transform.linearAt_andThen gzipFile_linear gzipFile_linear

end Silmaril.Formats.Compression.Catalog
