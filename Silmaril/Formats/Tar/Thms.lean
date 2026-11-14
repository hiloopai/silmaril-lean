module

public import Silmaril.Formats.Tar.Defs
public import Silmaril.Formats.Compression.Gzip.Thms
import Silmaril.Proofs.Formats.Tar.Archive

/-!
# tar archives: facts

Proved (standard axioms):

* numeric fields: `decodeOctal_encodeOctal` (every value that fits its field
  reads back), `encodeOctal_length`;
* pathnames: `splitPath_spec` (a split pathname rejoins to the original and fits
  `prefix` and `name`);
* headers: `parseHeader_encodeHeader` (the header round trip: every field of an
  entry reads back), `encodeHeader_checksum` (the `chksum` field holds the POSIX
  checksum of the record), `encodeHeader_length`, `encodeHeader_isSome` and
  `encodeHeader_eq_none` (exactly the admissible entries are written);
* archives: `decode_encode_append` (an archive decodes to its entries, whatever
  follows the end-of-archive marker), `decode_encode`, `roundTrip`,
  `encode_isSome_iff`, `encode_length` (whole records), `decode_blockArchive`;
* `decodeArchive_encodeArchive`, `decompressGz_compressGz`: the same through
  `ByteArray` and gzip;
* known answers: the header and archive GNU tar 1.35 writes for a 6-byte file
  `hello.txt` (`tar --format=ustar --owner=0 --group=0 --numeric-owner
  --mtime=@1700000000`, mode `0644`) are exactly what `encode` writes, padded to
  GNU tar's default blocking factor of 20 records, and read back.
-/

@[expose] public section

namespace Silmaril.Formats.Tar

/-! ## Numeric fields -/

@[simp] theorem encodeOctal_length (v w : Nat) : (encodeOctal v w).length = w :=
  Proofs.Formats.Tar.encodeOctal_length v w

theorem decodeOctal_encodeOctal {v w : Nat} (hw : 2 ≤ w) (hv : fitsOctal v w) :
    decodeOctal (encodeOctal v w) = some v :=
  Proofs.Formats.Tar.decodeOctal_encodeOctal hw (by simpa [fitsOctal] using hv)

/-- GNU tar writes `mode` 0644 as `0000644\0`. -/
theorem decodeOctal_mode : decodeOctal [0x30, 0x30, 0x30, 0x30, 0x36, 0x34, 0x34, 0] = some 0o644 := by
  decide
/-- Historic writers pad on the left with spaces and terminate with `<space>`. -/
theorem decodeOctal_spaces : decodeOctal [0x20, 0x20, 0x36, 0x34, 0x34, 0x20, 0, 0] = some 0o644 := by
  decide
/-- GNU base-256: `80` then big-endian bytes. -/
theorem decodeOctal_base256 :
    decodeOctal [0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0x02, 0, 0] = some (2 * 2 ^ 16) := by decide
theorem decodeOctal_blank : decodeOctal [0x20, 0, 0, 0] = none := by decide
theorem decodeOctal_junk : decodeOctal [0x36, 0x38, 0] = none := by decide

/-! ## Pathnames and headers -/

theorem splitPath_spec {path pre name : List UInt8} (h : splitPath path = some (pre, name)) :
    joinPath pre name = path ∧ name.length ≤ 100 ∧ pre.length ≤ 155 ∧
      (∀ b ∈ pre, b ∈ path) ∧ (∀ b ∈ name, b ∈ path) :=
  Proofs.Formats.Tar.splitPath_spec h

theorem encodeHeader_isSome {e : Entry} (h : e.admissible = true) : (encodeHeader e).isSome :=
  Proofs.Formats.Tar.encodeHeader_isSome h

theorem encodeHeader_eq_none {e : Entry} (h : e.admissible = false) : encodeHeader e = none :=
  Proofs.Formats.Tar.encodeHeader_eq_none h

theorem encodeHeader_length {e : Entry} {h : List UInt8} (he : encodeHeader e = some h) :
    h.length = 512 :=
  Proofs.Formats.Tar.encodeHeader_length he

/-- The `chksum` field (offsets 148–155) of a written header holds its POSIX
checksum. -/
theorem encodeHeader_checksum {e : Entry} {h : List UInt8} (he : encodeHeader e = some h) :
    decodeOctal ((h.drop 148).take 8) = some (headerChecksum h) :=
  Proofs.Formats.Tar.encodeHeader_checksum he

/-- **The header round trip**: `parseHeader` reads back every field of the
entry, and its data size. -/
theorem parseHeader_encodeHeader {e : Entry} {h : List UInt8} (he : encodeHeader e = some h) :
    parseHeader h = some ({ e with data := [] }, e.data.length) :=
  Proofs.Formats.Tar.parseHeader_encodeHeader he

/-! ## Archives -/

/-- `encode` succeeds exactly when every entry is admissible. -/
theorem encode_isSome_iff (es : List Entry) :
    (encode es).isSome ↔ ∀ e ∈ es, e.admissible = true :=
  Proofs.Formats.Tar.encode_isSome_iff es

/-- An archive is a whole number of 512-byte records. -/
theorem encode_length {es : List Entry} {bs : List UInt8} (h : encode es = some bs) :
    bs.length % 512 = 0 :=
  Proofs.Formats.Tar.encode_length h

/-- **The archive round trip**, whatever follows the end-of-archive marker. -/
theorem decode_encode_append {es : List Entry} {bs : List UInt8} (h : encode es = some bs)
    (tail : List UInt8) : decode (bs ++ tail) = some es :=
  Proofs.Formats.Tar.decode_encode_append h tail

theorem decode_encode {es : List Entry} {bs : List UInt8} (h : encode es = some bs) :
    decode bs = some es :=
  Proofs.Formats.Tar.decode_encode h

/-- Admissible entries are written, and read back exactly. -/
theorem roundTrip {es : List Entry} (h : ∀ e ∈ es, e.admissible = true) :
    ∃ bs, encode es = some bs ∧ decode bs = some es := by
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp ((encode_isSome_iff es).mpr h)
  exact ⟨bs, hbs, decode_encode hbs⟩

theorem decode_blockArchive {es : List Entry} {bs : List UInt8} (h : encode es = some bs)
    (factor : Nat) : decode (blockArchive factor bs) = some es :=
  Proofs.Formats.Tar.decode_blockArchive h factor

theorem decodeArchive_encodeArchive {es : List Entry} {bs : ByteArray}
    (h : encodeArchive es = some bs) : decodeArchive bs = some es :=
  Proofs.Formats.Tar.decodeArchive_encodeArchive h

theorem decompressGz_compressGz {es : List Entry} {gz : ByteArray}
    (h : compressGz es = some gz) : decompressGz gz = some es :=
  Proofs.Formats.Tar.decompressGz_compressGz h

/-! ## Known answers -/

/-- The bytes of an ASCII string. -/
def ascii (s : String) : List UInt8 := s.toList.map fun c => c.toNat.toUInt8

/-- The entry: `hello.txt`, mode `0644`, owner and group 0, the 6 bytes `hello\n`. -/
def helloEntry : Entry :=
  { name := "hello.txt", mode := 0o644, mtime := 1700000000,
    data := [0x68, 0x65, 0x6C, 0x6C, 0x6F, 0x0A] }

/-- The header record GNU tar 1.35 writes for `helloEntry`. -/
def gnuHelloHeader : List UInt8 :=
  ascii "hello.txt" ++ List.replicate 91 0 ++
  ascii "0000644" ++ [0] ++ ascii "0000000" ++ [0] ++ ascii "0000000" ++ [0] ++
  ascii "00000000006" ++ [0] ++ ascii "14524770400" ++ [0] ++
  ascii "007647" ++ [0] ++ ascii " 0" ++ List.replicate 100 0 ++
  ascii "ustar" ++ [0] ++ ascii "00" ++ List.replicate 247 0

/-- GNU tar's whole archive: the header, the data padded to a record, and zero
records up to its 10240-byte block. -/
def gnuHelloArchive : List UInt8 :=
  gnuHelloHeader ++ helloEntry.data ++ List.replicate (10240 - 512 - 6) 0

theorem encodeHeader_hello : encodeHeader helloEntry = some gnuHelloHeader := by decide +kernel

theorem encode_hello : (encode [helloEntry]).map (blockArchive 20) = some gnuHelloArchive := by
  decide +kernel

theorem decode_gnuHello : decode gnuHelloArchive = some [helloEntry] := by decide +kernel

end Silmaril.Formats.Tar
