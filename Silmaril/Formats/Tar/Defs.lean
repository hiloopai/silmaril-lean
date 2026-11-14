module

public import Silmaril.Formats.Compression.Gzip.Defs

/-!
# tar archives (POSIX ustar)

The ustar interchange format of POSIX.1-2017 (`pax`, "ustar Interchange
Format"). An archive is a sequence of members, each a 512-byte header record
followed by the member's data padded with NULs to a multiple of 512 bytes, and
ends with two zero-filled records.

The header record:

| offset | width | field      | offset | width | field      |
|--------|-------|------------|--------|-------|------------|
| 0      | 100   | `name`     | 257    | 6     | `magic`    |
| 100    | 8     | `mode`     | 263    | 2     | `version`  |
| 108    | 8     | `uid`      | 265    | 32    | `uname`    |
| 116    | 8     | `gid`      | 297    | 32    | `gname`    |
| 124    | 12    | `size`     | 329    | 8     | `devmajor` |
| 136    | 12    | `mtime`    | 337    | 8     | `devminor` |
| 148    | 8     | `chksum`   | 345    | 155   | `prefix`   |
| 156    | 1     | `typeflag` | 500    | 12    | (padding)  |
| 157    | 100   | `linkname` |        |       |            |

* **Numeric fields** are zero-filled octal numbers terminated by NUL or
  `<space>` (`encodeOctal`, `decodeOctal`). The reader also accepts leading
  spaces (historic writers) and GNU tar's base-256 form (leading byte `0x80`,
  then big-endian bytes); the writer only writes octal.
* **The checksum** is "the simple sum of all octets in the header logical
  record", with the `chksum` field counted as eight `<space>`s
  (`headerChecksum`). `parseHeader` verifies it.
* **Pathnames** up to 256 bytes are split at a `/` into `prefix` (at most 155
  bytes) and `name` (at most 100); the pathname is
  `prefix ++ "/" ++ name` when `prefix` is non-empty (`splitPath`, `joinPath`).
  The writer splits at the last `/` that fits (the longest prefix).
* **Magic**: `parseHeader` accepts POSIX's `ustar\0` + `00` and GNU tar's
  `ustar  \0`; `encodeHeader` writes the POSIX form.

`encode` returns `none` for an entry ustar cannot represent
(`Entry.admissible`) rather than truncating a name or wrapping a number.
`decode` verifies every header's magic and checksum, reads the data, and stops
at the first zero-filled record, so any bytes after the end-of-archive marker
(such as `blockArchive` padding) are ignored.

Scope: names are `String`s, so a header whose text fields are not UTF-8 is
rejected. pax extended headers (`typeflag` `x`, `g`) and vendor extensions
(GNU `L`, `K`, …) are returned as ordinary entries with their raw data; their
records are not applied to the following entry. Base-256 numbers are read but
never written, so file sizes are limited to `8 ^ 11 - 1` bytes.

## References

* IEEE Std 1003.1-2017 (POSIX.1-2017), `pax`, section "ustar Interchange
  Format", <https://pubs.opengroup.org/onlinepubs/9699919799/utilities/pax.html>.
* GNU tar manual, "Basic Tar Format",
  <https://www.gnu.org/software/tar/manual/html_node/Standard.html>.
-/

@[expose] public section

namespace Silmaril.Formats.Tar

/-! ## Numeric fields -/

/-- `b` is an ASCII octal digit `0`–`7`. -/
def isOctalDigit (b : UInt8) : Bool := 0x30 ≤ b.toNat ∧ b.toNat ≤ 0x37

/-- `b` is NUL or `<space>`: a numeric-field terminator. -/
def isPadByte (b : UInt8) : Bool := b.toNat = 0 ∨ b.toNat = 0x20

/-- `b` is not NUL. -/
def nonNul (b : UInt8) : Bool := b.toNat ≠ 0

/-- The ASCII digit of `d < 8`. -/
def octalDigit (d : Nat) : UInt8 := UInt8.ofNat (0x30 + d)

/-- The `k` low-order octal digits of `n`, most significant first. -/
def octalDigits (n : Nat) : Nat → List UInt8
  | 0 => []
  | k + 1 => octalDigits (n / 8) k ++ [octalDigit (n % 8)]

/-- The value of a string of ASCII octal digits. -/
def octalValue (digits : List UInt8) : Nat :=
  digits.foldl (fun acc b => acc * 8 + (b.toNat - 0x30)) 0

/-- The value of big-endian base-256 bytes. -/
def base256Value (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- A `width`-byte field holds `width - 1` octal digits and a NUL. -/
def fitsOctal (value width : Nat) : Bool := value < 8 ^ (width - 1)

/-- A `width`-byte numeric field: `width - 1` zero-filled octal digits and a NUL.
Only meaningful when `fitsOctal value width`; otherwise the value is reduced
modulo `8 ^ (width - 1)`. -/
def encodeOctal (value width : Nat) : List UInt8 :=
  if width = 0 then [] else octalDigits value (width - 1) ++ [0]

/-- Read a numeric field: optional leading `<space>`s, at least one octal digit,
then only NULs and `<space>`s; or GNU base-256 (leading byte `0x80`). -/
def decodeOctal (field : List UInt8) : Option Nat :=
  match field with
  | [] => none
  | b :: rest =>
    if b = 0x80 then some (base256Value rest)
    else if 0x80 ≤ b.toNat then none
    else
      let body := field.dropWhile (· == 0x20)
      let digits := body.takeWhile isOctalDigit
      if digits.isEmpty then none
      else if (body.dropWhile isOctalDigit).all isPadByte then some (octalValue digits)
      else none

/-- Like `decodeOctal`, but a blank field (only NULs and `<space>`s) reads as 0.
POSIX leaves `devmajor` and `devminor` unspecified except for device nodes, and
GNU tar leaves them all-NUL. -/
def decodeOctalOrZero (field : List UInt8) : Option Nat :=
  if field.all isPadByte then some 0 else decodeOctal field

/-! ## Text fields -/

/-- The UTF-8 bytes of a string. -/
def utf8 (s : String) : List UInt8 := s.toUTF8.data.toList

/-- Truncate or NUL-pad to exactly `n` bytes. -/
def padTo (bytes : List UInt8) (n : Nat) : List UInt8 :=
  bytes.take n ++ List.replicate (n - bytes.length) 0

/-- The contents of a NUL-terminated (or full) field. -/
def fieldBytes (field : List UInt8) : List UInt8 := field.takeWhile nonNul

/-- Read a text field as UTF-8. -/
def readText (bytes : List UInt8) : Option String := String.fromUTF8? bytes.toByteArray

/-! ## Entries -/

/-- The `typeflag` values: POSIX's file types, the pax extended headers, and
any other byte kept verbatim. -/
inductive TypeFlag where
  /-- `'0'`, or NUL (historic): regular file. -/
  | regular
  /-- `'1'`: hard link. -/
  | hardLink
  /-- `'2'`: symbolic link. -/
  | symLink
  /-- `'3'`: character special file. -/
  | charSpecial
  /-- `'4'`: block special file. -/
  | blockSpecial
  /-- `'5'`: directory. -/
  | directory
  /-- `'6'`: FIFO. -/
  | fifo
  /-- `'7'`: reserved; contiguous file. -/
  | contiguous
  /-- `'x'`: pax extended header for the next entry. -/
  | paxExtended
  /-- `'g'`: pax global extended header. -/
  | paxGlobal
  /-- Any other byte (vendor extensions). -/
  | other (c : UInt8)
  deriving DecidableEq

def TypeFlag.toByte : TypeFlag → UInt8
  | .regular => 0x30
  | .hardLink => 0x31
  | .symLink => 0x32
  | .charSpecial => 0x33
  | .blockSpecial => 0x34
  | .directory => 0x35
  | .fifo => 0x36
  | .contiguous => 0x37
  | .paxExtended => 0x78
  | .paxGlobal => 0x67
  | .other c => c

/-- POSIX: a `typeflag` of NUL "should be recognized as meaning a regular file
when extracting"; `'0'` is written. -/
def TypeFlag.ofByte (b : UInt8) : TypeFlag :=
  if b = 0x30 ∨ b = 0 then .regular
  else if b = 0x31 then .hardLink
  else if b = 0x32 then .symLink
  else if b = 0x33 then .charSpecial
  else if b = 0x34 then .blockSpecial
  else if b = 0x35 then .directory
  else if b = 0x36 then .fifo
  else if b = 0x37 then .contiguous
  else if b = 0x78 then .paxExtended
  else if b = 0x67 then .paxGlobal
  else .other b

/-- Whether data may follow the header. POSIX: links, directories, FIFOs and
device nodes have no data, and their `size` is ignored. -/
def TypeFlag.carriesData : TypeFlag → Bool
  | .regular | .contiguous | .paxExtended | .paxGlobal | .other _ => true
  | _ => false

/-- Whether `devmajor` and `devminor` are meaningful. -/
def TypeFlag.isDevice : TypeFlag → Bool
  | .charSpecial | .blockSpecial => true
  | _ => false

/-- An archive member. The header's `size` field is the length of `data`. -/
structure Entry where
  /-- The pathname, stored in `prefix` and `name`. -/
  name : String
  mode : Nat := 0
  uid : Nat := 0
  gid : Nat := 0
  mtime : Nat := 0
  typeflag : TypeFlag := .regular
  linkname : String := ""
  uname : String := ""
  gname : String := ""
  devmajor : Nat := 0
  devminor : Nat := 0
  data : List UInt8 := []
  deriving DecidableEq

/-! ## Pathnames -/

/-- The positions of `/` at which `path` can be split into a non-empty prefix
of at most 155 bytes and a non-empty name of at most 100. -/
def splitPoints (path : List UInt8) : List Nat :=
  (List.range (min 156 path.length)).filter fun i =>
    0 < i && path[i]? == some 0x2F && 0 < path.length - (i + 1) && path.length - (i + 1) ≤ 100

/-- Split a pathname into `(prefix, name)`: unsplit when it fits `name`, else at
the last legal `/`. `none` when it cannot be stored. -/
def splitPath (path : List UInt8) : Option (List UInt8 × List UInt8) :=
  if path.length ≤ 100 then some ([], path)
  else (splitPoints path).getLast?.map fun i => (path.take i, path.drop (i + 1))

/-- POSIX: a non-empty `prefix`, a `/`, then `name`. -/
def joinPath (pre name : List UInt8) : List UInt8 :=
  if pre.isEmpty then name else pre ++ 0x2F :: name

/-- What ustar can store without loss: a non-empty, NUL-free pathname that
`splitPath` can split; NUL-free `linkname`, `uname`, `gname` within 100, 32 and
32 bytes; every number within its octal field (`size` and `mtime` below
`8 ^ 11`, the others below `8 ^ 7`); a type flag that reads back as itself
(not `other` of a known flag byte); data only for types that carry data; device
numbers only for device nodes. -/
def Entry.admissible (e : Entry) : Bool :=
  (splitPath (utf8 e.name)).isSome && (utf8 e.name).all nonNul && !(utf8 e.name).isEmpty &&
  (utf8 e.linkname).length ≤ 100 && (utf8 e.linkname).all nonNul &&
  (utf8 e.uname).length ≤ 32 && (utf8 e.uname).all nonNul &&
  (utf8 e.gname).length ≤ 32 && (utf8 e.gname).all nonNul &&
  fitsOctal e.mode 8 && fitsOctal e.uid 8 && fitsOctal e.gid 8 &&
  fitsOctal e.devmajor 8 && fitsOctal e.devminor 8 &&
  fitsOctal e.mtime 12 && fitsOctal e.data.length 12 &&
  TypeFlag.ofByte e.typeflag.toByte == e.typeflag &&
  (e.typeflag.carriesData || e.data.isEmpty) &&
  (e.typeflag.isDevice || (e.devmajor == 0 && e.devminor == 0))

/-! ## Header records -/

/-- The header checksum of a 512-byte record: the sum of its bytes, with the
`chksum` field (offsets 148–155) counted as eight `<space>`s. -/
def headerChecksum (record : List UInt8) : Nat :=
  ((record.take 148).map UInt8.toNat).sum + 8 * 0x20 + ((record.drop 156).map UInt8.toNat).sum

def ustarMagic : List UInt8 := [0x75, 0x73, 0x74, 0x61, 0x72, 0x00]  -- "ustar\0"
def ustarVersion : List UInt8 := [0x30, 0x30]                        -- "00"

/-- POSIX ustar, or GNU tar's `ustar  \0` across `magic` and `version`. -/
def isUstarMagic (magic version : List UInt8) : Bool :=
  (magic == ustarMagic && version == ustarVersion) ||
  (magic == [0x75, 0x73, 0x74, 0x61, 0x72, 0x20] && version == [0x20, 0x00])

/-- A device number field: octal for device nodes, all-NUL otherwise. -/
def deviceField (t : TypeFlag) (v : Nat) : List UInt8 :=
  if t.isDevice then encodeOctal v 8 else List.replicate 8 0

/-- The `chksum` field as tar writers lay it out: six octal digits, NUL,
`<space>`. -/
def checksumField (chk : Nat) : List UInt8 := encodeOctal chk 7 ++ [0x20]

/-- The 512-byte record of `e` with pathname split `(pre, name)` and `chksum`
field `chk`. -/
def headerRecord (e : Entry) (pre name chk : List UInt8) : List UInt8 :=
  padTo name 100 ++ encodeOctal e.mode 8 ++ encodeOctal e.uid 8 ++ encodeOctal e.gid 8 ++
  encodeOctal e.data.length 12 ++ encodeOctal e.mtime 12 ++
  chk ++
  [e.typeflag.toByte] ++ padTo (utf8 e.linkname) 100 ++ ustarMagic ++ ustarVersion ++
  padTo (utf8 e.uname) 32 ++ padTo (utf8 e.gname) 32 ++
  deviceField e.typeflag e.devmajor ++ deviceField e.typeflag e.devminor ++
  padTo pre 155 ++ List.replicate 12 0

/-- The header of `e`, or `none` when `e` is not `admissible`. The checksum is
computed with the `chksum` field blank, exactly as POSIX defines it. -/
def encodeHeader (e : Entry) : Option (List UInt8) :=
  if e.admissible then
    (splitPath (utf8 e.name)).map fun (pre, name) =>
      headerRecord e pre name
        (checksumField (headerChecksum (headerRecord e pre name (List.replicate 8 0x20))))
  else none

/-- Read a 512-byte header record: the entry (with no data) and the declared
data size. Checks the magic and the checksum. -/
def parseHeader (record : List UInt8) : Option (Entry × Nat) := do
  guard (record.length = 512)
  let field (off len : Nat) := (record.drop off).take len
  guard (isUstarMagic (field 257 6) (field 263 2))
  let mode ← decodeOctal (field 100 8)
  let uid ← decodeOctal (field 108 8)
  let gid ← decodeOctal (field 116 8)
  let size ← decodeOctal (field 124 12)
  let mtime ← decodeOctal (field 136 12)
  let chk ← decodeOctal (field 148 8)
  let devmajor ← decodeOctalOrZero (field 329 8)
  let devminor ← decodeOctalOrZero (field 337 8)
  guard (chk = headerChecksum record)
  let name ← readText (joinPath (fieldBytes (field 345 155)) (fieldBytes (field 0 100)))
  let linkname ← readText (fieldBytes (field 157 100))
  let uname ← readText (fieldBytes (field 265 32))
  let gname ← readText (fieldBytes (field 297 32))
  let typeflag := TypeFlag.ofByte ((record.drop 156).headD 0)
  return ({ name, mode, uid, gid, mtime, typeflag, linkname, uname, gname, devmajor,
            devminor }, size)

/-! ## Archives -/

/-- Round up to a multiple of 512. -/
def roundUp512 (n : Nat) : Nat := (n + 511) / 512 * 512

/-- NUL-pad to a multiple of 512 bytes. -/
def padRecord (bytes : List UInt8) : List UInt8 :=
  bytes ++ List.replicate (roundUp512 bytes.length - bytes.length) 0

/-- The end-of-archive marker: two zero-filled records. -/
def endMarker : List UInt8 := List.replicate 1024 0

/-- Write an archive, or `none` when some entry is not `admissible`. -/
def encode : List Entry → Option (List UInt8)
  | [] => some endMarker
  | e :: es => do
    let header ← encodeHeader e
    let rest ← encode es
    return header ++ padRecord e.data ++ rest

/-- Read an archive: members up to the first zero-filled record. `none` on a
bad header or truncated data. -/
def decode (bytes : List UInt8) : Option (List Entry) :=
  if bytes.length < 512 then none
  else if (bytes.take 512).all (· == 0) then some []
  else do
    let (e, size) ← parseHeader (bytes.take 512)
    let body := bytes.drop 512
    if body.length < roundUp512 size then none
    else
      let es ← decode (body.drop (roundUp512 size))
      return { e with data := body.take size } :: es
termination_by bytes.length

/-- Pad an archive to whole blocks of `factor` records, as `tar -b factor`
writes to a device (GNU tar's default factor is 20). -/
def blockArchive (factor : Nat) (bytes : List UInt8) : List UInt8 :=
  let unit := factor * 512
  if unit = 0 then bytes
  else bytes ++ List.replicate ((bytes.length + unit - 1) / unit * unit - bytes.length) 0

/-- `encode` on `ByteArray`. -/
def encodeArchive (es : List Entry) : Option ByteArray := (encode es).map List.toByteArray

/-- `decode` on `ByteArray`. -/
def decodeArchive (bytes : ByteArray) : Option (List Entry) := decode bytes.data.toList

/-! ## Compressed archives -/

/-- A `.tar.gz` file: the archive as one gzip member (stored DEFLATE blocks). -/
def compressGz (es : List Entry) : Option ByteArray :=
  (encodeArchive es).map Compression.Gzip.compress

/-- Read a `.tar.gz` file (one or more gzip members). -/
def decompressGz (bytes : ByteArray) : Option (List Entry) :=
  (Compression.Gzip.decompress bytes).bind decodeArchive

end Silmaril.Formats.Tar
