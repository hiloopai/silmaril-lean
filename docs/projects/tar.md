# tar archives

The POSIX ustar interchange format: 512-byte header records, data padded to
whole records, and a two-record end-of-archive marker, with a proved round trip
between writing and reading archives.

## Definitions

[`Formats/Tar/Defs.lean`](../../Silmaril/Formats/Tar/Defs.lean):

| Concept | Definitions |
| --- | --- |
| Numeric fields | `encodeOctal` (zero-filled octal, NUL-terminated), `decodeOctal` (also leading spaces, `<space>` terminators and GNU base-256), `decodeOctalOrZero` (blank device fields) |
| Pathnames | `splitPath` into `prefix` (≤ 155 bytes) and `name` (≤ 100), at the last `/` that fits; `joinPath` |
| Entries | `Entry` (name, mode, owner, mtime, `TypeFlag`, link name, user and group names, device numbers, data); `Entry.admissible`: what ustar stores without loss |
| Headers | `headerRecord`, `headerChecksum` (byte sum with `chksum` as spaces), `encodeHeader`, `parseHeader` (checks magic and checksum; accepts GNU's `ustar  \0`) |
| Archives | `encode`, `decode` (stops at the first zero record), `blockArchive` (pad to `tar -b` blocks); `encodeArchive`, `decodeArchive` on `ByteArray` |
| `.tar.gz` | `compressGz`, `decompressGz`, through `Compression.Gzip.compress` and `decompress` |

## Results

[`Formats/Tar/Thms.lean`](../../Silmaril/Formats/Tar/Thms.lean), proofs in
`Silmaril/Proofs/Formats/Tar/`:

- `parseHeader_encodeHeader`: a written header reads back as the same entry and
  data size; `encodeHeader_checksum`: its `chksum` field is the POSIX checksum.
- `roundTrip`, `decode_encode_append`: admissible entries are written, and read
  back exactly, whatever follows the end-of-archive marker
  (`decode_blockArchive`).
- `encode_isSome_iff`: `encode` fails exactly when some entry is not admissible;
  it never truncates a name or wraps a number.
- `decodeArchive_encodeArchive`, `decompressGz_compressGz`: the same through
  `ByteArray` and gzip.
- Known answers: the 10240-byte archive GNU tar 1.35 writes for one small file
  (`--format=ustar`, numeric owner) is `blockArchive 20` of `encode`'s output,
  and `decode` reads it back.

Scope: text fields must be UTF-8. pax extended headers and GNU long-name records
are returned as ordinary entries; their records are not applied. Base-256 is
read, never written, so data is limited to `8 ^ 11 - 1` bytes.

## References

- IEEE Std 1003.1-2017 (POSIX.1-2017), `pax`, "ustar Interchange Format":
  <https://pubs.opengroup.org/onlinepubs/9699919799/utilities/pax.html>
- GNU tar manual, "Basic Tar Format":
  <https://www.gnu.org/software/tar/manual/html_node/Standard.html>

## Check

```sh
lake build --wfail Silmaril.Formats.Tar.Thms
```
