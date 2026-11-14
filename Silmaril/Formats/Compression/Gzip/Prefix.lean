module

public import Silmaril.Formats.Compression.Gzip.Basic

/-!
# gzip files with a trailing suffix (suffix-lenient profile)

`gzipDecompress` is the RFC 1952 §2.2 file: one or more members and nothing
else. Real tools are more lenient about bytes after the last member, in
different ways. Observed with GNU gzip 1.13 and zlib 1.3.1 on a member followed
by a suffix:

* GNU gzip (`gzip -d`): a suffix not starting with the gzip magic `1f 8b` is
  ignored with the warning "decompression OK, trailing garbage ignored" (exit
  status 2), or silently if it is all zero bytes; a suffix starting with the
  magic is decoded as a further member, and a failure there is an error; a
  one-byte suffix is an error ("unexpected end of file");
* zlib's `gzread` (`gz_look` in `gzread.c`): a suffix not starting with the
  magic ends the file without an error ("trailing garbage" is ignored); a suffix
  starting with the magic is decoded as a member, and a corrupt one is an error.

`decompressPrefix` is the simplest lenient profile: it decodes one member, then
further members as long as one decodes, and returns the concatenated output with
the first suffix at which no member decodes. It agrees with the tools above
whenever the suffix does not start with `1f 8b` (for GNU gzip, also not a
single byte); on a suffix that starts with the magic but is not a valid member,
the tools report an error while `decompressPrefix` returns it as the suffix. A
consumer modelling those tools can reject results whose suffix starts with
`1f 8b`.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Gzip

/-- Decode members greedily after the first, appending to `acc`; stop at the
first suffix where no member decodes. `fuel` bounds the number of members. -/
def membersPrefix : Nat → List UInt8 → List UInt8 → List UInt8 × List UInt8
  | 0, bs, acc => (acc, bs)
  | fuel + 1, bs, acc =>
    match gzipMember bs with
    | none => (acc, bs)
    | some (data, rest) => membersPrefix fuel rest (acc ++ data)

/-- **Suffix-lenient gzip file decoder**: at least one member, then as many
further members as decode; returns the output and the remaining bytes. -/
def decompressPrefix (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  match gzipMember bs with
  | none => none
  | some (data, rest) => some (membersPrefix (rest.length + 1) rest data)

end Silmaril.Formats.Compression.Gzip
