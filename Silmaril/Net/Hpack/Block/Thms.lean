module

public import Silmaril.Net.Hpack.Block.Defs
public import Silmaril.Net.Hpack.Table.Thms
import Silmaril.Proofs.Net.Hpack.Block

@[expose] public section

/-!
# HPACK field representations: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Hpack/Block.lean`):

* `decodeRep_encodeRep`: every well-formed representation (§6) is read back from its
  serialization, and the reader stops exactly after it; so the first-octet dispatch of §6 is
  unambiguous for the five representation kinds;
* `decodeReps_encodeReps`: a field block of well-formed representations round trips;
* `processRepsFrom_valid`, `decodeBlock_valid`: decoding a field block keeps the dynamic table
  within its maximum and the maximum within the protocol limit (§4.2, §7.3), whatever octets
  the peer sends;
* `processRep_literal_noindex`: literals without indexing and never-indexed literals (§6.2.2,
  §6.2.3) do not change the dynamic table.

CHECKED by evaluation: the field blocks of RFC 7541 Appendix C.2 and C.3 (without Huffman
coding): decoded fields and dynamic table sizes.
-/

namespace Silmaril.Net.Hpack

theorem decodeRep_encodeRep (r : Rep) (hwf : r.WellFormed) (rest : List UInt8) :
    decodeRep (encodeRep r ++ rest) = some (r, rest) :=
  Silmaril.Proofs.Net.Hpack.decodeRep_encodeRep r hwf rest

theorem decodeReps_encodeReps (rs : List Rep) (hwf : ∀ r ∈ rs, r.WellFormed) :
    decodeReps (encodeReps rs) = some rs :=
  Silmaril.Proofs.Net.Hpack.decodeReps_encodeReps rs hwf

theorem processRepsFrom_valid {seen : Bool} {t : DynTable} (ht : t.Valid) {rs : List Rep}
    {es : List Entry} {t' : DynTable} (h : processRepsFrom seen t rs = some (es, t')) :
    t'.Valid :=
  Silmaril.Proofs.Net.Hpack.processRepsFrom_valid ht h

theorem decodeBlock_valid {t : DynTable} (ht : t.Valid) {xs : List UInt8} {es : List Entry}
    {t' : DynTable} (h : decodeBlock t xs = some (es, t')) : t'.Valid := by
  unfold decodeBlock at h; split at h
  · cases h
  · exact processRepsFrom_valid ht h

theorem processRep_literal_noindex {t : DynTable} {ix : Indexing} (hix : ix ≠ .incremental)
    {nr : NameRef} {v : List UInt8} {e? : Option Entry} {t' : DynTable}
    (h : processRep t (.literal ix nr v) = some (e?, t')) : t' = t :=
  Silmaril.Proofs.Net.Hpack.processRep_literal_noindex hix h

/-! ## RFC 7541 Appendix C (raw string literals) -/

/-- The fields and dynamic table size after decoding `xs` from `t`. -/
def decodeSummary (t : DynTable) (xs : List UInt8) : Option (List Entry × Nat) :=
  (decodeBlock t xs).map fun (es, t') => (es, tableSize t'.entries)

/-- C.2.1: literal with indexing, `custom-key: custom-header`; table size 55. -/
example : decodeSummary (.empty 4096)
    ([0x40, 0x0a] ++ ascii "custom-key" ++ [0x0d] ++ ascii "custom-header") =
    some ([Entry.ofStrings "custom-key" "custom-header"], 55) := by decide +kernel

/-- C.2.2: literal without indexing, `:path: /sample/path`; the table stays empty. -/
example : decodeSummary (.empty 4096) ([0x04, 0x0c] ++ ascii "/sample/path") =
    some ([Entry.ofStrings ":path" "/sample/path"], 0) := by decide +kernel

/-- C.2.3: never-indexed literal, `password: secret`; the table stays empty. -/
example : decodeSummary (.empty 4096)
    ([0x10, 0x08] ++ ascii "password" ++ [0x06] ++ ascii "secret") =
    some ([Entry.ofStrings "password" "secret"], 0) := by decide +kernel

/-- C.2.4: indexed field `0x82`, `:method: GET`. -/
example : decodeSummary (.empty 4096) [0x82] = some ([Entry.ofStrings ":method" "GET"], 0) := by
  decide +kernel

/-- C.3.1: the first request; the table holds `:authority: www.example.com` (size 57). -/
def c31 : List UInt8 := [0x82, 0x86, 0x84, 0x41, 0x0f] ++ ascii "www.example.com"

example : decodeSummary (.empty 4096) c31 =
    some ([Entry.ofStrings ":method" "GET", Entry.ofStrings ":scheme" "http",
      Entry.ofStrings ":path" "/", Entry.ofStrings ":authority" "www.example.com"], 57) := by
  decide +kernel

/-- C.3.2: the second request on the same connection reuses index 62 (`0xbe`) and adds
`cache-control: no-cache` (table size 110). -/
def c32 : List UInt8 := [0x82, 0x86, 0x84, 0xbe, 0x58, 0x08] ++ ascii "no-cache"

example : ((decodeBlock (.empty 4096) c31).bind fun (_, t) => decodeSummary t c32) =
    some ([Entry.ofStrings ":method" "GET", Entry.ofStrings ":scheme" "http",
      Entry.ofStrings ":path" "/", Entry.ofStrings ":authority" "www.example.com",
      Entry.ofStrings "cache-control" "no-cache"], 110) := by
  decide +kernel

/-- A size update after a field is rejected (§4.2). -/
example : decodeBlock (.empty 4096) [0x82, 0x20] = none := by decide +kernel
/-- A size update above the limit is rejected (§6.3). -/
example : decodeBlock (.empty 100) [0x3f, 0x46] = none := by decide +kernel
/-- Index 0 is a decoding error (§6.1). -/
example : decodeBlock (.empty 4096) [0x80] = none := by decide +kernel
/-- Huffman-coded strings are not supported yet and are rejected. -/
example : decodeBlock (.empty 4096) [0x04, 0x81, 0x00] = none := by decide +kernel

end Silmaril.Net.Hpack
