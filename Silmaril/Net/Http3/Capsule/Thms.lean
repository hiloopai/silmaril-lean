module

public import Silmaril.Net.Http3.Capsule.Defs
import Silmaril.Proofs.Net.Http3.Capsule

@[expose] public section

/-!
# The HTTP Capsule Protocol: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Http3/Capsule.lean`), RFC 9297 §3.2:

* `read_encode`: a capsule whose integers fit (and whose value is within the reader's limit)
  reads back as itself, and the reader stops exactly where the capsule ends;
* `read_ok`: a successful read respects the limit, consumes at least one byte and yields a
  valid capsule;
* `read_local`: bytes after a capsule are passed through (a reader can work on a growing
  buffer);
* `readAll_encodeAll`: a data stream of capsules decodes back to the capsule list;
* `known_insert_unknown`: a capsule of an unknown type changes nothing, wherever it appears
  ("MUST silently drop that Capsule and skip over it to parse the next Capsule");
* `datagrams_map_datagram`, `datagrams_append`: DATAGRAM capsules (§3.5) carry their payloads
  in order.

CHECKED: sample encodings, a truncated capsule (§3.3) and the §3.2 message rules.
-/

namespace Silmaril.Net.Http3.Capsule

theorem read_encode {m : Nat} {c : Capsule} (hc : c.Valid) (hm : c.value.length ≤ m)
    (rest : List UInt8) : read m (c.encode ++ rest) = .ok (c, rest) :=
  Silmaril.Proofs.Net.Http3.Capsule.read_encode hc hm rest

theorem read_ok {m : Nat} {xs : List UInt8} {c : Capsule} {rest : List UInt8}
    (h : read m xs = .ok (c, rest)) :
    c.value.length ≤ m ∧ rest.length < xs.length ∧ c.Valid :=
  Silmaril.Proofs.Net.Http3.Capsule.read_ok h

theorem read_local {m : Nat} {xs : List UInt8} {c : Capsule} {rest : List UInt8}
    (tail : List UInt8) (h : read m xs = .ok (c, rest)) :
    read m (xs ++ tail) = .ok (c, rest ++ tail) :=
  Silmaril.Proofs.Net.Http3.Capsule.read_local tail h

theorem readAll_encodeAll {m : Nat} (cs : List Capsule) (hv : ∀ c ∈ cs, c.Valid)
    (hm : ∀ c ∈ cs, c.value.length ≤ m) : readAll m (encodeAll cs) = .ok cs :=
  Silmaril.Proofs.Net.Http3.Capsule.readAll_encodeAll cs hv hm

theorem known_insert_unknown (isKnown : Nat → Bool) (xs ys : List Capsule) (c : Capsule)
    (hc : isKnown c.type = false) : known isKnown (xs ++ c :: ys) = known isKnown (xs ++ ys) :=
  Silmaril.Proofs.Net.Http3.Capsule.known_insert_unknown isKnown xs ys c hc

theorem datagrams_append (xs ys : List Capsule) :
    datagrams (xs ++ ys) = datagrams xs ++ datagrams ys :=
  Silmaril.Proofs.Net.Http3.Capsule.datagrams_append xs ys

theorem datagrams_map_datagram (ps : List (List UInt8)) : datagrams (ps.map datagram) = ps :=
  Silmaril.Proofs.Net.Http3.Capsule.datagrams_map_datagram ps

/-! ## Known answers -/

/-- A DATAGRAM capsule with payload `01 02 03`: type `0x00`, length 3. -/
theorem encode_datagram : (datagram [1, 2, 3]).encode = [0x00, 0x03, 1, 2, 3] := by rfl

/-- A capsule with a four-byte type (WebTransport's `WT_DRAIN_SESSION`, `0x78ae`) and an empty
value. -/
theorem encode_drain : (⟨0x78ae, []⟩ : Capsule).encode = [0x80, 0x00, 0x78, 0xae, 0x00] := by
  rfl

theorem read_sample : read 16 [0x00, 0x02, 7, 8, 0x3f, 0x00] = .ok (⟨0, [7, 8]⟩, [0x3f, 0x00]) := by
  rfl

/-- A capsule truncated inside its value is `incomplete`; at a clean end of stream this is a
malformed message (§3.3). -/
theorem readAll_truncated : readAll 16 [0x00, 0x02, 7] = .error .incomplete := by rfl

/-- A value above the reader's limit is refused before it is buffered (§3.5). -/
theorem read_tooLarge : read 2 [0x00, 0x03, 7, 8, 9] = .error .tooLarge := by rfl

/-- Unknown capsule types are skipped (§3.2). -/
theorem known_sample :
    known (· == typeDatagram) [⟨0x17, [1]⟩, datagram [2], ⟨0x2843, []⟩] = [datagram [2]] := by
  rfl

/-- No `content-length` on a message using the Capsule Protocol (§3.2). -/
example : fieldsAllowCapsules [Silmaril.Net.Hpack.Entry.ofStrings "content-length" "5"] = false ∧
    fieldsAllowCapsules [Silmaril.Net.Hpack.Entry.ofStrings "capsule-protocol" "?1"] = true := by
  decide +kernel

example : statusAllowsCapsules 204 = false ∧ statusAllowsCapsules 200 = true := by decide
example : statusStartsDataStream 200 ∧ statusStartsDataStream 101 ∧
    ¬ statusStartsDataStream 301 := by decide

end Silmaril.Net.Http3.Capsule
