module

public import Silmaril.Net.Quic.StreamId.Defs
import Silmaril.Proofs.Net.Quic.StreamId

@[expose] public section

/-!
# QUIC stream identifiers and stream limits: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Quic/StreamId.lean`):

* `type_nth`, `index_nth`: the `n`-th stream of type `t` has type `t` and index `n` (§2.1:
  "The two least significant bits from a stream ID therefore identify a stream as one of four
  types");
* `nth_type_index`: every natural number is a stream id, the `index`-th of its `type`;
* `nth_inj`: distinct (type, index) pairs give distinct ids, so ids are never reused;
* `nth_lt_nth`: "successive streams of each type are created with numerically increasing
  stream IDs";
* `nth_valid`: the `n`-th stream id fits in 62 bits iff `n < 2^60`, which is why MAX_STREAMS
  is capped at `2^60` (§4.6);
* `withinLimit_iff`: the §4.6 bound "stream ID less than max_streams * 4 +
  first_stream_id_of_type" is exactly "index below max_streams";
* `canSend_peer`, `uni_exclusive`: on a unidirectional stream exactly one endpoint sends,
  and the other receives;
* `Opener.open_ok`, `Opener.open_valid`, `Opener.onMaxStreams_ok`: a locally initiating
  endpoint never opens more streams than the peer allowed, every id it opens fits in 62 bits,
  and MAX_STREAMS only ever raises the limit, never beyond `2^60`;
* `Acceptor.accept_error`, `Acceptor.accept_ok`, `Acceptor.accept_lower`: a stream id beyond
  the advertised limit is STREAM_LIMIT_ERROR; an accepted id is open together with every
  lower-numbered stream of its type, and open streams stay open.

CHECKED: the first stream ids of Table 1 and the example of §19.11 ("a server that receives
a unidirectional stream limit of 3 is permitted to open streams 3, 7, and 11, but not stream
15").
-/

namespace Silmaril.Net.Quic

namespace StreamId

theorem type_nth (t : StreamType) (n : Nat) : type (nth t n) = t :=
  Silmaril.Proofs.Net.Quic.StreamId.type_nth t n

theorem index_nth (t : StreamType) (n : Nat) : index (nth t n) = n :=
  Silmaril.Proofs.Net.Quic.StreamId.index_nth t n

theorem nth_type_index (id : Nat) : nth (type id) (index id) = id :=
  Silmaril.Proofs.Net.Quic.StreamId.nth_type_index id

theorem nth_inj {t t' : StreamType} {n n' : Nat} (h : nth t n = nth t' n') : t = t' ∧ n = n' :=
  Silmaril.Proofs.Net.Quic.StreamId.nth_inj h

theorem nth_lt_nth (t : StreamType) (n m : Nat) : nth t n < nth t m ↔ n < m :=
  Silmaril.Proofs.Net.Quic.StreamId.nth_lt_nth t n m

theorem nth_valid (t : StreamType) (n : Nat) : Valid (nth t n) ↔ n < maxStreamsLimit :=
  Silmaril.Proofs.Net.Quic.StreamId.nth_valid t n

theorem withinLimit_iff (m id : Nat) : withinLimit m id = true ↔ index id < m :=
  Silmaril.Proofs.Net.Quic.StreamId.withinLimit_iff m id

theorem canSend_peer (r : Role) (id : Nat) : canSend r.peer id = canRecv r id :=
  Silmaril.Proofs.Net.Quic.StreamId.canSend_peer r id

theorem uni_exclusive (r : Role) (id : Nat) (h : dir id = .uni) :
    canSend r id = !canRecv r id :=
  Silmaril.Proofs.Net.Quic.StreamId.uni_exclusive r id h

theorem bidi_both (r : Role) (id : Nat) (h : dir id = .bidi) :
    canSend r id = true ∧ canRecv r id = true := by
  simp [canSend, canRecv, h]

/-! Table 1: the first stream of each type is `0x00`–`0x03`. -/
example : StreamType.all.map (nth · 0) = [0, 1, 2, 3] := by decide
example : StreamType.all.map (nth · 1) = [4, 5, 6, 7] := by decide
/-- Stream 0 is the client's first bidirectional stream (HTTP/3 uses it for the first
request, RFC 9114 §6.1). -/
example : type 0 = ⟨.client, .bidi⟩ := by decide
example : type 7 = ⟨.server, .uni⟩ ∧ index 7 = 1 := by decide

/-- §19.11: with a unidirectional limit of 3 a server may open 3, 7 and 11 but not 15. -/
example : [3, 7, 11, 15].map (withinLimit 3) = [true, true, true, false] := by decide

end StreamId

namespace Opener

theorem open_ok {o o' : Opener} {id : Nat} (h : o.open = some (id, o')) : o'.Ok :=
  Silmaril.Proofs.Net.Quic.StreamId.open_ok h

theorem open_spec {o o' : Opener} {id : Nat} (h : o.open = some (id, o')) :
    id = StreamId.nth o.type o.opened ∧ o'.opened = o.opened + 1 ∧ o'.type = o.type ∧
      o'.limit = o.limit ∧ o.opened < o.limit :=
  Silmaril.Proofs.Net.Quic.StreamId.open_spec h

theorem open_valid {o o' : Opener} {id : Nat} (hl : o.limit ≤ maxStreamsLimit)
    (h : o.open = some (id, o')) : StreamId.Valid id :=
  Silmaril.Proofs.Net.Quic.StreamId.open_valid hl h

theorem open_blocked {o : Opener} : o.open = none ↔ o.limit ≤ o.opened := by
  unfold Opener.open; split <;> simp_all <;> omega

theorem onMaxStreams_ok {o o' : Opener} {m : Nat} (ho : o.Ok) (h : o.onMaxStreams m = .ok o') :
    o'.Ok ∧ o.limit ≤ o'.limit ∧ o'.limit ≤ max o.limit maxStreamsLimit ∧ o'.opened = o.opened :=
  Silmaril.Proofs.Net.Quic.StreamId.onMaxStreams_ok ho h

/-- A server allowed 3 unidirectional streams opens 3, 7, 11 and is then blocked (§19.11). -/
example : (do
    let (a, o) ← Opener.open ⟨⟨.server, .uni⟩, 3, 0⟩
    let (b, o) ← o.open
    let (c, o) ← o.open
    pure ([a, b, c], o.open.isNone)) = some ([3, 7, 11], true) := by decide

end Opener

namespace Acceptor

theorem accept_error {a : Acceptor} {id : Nat} :
    a.accept id = .error .streamLimitError ↔ a.limit ≤ StreamId.index id :=
  Silmaril.Proofs.Net.Quic.StreamId.accept_error

theorem accept_ok {a a' : Acceptor} {id : Nat} (ha : a.Ok) (h : a.accept id = .ok a') :
    a'.Ok ∧ a'.isOpen id = true ∧ (∀ j, a.isOpen j = true → a'.isOpen j = true) :=
  Silmaril.Proofs.Net.Quic.StreamId.accept_ok ha h

theorem accept_lower {a a' : Acceptor} {id j : Nat} (h : a.accept id = .ok a')
    (hj : StreamId.index j ≤ StreamId.index id) : a'.isOpen j = true :=
  Silmaril.Proofs.Net.Quic.StreamId.accept_lower h hj

theorem raise_mono (a : Acceptor) (m : Nat) :
    a.limit ≤ (a.raise m).limit ∧ (a.raise m).limit ≤ max a.limit maxStreamsLimit := by
  simp only [raise]; omega

end Acceptor

end Silmaril.Net.Quic
