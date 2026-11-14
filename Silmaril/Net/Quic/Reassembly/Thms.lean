module

public import Silmaril.Net.Quic.Reassembly.Defs
import Silmaril.Proofs.Net.Quic.Reassembly

@[expose] public section

/-!
# QUIC stream reassembly: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Quic/Reassembly.lean`). Throughout,
`s` is the byte string the peer's application wrote, and every received segment is a slice of
it (the peer obeys "The data at a given offset MUST NOT change", §2.2):

* `contiguous_prefix`: **the bytes delivered in order are a prefix of `s`**;
* `contiguous_take`: **once the received segments cover offsets `[0, n)`, the first `n`
  delivered bytes are `s.take n`**;
* `contiguous_eq_of_mem`: the delivered bytes depend only on *which* segments arrived, not on
  arrival order or duplication; `contiguous_eq_of_covered`: in fact only on which offsets are
  covered (frame boundaries are invisible: "STREAM frame boundaries are not expected to be
  preserved", §2.2);
* `contiguous_spec`: the delivered prefix is gap-free and stops at the first uncovered offset;
* `contiguous_append`: receiving more segments only extends what can be delivered;
* `RecvBuffer.insert_inv`, `RecvBuffer.read_inv`: the buffer invariant (slices of `s`, no
  more delivered than contiguous) is kept, arrivals never change what was already delivered,
  and a read hands out exactly the new contiguous bytes;
* `conflict_slices`, `insert_slices`: slices of one string never conflict, so the strict
  buffer (PROTOCOL_VIOLATION on changed data) accepts every honest retransmission;
* `run_delivers`: **for any interleaving of arrivals (in any order, with duplicates) and
  application reads, the strict buffer never fails, everything read is a prefix of `s`, and
  after a final read covering `[0, n)` the application has read `s.take n`.**

CHECKED: out-of-order and overlapping arrivals; a conflicting retransmission rejected under
`strict` and ignored (first data wins) otherwise.
-/

namespace Silmaril.Net.Quic

theorem contiguous_prefix {s : List UInt8} {segs : List Segment}
    (hs : ∀ g ∈ segs, g.SliceOf s) : contiguous segs <+: s :=
  Silmaril.Proofs.Net.Quic.Reassembly.contiguous_prefix hs

theorem contiguous_take {s : List UInt8} {segs : List Segment} (hs : ∀ g ∈ segs, g.SliceOf s)
    {n : Nat} (h : ∀ j < n, Covered segs j) :
    (contiguous segs).take n = s.take n ∧ n ≤ (contiguous segs).length :=
  Silmaril.Proofs.Net.Quic.Reassembly.contiguous_take hs h

theorem contiguous_spec (segs : List Segment) :
    (∀ j < (contiguous segs).length, Covered segs j) ∧
      ¬ Covered segs (contiguous segs).length :=
  Silmaril.Proofs.Net.Quic.Reassembly.contiguous_spec segs

theorem contiguous_eq_of_covered {s : List UInt8} {segs₁ segs₂ : List Segment}
    (hs₁ : ∀ g ∈ segs₁, g.SliceOf s) (hs₂ : ∀ g ∈ segs₂, g.SliceOf s)
    (hc : ∀ i, Covered segs₁ i ↔ Covered segs₂ i) : contiguous segs₁ = contiguous segs₂ :=
  Silmaril.Proofs.Net.Quic.Reassembly.contiguous_eq_of_covered hs₁ hs₂ hc

theorem contiguous_eq_of_mem {s : List UInt8} {segs₁ segs₂ : List Segment}
    (hs₁ : ∀ g ∈ segs₁, g.SliceOf s) (hm : ∀ g, g ∈ segs₁ ↔ g ∈ segs₂) :
    contiguous segs₁ = contiguous segs₂ :=
  Silmaril.Proofs.Net.Quic.Reassembly.contiguous_eq_of_mem hs₁ hm

theorem contiguous_append (segs more : List Segment) :
    contiguous segs <+: contiguous (segs ++ more) :=
  Silmaril.Proofs.Net.Quic.Reassembly.contiguous_append segs more

theorem conflict_slices {s : List UInt8} {segs : List Segment} (hs : ∀ g ∈ segs, g.SliceOf s)
    {g : Segment} (hg : g.SliceOf s) : conflict segs g = false :=
  Silmaril.Proofs.Net.Quic.Reassembly.conflict_slices hs hg

theorem RecvBuffer.insert_slices {s : List UInt8} {b : RecvBuffer} (strict : Bool)
    (hs : b.SlicesOf s) {g : Segment} (hg : g.SliceOf s) :
    b.insert strict g = .ok { b with segs := b.segs ++ [g] } :=
  Silmaril.Proofs.Net.Quic.Reassembly.insert_slices strict hs hg

theorem RecvBuffer.insert_inv {s : List UInt8} {b : RecvBuffer} {g : Segment}
    (hb : b.SlicesOf s ∧ b.delivered ≤ (contiguous b.segs).length) (hg : g.SliceOf s) :
    (({ b with segs := b.segs ++ [g] } : RecvBuffer).SlicesOf s ∧
      b.delivered ≤ (contiguous (b.segs ++ [g])).length) ∧
      (contiguous (b.segs ++ [g])).take b.delivered = (contiguous b.segs).take b.delivered :=
  Silmaril.Proofs.Net.Quic.Reassembly.insert_inv hb hg

theorem RecvBuffer.read_inv {s : List UInt8} {b : RecvBuffer}
    (hb : b.SlicesOf s ∧ b.delivered ≤ (contiguous b.segs).length) :
    (b.read.2.SlicesOf s ∧ b.read.2.delivered ≤ (contiguous b.read.2.segs).length) ∧
      (contiguous b.segs).take b.delivered ++ b.read.1 =
        (contiguous b.read.2.segs).take b.read.2.delivered ∧
      b.read.2.delivered = (contiguous b.read.2.segs).length :=
  Silmaril.Proofs.Net.Quic.Reassembly.read_inv hb

theorem RecvBuffer.run_delivers (strict : Bool) {s : List UInt8} (es : List Event)
    (hes : ∀ g, Event.recv g ∈ es → g.SliceOf s) :
    ∃ out b', run strict {} es = .ok (out, b') ∧ out <+: s ∧
      out = (contiguous b'.segs).take b'.delivered ∧
      (es.getLast? = some .read → ∀ n, (∀ j < n, ∃ g, Event.recv g ∈ es ∧ g.Covers j) →
        out.take n = s.take n ∧ n ≤ out.length) :=
  Silmaril.Proofs.Net.Quic.Reassembly.run_delivers strict es hes

/-! ## Examples: the stream "hello" (`[104, 101, 108, 108, 111]`) -/

/-- "llo" then "he": nothing is deliverable until offset 0 arrives. -/
example : contiguous [⟨2, [108, 108, 111]⟩] = [] := by decide
example : contiguous [⟨2, [108, 108, 111]⟩, ⟨0, [104, 101]⟩] = [104, 101, 108, 108, 111] := by
  decide

/-- Overlapping retransmission ("ell" over "he" and "llo"). -/
example : contiguous [⟨1, [101, 108, 108]⟩, ⟨0, [104, 101]⟩, ⟨3, [108, 111]⟩] =
    [104, 101, 108, 108, 111] := by decide

/-- A gap at offset 2 stops delivery. -/
example : contiguous [⟨0, [104, 101]⟩, ⟨3, [108, 111]⟩] = [104, 101] := by decide

/-- Reads deliver each byte once, in order. -/
example : (match RecvBuffer.run true {} [.recv ⟨3, [108, 111]⟩, .read, .recv ⟨0, [104, 101]⟩,
      .read, .recv ⟨2, [108]⟩, .read] with
    | .ok (out, _) => out == [104, 101, 108, 108, 111] | .error _ => false) = true := by decide

/-- Changed data at offset 1 (`'a'` instead of `'e'`): PROTOCOL_VIOLATION when strict … -/
example : (match RecvBuffer.run true {} [.recv ⟨0, [104, 101]⟩, .recv ⟨1, [97, 108]⟩, .read] with
    | .error e => e == .protocolViolation | .ok _ => false) = true := by decide

/-- … and otherwise the first data wins. -/
example : (match RecvBuffer.run false {} [.recv ⟨0, [104, 101]⟩, .recv ⟨1, [97, 108]⟩, .read] with
    | .ok (out, _) => out == [104, 101, 108] | .error _ => false) = true := by decide

end Silmaril.Net.Quic
