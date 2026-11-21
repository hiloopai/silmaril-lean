module

public import Silmaril.Formats.Blake3Cas.RangeFacts.Defs
import Silmaril.Proofs.Formats.Blake3Cas.RangeFacts.Relations

@[expose] public section

namespace Silmaril.Formats.Blake3Cas.RangeFacts

open Silmaril.Crypto.Blake3
open Silmaril.Semantics.Naming.ByteRange (Slice slice_iff)

theorem suffix_iff {whole bytes : Bytes} {start : Nat} :
    SuffixAt whole start bytes ↔ ExactAt whole start whole.length bytes :=
  Proofs.Formats.Blake3Cas.RangeFacts.suffix_iff

theorem suffix_split {whole bytes : Bytes} {start stop : Nat} :
    (SuffixAt whole start bytes ∧ start + bytes.length = stop) ↔
      ExactAt whole start stop bytes ∧ whole.length = stop :=
  ⟨fun ⟨suffix, exactLength⟩ => ⟨⟨exactLength, (suffix_iff.mp suffix).2⟩,
      (suffix_iff.mp suffix).1.symm.trans exactLength⟩,
    fun ⟨exactRange, extent⟩ => ⟨suffix_iff.mpr (extent.symm ▸ exactRange), exactRange.1⟩⟩

theorem empty_bounded_iff {whole : Bytes} {start : Nat} : ExactAt whole start start [] ↔ start ≤ whole.length :=
  Proofs.Formats.Blake3Cas.RangeFacts.emptyBound

theorem empty_suffix_iff {whole : Bytes} {start : Nat} : SuffixAt whole start [] ↔ start = whole.length :=
  ⟨fun proof => by simpa using (suffix_iff.mp proof).1,
    fun extent => by simp [SuffixAt, extent]⟩

theorem whole_iff {whole bytes : Bytes} : SuffixAt whole 0 bytes ↔ whole = bytes := by
  simp [SuffixAt]

def Done.seal {claim : Nat} {digest : Bytes} {request : Request} (done : Done claim digest request)
    (eof : Extent digest claim) : Bounded digest (request.window claim).start
      ((request.window claim).start + (request.window claim).count) :=
  ⟨done.bytes, done.range.coverage.exactLength,
    fun named => (done.range.coverage.soundEOF eof.down named done.range.within).imp
      (⟨done.range.coverage.exactLength, ·⟩) id⟩

/-- Seal a span from a checked prefix without requiring a completed response. -/
def sealSpan {claim : Nat} {digest : Bytes} (span : SpanFact claim digest) (eof : Extent digest claim) :
    Bounded digest span.offset (span.offset + span.bytes.length) :=
  ⟨span.bytes, rfl, fun named => (span.soundEOF eof.down named).imp (⟨rfl, ·⟩) id⟩

def Done.suffix {claim start : Nat} {digest : Bytes} (done : Done claim digest (.toEnd start))
    (eof : Extent digest claim) : Suffix digest start :=
  let bound : start ≤ claim := Nat.le_trans (Nat.le_add_right ..) done.range.within
  ⟨claim, Nat.add_sub_of_le bound ▸ done.seal eof, eof⟩

def Response.suffix? {digest : Bytes} {start : Nat} (response : Response digest (.toEnd start)) :
    Option (Suffix digest start) := response.eof.map response.done.suffix

def emptySuffix {digest : Bytes} {size : Nat} (eof : Extent digest size) : Suffix digest size :=
  ⟨size, ⟨[], Nat.add_zero _, fun named => (eof.down.concreteExtentOrCollision named).imp
    (fun eq => empty_bounded_iff.mpr (Nat.le_of_eq eq)) id⟩, eof⟩

theorem Suffix.against {digest whole : Bytes} {start : Nat} (suffix : Suffix digest start)
    (named : Named concrete digest whole) : SuffixAt whole start suffix.bytes ∨ ConcreteCollision :=
  Proofs.Formats.Blake3Cas.RangeFacts.suffixAgainst suffix named

def Bounded.sub {digest part : Bytes} {start stop shift : Nat} (bounded : Bounded digest start stop)
    (slice : Slice bounded.bytes shift part) : Bounded digest (start + shift) (start + shift + part.length) :=
  ⟨part, rfl, fun named => (bounded.against named).imp (fun exactRange => ⟨rfl, exactRange.2.sub slice⟩) id⟩

def Bounded.slice? {digest : Bytes} {start stop : Nat} (bounded : Bounded digest start stop)
    (shift count : Nat) : Option (Bounded digest (start + shift) (start + shift + count)) :=
  if within : shift + count ≤ bounded.bytes.length then
    let part := (bounded.bytes.drop shift).take count
    let len : part.length = count := by simp [part, List.length_take]; omega
    let slice : Slice bounded.bytes shift part := slice_iff.mpr ⟨len.symm ▸ within, by rw [len]⟩
    some (len ▸ bounded.sub slice)
  else none

theorem ExactAt.join {whole left right : Bytes} {start middle stop : Nat}
    (lhs : ExactAt whole start middle left) (rhs : ExactAt whole middle stop right) :
    ExactAt whole start stop (left ++ right) :=
  ⟨by rw [List.length_append, ← Nat.add_assoc, lhs.1, rhs.1],
    Proofs.Formats.Blake3Cas.RangeFacts.joinSlices lhs.2 rhs.2 lhs.1⟩

def Bounded.append {digest : Bytes} {start middle stop : Nat}
    (left : Bounded digest start middle) (right : Bounded digest middle stop) : Bounded digest start stop :=
  ⟨left.bytes ++ right.bytes, by rw [List.length_append, ← Nat.add_assoc, left.exact, right.exact], fun named =>
    (left.against named).elim (fun lhs => (right.against named).imp lhs.join id) Or.inr⟩

def Bounded.prependSuffix {digest : Bytes} {start middle : Nat}
    (bounded : Bounded digest start middle) (suffix : Suffix digest middle) : Suffix digest start :=
  ⟨suffix.stop, bounded.append suffix.bounded, suffix.extent⟩

end Silmaril.Formats.Blake3Cas.RangeFacts
