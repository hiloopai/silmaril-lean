module

public import Silmaril.Formats.Compression.Inflate.Stream.MemberMachine
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.MemberSemantics
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.CheckedRaw
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.GzipHeader

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.MemberMachine`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream

open Silmaril.Formats.Compression
open MemberSemantics

namespace MemberMachine

theorem enterBody_denote (kind : Kind) (reservoir : Reservoir) (reader : LSBReader) :
    (enterBody kind reservoir).denote reader = MemberSemantics.body kind reader := by
  change afterRaw kind (RawSemantics.denote (.header Blocks.header (emptyState reservoir)) reader) = _
  rw [show RawSemantics.denote (.header Blocks.header (emptyState reservoir)) reader =
      RawSemantics.format reader [] from (RawSemantics.format_unfold reader []).symm]
  rfl

theorem enterBody_wellFormed (kind : Kind) (reservoir : Reservoir) (reader : LSBReader) :
    (enterBody kind reservoir).WellFormed reader := by
  refine ⟨CheckedRaw.ofMachine_invariant _ _, ?_⟩
  change Window.Represents (Window.ofOutput []) [] ∧ True
  exact ⟨rfl, trivial⟩

theorem enterBody_reservoir (kind : Kind) (reservoir : Reservoir) :
    (enterBody kind reservoir).reservoir = reservoir := rfl

theorem checkedTrailer_eq (kind : Kind) (checked : CheckedRaw.State)
    (h : CheckedRaw.Invariant kind.checksumKind checked) :
    checkedTrailer kind checked = MemberSemantics.trailer kind checked.output := by
  cases kind with
  | zlib =>
    have hc := (CheckedRaw.adler32_values checked h).1
    simp only [checkedTrailer, MemberSemantics.trailer, ContainerFields.zlibTrailer, hc]
  | gzip =>
    obtain ⟨hc, hs⟩ := CheckedRaw.crc32_values checked h
    simp only [checkedTrailer, MemberSemantics.trailer, ContainerFields.gzipTrailer, hc, hs]
    unfold ContainerFields.gzipTrailerValue
    simp only [Protocol.word32, Nat.mod_mod]

theorem feed_denote (machine : MemberMachine) (input : List UInt8) (reader : LSBReader) :
    (machine.feed input).denote reader = machine.denote reader := by
  cases machine <;> simp only [feed, denote, CheckedRaw.feed_denote, RawState.feed]
  rfl

theorem feed_normalizes (machine : MemberMachine) (input : List UInt8) (reader : LSBReader)
    (h : Reservoir.Normalizes machine.reservoir reader) :
    Reservoir.Normalizes (machine.feed input).reservoir (Reservoir.readerFeed reader input) := by
  cases machine with
  | body kind checked => exact CheckedRaw.feed_normalizes checked input reader h
  | header _ _ _ | gzipHeader _ | trailer _ _ | done _ | bad _ _ => exact h.feed input

theorem feed_wellFormed (machine : MemberMachine) (input : List UInt8) (reader : LSBReader)
    (h : machine.WellFormed reader) :
    (machine.feed input).WellFormed (Reservoir.readerFeed reader input) := by
  cases machine with
  | gzipHeader header => exact h
  | body kind checked =>
    exact ⟨CheckedRaw.feed_invariant _ _ _ h.1, CheckedRaw.feed_wellFormed _ _ _ h.2⟩
  | header _ _ _ | trailer _ _ | done _ | bad _ _ => trivial

theorem runCalls_append (version : Version) (machine : MemberMachine)
    (first second : List RawMachine.Call) :
    runCalls version machine (first ++ second) =
      runCalls version (runCalls version machine first) second := List.foldl_append

end MemberMachine
end Silmaril.Formats.Compression.Inflate.Stream
