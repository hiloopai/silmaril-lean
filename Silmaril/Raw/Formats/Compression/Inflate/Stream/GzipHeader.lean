module

public import Silmaril.Formats.Compression.Inflate.Stream.GzipHeader
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.ContainerFields
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.RawContainers

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.GzipHeader`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.GzipHeader

open Silmaril.Formats.Compression

namespace Machine

end Machine

theorem evaluate_done (flags : UInt8) (covered input : List UInt8) :
    evaluate ⟨.done, flags, covered⟩ input = some input := by rw [evaluate.eq_def]

theorem evaluate_bad (flags : UInt8) (covered input : List UInt8) :
    evaluate ⟨.bad, flags, covered⟩ input = none := by rw [evaluate.eq_def]

theorem evaluate_cons (control : Control) (byte : UInt8) (rest : List UInt8)
    (hactive : control.active = true) :
    evaluate control (byte :: rest) = evaluate (control.advance byte) rest := by
  cases hp : control.phase <;> simp only [Control.active, hp, bne_iff_ne, Bool.and_eq_true,
    ne_eq, reduceCtorEq, not_true_eq_false, and_false, false_and] at hactive
  all_goals rw [evaluate.eq_def, hp]

theorem evaluate_nil (control : Control) :
    evaluate control [] = if control.phase = .done then some [] else none := by
  cases hp : control.phase <;> rw [evaluate.eq_def, hp] <;> simp

/-- Header parsing only consumes a prefix, including when optional strings
have arbitrarily many bytes. -/
theorem evaluate_suffix (control : Control) (input rest : List UInt8)
    (h : evaluate control input = some rest) : rest <:+ input := by
  induction input generalizing control with
  | nil =>
    rw [evaluate_nil] at h
    split at h
    · obtain rfl := Option.some.inj h
      exact ⟨[], rfl⟩
    · cases h
  | cons byte input ih =>
    by_cases hd : control.phase = .done
    · rw [evaluate.eq_def, hd] at h
      obtain rfl := Option.some.inj h
      exact ⟨[], rfl⟩
    · by_cases hb : control.phase = .bad
      · rw [evaluate.eq_def, hb] at h
        cases h
      · have ha : control.active = true := by simp [Control.active, hd, hb]
        rw [evaluate_cons control byte input ha] at h
        exact (ih (control.advance byte) h).trans ⟨[byte], rfl⟩

theorem denoteReader_cons (control : Control) (before after : Reservoir)
    (byte : UInt8) (rest : List UInt8) (total : Nat)
    (ha : control.active = true) :
    Machine.denoteReader ⟨control, before⟩
        (ContainerFields.alignedReader (byte :: rest) total) =
      Machine.denoteReader ⟨control.advance byte, after⟩
        (ContainerFields.alignedReader rest (total + 8)) := by
  simp only [Machine.denoteReader, Machine.denote, ContainerFields.alignedReader]
  rw [evaluate_cons control byte rest ha]
  cases h : evaluate (control.advance byte) rest with
  | none => rfl
  | some suffix =>
    have hlength := (evaluate_suffix (control.advance byte) rest suffix h).length_le
    simp only [Option.map_some, List.length_cons]
    congr 1
    congr 1
    omega

/-- One header step preserves its complete logical meaning under every later
input extension. Successful byte reads retain an aligned normalized reader;
physical refill suspension retains the same logical reader and phase. -/
theorem step_correct_feed (machine : Machine) (input : List UInt8) (total : Nat)
    (hnorm : Reservoir.Normalizes machine.reservoir (ContainerFields.alignedReader input total)) :
    ∃ rest nextTotal,
      Reservoir.Normalizes machine.step.reservoir (ContainerFields.alignedReader rest nextTotal) ∧
      ∀ future,
        machine.denote (ContainerFields.alignedReader (input ++ future) total) =
          machine.step.denote (ContainerFields.alignedReader (rest ++ future) nextTotal) := by
  cases hactive : machine.control.active with
  | false =>
    refine ⟨input, total, ?_, ?_⟩
    · simpa only [Machine.step, hactive, Bool.false_eq_true, ↓reduceIte] using hnorm
    · intro future
      simp only [Machine.step, hactive, Bool.false_eq_true, ↓reduceIte]
  | true =>
    cases hread : Reservoir.readBits 8 machine.reservoir with
    | needInput physical =>
      refine ⟨input, total, ?_, ?_⟩
      · simpa only [Machine.step, hactive, ↓reduceIte, hread] using hnorm.readBits_needInput hread
      · intro future
        simp only [Machine.denote, Machine.step, hactive, ↓reduceIte, hread]
    | value value physical =>
      obtain ⟨logicalRest, hlogical, hphysical⟩ := hnorm.readBits hread
      cases input with
      | nil => cases hlogical
      | cons first rest =>
        rw [ContainerFields.readBits_byte_cons] at hlogical
        obtain ⟨rfl, rfl⟩ := Option.some.inj hlogical
        refine ⟨rest, total + 8, ?_, ?_⟩
        · simpa only [Machine.step, hactive, ↓reduceIte, hread, UInt8.ofNat_toNat] using hphysical
        · intro future
          simpa only [Machine.denote, Machine.step, hactive, ↓reduceIte, hread,
            UInt8.ofNat_toNat, ContainerFields.alignedReader, List.cons_append] using
            evaluate_cons machine.control first (rest ++ future) hactive

/-- Exact-reader version of header-step preservation. The successful observed
reader agrees in buffer, bit count, suffix and consumed-bit cursor. -/
theorem step_correct_reader_feed (machine : Machine) (input : List UInt8) (total : Nat)
    (hnorm : Reservoir.Normalizes machine.reservoir (ContainerFields.alignedReader input total)) :
    ∃ rest nextTotal,
      Reservoir.Normalizes machine.step.reservoir (ContainerFields.alignedReader rest nextTotal) ∧
      ∀ future,
        machine.denoteReader (ContainerFields.alignedReader (input ++ future) total) =
          machine.step.denoteReader (ContainerFields.alignedReader (rest ++ future) nextTotal) := by
  cases hactive : machine.control.active with
  | false =>
    refine ⟨input, total, ?_, ?_⟩
    · simpa only [Machine.step, hactive, Bool.false_eq_true, ↓reduceIte] using hnorm
    · intro future
      simp only [Machine.step, hactive, Bool.false_eq_true, ↓reduceIte]
  | true =>
    cases hread : Reservoir.readBits 8 machine.reservoir with
    | needInput physical =>
      refine ⟨input, total, ?_, ?_⟩
      · simpa only [Machine.step, hactive, ↓reduceIte, hread] using hnorm.readBits_needInput hread
      · intro future
        simp only [Machine.denoteReader, Machine.denote, Machine.step, hactive, ↓reduceIte, hread]
    | value value physical =>
      obtain ⟨logicalRest, hlogical, hphysical⟩ := hnorm.readBits hread
      cases input with
      | nil => cases hlogical
      | cons first rest =>
        rw [ContainerFields.readBits_byte_cons] at hlogical
        obtain ⟨rfl, rfl⟩ := Option.some.inj hlogical
        refine ⟨rest, total + 8, ?_, ?_⟩
        · simpa only [Machine.step, hactive, ↓reduceIte, hread, UInt8.ofNat_toNat] using hphysical
        · intro future
          simpa only [Machine.step, hactive, ↓reduceIte, hread, UInt8.ofNat_toNat,
            ContainerFields.alignedReader, List.cons_append] using
            denoteReader_cons machine.control machine.reservoir physical first (rest ++ future) total hactive

end Silmaril.Formats.Compression.Inflate.Stream.GzipHeader
