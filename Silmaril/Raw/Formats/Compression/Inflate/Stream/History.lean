module

public import Silmaril.Formats.Compression.Inflate.Stream.History
public import Silmaril.Raw.Formats.Compression.Bits.Bit
public import Silmaril.Formats.Compression.Bits.Bitstream
public import Silmaril.Raw.Formats.Compression.Deflate.Huffman
public import Silmaril.Formats.Compression.Deflate.Decompress
public import Silmaril.Raw.Formats.Compression.Deflate.Stored
public import Silmaril.Raw.Formats.Compression.Deflate.WithHistory
public import Silmaril.Formats.Compression.Deflate.Compress
public import Silmaril.Raw.Formats.Compression.Deflate.LZ77
public import Silmaril.Raw.Formats.Compression.Bits.ByteFields
public import Silmaril.Raw.Formats.Compression.Checksum.Adler32
public import Silmaril.Raw.Formats.Compression.Checksum.CRC32
public import Silmaril.Raw.Formats.Compression.Zlib.Basic
public import Silmaril.Raw.Formats.Compression.Zlib.Take
public import Silmaril.Raw.Formats.Compression.Zlib.Dictionary
public import Silmaril.Raw.Formats.Compression.Gzip.Basic

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.History`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream

open Silmaril.Formats.Compression

theorem keepWindow_length (bytes : List UInt8) :
    (keepWindow bytes).length = min bytes.length windowLimit := by
  simp only [keepWindow, List.length_drop]
  omega

theorem keepWindow_of_short (bytes : List UInt8) (h : bytes.length ≤ windowLimit) :
    keepWindow bytes = bytes := by
  rw [keepWindow, Nat.sub_eq_zero_of_le h, List.drop_zero]

/-- Discarding already-unreachable old history commutes with later writes. -/
theorem keepWindow_append (before added : List UInt8) :
    keepWindow (keepWindow before ++ added) = keepWindow (before ++ added) := by
  simp only [keepWindow, List.length_append, List.length_drop]
  rw [← List.drop_append_of_le_length (Nat.sub_le before.length windowLimit), List.drop_drop]
  apply congrArg (fun count => (before ++ added).drop count)
  omega

theorem Window.valid_of_represents (w : Window) (output : List UInt8)
    (h : w.Represents output) : w.Valid := by
  simp only [Window.Valid, Window.Represents] at *
  rw [h, keepWindow_length]
  exact Nat.min_le_right _ _

theorem Window.push_represents (w : Window) (output : List UInt8) (byte : UInt8)
    (h : w.Represents output) : (w.push byte).Represents (output ++ [byte]) := by
  simp only [Window.Represents, Window.push] at *
  rw [h, keepWindow_append]

/-- A bounded-window read is exactly the corresponding logical-history read
for every available distance, even when the logical trace exceeds 32 KiB. -/
theorem Window.back_eq (w : Window) (output : List UInt8) (distance : Nat)
    (h : w.Represents output) (hlimit : distance ≤ windowLimit)
    (havailable : distance ≤ output.length) :
    w.back distance = output.getD (output.length - distance) 0 := by
  simp only [Window.back, Window.Represents] at *
  rw [h]
  simp only [keepWindow, List.length_drop, List.getD_eq_getElem?_getD, List.getElem?_drop]
  congr 2
  omega

theorem Window.available (w : Window) (output : List UInt8) (distance : Nat)
    (h : w.Represents output) (hlimit : distance ≤ windowLimit)
    (havailable : distance ≤ output.length) : distance ≤ w.bytes.length := by
  rw [h, keepWindow_length]
  omega

theorem copyWindow_length (distance count : Nat) (window : Window) (output : List UInt8) :
    (copyWindow distance count window output).2.length = output.length + count := by
  induction count generalizing window output with
  | zero => rfl
  | succ count ih =>
    simp only [copyWindow, ih, List.length_append, List.length_singleton]
    omega

theorem copyWindow_append (distance count : Nat) (window : Window) (output : List UInt8) :
    ∃ added, (copyWindow distance count window output).2 = output ++ added := by
  induction count generalizing window output with
  | zero => exact ⟨[], by simp only [copyWindow, List.append_nil]⟩
  | succ count ih =>
    obtain ⟨added, hadded⟩ := ih (window.push (window.back distance))
      (output ++ [window.back distance])
    exact ⟨window.back distance :: added, by
      simpa only [copyWindow, List.append_assoc, List.singleton_append] using hadded⟩

/-- This is a simulation of the bytewise bounded-window implementation, not a
postulated copy law. It also establishes the final representation invariant. -/
theorem copyWindow_correct (distance count : Nat) (window : Window) (output : List UInt8)
    (h : window.Represents output) (hlimit : distance ≤ windowLimit)
    (havailable : distance ≤ output.length) :
    (copyWindow distance count window output).2 = Deflate.copyBack distance output count ∧
      (copyWindow distance count window output).1.Represents
        (copyWindow distance count window output).2 := by
  induction count generalizing window output with
  | zero => exact ⟨rfl, h⟩
  | succ count ih =>
    have hbyte := Window.back_eq window output distance h hlimit havailable
    have hnext := Window.push_represents window output (window.back distance) h
    have hdnext : distance ≤ (output ++ [window.back distance]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    obtain ⟨hresult, hrep⟩ := ih (window.push (window.back distance))
      (output ++ [window.back distance]) hnext hdnext
    refine ⟨?_, hrep⟩
    simpa only [copyWindow, Deflate.copyBack, hbyte] using hresult

/-- Splitting the loop does not change any read, including overlapping reads. -/
theorem copyWindow_add (distance first second : Nat) (window : Window) (output : List UInt8) :
    copyWindow distance second (copyWindow distance first window output).1
        (copyWindow distance first window output).2 =
      copyWindow distance (first + second) window output := by
  induction first generalizing window output with
  | zero => simp only [copyWindow, Nat.zero_add]
  | succ first ih =>
    simpa only [copyWindow, Nat.succ_add] using
      ih (window.push (window.back distance)) (output ++ [window.back distance])

theorem PendingMatch.distanceAvailable (s : PendingMatch) (h : s.Valid) :
    s.DistanceAvailable := by
  obtain ⟨hrep, hpos, hlimit, havail⟩ := h
  exact ⟨hpos, hlimit, Window.available _ _ _ hrep hlimit havail⟩

@[simp] theorem PendingMatch.copyN_zero (s : PendingMatch) : s.copyN 0 = s := by
  cases s
  rfl

@[simp] theorem PendingMatch.copyN_remaining (s : PendingMatch) (count : Nat) :
    (s.copyN count).remaining = s.remaining - count := rfl

@[simp] theorem PendingMatch.copyN_distance (s : PendingMatch) (count : Nat) :
    (s.copyN count).distance = s.distance := rfl

theorem PendingMatch.copyN_length (s : PendingMatch) (count : Nat) :
    (s.copyN count).output.length = s.output.length + count :=
  copyWindow_length s.distance count s.window s.output

theorem PendingMatch.copyN_output (s : PendingMatch) (count : Nat) (h : s.Valid) :
    (s.copyN count).output = Deflate.copyBack s.distance s.output count :=
  (copyWindow_correct s.distance count s.window s.output h.1 h.2.2.1 h.2.2.2).1

theorem PendingMatch.copyN_valid (s : PendingMatch) (count : Nat) (h : s.Valid) :
    (s.copyN count).Valid := by
  obtain ⟨hrep, hpos, hlimit, havail⟩ := h
  have hcopy := copyWindow_correct s.distance count s.window s.output hrep hlimit havail
  refine ⟨hcopy.2, hpos, hlimit, ?_⟩
  change s.distance ≤ (s.copyN count).output.length
  rw [s.copyN_length count]
  omega

/-- Exact composition includes the pending count, window and observation trace. -/
theorem PendingMatch.copyN_add (s : PendingMatch) (first second : Nat) :
    (s.copyN first).copyN second = s.copyN (first + second) := by
  have hcopy := copyWindow_add s.distance first second s.window s.output
  simp only [PendingMatch.copyN] at *
  rw [hcopy, Nat.sub_sub]

@[simp] theorem PendingMatch.advance_remaining (s : PendingMatch) (capacity : Nat) :
    (s.advance capacity).remaining = s.remaining - min s.remaining capacity := rfl

theorem PendingMatch.advance_count (s : PendingMatch) (capacity : Nat) :
    (s.advance capacity).output.length - s.output.length = min s.remaining capacity := by
  rw [PendingMatch.advance, s.copyN_length]
  omega

theorem PendingMatch.advance_output (s : PendingMatch) (capacity : Nat) (h : s.Valid) :
    (s.advance capacity).output =
      Deflate.copyBack s.distance s.output (min s.remaining capacity) :=
  s.copyN_output _ h

theorem PendingMatch.advance_append_emitted (s : PendingMatch) (capacity : Nat) :
    (s.advance capacity).output = s.output ++ s.emitted capacity := by
  obtain ⟨added, hadded⟩ := copyWindow_append s.distance (min s.remaining capacity)
    s.window s.output
  change (s.advance capacity).output = s.output ++ (s.advance capacity).output.drop s.output.length
  change (s.advance capacity).output = s.output ++ added at hadded
  rw [hadded]
  simp only [List.drop_left]

theorem PendingMatch.emitted_length (s : PendingMatch) (capacity : Nat) :
    (s.emitted capacity).length = min s.remaining capacity := by
  simp only [PendingMatch.emitted, List.length_drop, PendingMatch.advance, PendingMatch.copyN_length]
  omega

theorem PendingMatch.emitted_eq (s : PendingMatch) (capacity : Nat) (h : s.Valid) :
    s.emitted capacity =
      (Deflate.copyBack s.distance s.output (min s.remaining capacity)).drop s.output.length := by
  rw [PendingMatch.emitted, s.advance_output capacity h]

theorem PendingMatch.advance_valid (s : PendingMatch) (capacity : Nat) (h : s.Valid) :
    (s.advance capacity).Valid := s.copyN_valid _ h

@[simp] theorem PendingMatch.advance_zero (s : PendingMatch) : s.advance 0 = s := by
  simp only [PendingMatch.advance, Nat.min_zero, PendingMatch.copyN_zero]

theorem PendingMatch.advance_done (s : PendingMatch) (capacity : Nat) (h : s.remaining = 0) :
    s.advance capacity = s := by
  simp only [PendingMatch.advance, h, Nat.zero_min, PendingMatch.copyN_zero]

/-- A resumed MATCH can use different output-buffer boundaries without changing
the final pending count, history window or emitted bytes. -/
theorem PendingMatch.advance_add (s : PendingMatch) (first second : Nat) :
    (s.advance first).advance second = s.advance (first + second) := by
  simp only [PendingMatch.advance, PendingMatch.copyN_remaining, PendingMatch.copyN_add]
  have hcount : min s.remaining first + min (s.remaining - min s.remaining first) second =
      min s.remaining (first + second) := by omega
  rw [hcount]

theorem PendingMatch.advance_complete (s : PendingMatch) (capacity : Nat)
    (hcapacity : s.remaining ≤ capacity) (h : s.Valid) :
    (s.advance capacity).remaining = 0 ∧
      (s.advance capacity).output = Deflate.copyBack s.distance s.output s.remaining ∧
      (s.advance capacity).Valid := by
  refine ⟨?_, ?_, s.advance_valid capacity h⟩
  · simp only [PendingMatch.advance_remaining, Nat.min_eq_left hcapacity, Nat.sub_self]
  · simpa only [Nat.min_eq_left hcapacity] using s.advance_output capacity h

theorem PendingMatch.step_ok (s : PendingMatch) (capacity : Nat) (h : s.Valid) :
    s.step capacity = .ok (s.advance capacity) := by
  exact ite_eq_left (s.distanceAvailable h)

theorem PendingMatch.step_invalid (s : PendingMatch) (capacity : Nat)
    (h : ¬ s.DistanceAvailable) : s.step capacity = .error .invalidDistance :=
  ite_eq_right h

/-- The public checked helper composes on valid states, not merely its unchecked
arithmetic core. Suspension therefore preserves the precondition for resumption. -/
theorem PendingMatch.step_add (s : PendingMatch) (first second : Nat) (h : s.Valid) :
    (s.step first).bind (fun next => next.step second) = s.step (first + second) := by
  rw [s.step_ok first h, s.step_ok (first + second) h]
  dsimp only [Except.bind]
  rw [(s.advance first).step_ok second (s.advance_valid first h), s.advance_add]

/-- Saved history represents the preceding calls; the current buffer is an
additional suffix of the complete logical output. -/
theorem BufferedHistory.window_represents (s : BufferedHistory) (past : List UInt8)
    (h : s.saved.Represents past) : s.window.Represents (past ++ s.current) := by
  simp only [BufferedHistory.window, Window.ofOutput, Window.Represents] at *
  rw [h, keepWindow_append]

theorem BufferedHistory.nextBuffer_represents (s : BufferedHistory) (past : List UInt8)
    (h : s.saved.Represents past) :
    s.nextBuffer.saved.Represents (past ++ s.current) := s.window_represents past h

theorem BufferedHistory.nextBuffer_window (s : BufferedHistory) :
    s.nextBuffer.window = s.window := by
  have hid := keepWindow_append (s.saved.bytes ++ s.current) []
  simpa only [BufferedHistory.nextBuffer, BufferedHistory.window, Window.ofOutput,
    List.append_nil, Window.mk.injEq] using hid

/-- The source's current-output case uses precisely these bytes. -/
theorem BufferedHistory.back_current (s : BufferedHistory) (distance : Nat)
    (hlimit : distance ≤ windowLimit) (hcurrent : distance ≤ s.current.length) :
    s.window.back distance = s.current.getD (s.current.length - distance) 0 := by
  have hrep : s.window.Represents (s.saved.bytes ++ s.current) := by
    simp only [BufferedHistory.window, Window.ofOutput, Window.Represents]
  rw [Window.back_eq _ _ _ hrep hlimit (by simp only [List.length_append]; omega)]
  simp only [List.length_append, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  rw [show s.saved.bytes.length + s.current.length - distance - s.saved.bytes.length =
    s.current.length - distance by omega]

/-- When current output is too short, the remainder of the distance addresses
the saved window. This distinguishes the two source MATCH addressing cases. -/
theorem BufferedHistory.back_saved (s : BufferedHistory) (distance : Nat)
    (hlimit : distance ≤ windowLimit) (hpast : s.current.length < distance)
    (havailable : distance ≤ s.saved.bytes.length + s.current.length) :
    s.window.back distance =
      s.saved.bytes.getD (s.saved.bytes.length - (distance - s.current.length)) 0 := by
  have hrep : s.window.Represents (s.saved.bytes ++ s.current) := by
    simp only [BufferedHistory.window, Window.ofOutput, Window.Represents]
  rw [Window.back_eq _ _ _ hrep hlimit (by simpa only [List.length_append] using havailable)]
  simp only [List.length_append, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by omega)]
  rw [show s.saved.bytes.length + s.current.length - distance =
    s.saved.bytes.length - (distance - s.current.length) by omega]

theorem overlap_reads_new_bytes (byte : UInt8) :
    (copyWindow 1 2 ⟨[byte]⟩ [byte]).2 = [byte, byte, byte] := by
  have hrep : (Window.mk [byte]).Represents [byte] := by
    change [byte] = keepWindow [byte]
    exact (keepWindow_of_short [byte] (by change 1 ≤ 32768; decide)).symm
  calc
    _ = Deflate.copyBack 1 [byte] 2 :=
      (copyWindow_correct 1 2 ⟨[byte]⟩ [byte] hrep (by decide) (by simp)).1
    _ = _ := rfl

theorem reject_unavailable_distance :
    (PendingMatch.mk 2 3 ⟨[65]⟩ [65]).step 3 = .error .invalidDistance := by rfl

theorem reject_zero_distance :
    (PendingMatch.mk 0 3 ⟨[65]⟩ [65]).step 3 = .error .invalidDistance := by rfl

end Silmaril.Formats.Compression.Inflate.Stream
