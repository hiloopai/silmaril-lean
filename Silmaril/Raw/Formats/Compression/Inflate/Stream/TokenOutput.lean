module

public import Silmaril.Formats.Compression.Inflate.Stream.TokenOutput
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.History
public import Silmaril.Raw.Formats.Compression.Inflate.Manual.Symbols

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.TokenOutput`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream

open Silmaril.Formats.Compression

theorem TokenOutput.start_valid (window : Window) (output : List UInt8) (token : Manual.Token)
    (hrep : window.Represents output) (h : TokenFitsHistory output token) :
    (TokenOutput.start window output token).Valid := by
  cases token <;> exact ⟨hrep, h⟩

theorem TokenOutput.start_remaining (window : Window) (output : List UInt8) (token : Manual.Token) :
    (TokenOutput.start window output token).remaining = tokenLength token := by
  cases token <;> rfl

theorem TokenOutput.finishMatch_remaining (m : PendingMatch) :
    (TokenOutput.finishMatch m).remaining = m.remaining := by
  by_cases hz : m.remaining = 0
  · simp only [TokenOutput.finishMatch, TokenOutput.remaining, hz, ite_true]
  · simp only [TokenOutput.finishMatch, ite_eq_right hz, TokenOutput.remaining]

theorem TokenOutput.advance_remaining (s : TokenOutput) (capacity : Nat) :
    (s.advance capacity).remaining = s.remaining - min s.remaining capacity := by
  cases hp : s.phase with
  | literal byte =>
    by_cases hc : capacity = 0
    · simp only [TokenOutput.advance, hp, TokenOutput.remaining,
        hc, Nat.min_zero, Nat.sub_zero, ite_true]
    · have hmin : min 1 capacity = 1 := by omega
      simp only [TokenOutput.advance, hp, ite_eq_right hc, TokenOutput.remaining, hmin, Nat.sub_self]
  | matchBytes count distance =>
    simp only [TokenOutput.advance, hp]
    rw [TokenOutput.finishMatch_remaining, PendingMatch.advance_remaining]
    simp only [TokenOutput.asMatch, TokenOutput.remaining, hp]
  | endBlock | complete _ =>
    simp only [TokenOutput.advance, hp, TokenOutput.remaining, Nat.zero_min, Nat.sub_zero]

theorem TokenOutput.advance_length (s : TokenOutput) (capacity : Nat) :
    (s.advance capacity).output.length = s.output.length + min s.remaining capacity := by
  cases hp : s.phase with
  | literal byte =>
    by_cases hc : capacity = 0
    · simp only [TokenOutput.advance, hp, TokenOutput.remaining,
        hc, Nat.min_zero, Nat.add_zero, ite_true]
    · have hmin : min 1 capacity = 1 := by omega
      simp only [TokenOutput.advance, hp, ite_eq_right hc, TokenOutput.remaining,
        List.length_append, List.length_singleton, hmin]
  | matchBytes count distance =>
    simp only [TokenOutput.advance, hp, TokenOutput.finishMatch, TokenOutput.remaining]
    exact PendingMatch.copyN_length (s.asMatch count distance) (min count capacity)
  | endBlock | complete _ =>
    simp only [TokenOutput.advance, hp, TokenOutput.remaining, Nat.zero_min, Nat.add_zero]

theorem TokenOutput.advance_append_emitted (s : TokenOutput) (capacity : Nat) :
    (s.advance capacity).output = s.output ++ s.emitted capacity := by
  cases hp : s.phase with
  | literal byte =>
    by_cases hc : capacity = 0
    · simp only [TokenOutput.emitted, TokenOutput.advance, hp, ite_eq_left hc,
        List.drop_length, List.append_nil]
    · simp only [TokenOutput.emitted, TokenOutput.advance, hp, ite_eq_right hc,
        List.drop_left]
  | matchBytes count distance =>
    simpa only [TokenOutput.emitted, TokenOutput.advance, hp, TokenOutput.finishMatch,
      PendingMatch.emitted, TokenOutput.asMatch] using
      PendingMatch.advance_append_emitted (s.asMatch count distance) capacity
  | endBlock | complete _ =>
    simp only [TokenOutput.emitted, TokenOutput.advance, hp, List.drop_length, List.append_nil]

theorem TokenOutput.emitted_length (s : TokenOutput) (capacity : Nat) :
    (s.emitted capacity).length = min s.remaining capacity := by
  simp only [TokenOutput.emitted, List.length_drop, TokenOutput.advance_length]
  omega

theorem TokenOutput.emitted_capacity (s : TokenOutput) (capacity : Nat) :
    (s.emitted capacity).length ≤ capacity := by
  rw [s.emitted_length]
  exact Nat.min_le_right _ _

theorem TokenOutput.finishMatch_valid (m : PendingMatch) (h : m.Valid) :
    (TokenOutput.finishMatch m).Valid := by
  by_cases hz : m.remaining = 0
  · simp only [TokenOutput.finishMatch, ite_eq_left hz, TokenOutput.Valid]
    exact ⟨h.1, trivial⟩
  · simp only [TokenOutput.finishMatch, ite_eq_right hz, TokenOutput.Valid]
    exact ⟨h.1, h.2⟩

theorem TokenOutput.advance_valid (s : TokenOutput) (capacity : Nat) (h : s.Valid) :
    (s.advance capacity).Valid := by
  cases hp : s.phase with
  | literal byte =>
    by_cases hc : capacity = 0
    · simpa only [TokenOutput.advance, hp, ite_eq_left hc] using h
    · simp only [TokenOutput.advance, hp, ite_eq_right hc, TokenOutput.Valid]
      exact ⟨Window.push_represents s.window s.output byte h.1, trivial⟩
  | matchBytes count distance =>
    have hm : (s.asMatch count distance).Valid := by
      change s.window.Represents s.output ∧
        0 < distance ∧ distance ≤ windowLimit ∧ distance ≤ s.output.length
      exact ⟨h.1, by simpa only [hp] using h.2⟩
    simpa only [TokenOutput.advance, hp] using
      TokenOutput.finishMatch_valid _ (PendingMatch.advance_valid _ capacity hm)
  | endBlock =>
    simp only [TokenOutput.advance, hp, TokenOutput.Valid]
    exact ⟨h.1, trivial⟩
  | complete flag => simpa only [TokenOutput.advance, hp] using h

theorem TokenOutput.finishMatch_advance (m : PendingMatch) (capacity : Nat) :
    (TokenOutput.finishMatch m).advance capacity = TokenOutput.finishMatch (m.advance capacity) := by
  by_cases hz : m.remaining = 0
  · rw [m.advance_done capacity hz]
    simp only [TokenOutput.finishMatch, hz, ite_eq_left, TokenOutput.advance]
  · simp only [TokenOutput.finishMatch, ite_eq_right hz, TokenOutput.advance,
      TokenOutput.asMatch]

/-- Output chunking preserves every state component, including the pending
distance/length and the updated bounded window. -/
theorem TokenOutput.advance_add (s : TokenOutput) (first second : Nat) :
    (s.advance first).advance second = s.advance (first + second) := by
  cases hp : s.phase with
  | literal byte =>
    by_cases ha : first = 0
    · simp only [TokenOutput.advance, hp, ha, ite_eq_left, Nat.zero_add]
    · have hab : first + second ≠ 0 := by omega
      simp only [TokenOutput.advance, hp, ite_eq_right ha, ite_eq_right hab]
  | matchBytes count distance =>
    have hfirst : s.advance first = TokenOutput.finishMatch ((s.asMatch count distance).advance first) := by
      simp only [TokenOutput.advance, hp]
    have htotal : s.advance (first + second) =
        TokenOutput.finishMatch ((s.asMatch count distance).advance (first + second)) := by
      simp only [TokenOutput.advance, hp]
    rw [hfirst, htotal, TokenOutput.finishMatch_advance, PendingMatch.advance_add]
  | endBlock => simp only [TokenOutput.advance, hp]
  | complete flag => simp only [TokenOutput.advance, hp]

theorem TokenOutput.advance_fold (s : TokenOutput) (capacities : List Nat) (spent : Nat) :
    capacities.foldl TokenOutput.advance (s.advance spent) = s.advance (spent + capacities.sum) := by
  induction capacities generalizing spent with
  | nil => simp only [List.foldl_nil, List.sum_nil, Nat.add_zero]
  | cons capacity rest ih =>
    simp only [List.foldl_cons, List.sum_cons]
    rw [s.advance_add, ih]
    rw [Nat.add_assoc]

theorem TokenOutput.runBuffers_eq (s : TokenOutput) (capacities : List Nat) :
    s.runBuffers capacities = s.advance capacities.sum := by
  simpa only [TokenOutput.runBuffers, Nat.zero_add] using s.advance_fold capacities 0

theorem TokenOutput.distanceAvailable (s : TokenOutput) (h : s.Valid) : s.DistanceAvailable := by
  cases hp : s.phase with
  | matchBytes count distance =>
    have hd : 0 < distance ∧ distance ≤ windowLimit ∧ distance ≤ s.output.length := by
      simpa only [hp] using h.2
    simp only [TokenOutput.DistanceAvailable, hp]
    exact ⟨hd.1, hd.2.1, Window.available s.window s.output distance h.1 hd.2.1 hd.2.2⟩
  | literal _ | endBlock | complete _ => simp only [TokenOutput.DistanceAvailable, hp]

theorem TokenOutput.step_ok (s : TokenOutput) (capacity : Nat) (h : s.Valid) :
    s.step capacity = .ok (s.advance capacity) := ite_eq_left (s.distanceAvailable h)

theorem TokenOutput.step_invalid (s : TokenOutput) (capacity : Nat)
    (h : ¬ s.DistanceAvailable) : s.step capacity = .error .invalidDistance := ite_eq_right h

theorem TokenOutput.step_add (s : TokenOutput) (first second : Nat) (h : s.Valid) :
    (s.step first).bind (fun next => next.step second) = s.step (first + second) := by
  rw [s.step_ok first h, s.step_ok (first + second) h]
  dsimp only [Except.bind]
  rw [(s.advance first).step_ok second (s.advance_valid first h), s.advance_add]

/-- Completing an arbitrarily long well-formed token agrees exactly with the
existing token application, including the unchanged reader and EOB flag. -/
theorem TokenOutput.complete_eq_applyToken (window : Window) (output : List UInt8)
    (token : Manual.Token) (reader : LSBReader) (capacity : Nat)
    (hrep : window.Represents output) (h : TokenFitsHistory output token)
    (hcapacity : tokenLength token ≤ capacity) :
    Except.ok ((TokenOutput.start window output token).advance capacity |>.observe reader) =
      (Manual.applyToken output token reader).map some := by
  cases token with
  | literal byte =>
    have hc : capacity ≠ 0 := by change 1 ≤ capacity at hcapacity; omega
    simp only [TokenOutput.start, TokenOutput.advance, ite_eq_right hc,
      TokenOutput.observe, Manual.applyToken, Except.map]
  | endBlock => rfl
  | matchBytes length distance =>
    let m : PendingMatch := ⟨distance, length, window, output⟩
    have hm : m.Valid := ⟨hrep, h⟩
    have hc := m.advance_complete capacity hcapacity hm
    have hno : ¬ distance > output.length := by
      have := h.2.2
      omega
    simp only [Manual.applyToken, ite_eq_right hno, Except.map]
    change Except.ok ((TokenOutput.finishMatch (m.advance capacity)).observe reader) = _
    simp only [TokenOutput.finishMatch, hc.1, ite_true, TokenOutput.observe]
    rw [hc.2.1]

/-- Checked output completion has the same successful observation, rather than
only the unchecked transition used inside the implementation. -/
theorem TokenOutput.step_complete_eq_applyToken (window : Window) (output : List UInt8)
    (token : Manual.Token) (reader : LSBReader) (capacity : Nat)
    (hrep : window.Represents output) (h : TokenFitsHistory output token)
    (hcapacity : tokenLength token ≤ capacity) :
    ((TokenOutput.start window output token).step capacity).map
        (fun next => next.observe reader) =
      ((Manual.applyToken output token reader).map some).mapError
        (fun _ => MatchError.invalidDistance) := by
  rw [(TokenOutput.start window output token).step_ok capacity
    (TokenOutput.start_valid window output token hrep h)]
  rw [← TokenOutput.complete_eq_applyToken window output token reader capacity hrep h hcapacity]
  rfl

/-- Any two capacities with enough combined space yield the very same completed
observation. Neither output-buffer boundary alters token semantics. -/
theorem TokenOutput.split_complete_eq_applyToken (window : Window) (output : List UInt8)
    (token : Manual.Token) (reader : LSBReader) (first second : Nat)
    (hrep : window.Represents output) (h : TokenFitsHistory output token)
    (hcapacity : tokenLength token ≤ first + second) :
    Except.ok (((TokenOutput.start window output token).advance first).advance second |>.observe reader) =
      (Manual.applyToken output token reader).map some := by
  rw [TokenOutput.advance_add]
  exact TokenOutput.complete_eq_applyToken window output token reader _ hrep h hcapacity

/-- Any finite sequence of offered capacities has the same completion result
as their total, including zero-capacity buffers at any positions. -/
theorem TokenOutput.buffers_complete_eq_applyToken (window : Window) (output : List UInt8)
    (token : Manual.Token) (reader : LSBReader) (capacities : List Nat)
    (hrep : window.Represents output) (h : TokenFitsHistory output token)
    (hcapacity : tokenLength token ≤ capacities.sum) :
    Except.ok ((TokenOutput.start window output token).runBuffers capacities |>.observe reader) =
      (Manual.applyToken output token reader).map some := by
  rw [TokenOutput.runBuffers_eq]
  exact TokenOutput.complete_eq_applyToken window output token reader _ hrep h hcapacity

/-- Distances beyond available logical history are also absent from its bounded
representation, so they are rejected before any output is emitted. -/
theorem TokenOutput.reject_unavailable_match (window : Window) (output : List UInt8)
    (count distance capacity : Nat) (hrep : window.Represents output)
    (hdistance : output.length < distance) :
    (TokenOutput.start window output (.matchBytes count distance)).step capacity =
      .error .invalidDistance := by
  apply TokenOutput.step_invalid
  simp only [TokenOutput.start, TokenOutput.DistanceAvailable]
  intro havail
  have hlen : window.bytes.length ≤ output.length := by
    rw [hrep, keepWindow_length]
    exact Nat.min_le_left _ _
  omega

theorem TokenOutput.reject_zero_match (window : Window) (output : List UInt8)
    (count capacity : Nat) :
    (TokenOutput.start window output (.matchBytes count 0)).step capacity =
      .error .invalidDistance := by
  apply TokenOutput.step_invalid
  simp only [TokenOutput.start, TokenOutput.DistanceAvailable, Nat.lt_irrefl, false_and, not_false_eq_true]

theorem TokenOutput.reject_oversize_match (window : Window) (output : List UInt8)
    (count distance capacity : Nat) (h : windowLimit < distance) :
    (TokenOutput.start window output (.matchBytes count distance)).step capacity =
      .error .invalidDistance := by
  apply TokenOutput.step_invalid
  simp only [TokenOutput.start, TokenOutput.DistanceAvailable]
  omega

end Silmaril.Formats.Compression.Inflate.Stream
