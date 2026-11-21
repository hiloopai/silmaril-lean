module

public import Silmaril.Formats.Blake3Cas.RangeFacts.Projection.Defs

public section

namespace Silmaril.Proofs.Formats.Blake3Cas.RangeFacts.Projection

open Silmaril.Crypto.Blake3
open Silmaril.Formats
open Silmaril.Formats.Blake3Cas
open Silmaril.Formats.Blake3Cas.RangeFacts.Projection

theorem append {size base : Nat} {digest left right : Bytes} {lhs rhs : List (SpanFact size digest)}
    (first : Contiguous base lhs left) (last : Contiguous (base + left.length) rhs right) :
    Contiguous base (lhs ++ rhs) (left ++ right) := by
  induction first with
  | nil => simpa using last
  | cons offset next ih =>
    rw [List.cons_append, List.append_assoc]
    exact .cons offset (ih (by simpa [Nat.add_assoc] using last))

private theorem clip_take_drop (request : Bao.RangeRequest) (base : Nat) (bytes : Bytes) :
    clip request base bytes = (bytes.take (request.start + request.count - base)).drop (request.start - base) := by
  rw [clip, List.drop_take]
  have width : min (request.start + request.count) (base + bytes.length) - max request.start base =
      min (request.start + request.count - base - (request.start - base)) (bytes.drop (request.start - base)).length := by
    simp only [List.length_drop]
    omega
  rw [width, ← List.take_take, List.take_length]

private theorem clip_append (request : Bao.RangeRequest) (base : Nat) (left right : Bytes) :
    clip request base (left ++ right) = clip request base left ++ clip request (base + left.length) right := by
  simp only [clip_take_drop, List.take_append, List.drop_append, List.length_take]
  have count : request.start + request.count - base - left.length = request.start + request.count - (base + left.length) := by
    omega
  have start : request.start - base - min (request.start + request.count - base) left.length = request.start - (base + left.length) := by
    omega
  rw [count, start]

private theorem project_data {size base : Nat} {digest : Bytes} (request : Bao.RangeRequest) (fact : SpanFact size digest)
    (offset : fact.offset = base) :
    ∃ advance,
      project? request (cursorAt request base) fact = some ⟨cursorAt request (base + fact.bytes.length), advance⟩ ∧
      advance.bytes = clip request base fact.bytes := by
  cases fact with
  | mk start raw checked =>
    change start = base at offset
    subst base
    let lo := max request.start start
    let hi := min (request.start + request.count) (start + raw.length)
    by_cases overlap : lo < hi
    · let shift := lo - start
      let bytes := (raw.drop shift).take (hi - lo)
      have front : cursorAt request start = lo := by unfold cursorAt; dsimp [lo, hi] at *; omega
      have back : cursorAt request (start + raw.length) = hi := by unfold cursorAt; dsimp [lo, hi] at *; omega
      have shiftEq : shift = request.start - start := by dsimp [shift, lo]; omega
      have len : bytes.length = hi - lo := by
        simp only [bytes, List.length_take, List.length_drop]
        dsimp [shift, lo, hi] at *
        omega
      have valid : start + shift = cursorAt request start ∧ 0 < bytes.length ∧
          shift + bytes.length ≤ raw.length ∧ cursorAt request start + bytes.length = hi := by
        rw [front, len]
        dsimp [shift, lo, hi] at *
        omega
      rw [back, ← valid.2.2.2]
      unfold project?
      dsimp only
      rw [ite_eq_left overlap, dite_eq_left valid]
      exact ⟨_, rfl, by change bytes = clip request start raw; simp only [bytes, clip, shiftEq, lo, hi]⟩
    · have back : cursorAt request (start + raw.length) = cursorAt request start := by
        unfold cursorAt
        dsimp [lo, hi] at overlap
        omega
      have empty : clip request start raw = [] := by
        have zero : hi - lo = 0 := by omega
        change (raw.drop (request.start - start)).take (hi - lo) = []
        simp [zero]
      rw [back, empty]
      refine ⟨.skip _, ?_, rfl⟩
      unfold project?
      dsimp only
      rw [ite_eq_right overlap]

theorem project {size base : Nat} {digest bytes : Bytes} {fields : List Bytes} (request : Bao.RangeRequest)
    (tape : Tape size digest fields) (contiguous : Contiguous base tape.spans bytes) :
    ∃ coverage,
      tape.project? request (cursorAt request base) = some ⟨cursorAt request (base + bytes.length), coverage⟩ ∧
      coverage.bytes = clip request base bytes := by
  induction tape generalizing base bytes with
  | nil =>
    cases contiguous
    simp only [List.length_nil, Nat.add_zero]
    exact ⟨.nil _, rfl, by simp [clip, Coverage.bytes]⟩
  | cons cell tail ih =>
    cases cell with
    | pair span root lcv rcv expected wire hit location =>
      obtain ⟨coverage, done, values⟩ := ih contiguous
      exact ⟨.cons (.skip _) coverage, by simp [Tape.project?, Cell.project?, done], by simpa [Coverage.bytes, Advance.bytes]⟩
    | data span fact location =>
      change Contiguous base (fact :: tail.spans) bytes at contiguous
      cases contiguous with
      | cons offset next =>
        rename_i rest
        have total : base + (fact.bytes ++ rest).length = base + fact.bytes.length + rest.length := by simp [Nat.add_assoc]
        rw [total]
        obtain ⟨advance, advanced, headBytes⟩ := project_data request fact offset
        obtain ⟨coverage, done, tailBytes⟩ := ih next
        exact ⟨.cons advance coverage, by simp [Tape.project?, Cell.project?, advanced, done],
          by simp [Coverage.bytes, headBytes, tailBytes, clip_append]⟩

theorem range {size base : Nat} {digest bytes : Bytes} {fields : List Bytes} (request : Bao.RangeRequest)
    (body : CompleteBody size digest fields) (contiguous : Contiguous base body.tape.spans bytes)
    (starts : base ≤ request.start) (ends : request.start + request.count ≤ base + bytes.length)
    (within : request.start + request.count ≤ size) :
    ∃ result, body.range? request = some result ∧
      result.coverage.bytes = (bytes.drop (request.start - base)).take request.count := by
  have startEq : cursorAt request base = request.start := by unfold cursorAt; omega
  have endEq : cursorAt request (base + bytes.length) = request.start + request.count := by unfold cursorAt; omega
  have projection := project request body.tape contiguous
  rw [startEq, endEq] at projection
  obtain ⟨coverage, projected, values⟩ := projection
  refine ⟨⟨within, coverage⟩, ?_, ?_⟩
  · simp only [CompleteBody.range?, dite_eq_left within, projected, Option.bind_eq_bind, Option.bind_some]
    rfl
  · simpa only [clip, Nat.min_eq_left ends, Nat.max_eq_left starts, Nat.add_sub_cancel_left] using values

end Silmaril.Proofs.Formats.Blake3Cas.RangeFacts.Projection
