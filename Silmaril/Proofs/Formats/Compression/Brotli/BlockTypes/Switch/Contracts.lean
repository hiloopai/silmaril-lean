module

public import Silmaril.Formats.Compression.Brotli.BlockTypes.Switch.Defs
import Silmaril.Formats.Compression.Brotli.BlockTypes.Thms
import Silmaril.Formats.Compression.Brotli.Huffman.Description.Thms
import Silmaril.Formats.Compression.Bits.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.BlockTypes.Switch

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.BlockTypes
open Silmaril.Formats.Compression.Brotli.BlockTypes.Switch
open Huffman.Description (Table)

private theorem bind_ok {ε α β : Type} {action : Except ε α} {next : α → Except ε β} {out : β}
    (read : (action >>= next) = .ok out) :
    ∃ value, action = .ok value ∧ next value = .ok out := by
  cases action with
  | error _ => cases read
  | ok value => exact ⟨value, rfl, read⟩

private theorem map_ok {ε δ α : Type} {action : Except ε α} {f : ε → δ} {out : α}
    (read : action.mapError f = .ok out) : action = .ok out := by
  cases action <;> cases read <;> rfl

theorem start_valid {control : Control} {bits : List Bool} (wire : ControlWire bits control) :
    (Run.start control).Valid control ∧ 0 < (Run.start control).remaining := by
  have limits := wire.bounds
  cases wire with
  | single => decide
  | @multiple types base _ _ _ _ extra _ _ _ _ _ multi _ _ _ _ _ _ _ =>
    obtain ⟨_, _, low, high⟩ := limits
    change (0 < types ∧ 1 < types ∧ base + extra ≤ 16793840) ∧ 0 < base + extra
    exact ⟨⟨by omega, by omega, high⟩, low⟩

theorem read_sound {category : Category} {control : Control} {bitLimit : Nat} {run next : Run}
    {before after : LSBReader} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (read : Switch.read category control bitLimit run before = .ok (next, after)) :
    next.Valid control ∧
    ∃ used suffix, Wire control run used next ∧ input = used ++ suffix ∧ after.Rep suffix ∧
      after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit := by
  unfold Switch.read at read
  split at read
  · cases read
  · rename_i valid
    have validState : run.Valid control := Decidable.not_not.mp valid
    split at read
    · rename_i hasRemaining
      cases read
      exact ⟨⟨validState.1, validState.2.1, Nat.le_trans (Nat.sub_le ..) validState.2.2⟩,
        [], input, .keep (Nat.pos_of_ne_zero hasRemaining), rfl, rep, count, by simp, by simp⟩
    · rename_i depleted
      cases control with
      | single => cases read
      | multiple types typeTable countTable initial =>
        obtain ⟨⟨symbol, cursor⟩, typeRead, read⟩ := bind_ok read
        dsimp only at read
        split at read
        · cases read
        · rename_i target
          obtain ⟨⟨length, stop⟩, lengthRead, done⟩ := bind_ok read
          cases done
          obtain ⟨code, width, tail, assigned, codeBound, typeCap, split, tailRep, tailCount, position⟩ :=
            Table.readBounded_sound rep count (map_ok typeRead)
          obtain ⟨usedLength, suffix, lengthWire, splitTail, afterRep, afterCount, afterPosition, lengthCap⟩ :=
            readLength_sound tailRep tailCount (map_ok lengthRead)
          have lengthBound := lengthWire.bounds
          have targetFit := Nat.lt_of_not_ge target
          refine ⟨⟨targetFit, validState.1, ?_⟩, _, suffix,
            .switch rfl (by omega) assigned codeBound targetFit lengthWire,
            ?_, afterRep, afterCount, ?_, ?_⟩
          · change length - 1 ≤ 16793840
            omega
          · rw [split, splitTail, List.append_assoc]
          · simp only [afterPosition, position, List.length_append, msbBits_length, Nat.add_assoc]
          · simp only [List.length_append, msbBits_length]
            omega

theorem select_sound {controls : Controls} {category : Category} {bitLimit : Nat}
    {state next : State} {before after : LSBReader} {input : List Bool} (rep : before.Rep input)
    (count : before.count < 8) (read : select controls category bitLimit state before = .ok (next, after)) :
    (next.get category).Valid (category.control controls) ∧
    (∀ other, other ≠ category → next.get other = state.get other) ∧
    ∃ used suffix, Wire (category.control controls) (state.get category) used (next.get category) ∧
      input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit := by
  unfold select at read
  obtain ⟨⟨run, reader⟩, step, done⟩ := bind_ok read
  cases done
  have only : (state.set run category).get category = run := by cases category <;> rfl
  rw [only]
  obtain ⟨valid, wire⟩ := read_sound rep count step
  refine ⟨valid, ?_, wire⟩
  intro other different
  cases category <;> cases other <;> simp_all [State.get, State.set]

theorem read_error {category : Category} {control : Control} {bitLimit : Nat} {run : Run}
    {before : LSBReader} {input : List Bool} {error : Switch.Error}
    (rep : before.Rep input) (count : before.count < 8)
    (read : Switch.read category control bitLimit run before = .error error) :
    Failure category control bitLimit run before input error := by
  unfold Switch.read at read
  split at read
  · rename_i invalid
    cases read
    exact .invalidState invalid
  · rename_i valid
    have validState : run.Valid control := Decidable.not_not.mp valid
    split at read
    · cases read
    · rename_i depleted
      cases control with
      | single =>
        cases read
        exact .singleExhausted validState rfl (by omega)
      | multiple types typeTable countTable initial =>
        cases decoded : typeTable.readBounded bitLimit before with
        | error reason =>
          simp only [decoded, Except.mapError, bind, Except.bind] at read
          cases read
          exact .typeSymbol validState (by omega) rfl decoded
        | ok pair =>
          obtain ⟨symbol, cursor⟩ := pair
          simp only [decoded, Except.mapError, bind, Except.bind] at read
          split at read
          · rename_i outside
            cases read
            exact .typeRange validState (by omega) rfl decoded outside
          · rename_i target
            cases parsed : readLength countTable (bitLimit - (cursor.totalRead - before.totalRead)) cursor with
            | ok pair =>
              obtain ⟨_, _⟩ := pair
              simp only [parsed] at read
              cases read
            | error reason =>
              simp only [parsed] at read
              cases read
              obtain ⟨code, width, suffix, assigned, _, budget, split, tailRep, _, position⟩ :=
                Table.readBounded_sound rep count decoded
              exact .length validState (by omega) rfl decoded (Nat.lt_of_not_ge target)
                assigned split tailRep position budget parsed

theorem select_error {controls : Controls} {category : Category} {bitLimit : Nat}
    {state : State} {before : LSBReader} {input : List Bool} {error : Switch.Error}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : select controls category bitLimit state before = .error error) :
    Failure category (category.control controls) bitLimit (state.get category) before input error := by
  unfold select at parsed
  cases step : Switch.read category (category.control controls) bitLimit (state.get category) before with
  | error reason =>
    simp only [step, bind, Except.bind] at parsed
    cases parsed
    exact read_error rep count step
  | ok value =>
    obtain ⟨_, _⟩ := value
    simp only [step, bind, Except.bind] at parsed
    cases parsed

theorem Failure.offset {category : Category} {control : Control} {bitLimit : Nat} {state : Run}
    {before : LSBReader} {input : List Bool} {error : Switch.Error}
    (failure : Failure category control bitLimit state before input error) :
    ∃ used suffix, input = used ++ suffix ∧ error.bit = before.totalRead + used.length := by
  cases failure with
  | invalidState | singleExhausted | typeSymbol | typeRange =>
    exact ⟨[], input, rfl, by simp⟩
  | length _ _ _ _ _ _ split _ position _ _ =>
    exact ⟨_, _, split, by simpa only [msbBits_length] using position⟩

end Silmaril.Proofs.Formats.Compression.Brotli.BlockTypes.Switch
