module

public import Silmaril.Formats.Compression.Brotli.BlockTypes.Switch.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.BlockTypes.Switch.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.BlockTypes.Switch

theorem start_valid {control : Control} {bits : List Bool} (wire : ControlWire bits control) :
    (Run.start control).Valid control ∧ 0 < (Run.start control).remaining :=
  Proofs.Formats.Compression.Brotli.BlockTypes.Switch.start_valid wire

theorem read_sound {category : Category} {control : Control} {bitLimit : Nat} {run next : Run}
    {before after : LSBReader} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (read : read category control bitLimit run before = .ok (next, after)) :
    next.Valid control ∧
    ∃ used suffix, Wire control run used next ∧ input = used ++ suffix ∧ after.Rep suffix ∧
      after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit :=
  Proofs.Formats.Compression.Brotli.BlockTypes.Switch.read_sound rep count read

/-- One category's switch and debit leave the other two histories intact. -/
theorem select_sound {controls : Controls} {category : Category} {bitLimit : Nat}
    {state next : State} {before after : LSBReader} {input : List Bool} (rep : before.Rep input)
    (count : before.count < 8) (read : select controls category bitLimit state before = .ok (next, after)) :
    (next.get category).Valid (category.control controls) ∧
    (∀ other, other ≠ category → next.get other = state.get other) ∧
    ∃ used suffix, Wire (category.control controls) (state.get category) used (next.get category) ∧
      input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit :=
  Proofs.Formats.Compression.Brotli.BlockTypes.Switch.select_sound rep count read

theorem read_error {category : Category} {control : Control} {bitLimit : Nat} {run : Run}
    {before : LSBReader} {input : List Bool} {error : Error}
    (rep : before.Rep input) (count : before.count < 8)
    (read : read category control bitLimit run before = .error error) :
    Failure category control bitLimit run before input error :=
  Proofs.Formats.Compression.Brotli.BlockTypes.Switch.read_error rep count read

theorem select_error {controls : Controls} {category : Category} {bitLimit : Nat}
    {state : State} {before : LSBReader} {input : List Bool} {error : Error}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : select controls category bitLimit state before = .error error) :
    Failure category (category.control controls) bitLimit (state.get category) before input error :=
  Proofs.Formats.Compression.Brotli.BlockTypes.Switch.select_error rep count parsed

end Silmaril.Formats.Compression.Brotli.BlockTypes.Switch
