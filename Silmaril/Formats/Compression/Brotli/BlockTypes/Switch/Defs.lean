module

public import Silmaril.Formats.Compression.Brotli.BlockTypes.Defs

/-! RFC 7932 §6 and §9.3 payload block switches. One selection is
    debited per coded symbol of the selected category. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.BlockTypes.Switch

inductive Category where
  | literal
  | insertCopy
  | distance
  deriving DecidableEq, Repr

def Category.control (controls : Controls) : Category → Control
  | .literal => controls.literal
  | .insertCopy => controls.insertCopy
  | .distance => controls.distance

structure Run where
  current : Nat
  previous : Nat
  remaining : Nat
  deriving DecidableEq, Repr

def maxCount : Control → Nat
  | .single => 16777216
  | .multiple .. => 16793840

/-- The implicit single-type quota is the maximum MLEN. Multi-type
    runs begin at type zero with previous type one. -/
def Run.start : Control → Run
  | .single => ⟨0, 0, 16777216⟩
  | .multiple _ _ _ count => ⟨0, 1, count⟩

abbrev Run.Valid (control : Control) (run : Run) : Prop :=
  run.current < control.typeCount ∧ run.previous < control.typeCount ∧ run.remaining ≤ maxCount control

structure State where
  literal : Run
  insertCopy : Run
  distance : Run
  deriving DecidableEq, Repr

def State.start (controls : Controls) : State :=
  ⟨Run.start controls.literal, Run.start controls.insertCopy, Run.start controls.distance⟩

def State.get (state : State) : Category → Run
  | .literal => state.literal
  | .insertCopy => state.insertCopy
  | .distance => state.distance

def State.set (state : State) (run : Run) : Category → State
  | .literal => { state with literal := run }
  | .insertCopy => { state with insertCopy := run }
  | .distance => { state with distance := run }

def nextType (types : Nat) (run : Run) : Nat → Nat
  | 0 => run.previous
  | 1 => if run.current + 1 = types then 0 else run.current + 1
  | symbol + 2 => symbol

def Run.debit (run : Run) : Run := { run with remaining := run.remaining - 1 }

def Run.switched (run : Run) (types symbol length : Nat) : Run :=
  ⟨nextType types run symbol, run.current, length - 1⟩

inductive Cause where
  | invalidState
  | singleExhausted
  | typeSymbol (reason : Huffman.Description.SymbolError)
  | typeRange
  | length (reason : BlockTypes.Error)
  deriving DecidableEq, Repr

/-- Absolute start bit of the operation that failed. -/
structure Error where
  bit : Nat
  category : Category
  cause : Cause
  deriving DecidableEq, Repr

inductive Wire (control : Control) (before : Run) : List Bool → Run → Prop where
  | keep : 0 < before.remaining → Wire control before [] before.debit
  | switch {types symbol code width length initial : Nat}
      {typeTable countTable : Huffman.Description.Table} {lengthBits : List Bool} :
      control = .multiple types typeTable countTable initial → before.remaining = 0 →
      typeTable.codeFor symbol = some (code, width) → width ≤ 15 →
      nextType types before symbol < types → LengthWire countTable lengthBits length →
      Wire control before (msbBits code width ++ lengthBits) (before.switched types symbol length)

/-- Select the block type for one symbol and debit that symbol from the
    run. A positive remainder consumes zero switch bits. -/
def read (category : Category) (control : Control) (bitLimit : Nat) (run : Run)
    (before : LSBReader) : Except Error (Run × LSBReader) :=
  if ¬ run.Valid control then .error ⟨before.totalRead, category, .invalidState⟩
  else if run.remaining ≠ 0 then .ok (run.debit, before)
  else match control with
    | .single => .error ⟨before.totalRead, category, .singleExhausted⟩
    | .multiple types typeTable countTable _ => do
      let (symbol, cursor) ← (typeTable.readBounded bitLimit before).mapError
        (fun reason => ⟨before.totalRead, category, .typeSymbol reason⟩)
      if types ≤ nextType types run symbol then .error ⟨before.totalRead, category, .typeRange⟩
      else do
        let (length, after) ← (readLength countTable (bitLimit - (cursor.totalRead - before.totalRead)) cursor).mapError
          (fun reason => ⟨cursor.totalRead, category, .length reason⟩)
        return (run.switched types symbol length, after)

/-- Select from one category. The other categories share no run state
    with it, even if their block type codes happen to agree. -/
def select (controls : Controls) (category : Category) (bitLimit : Nat) (state : State)
    (before : LSBReader) : Except Error (State × LSBReader) := do
  let (run, after) ← read category (category.control controls) bitLimit (state.get category) before
  return (state.set run category, after)

/-- Preserve the cause of an operation at its own cursor. The length
    failure carries the preceding checked type prefix. -/
inductive Failure (category : Category) (control : Control) (bitLimit : Nat)
    (run : Run) (before : LSBReader) (input : List Bool) : Error → Prop where
  | invalidState : ¬ run.Valid control →
      Failure category control bitLimit run before input ⟨before.totalRead, category, .invalidState⟩
  | singleExhausted : run.Valid control → control = .single → run.remaining = 0 →
      Failure category control bitLimit run before input ⟨before.totalRead, category, .singleExhausted⟩
  | typeSymbol {types initial : Nat} {typeTable countTable : Huffman.Description.Table}
      {reason : Huffman.Description.SymbolError} :
      run.Valid control → run.remaining = 0 → control = .multiple types typeTable countTable initial →
      typeTable.readBounded bitLimit before = .error reason →
      Failure category control bitLimit run before input ⟨before.totalRead, category, .typeSymbol reason⟩
  | typeRange {types initial symbol : Nat} {typeTable countTable : Huffman.Description.Table} {cursor : LSBReader} :
      run.Valid control → run.remaining = 0 → control = .multiple types typeTable countTable initial →
      typeTable.readBounded bitLimit before = .ok (symbol, cursor) → types ≤ nextType types run symbol →
      Failure category control bitLimit run before input ⟨before.totalRead, category, .typeRange⟩
  | length {types initial symbol code width : Nat} {typeTable countTable : Huffman.Description.Table}
      {cursor : LSBReader} {suffix : List Bool} {reason : BlockTypes.Error} :
      run.Valid control → run.remaining = 0 → control = .multiple types typeTable countTable initial →
      typeTable.readBounded bitLimit before = .ok (symbol, cursor) → nextType types run symbol < types →
      typeTable.codeFor symbol = some (code, width) → input = msbBits code width ++ suffix →
      cursor.Rep suffix → cursor.totalRead = before.totalRead + width → width ≤ bitLimit →
      readLength countTable (bitLimit - (cursor.totalRead - before.totalRead)) cursor = .error reason →
      Failure category control bitLimit run before input ⟨cursor.totalRead, category, .length reason⟩

end Silmaril.Formats.Compression.Brotli.BlockTypes.Switch
