module

public import Silmaril.Formats.Compression.HistoryCopy.Defs

/-! # Execution of decoded Zstandard sequences

RFC 8878 §§3.1.1.3.2, 3.1.1.4 and 3.1.1.5. The executor takes a decoded
literal buffer, the available frame history and the incoming repeat offsets.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Zstd.Sequence

/-- One entropy-decoded sequence. The offset value still includes repeat codes. -/
structure Command where
  literalLength : Nat
  offsetValue : Nat
  matchLength : Nat
  deriving DecidableEq, Repr

def Command.outputLength (command : Command) : Nat :=
  command.literalLength + command.matchLength

structure RepeatOffsets where
  first : Nat
  second : Nat
  third : Nat
  deriving DecidableEq, Repr

/-- Initial repeat offsets for a frame without a dictionary. -/
def RepeatOffsets.initial : RepeatOffsets := ⟨1, 4, 8⟩

def RepeatOffsets.Valid (offsets : RepeatOffsets) : Prop :=
  0 < offsets.first ∧ 0 < offsets.second ∧ 0 < offsets.third

instance (offsets : RepeatOffsets) : Decidable offsets.Valid :=
  inferInstanceAs (Decidable (0 < offsets.first ∧ 0 < offsets.second ∧ 0 < offsets.third))

structure Limits where
  window : Nat
  output : Nat
  deriving DecidableEq, Repr

/-- Caller budget intersected with the RFC regenerated block maximum. -/
def Limits.capacity (limits : Limits) : Nat :=
  min limits.output (min limits.window 131072)

inductive Error where
  | historyLimit
  | invalidRepeats
  | outputLimit
  | shortMatch
  | literalUnderflow
  | invalidOffset
  | offsetOutsideWindow
  | historyUnderflow
  deriving DecidableEq, Repr

structure Result where
  bytes : List UInt8
  offsets : RepeatOffsets
  deriving DecidableEq, Repr

/-- Resolve an offset value and move the referenced distance to the front.
    A zero result from the special case is rejected during execution. -/
def resolve (offsets : RepeatOffsets) (literalLength : Nat) : Nat → Option (Nat × RepeatOffsets)
  | 0 => none
  | 1 =>
    if literalLength = 0 then
      some (offsets.second, ⟨offsets.second, offsets.first, offsets.third⟩)
    else some (offsets.first, offsets)
  | 2 =>
    if literalLength = 0 then
      some (offsets.third, ⟨offsets.third, offsets.first, offsets.second⟩)
    else some (offsets.second, ⟨offsets.second, offsets.first, offsets.third⟩)
  | 3 =>
    if literalLength = 0 then
      let distance := offsets.first - 1
      some (distance, ⟨distance, offsets.first, offsets.second⟩)
    else some (offsets.third, ⟨offsets.third, offsets.first, offsets.second⟩)
  | n + 4 => some (n + 1, ⟨n + 1, offsets.first, offsets.second⟩)

/-- The repeat transformations from §3.1.1.5, including its zero-literal cases. -/
inductive OffsetWire (offsets : RepeatOffsets) : Nat → Nat → Nat → RepeatOffsets → Prop where
  | first {n : Nat} : 0 < n → OffsetWire offsets n 1 offsets.first offsets
  | second {n : Nat} : 0 < n →
      OffsetWire offsets n 2 offsets.second ⟨offsets.second, offsets.first, offsets.third⟩
  | third {n : Nat} : 0 < n →
      OffsetWire offsets n 3 offsets.third ⟨offsets.third, offsets.first, offsets.second⟩
  | zeroFirst :
      OffsetWire offsets 0 1 offsets.second ⟨offsets.second, offsets.first, offsets.third⟩
  | zeroSecond :
      OffsetWire offsets 0 2 offsets.third ⟨offsets.third, offsets.first, offsets.second⟩
  | zeroThird :
      OffsetWire offsets 0 3 (offsets.first - 1) ⟨offsets.first - 1, offsets.first, offsets.second⟩
  | explicit (n value : Nat) :
      OffsetWire offsets n (value + 4) (value + 1) ⟨value + 1, offsets.first, offsets.second⟩

/-- A match reads from the then-current history at each byte. The read byte
    extends history immediately, so the next byte can come from this match. -/
inductive MatchWire (distance : Nat) : List UInt8 → List UInt8 → Prop where
  | nil (history : List UInt8) : MatchWire distance history []
  | cons {history bytes : List UInt8} {byte : UInt8} :
      0 < distance → distance ≤ history.length →
      history[history.length - distance]? = some byte →
      MatchWire distance (history ++ [byte]) bytes →
      MatchWire distance history (byte :: bytes)

/-- Denotation of one command with exact literal extent and a checked distance
    from the position after those literals have been emitted. -/
def StepWire (window : Nat) (command : Command) (history literals : List UInt8)
    (offsets : RepeatOffsets) (bytes suffix : List UInt8) (next : RepeatOffsets) : Prop :=
  ∃ taken matched distance,
    literals = taken ++ suffix ∧ taken.length = command.literalLength ∧
    OffsetWire offsets command.literalLength command.offsetValue distance next ∧
    0 < distance ∧ distance < window ∧ distance ≤ (history ++ taken).length ∧
    3 ≤ command.matchLength ∧ matched.length = command.matchLength ∧
    MatchWire distance (history ++ taken) matched ∧ bytes = taken ++ matched

/-- Execution of the command list, leaving exactly the final literal suffix. -/
inductive Runs (window : Nat) :
    List Command → List UInt8 → List UInt8 → RepeatOffsets →
      List UInt8 → List UInt8 → RepeatOffsets → Prop where
  | nil (history literals : List UInt8) (offsets : RepeatOffsets) :
      Runs window [] history literals offsets [] literals offsets
  | cons {command : Command} {commands : List Command}
      {history literals emitted tail bytes suffix : List UInt8}
      {offsets middle next : RepeatOffsets} :
      StepWire window command history literals offsets emitted tail middle →
      Runs window commands (history ++ emitted) tail middle bytes suffix next →
      Runs window (command :: commands) history literals offsets (emitted ++ bytes) suffix next

namespace Internal

/-- Use the shared bytewise copy, with overlapping reads of the growing output. -/
abbrev copy := HistoryCopy.copy

def step (window remaining : Nat) (history : Array UInt8) (literals : List UInt8)
    (offsets : RepeatOffsets) (command : Command) :
    Except Error (Array UInt8 × List UInt8 × RepeatOffsets) := do
  if command.matchLength < 3 then throw .shortMatch
  if remaining < command.outputLength then throw .outputLimit
  let (taken, suffix) := literals.splitAt command.literalLength
  if taken.length ≠ command.literalLength then throw .literalUnderflow
  let some (distance, next) := resolve offsets command.literalLength command.offsetValue
    | throw .invalidOffset
  if positive : 0 < distance then
    if window ≤ distance then throw .offsetOutsideWindow
    else if available : distance ≤ history.size + taken.length then
      let beforeMatch := history ++ taken.toArray
      let afterMatch := copy distance positive command.matchLength beforeMatch (by simpa [beforeMatch] using available)
      return (afterMatch, suffix, next)
    else throw .historyUnderflow
  else throw .invalidOffset

def run (window : Nat) :
    List Command → Nat → Array UInt8 → List UInt8 → RepeatOffsets →
      Except Error (Array UInt8 × List UInt8 × RepeatOffsets)
  | [], _, history, literals, offsets => .ok (history, literals, offsets)
  | command :: commands, remaining, history, literals, offsets => do
    let (written, suffix, next) ← step window remaining history literals offsets command
    run window commands (remaining - command.outputLength) written suffix next

end Internal

/-- Execute a block from decoded inputs and append the exact final literal
    suffix. The initial history is an available recent suffix of the frame. -/
def execute (limits : Limits) (history : Array UInt8) (literals : List UInt8)
    (offsets : RepeatOffsets) (commands : List Command) : Except Error Result := do
  if limits.window < history.size then throw .historyLimit
  if ¬offsets.Valid then throw .invalidRepeats
  let (written, suffix, next) ← Internal.run limits.window commands limits.capacity history literals offsets
  if limits.capacity - (written.size - history.size) < suffix.length then throw .outputLimit
  return ⟨written.toList.drop history.size ++ suffix, next⟩

end Silmaril.Formats.Compression.Zstd.Sequence
