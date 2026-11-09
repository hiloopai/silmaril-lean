module

public import Silmaril.Formats.Compression.Inflate.Stream.History
public import Silmaril.Formats.Compression.Inflate.Manual.Symbols

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream

open Silmaril.Formats.Compression

/-!
# Resumable literal, end-of-block and match output

The parser supplies a mathematical token; output capacity can then suspend
literal or overlapping match emission. The bounded window is the actual source
of match bytes. The output list is a logical trace for observations/proofs.
No input is consumed here. Representation of source tables, buffers, bit fields
and the physical ring, and execution of the C state machine, remain separate.
-/

inductive OutputPhase where
  | literal (byte : UInt8)
  | matchBytes (remaining distance : Nat)
  | endBlock
  | complete (isEndBlock : Bool)
deriving Repr, DecidableEq

structure TokenOutput where
  window : Window
  output : List UInt8
  phase : OutputPhase
deriving Repr, DecidableEq

def TokenOutput.start (window : Window) (output : List UInt8) (token : Manual.Token) : TokenOutput :=
  ⟨window, output, match token with
    | .literal byte => .literal byte
    | .endBlock => .endBlock
    | .matchBytes length distance => .matchBytes length distance⟩

def TokenOutput.remaining (s : TokenOutput) : Nat :=
  match s.phase with
  | .literal _ => 1
  | .matchBytes count _ => count
  | .endBlock | .complete _ => 0

/-- The output work represented by a parsed token. -/
def tokenLength : Manual.Token → Nat
  | .literal _ => 1
  | .endBlock => 0
  | .matchBytes length _ => length

/-- The history premises established by a valid parsed back-reference. The
copy lemmas work for every length; the format's separate 3..258 bound is unused. -/
def TokenFitsHistory (output : List UInt8) : Manual.Token → Prop
  | .matchBytes _ distance =>
    0 < distance ∧ distance ≤ windowLimit ∧ distance ≤ output.length
  | _ => True

def TokenOutput.Valid (s : TokenOutput) : Prop :=
  s.window.Represents s.output ∧
    match s.phase with
    | .matchBytes _ distance =>
      0 < distance ∧ distance ≤ windowLimit ∧ distance ≤ s.output.length
    | _ => True

def TokenOutput.asMatch (s : TokenOutput) (count distance : Nat) : PendingMatch :=
  ⟨distance, count, s.window, s.output⟩

def TokenOutput.finishMatch (m : PendingMatch) : TokenOutput :=
  ⟨m.window, m.output,
    if m.remaining = 0 then .complete false else .matchBytes m.remaining m.distance⟩

def TokenOutput.advance (s : TokenOutput) (capacity : Nat) : TokenOutput :=
  match s.phase with
  | .literal byte =>
    if capacity = 0 then s
    else ⟨s.window.push byte, s.output ++ [byte], .complete false⟩
  | .matchBytes count distance => TokenOutput.finishMatch ((s.asMatch count distance).advance capacity)
  | .endBlock => ⟨s.window, s.output, .complete true⟩
  | .complete _ => s

/-- The new bytes observed by the caller in this offered output buffer. -/
def TokenOutput.emitted (s : TokenOutput) (capacity : Nat) : List UInt8 :=
  (s.advance capacity).output.drop s.output.length

/-- Normalize zero-output token completion before offering a list of buffers. -/
def TokenOutput.runBuffers (s : TokenOutput) (capacities : List Nat) : TokenOutput :=
  capacities.foldl TokenOutput.advance (s.advance 0)

/-- Readiness to emit an active match is checked from bounded stored history. -/
def TokenOutput.DistanceAvailable (s : TokenOutput) : Prop :=
  match s.phase with
  | .matchBytes _ distance =>
    0 < distance ∧ distance ≤ windowLimit ∧ distance ≤ s.window.bytes.length
  | _ => True

instance (s : TokenOutput) : Decidable s.DistanceAvailable :=
  match s with
  | ⟨window, _, .matchBytes _ distance⟩ =>
    inferInstanceAs (Decidable
      (0 < distance ∧ distance ≤ windowLimit ∧ distance ≤ window.bytes.length))
  | ⟨_, _, .literal _⟩ | ⟨_, _, .endBlock⟩ | ⟨_, _, .complete _⟩ => isTrue trivial

/-- Eager token-level distance validation, including at zero capacity. As with
PendingMatch.step this does not claim source-level error/exit ordering. -/
def TokenOutput.step (s : TokenOutput) (capacity : Nat) : Except MatchError TokenOutput :=
  if s.DistanceAvailable then .ok (s.advance capacity) else .error .invalidDistance

/-- Observe a completed token, preserving the parser's reader exactly. An
unfinished token has no completed observation, rather than a format error. -/
def TokenOutput.observe (s : TokenOutput) (reader : LSBReader) : Option Deflate.SymbolStep :=
  match s.phase with
  | .complete false => some (.more s.output reader)
  | .complete true => some (.done s.output reader)
  | _ => none

end Silmaril.Formats.Compression.Inflate.Stream
