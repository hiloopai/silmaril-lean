module

public import Silmaril.Formats.Compression.Inflate.Stream.MemberSemantics
public import Silmaril.Formats.Compression.Inflate.Stream.CheckedRaw
public import Silmaril.Formats.Compression.Inflate.Stream.GzipHeader

/-!
# Incremental zlib and gzip member controller

Header, body and trailer phases retain their exact
continuations across caller input and output boundaries. Data checksums and
ISIZE advance over newly emitted bytes. A completed gzip controller stops at
one member and leaves the suffix for its caller.

This is the dictionary-free mathematical controller, not execution of either
version's C, packed tables, fast loop, allocation or public status protocol.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream

open Silmaril.Formats.Compression
open MemberSemantics

inductive MemberError where
  | header
  | raw (error : Deflate.DecompressError)
  | trailer
  deriving Repr

inductive MemberMachine where
  | header (kind : Kind) (parser : Parser (Option Unit)) (reservoir : Reservoir)
  | gzipHeader (machine : GzipHeader.Machine)
  | body (kind : Kind) (state : CheckedRaw.State)
  | trailer (parser : Parser (Option Unit)) (state : RawState)
  | done (state : RawState)
  | bad (error : MemberError) (state : RawState)

namespace MemberMachine

def emptyState (reservoir : Reservoir) : RawState :=
  ⟨reservoir, Window.ofOutput [], []⟩

def state : MemberMachine → RawState
  | .header _ _ reservoir => emptyState reservoir
  | .gzipHeader machine => emptyState machine.reservoir
  | .body _ checked => checked.machine.state
  | .trailer _ state | .done state | .bad _ state => state

def reservoir (machine : MemberMachine) : Reservoir := machine.state.reservoir
def window (machine : MemberMachine) : Window := machine.state.window
def output (machine : MemberMachine) : List UInt8 := machine.state.output

def start (kind : Kind) (input : List UInt8) : MemberMachine :=
  match kind with
  | .zlib => .header .zlib ContainerFields.zlibHeader (Reservoir.ofBytes input)
  | .gzip => .gzipHeader (GzipHeader.Machine.start input)

def feed : MemberMachine → List UInt8 → MemberMachine
  | .header kind parser reservoir, input => .header kind parser (reservoir.feed input)
  | .gzipHeader machine, input => .gzipHeader (machine.feed input)
  | .body kind checked, input => .body kind (CheckedRaw.feed checked input)
  | .trailer parser state, input => .trailer parser (state.feed input)
  | .done state, input => .done (state.feed input)
  | .bad error state, input => .bad error (state.feed input)

/-- Enter at the existing byte cursor, without resetting consumed bits. -/
def enterBody (kind : Kind) (reservoir : Reservoir) : MemberMachine :=
  .body kind (CheckedRaw.ofMachine kind.checksumKind
    (.header Blocks.header (emptyState reservoir)))

def checkedTrailer (kind : Kind) (checked : CheckedRaw.State) : Parser (Option Unit) :=
  match kind with
  | .zlib => ContainerFields.zlibTrailerValue checked.check
  | .gzip => ContainerFields.gzipTrailerValue checked.check checked.size

def step (version : Version) (machine : MemberMachine) (fuel capacity : Nat) : MemberMachine :=
  match machine with
  | .header kind parser reservoir =>
    match Parser.run fuel parser reservoir with
    | .done (some ()) rest => enterBody kind rest
    | .done none rest | .error _ rest => .bad .header (emptyState rest)
    | .needInput next rest | .yield next rest => .header kind next rest
  | .gzipHeader gzip =>
    if gzip.isDone then enterBody .gzip gzip.reservoir
    else if gzip.isBad then .bad .header (emptyState gzip.reservoir)
    else .gzipHeader gzip.step
  | .body kind checked =>
    match checked.machine with
    | .done state => .trailer (checkedTrailer kind checked) state
    | .bad error state => .bad (.raw error) state
    | _ => .body kind (CheckedRaw.step kind.checksumKind version checked fuel capacity)
  | .trailer parser state =>
    match Parser.run fuel parser state.reservoir with
    | .done (some ()) rest => .done { state with reservoir := rest }
    | .done none rest | .error _ rest => .bad .trailer { state with reservoir := rest }
    | .needInput next rest | .yield next rest => .trailer next { state with reservoir := rest }
  | .done _ | .bad _ _ => machine

def applyCall (version : Version) (machine : MemberMachine) (call : RawMachine.Call) :
    MemberMachine :=
  step version (machine.feed call.input) call.schedulerFuel call.capacity

def runCalls (version : Version) (machine : MemberMachine) (calls : List RawMachine.Call) :
    MemberMachine := calls.foldl (applyCall version) machine

def denote : MemberMachine → LSBReader → Option (List UInt8 × LSBReader)
  | .header kind parser _, reader =>
    (ContainerFields.validationReader (parser.eval reader)).bind (MemberSemantics.body kind)
  | .gzipHeader gzip, reader =>
    (gzip.denoteReader reader).bind (MemberSemantics.body .gzip)
  | .body kind checked, reader =>
    afterRaw kind (RawSemantics.denote checked.machine reader)
  | .trailer parser state, reader =>
    (ContainerFields.validationReader (parser.eval reader)).map (state.output, ·)
  | .done state, reader => some (state.output, reader)
  | .bad _ _, _ => none

/-- Gzip's byte controller requires an aligned logical reader. Other parsing
phases use the general bit-reader correspondence. -/
def WellFormed : MemberMachine → LSBReader → Prop
  | .gzipHeader _, reader => reader.buffer = 0 ∧ reader.count = 0
  | .body kind checked, reader =>
    CheckedRaw.Invariant kind.checksumKind checked ∧
      RawSemantics.WellFormed checked.machine reader
  | _, _ => True

end MemberMachine
end Silmaril.Formats.Compression.Inflate.Stream
