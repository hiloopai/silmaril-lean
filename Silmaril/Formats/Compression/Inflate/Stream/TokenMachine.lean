module

public import Silmaril.Formats.Compression.Inflate.Stream.ParserBridge
public import Silmaril.Formats.Compression.Inflate.Stream.TokenOutput
public import Silmaril.Formats.Compression.Inflate.Stream.ParserPhases

/-!
# A resumable one-token inflater

Parsing and output are separate execution phases.
Input suspension retains the parser continuation and its partially filled bit
reservoir. Output suspension retains the decoded token's remaining work and
bounded history, so later buffers never cause the token to be parsed again.

The completion theorems connect actual reservoir parsing and bounded-window
copying to `Manual.decodeStep` and the shared mathematical DEFLATE specification.
They explicitly require a token that fits the available history. This is not
yet a C/Core execution theorem, a physical circular-buffer representation, or
a full zlib streaming-API model; scheduler fuel and output capacity are separate.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream

open Silmaril.Formats.Compression

inductive TokenMachine where
  | parsing (continuation : Parser Manual.Token) (reservoir : Reservoir)
      (window : Window) (output : List UInt8)
  | emitting (reservoir : Reservoir) (pending : TokenOutput)
  | done (reservoir : Reservoir) (completed : TokenOutput)
  | error (error : Deflate.DecompressError) (reservoir : Reservoir)
      (window : Window) (output : List UInt8)

namespace TokenMachine

def reservoir : TokenMachine → Reservoir
  | .parsing _ state _ _ | .emitting state _ | .done state _ | .error _ state _ _ => state

def window : TokenMachine → Window
  | .parsing _ _ history _ | .error _ _ history _ => history
  | .emitting _ pending | .done _ pending => pending.window

def output : TokenMachine → List UInt8
  | .parsing _ _ _ bytes | .error _ _ _ bytes => bytes
  | .emitting _ pending | .done _ pending => pending.output

def start (litLen dist : HuffmanTable) (state : Reservoir)
    (history : Window) (bytes : List UInt8) : TokenMachine :=
  .parsing (ParserPhases.token litLen dist) state history bytes

def feed (machine : TokenMachine) (added : List UInt8) : TokenMachine :=
  match machine with
  | .parsing continuation state history bytes =>
    .parsing continuation (state.feed added) history bytes
  | .emitting state pending => .emitting (state.feed added) pending
  | .done state completed => .done (state.feed added) completed
  | .error err state history bytes => .error err (state.feed added) history bytes

/-- Mark a completed output phase without discarding its final window or trace. -/
def finish (state : Reservoir) (pending : TokenOutput) : TokenMachine :=
  match pending.phase with
  | .complete _ => .done state pending
  | _ => .emitting state pending

/-- Output steps consume no input. Invalid history becomes a format error; the
mathematical helper checks it even for zero output capacity. -/
def emit (state : Reservoir) (pending : TokenOutput) (capacity : Nat) : TokenMachine :=
  match pending.step capacity with
  | .error _ => .error .decodeOverrun state pending.window pending.output
  | .ok next => finish state next

def step (machine : TokenMachine) (schedulerFuel capacity : Nat) : TokenMachine :=
  match machine with
  | .parsing continuation state history bytes =>
    match Parser.run schedulerFuel continuation state with
    | .done token rest => emit rest (TokenOutput.start history bytes token) capacity
    | .error err rest => .error err rest history bytes
    | .needInput next rest | .yield next rest => .parsing next rest history bytes
  | .emitting state pending => emit state pending capacity
  | .done _ _ | .error _ _ _ _ => machine

/-- Pending input/output is observable as `none`, rather than a format error.
Completed observations preserve the normalized reader supplied by the parser
correspondence, including all unread prefetched bits and future input. -/
def observe (machine : TokenMachine) (reader : LSBReader) :
    Except Deflate.DecompressError (Option Deflate.SymbolStep) :=
  match machine with
  | .parsing _ _ _ _ => .ok none
  | .emitting _ pending | .done _ pending => .ok (pending.observe reader)
  | .error err _ _ _ => .error err

/-- Supply arbitrary later output buffers, normalizing zero-output tokens even
when the list is empty. Scheduler fuel is zero because emission never parses. -/
def runBuffers (machine : TokenMachine) (capacities : List Nat) : TokenMachine :=
  capacities.foldl (fun current capacity => current.step 0 capacity) (machine.step 0 0)

/-! ## Kernel-checked split-input and split-output executions -/

/-- Nine-bit literal 144, split after its first eight code bits. -/
def literalPrefix : TokenMachine :=
  (start ParserBridge.longLiteralTable (HuffmanTable.empty 0)
    (Reservoir.ofBytes [0x13]) (Window.ofOutput []) []).step 32 0

def literalPending : TokenMachine := (literalPrefix.feed [0]).step 32 0

/-- Tiny witness alphabets isolate a nine-bit length code and distance one;
they are not asserted to be complete fixed/dynamic DEFLATE alphabets. -/
def longMatchTable : HuffmanTable :=
  { maxBits := 9, entries := [⟨257, 400, 9⟩], symbolCodes := [], alphabetSize := 286 }

def distanceOneTable : HuffmanTable :=
  { maxBits := 1, entries := [⟨0, 0, 1⟩], symbolCodes := [], alphabetSize := 1 }

def matchPrefix : TokenMachine :=
  (start longMatchTable distanceOneTable (Reservoir.ofBytes [0x13])
    (Window.ofOutput [65]) [65]).step 32 0

def matchPending : TokenMachine := (matchPrefix.feed [0]).step 32 1

end TokenMachine
end Silmaril.Formats.Compression.Inflate.Stream
