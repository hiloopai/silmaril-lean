module

public import Silmaril.Formats.Compression.Inflate.Stream.Blocks
public import Silmaril.Formats.Compression.Inflate.Stream.TokenMachine

/-!
# A whole-stream raw inflater controller

This mathematical controller composes the resumable
header, stored, dynamic-table and token phases with bounded-window output.
There is no semantic token/block fuel in its state: repeated calls can decode
arbitrarily many blocks and tokens. Each `step` has a caller-supplied parser
scheduler budget and output capacity. Scheduler or input suspension retains
the exact continuation; output suspension retains pending work.

The two versions have separately defined block dispatchers. The controller is
an executable abstract algorithm, not a translation-validation theorem for
the source's packed tables, fast loop, pointers, word arithmetic or C/Core
execution. Raw DEFLATE has no wrapper or trailer checks; those belong to a
separate protocol layer.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream

open Silmaril.Formats.Compression

inductive Version where
  | v131
  | develop
  deriving Repr, DecidableEq

structure RawState where
  reservoir : Reservoir
  window : Window
  output : List UInt8
  deriving Repr, DecidableEq

namespace RawState

def Valid (state : RawState) : Prop :=
  state.reservoir.Valid ∧ state.window.Represents state.output

def feed (state : RawState) (added : List UInt8) : RawState :=
  { state with reservoir := state.reservoir.feed added }

def emitByte (state : RawState) (rest : Reservoir) (byte : UInt8) : RawState :=
  { reservoir := rest, window := state.window.push byte, output := state.output ++ [byte] }

def ofTokenMachine (machine : TokenMachine) : RawState :=
  ⟨machine.reservoir, machine.window, machine.output⟩

end RawState

inductive RawMachine where
  | header (continuation : Parser (Bool × Nat)) (state : RawState)
  | storedHeader (last : Bool) (continuation : Parser Nat) (state : RawState)
  | storedCopy (last : Bool) (remaining : Nat) (state : RawState)
  | dynamicTables (last : Bool) (continuation : Parser (HuffmanTable × HuffmanTable))
      (state : RawState)
  | symbols (last : Bool) (litLen dist : HuffmanTable) (machine : TokenMachine)
  | done (state : RawState)
  | bad (error : Deflate.DecompressError) (state : RawState)

namespace RawMachine

def state : RawMachine → RawState
  | .header _ state | .storedHeader _ _ state | .storedCopy _ _ state
  | .dynamicTables _ _ state | .done state | .bad _ state => state
  | .symbols _ _ _ machine => RawState.ofTokenMachine machine

def reservoir (machine : RawMachine) : Reservoir := machine.state.reservoir
def window (machine : RawMachine) : Window := machine.state.window
def output (machine : RawMachine) : List UInt8 := machine.state.output

def start (bytes : List UInt8) : RawMachine :=
  .header Blocks.header ⟨Reservoir.ofBytes bytes, Window.ofOutput [], []⟩

def feed (machine : RawMachine) (added : List UInt8) : RawMachine :=
  match machine with
  | .header continuation state => .header continuation (state.feed added)
  | .storedHeader last continuation state => .storedHeader last continuation (state.feed added)
  | .storedCopy last remaining state => .storedCopy last remaining (state.feed added)
  | .dynamicTables last continuation state => .dynamicTables last continuation (state.feed added)
  | .symbols last litLen dist next => .symbols last litLen dist (next.feed added)
  | .done state => .done (state.feed added)
  | .bad error state => .bad error (state.feed added)

/-- EOB of a final block discards only byte padding. Whole prefetched bytes
remain in the reservoir; a later normalized suffix observation retains them. -/
def finishBlock (last : Bool) (state : RawState) : RawMachine :=
  if last then .done { state with reservoir := state.reservoir.byteBits }
  else .header Blocks.header state

def fixed (last : Bool) (state : RawState) : RawMachine :=
  match Deflate.fixedLitLenTable, Deflate.fixedDistTable with
  | some litLen, some dist =>
    .symbols last litLen dist (TokenMachine.start litLen dist state.reservoir state.window state.output)
  | _, _ => .bad .badFixedTable state

def dispatch131 (kind : Nat) (last : Bool) (state : RawState) : RawMachine :=
  if kind = 0 then .storedHeader last ParserPhases.storedHeader state
  else if kind = 1 then fixed last state
  else if kind = 2 then .dynamicTables last ParserPhases.dynamicTables state
  else .bad (.badBlockType kind) state

def dispatchDevelop (kind : Nat) (last : Bool) (state : RawState) : RawMachine :=
  match kind with
  | 0 => .storedHeader last ParserPhases.storedHeader state
  | 1 => fixed last state
  | 2 => .dynamicTables last ParserPhases.dynamicTables state
  | _ => .bad (.badBlockType kind) state

def dispatch (version : Version) (kind : Nat) (last : Bool) (state : RawState) : RawMachine :=
  match version with
  | .v131 => dispatch131 kind last state
  | .develop => dispatchDevelop kind last state

/-- Route the completed token without re-parsing its input. Invalid externally
constructed `done` phases stay visible; reachable token completion is `.complete`.
The controller refinement invariant supplies that reachability condition. -/
def acceptToken (last : Bool) (litLen dist : HuffmanTable) (machine : TokenMachine) : RawMachine :=
  match machine with
  | .error error reservoir window output => .bad error ⟨reservoir, window, output⟩
  | .done reservoir completed =>
    let state : RawState := ⟨reservoir, completed.window, completed.output⟩
    match completed.phase with
    | .complete true => finishBlock last state
    | .complete false =>
      .symbols last litLen dist (TokenMachine.start litLen dist reservoir completed.window completed.output)
    | _ => .symbols last litLen dist machine
  | _ => .symbols last litLen dist machine

/-- One controller boundary, one parsed token/output advance, or one stored
byte. Stored COPY tests output capacity before reading any input. -/
def step (version : Version) (machine : RawMachine) (schedulerFuel capacity : Nat) : RawMachine :=
  match machine with
  | .header continuation state =>
    match Parser.run schedulerFuel continuation state.reservoir with
    | .done (last, kind) rest => dispatch version kind last { state with reservoir := rest }
    | .error error rest => .bad error { state with reservoir := rest }
    | .needInput next rest | .yield next rest => .header next { state with reservoir := rest }
  | .storedHeader last continuation state =>
    match Parser.run schedulerFuel continuation state.reservoir with
    | .done remaining rest => .storedCopy last remaining { state with reservoir := rest }
    | .error error rest => .bad error { state with reservoir := rest }
    | .needInput next rest | .yield next rest => .storedHeader last next { state with reservoir := rest }
  | .storedCopy last remaining state =>
    match remaining with
    | 0 => finishBlock last state
    | count + 1 =>
      if capacity = 0 then machine
      else
        match Reservoir.readBits 8 state.reservoir with
        | .value byte rest => .storedCopy last count (state.emitByte rest (UInt8.ofNat byte))
        | .needInput rest => .storedCopy last remaining { state with reservoir := rest }
  | .dynamicTables last continuation state =>
    match Parser.run schedulerFuel continuation state.reservoir with
    | .done (litLen, dist) rest =>
      .symbols last litLen dist (TokenMachine.start litLen dist rest state.window state.output)
    | .error error rest => .bad error { state with reservoir := rest }
    | .needInput next rest | .yield next rest => .dynamicTables last next { state with reservoir := rest }
  | .symbols last litLen dist tokenMachine =>
    acceptToken last litLen dist (tokenMachine.step schedulerFuel capacity)
  | .done _ | .bad _ _ => machine

structure Call where
  input : List UInt8
  schedulerFuel : Nat
  capacity : Nat
  deriving Repr, DecidableEq

def applyCall (version : Version) (machine : RawMachine) (call : Call) : RawMachine :=
  step version (machine.feed call.input) call.schedulerFuel call.capacity

/-- A finite observation schedule, not semantic decoder fuel. More calls may
be appended without changing or recreating any saved block/token budget. -/
def runCalls (version : Version) (machine : RawMachine) (calls : List Call) : RawMachine :=
  calls.foldl (applyCall version) machine

/-! ## A stored block through the actual controller -/

def storedOneHeader : RawMachine := step .v131 (start [1, 1, 0, 0xfe, 0xff, 65]) 8 0
def storedOneReady : RawMachine := step .v131 storedOneHeader 8 0
def storedOneCopied : RawMachine := step .v131 storedOneReady 8 1

end RawMachine
end Silmaril.Formats.Compression.Inflate.Stream
