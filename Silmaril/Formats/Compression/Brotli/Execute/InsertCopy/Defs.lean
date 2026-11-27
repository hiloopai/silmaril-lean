module

public import Silmaril.Formats.Compression.Brotli.Execute.Defs
public import Silmaril.Formats.Compression.Brotli.BlockTypes.Switch.Defs

/-! Execute a command with insert-and-copy block switching. Literal and
    distance decoding still use the one-block-type profile. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Execute.InsertCopy

open BlockTypes (Control)
open BlockTypes.Switch (Run)
open Huffman.Description (Table)

structure State where
  execution : Execute.State
  runs : BlockTypes.Switch.State
  deriving DecidableEq, Repr

def State.start (header : CompressedHeader.Header) (execution : Execute.State) : State :=
  ⟨execution, BlockTypes.Switch.State.start header.initial.controls⟩

structure Result where
  execution : Execute.Result
  runs : BlockTypes.Switch.State
  deriving DecidableEq, Repr

def Result.state (result : Result) : State := ⟨result.execution.state, result.runs⟩

inductive Error where
  | literalBlockTypes (bit : Nat)
  | distanceBlockTypes (bit : Nat)
  | switch (reason : BlockTypes.Switch.Error)
  | commandTree (bit ordinal : Nat)
  | execute (bit : Nat) (reason : Execute.Error)
  deriving DecidableEq, Repr

/-- The original header supplies the literal and distance paths. Only
    the checked command ordinal's tree is presented to the executor. -/
def commandHeader (header : CompressedHeader.Header) (tree : Table) : CompressedHeader.Header :=
  { header with
    initial := { header.initial with controls := { header.initial.controls with insertCopy := .single } }
    insertCopyTrees := [tree] }

def read (header : CompressedHeader.Header) (block : Block) (limits : Limits)
    (initial : State) (before : LSBReader) : Except Error (Result × LSBReader) := do
  match header.initial.controls.literal with
  | .multiple .. => throw (.literalBlockTypes before.totalRead)
  | .single =>
    match header.initial.controls.distance with
    | .multiple .. => throw (.distanceBlockTypes before.totalRead)
    | .single =>
      let (runs, atCommand) ←
        (BlockTypes.Switch.select header.initial.controls .insertCopy limits.bits initial.runs before).mapError
          Error.switch
      let ordinal := runs.insertCopy.current
      let some tree := header.insertCopyTrees[ordinal]? | throw (.commandTree atCommand.totalRead ordinal)
      let (execution, after) ←
        (Execute.read (commandHeader header tree) block
          { limits with bits := limits.bits - (atCommand.totalRead - before.totalRead) }
          initial.execution atCommand).mapError (Error.execute atCommand.totalRead)
      pure (⟨execution, runs⟩, after)

structure Wire (header : CompressedHeader.Header) (block : Block) (initial : State)
    (bits : List Bool) (result : Result) : Prop where
  literalSingle : header.initial.controls.literal = .single
  distanceSingle : header.initial.controls.distance = .single
  parts : ∃ switchBits commandBits tree,
    bits = switchBits ++ commandBits ∧
    BlockTypes.Switch.Wire header.initial.controls.insertCopy initial.runs.insertCopy switchBits
      result.runs.insertCopy ∧
    header.insertCopyTrees[result.runs.insertCopy.current]? = some tree ∧
    Execute.Wire (commandHeader header tree) block initial.execution commandBits result.execution

/-- The switch prefix preceding a command error still has its exact
    original extent. The lower operation fails at the resulting cursor. -/
structure CommandSite (header : CompressedHeader.Header) (limits : Limits) (initial : State)
    (before atCommand : LSBReader) (input : List Bool) (run : Run) : Prop where
  extent : ∃ used suffix,
    BlockTypes.Switch.Wire header.initial.controls.insertCopy initial.runs.insertCopy used run ∧
    input = used ++ suffix ∧ atCommand.Rep suffix ∧ atCommand.totalRead = before.totalRead + used.length ∧
    used.length ≤ limits.bits

inductive Failure (header : CompressedHeader.Header) (block : Block) (limits : Limits)
    (initial : State) (before : LSBReader) (input : List Bool) : Error → Prop where
  | literalBlockTypes : header.initial.controls.literal ≠ .single →
      Failure header block limits initial before input (.literalBlockTypes before.totalRead)
  | distanceBlockTypes : header.initial.controls.distance ≠ .single →
      Failure header block limits initial before input (.distanceBlockTypes before.totalRead)
  | switch {error : BlockTypes.Switch.Error} :
      BlockTypes.Switch.Failure .insertCopy header.initial.controls.insertCopy limits.bits
        initial.runs.insertCopy before input error →
      Failure header block limits initial before input (.switch error)
  | commandTree {atCommand : LSBReader} {run : Run} :
      CommandSite header limits initial before atCommand input run →
      header.insertCopyTrees[run.current]? = none →
      Failure header block limits initial before input (.commandTree atCommand.totalRead run.current)
  | execute {atCommand : LSBReader} {run : Run} {tree : Table} {reason : Execute.Error} :
      CommandSite header limits initial before atCommand input run →
      header.insertCopyTrees[run.current]? = some tree →
      Execute.read (commandHeader header tree) block
        { limits with bits := limits.bits - (atCommand.totalRead - before.totalRead) }
        initial.execution atCommand = .error reason →
      Failure header block limits initial before input (.execute atCommand.totalRead reason)

end Silmaril.Formats.Compression.Brotli.Execute.InsertCopy
