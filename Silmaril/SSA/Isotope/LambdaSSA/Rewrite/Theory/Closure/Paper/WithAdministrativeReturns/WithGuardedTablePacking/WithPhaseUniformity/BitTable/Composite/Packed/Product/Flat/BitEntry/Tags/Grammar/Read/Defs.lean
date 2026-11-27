module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.Tags.Grammar.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.PollTable.Read.Defs

/-! # Reading a scoped flat graph as a table of the grammar, at any size

`NTable.read g` matches the constructors of a scoped flat graph
`g : FiniteCFG signature.Instr (K + 1) 1 1` against the exact shape of
`NTable.flat`:

* the entry is a jump to a block with the input, variable `0`;
* each of the `K + 1` blocks is a case on one request whose operand is
  the block parameter, variable `0`;
* each arm is a jump to a label with the reply payload, variable `0`.

It returns `none` for every other graph. `none` means that the graph is
not written in this shape. It says nothing about which sources the graph
is equal to. The reader does not normalize.

`PollTable.toN` is the table of the grammar at two blocks that
corresponds to a table of the two-block fragment of #5336. The reader of
#5340, `PollTable.read`, is unchanged.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Trace model modelCoherent)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Word)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open _root_.Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep)

variable {K : Nat}

/-! ## The reader -/

/-- The leaf that jumps to a label of the graph: the last label is the exit. -/
def NLeaf.ofFin (i : Fin (K + 1 + 1)) : NLeaf K :=
  if h : i.val < K + 1 then .goto ⟨i.val, h⟩ else .exit

/-- The block that a label of the graph names, if it is a block. -/
def startOfFinN (i : Fin (K + 1 + 1)) : Option (Fin (K + 1)) :=
  if h : i.val < K + 1 then some ⟨i.val, h⟩ else none

/-- An arm of a block: a jump with the reply payload. -/
def readLeafN : LambdaSSA.Flat signature.Instr (K + 1 + 1) 3 → Option (NLeaf K)
  | .br i a => if isBv0 a then some (NLeaf.ofFin i) else none
  | _ => none

/-- A block: a case on one request, with two jumping arms. -/
def readBlockN : LambdaSSA.Flat signature.Instr (K + 1 + 1) 2 → Option (Bool × NLeaf K × NLeaf K)
  | .case e l r =>
    (readOp e).bind fun lab => (readLeafN l).bind fun b₁ => (readLeafN r).map fun b₂ => (lab, b₁, b₂)
  | _ => none

/-- The entry: a jump to a block with the input. -/
def readEntryN : LambdaSSA.Flat signature.Instr (K + 1 + 1) 1 → Option (Fin (K + 1))
  | .br i a => if isBv0 a then startOfFinN i else none
  | _ => none

/-- The table of the rows that were read. -/
def NTable.ofRows (s : Fin (K + 1)) (rows : Fin (K + 1) → Bool × NLeaf K × NLeaf K) : NTable K where
  label := fun i => (rows i).1
  branch := fun i tag => match tag with
    | false => (rows i).2.1
    | true => (rows i).2.2
  start := s

/-- Read a scoped flat graph as a table of the grammar. Every block is read. -/
def NTable.read (g : LambdaSSA.FiniteCFG signature.Instr (K + 1) 1 1) : Option (NTable K) :=
  (readEntryN g.entry).bind fun s =>
    (Bridge.NamedFlat.tabulate (K + 1) fun i => readBlockN (g.block i)).map (NTable.ofRows s)

/-! ## The two-block fragment inside the grammar -/

/-- A leaf of the two-block fragment as a leaf of the grammar. -/
def PollLeaf.toN : PollLeaf → NLeaf 1
  | .exit => .exit
  | .goto c => .goto (pairIdx c)

/-- A table of the two-block fragment as a table of the grammar. -/
def PollTable.toN (d : PollTable) : NTable 1 where
  label := fun i => d.label (pairBit i)
  branch := fun i tag => (d.branch (pairBit i) tag).toN
  start := pairIdx d.start

/-! ## A rejected graph with three blocks -/

/-- The cycle of three blocks with a request-free second block. -/
def cycleSilent (l : Bool) : LambdaSSA.FiniteCFG signature.Instr 3 1 1 where
  entry := .br 0 (.bv 0)
  block := fun i => match i with
    | 0 => .case (.op (.ask l) (.bv 0)) (.br 3 (.bv 0)) (.br 1 (.bv 0))
    | 1 => .br 2 (.bv 0)
    | 2 => .case (.op (.ask l) (.bv 0)) (.br 3 (.bv 0)) (.br 0 (.bv 0))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
