module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.Tags.Grammar.Read.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.Tags.Grammar.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.GrammarRead

/-! # The reader and the flat typing of the grammar, at every size

No seed and no quotient law is added. Default Paper is unchanged. The
reader does not normalize.

## Flat typing

* `NTable.flat_typed`: the scoped flat graph of every table, at every
  size, is typed in the flat judgment.

## The reader is exact

`NTable.read` matches the entry and each of the `K + 1` blocks by
constructors.

* `NTable.read_sound`: if `read g = some d` then `g = d.flat`.
* `NTable.read_flat`: `read d.flat = some d`.
* `NTable.read_eq_some_iff`: `read g = some d ↔ g = d.flat`.

These are equalities of syntax, for every size.

## Sources given as flat syntax, at any two sizes

For accepted graphs `g` with `K + 1` blocks and `g'` with `K' + 1` blocks,
with tables `d` and `d'`:

* `NTable.read_typed`, `NTable.read_flat_typed`: the region of `g` is a
  guarded source, and `g` is typed in the flat judgment.
* `NTable.read_bitPointed`: the certificate of #5332 for the region of
  `g`.
* `NTable.read_source_eqv_entered`: the region of `g` is the router table
  of `d` entered at its start row, in the table-packing quotient.
* `NTable.read_complete`: the regions of `g` and `g'` are equal at their
  source entries exactly when they are valid in every supported model.
* `NTable.read_eqv_iff_bisimulation`: exactly when the two router tables
  are bisimilar from their start rows.

These are #5351's theorems along `read_sound`. Completeness is in the
opt-in quotient and for the supported models; the router tables are
`Tidy` because every row is labelled.

## The reader of #5340

`PollTable.read` and its theorems are unchanged.

* `PollTable.toN_flat`: the graph of a two-block table is the graph of
  its table of the grammar.
* `PollTable.read_iff_ntable`: the two readers accept the same graphs
  with two blocks, with corresponding tables.

## Regression across sizes

* `read_cycleFlat`: the cycle of three blocks is accepted, with the table
  `cycleN l`.
* `read_selfLit_ntable`: the two-block literal of #5340 is accepted.
* `cycleFlat_eqv_selfLit`: the two have equal sources. The graphs have
  three and two blocks.
* `cycleFlat_eqv_selfLit_iff`: for two labels, they are equal exactly
  when the labels agree.

## Rejection is not inequality

`none` says that the graph is not written in the shape of the grammar.

* `read_cycleSilent`: a cycle of three blocks with a request-free block
  is rejected. Nothing is proved about its source.
* `read_aliasMiss_ntable`: the two-block graph with a block behind a let
  is rejected by this reader too. By #5340's `aliasMiss_eqv_selfLit` its
  source is the source of an accepted graph, in default Paper.

No theorem here derives an inequality of sources from a rejection.

## Not covered

* A reader that normalizes before matching.
* Blocks that use the captured input, request-free blocks, more than one
  exit, and completeness in default Paper.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofRegion ofType)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking
  (Valid.symm Valid.trans)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity
open Silmaril.DeBruijn (lift)

variable {K K' : Nat}

namespace NTable

variable {g : LambdaSSA.FiniteCFG signature.Instr (K + 1) 1 1}
  {g' : LambdaSSA.FiniteCFG signature.Instr (K' + 1) 1 1} {d : NTable K} {d' : NTable K'}

/-! ## Flat typing -/

/-- The graph of every table is typed in the flat judgment. -/
theorem flat_typed (d : NTable K) :
    LambdaSSA.FiniteCFG.HasType (.snoc .nil Bit) (fun _ : Fin (K + 1) => Bit) (fun _ : Fin 1 => Bit) d.flat :=
  Tables.nflat_typed d

/-! ## The reader is exact -/

/-- A graph that the reader accepts is the graph of the table it returns. -/
theorem read_sound (h : read g = some d) : g = d.flat :=
  Tables.nread_sound h

/-- The reader accepts the graph of every table and returns that table. -/
theorem read_flat (d : NTable K) : read d.flat = some d :=
  Tables.nread_flat d

theorem read_eq_some_iff : read g = some d ↔ g = d.flat :=
  Tables.nread_iff

/-! ## Sources given as flat syntax -/

/-- The region of an accepted graph is a guarded source. -/
theorem read_typed (h : read g = some d) : ValueBranches [Bit] g.erase [Bit] :=
  Tables.nread_typed h

/-- An accepted graph is typed in the flat judgment. -/
theorem read_flat_typed (h : read g = some d) :
    LambdaSSA.FiniteCFG.HasType (.snoc .nil Bit) (fun _ : Fin (K + 1) => Bit) (fun _ : Fin 1 => Bit) g :=
  Tables.nread_flat_typed h

/-- The certificate at the two constant inputs, for an accepted graph. -/
theorem read_bitPointed (h : read g = some d) :
    BitPointed g.erase (fun i => some (d.label i)) d.act (fun _ => d.start) :=
  Tables.nread_bitPointed h

/-- The region of an accepted graph is the router table of its table
entered at the start row, in the table-packing quotient. -/
theorem read_source_eqv_entered (h : read g = some d) :
    WithGuardedTablePacking.Eqv false [Bit] g.erase
      (seqRegion (.br 0 (.inl (.var 0))) (d.router.entered d.start)) [Bit] :=
  Tables.nread_entered h

/-- Two accepted graphs of any two sizes have equal regions at their
source entries exactly when they are valid in every supported model. -/
theorem read_complete (h : read g = some d) (h' : read g' = some d') :
    Eqv false [Bit] g.erase g'.erase [Bit] ↔ Valid (read_typed h).hasType (read_typed h').hasType :=
  Tables.nread_complete h h'

/-- Exactly when their router tables are bisimilar from their start rows. -/
theorem read_eqv_iff_bisimulation (h : read g = some d) (h' : read g' = some d') :
    Eqv false [Bit] g.erase g'.erase [Bit] ↔
      ∃ R : Fin (K + 1) → Fin (K' + 1) → Prop, (∀ x y, R x y → d.label x = d'.label y) ∧
        (∀ x y, R x y → ∀ tag pl, Act.Rel R (d.act x tag pl) (d'.act y tag pl)) ∧ R d.start d'.start :=
  Tables.nread_bisim h h'

end NTable

/-! ## The reader of #5340 -/

/-- The graph of a two-block table is the graph of its table of the grammar. -/
theorem PollTable.toN_flat (d : PollTable) : d.toN.flat = d.flat :=
  Tables.toN_flat d

/-- The two readers accept the same graphs with two blocks. -/
theorem PollTable.read_iff_ntable {g : LambdaSSA.FiniteCFG signature.Instr 2 1 1} {d : PollTable} :
    PollTable.read g = some d ↔ NTable.read (K := 1) g = some d.toN :=
  Tables.poll_read_iff

/-! ## Regression across sizes -/

theorem read_cycleFlat (l : Bool) : NTable.read (K := 2) (cycleFlat l) = some (cycleN l) :=
  Tables.nread_cycle l

theorem read_selfLit_ntable (l : Bool) : NTable.read (K := 1) (selfLit l) = some (selfTable l).toN :=
  Tables.nread_selfLit l

/-- The cycle of three blocks and the two-block literal have equal sources. -/
theorem cycleFlat_eqv_selfLit (l : Bool) : Eqv false [Bit] (cycleFlat l).erase (selfLit l).erase [Bit] :=
  Tables.cycle_selfLit l

/-- For two labels, exactly when the labels agree. -/
theorem cycleFlat_eqv_selfLit_iff (l l' : Bool) :
    Eqv false [Bit] (cycleFlat l).erase (selfLit l').erase [Bit] ↔ l = l' :=
  Tables.cycle_selfLit_iff l l'

/-! ## Rejected graphs -/

theorem read_cycleSilent (l : Bool) : NTable.read (K := 2) (cycleSilent l) = none := rfl

theorem read_aliasMiss_ntable (l : Bool) : NTable.read (K := 1) (aliasMiss l) = none := rfl

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
