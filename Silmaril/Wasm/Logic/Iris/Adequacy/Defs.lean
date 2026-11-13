module

public import Silmaril.Wasm.Logic.Iris.Heap.Defs

/-!
# The Iris logic of Wasm Core 3.0: triples

`ITriple GF P host Pre own code Q` is a Hoare triple proved in Iris: from every
store and frame satisfying `Pre`, the cells `own s f` (distinct locations that the
store holds) give, for every allocation of the ghost names, Iris's weakest
precondition of `code` with the pure postcondition `Q` on the final store, frame
and outcome. `ITriple.sound` (`Silmaril.Wasm.Logic.Iris.Adequacy.Thms`) turns it
into the every-run triple `Silmaril.Wasm.Logic.Hoare.Triple` of the Silmaril Hoare logic.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.IrisWasm

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Post)
open _root_.Iris _root_.Iris.BI _root_.Iris.ProgramLogic

variable {H : Type}

/-- **An Iris triple** for Wasm code, with the precondition's footprint `own`. -/
def ITriple (GF : BundledGFunctors) (P : Profile) (host : HostSemantics H)
    (Pre : Store H → Frame → Prop) (own : Store H → Frame → List (ILoc × ICell))
    (code : List Admin) (Q : Post H) : Prop :=
  ∀ s f, Pre s f → ((own s f).map Prod.fst).Nodup ∧ Cells (own s f) s f ∧
    ∀ [WasmGS GF], ⊢@{IProp GF} ownCells (own s f) -∗
      WP (IExpr.run code : IExpr P host) {{ r, ⌜Q r.store r.frame r.out⌝ }}

end Silmaril.Wasm.Logic.IrisWasm
