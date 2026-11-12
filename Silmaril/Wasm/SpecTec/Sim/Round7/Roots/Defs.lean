module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Swap.Defs

/-!
# Round 7, the export swap: record updates and their roots (round 3, pass 1)

Item 2 of the plan for `Round7.Swap.Task.stepErase` ("typed update roots"). The swap set
`AllIn (QC c)` is kept by every value operation of the evaluator except a field update of a record
that has an `EXPORTS` field (`Round7.Swap.AllIn.setField`). This header names the side condition
under which a whole path update `pathSet` keeps it, and the atoms of a module-instance image.

* `SafeWrites Q env ρ v p`: every record that `pathSet … v p …` writes a field into either has no
  `EXPORTS` field, or stays in `Q` under that write. `pathGet` of each `.a` step's prefix is the
  record written into.
* `IsWrite q a p`: `.a` at prefix `q` is a step of `p`.
* `numAtoms`: the fields of `moduleinst` that hold lists of addresses (`TAGS`, `GLOBALS`, `MEMS`,
  `TABLES`, `FUNCS`, `DATAS`, `ELEMS`). `modAtoms`: all nine fields of `moduleinst`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Roots

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (AllIn hasExp)

/-- `gs` with every field named `a` set to `w` (`Value.setField` on a record). -/
def setF (gs : List (AtomS × Value)) (a : AtomS) (w : Value) : List (AtomS × Value) :=
  gs.map fun f => if f.1 = a then (f.1, w) else f

/-- `.a` at prefix `q` is one of the steps of `p`: `pathSet … p …` writes field `a` into the record
that `pathGet` reads at `q`. -/
inductive IsWrite (q : Path) (a : AtomS) : Path → Prop where
  | here : IsWrite q a (.dotP q a)
  | idx {p : Path} {e : Exp} : IsWrite q a p → IsWrite q a (.idxP p e)
  | slice {p : Path} {e₁ e₂ : Exp} : IsWrite q a p → IsWrite q a (.sliceP p e₁ e₂)
  | dot {p : Path} {b : AtomS} : IsWrite q a p → IsWrite q a (.dotP p b)

/-- **The writes of a path update stay in `Q`**: for each `.a` step of `p`, the record that
`pathGet` reads at its prefix (at any fuel) either has no `EXPORTS` field, or is still in `Q` after
setting `a` to any `AllIn Q` value. -/
def SafeWrites (Q : Value → Prop) (env : Env) (ρ : VarEnv) (v : Value) : Path → Prop
  | .rootP => True
  | .idxP p _ => SafeWrites Q env ρ v p
  | .sliceP p _ _ => SafeWrites Q env ρ v p
  | .dotP p a =>
    (∀ m gs, pathGet m env ρ v p = .ok (.struct gs) → hasExp gs = true →
      ∀ w, AllIn Q w → Q (.struct (setF gs a w))) ∧ SafeWrites Q env ρ v p

/-- The fields of `moduleinst` that hold lists of addresses. -/
def numAtoms : List AtomS := ["TAGS", "GLOBALS", "MEMS", "TABLES", "FUNCS", "DATAS", "ELEMS"]

/-- The fields of `moduleinst`. -/
def modAtoms : List AtomS := "TYPES" :: "EXPORTS" :: numAtoms

end Silmaril.Wasm.SpecTec.Sim.Round7.Roots
