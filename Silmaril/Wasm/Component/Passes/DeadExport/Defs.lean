module

public import Silmaril.Wasm.Component.IR.Defs

/-!
# Dead export elimination: the transformation

A program observes only some exports of its component (`Program.observe`).
`deadExports` keeps exactly the observed exports, in the order observed (an
observed index out of range becomes a trapping export), and then observes all
of them. Instances only used by the removed exports become dead, and can then
be removed by dead instance elimination.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

variable {M : Type}

/-- A trapping export (used for observed indices out of range). -/
def Export.trap : Export := ⟨"", ⟨[], []⟩, Impl.trap⟩

/-- Keep the observed exports. -/
def deadExports (p : Program M) : Program M :=
  match p.observe, p.comp with
  | none, _ => p
  | some obs, .mk I ns xs =>
    { comp := .mk I ns (obs.map fun j => xs[j]?.getD Export.trap), observe := none }

end Silmaril.Wasm.Component
