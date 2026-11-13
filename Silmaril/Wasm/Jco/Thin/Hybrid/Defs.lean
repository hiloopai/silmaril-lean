module

public import Silmaril.Wasm.Jco.Thin.Defs

/-!
# Hybrid wrappers: partial thin-wrapper recognition

Recognition is all-or-nothing (`recognize`). Its per-export variant
`recognizeExports` records, for each world export, the core export of the
module implementing it (`some j`) or nothing. A *hybrid* adaptor forwards the
recognized exports (identity glue, no adaptor code) and uses supplied glue
`G` for the others: `hybridGlue rs G`. The partial recognition is kept as
data, and the thin wrapper is the special case where every export is
recognized (`Silmaril.Wasm.Jco.Thin.hybridGlue_all`).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Thin

open Silmaril.Wasm.Component

/-- Per-export recognition: the core export implementing each world export. -/
def recognizeExports (s : Style) (w : World) (exps : CoreIface) : List (Option Nat) :=
  w.exports.map fun f => findCore (s.exportName f.1) f.2.flat exps

/-- The hybrid glue: forward recognized exports, use `G` for the others (a
missing entry of `G` traps). -/
def hybridGlue (rs : List (Option Nat)) (G : List Impl) : List Impl :=
  (List.range rs.length).map fun k =>
    match rs[k]? with
    | some (some j) => Impl.fwd j
    | _ => G[k]?.getD Impl.trap

end Silmaril.Wasm.Jco.Thin
