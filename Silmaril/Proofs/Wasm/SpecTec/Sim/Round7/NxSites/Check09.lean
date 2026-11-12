module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxSites.Sig

/-!
# Round 7, REH route 2: the site check on top-level definitions 450–499 of the script

One kernel computation (`decide +kernel`, kernel reduction, no native code): every top-level definition in
this slice of the fixed wasm-3.0 script passes `NxSites.itemOk sigFixed`, and its binding sites
are as listed. `Round7/NxSites/Thms.lean` puts the twenty slices together.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxSites

open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)

set_option maxRecDepth 100000 in
/-- Slice 9 of `itemsOk_fixed` and `bindSites_fixed`. -/
theorem check09 :
    ((fixed.drop 450).take 50).all (itemOk sigFixed) = true ∧
      bindSitesL sigFixed ((fixed.drop 450).take 50) =
        [] := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
