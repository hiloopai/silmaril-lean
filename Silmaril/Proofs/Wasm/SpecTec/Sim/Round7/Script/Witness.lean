module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Script.Defs

/-!
# Round 7: the `Step` closure facts are not vacuous

Kernel computations on single definitions of the fixed wasm-3.0 script, showing that the
traversal of `Defs.lean` sees what the closure facts are about:

* the type `name` (definition 53) is reachable and calls `$utf8` (`name_calls_utf8`);
* the type `moduleinst` (definition 265) is reachable and declares the field `EXPORTS`, which is
  a type-level atom and so not an event (`moduleinst_declares_exports`);
* `$with_tableinst` (definition 610) updates `$sof(z)` along `.TABLES[…]`
  (`with_tableinst_upd`);
* `Deftype_ok` (definition 334) composes records (`deftype_ok_comp`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Script

set_option maxRecDepth 100000

theorem name_reach : (2, "name") ∈ stepReach ∧ (2, "moduleinst") ∈ stepReach ∧
    (2, "exportinst") ∈ stepReach ∧ (1, "utf8") ∈ stepReach := by decide +kernel

/-- **The type `name` calls `$utf8`.** -/
theorem name_calls_utf8 :
    ((items ((Scripts.Wasm30.fixed.drop 53).take 1)).any fun it =>
      it.1 == 2 && it.2.1 == "name" && (evRefs it.2.2).contains (1, "utf8")) = true := by
  decide +kernel

/-- **The type `moduleinst` declares the field `EXPORTS`.** -/
theorem moduleinst_declares_exports :
    ((Scripts.Wasm30.fixed.drop 265).take 1).any (declaresField "moduleinst" "EXPORTS") = true := by
  decide +kernel

/-- **`$with_tableinst` updates the store of `$sof(z)` along `.TABLES[…]`.** -/
theorem with_tableinst_upd :
    updSites stepReach ((Scripts.Wasm30.fixed.drop 610).take 1) =
      [(1, "with_tableinst", "sof", ["TABLES"])] := by
  decide +kernel

/-- **`Deftype_ok` composes records.** -/
theorem deftype_ok_comp :
    compSites stepReach ((Scripts.Wasm30.fixed.drop 334).take 1) = [(0, "Deftype_ok")] := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.Script
