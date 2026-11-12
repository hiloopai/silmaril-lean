module

public import Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.CodeErase.HypsB

/-!
# Round 8, function code erasure: the evaluator commutes with erasing `CODE` fields

Namespaces `Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.{Swap,Erase,EraseAll}`; see
`docs/projects/spectec/README.md`. Definitions are in `Round8/CodeErase/Defs.lean`.

Round 3's evaluator-level export erasure (`Round7.EraseAll.eraseAt`), copied for `CODE` fields,
with the injective replacement `hostC` (the code of a host function named by an injective code of
the old contents). The copies are unrefined and live in `Raw/…/Round8/CodeErase/`:

* `Swap.eraseC_injective`, `Swap.qInj`: `eraseC` is injective, so `QInj Q` holds for every `Q`;
* `EraseAll.eraseAt`: every one of the 29 members of the evaluator's mutual block commutes with
  `eraseC`, on syntax that passes the check `xExp` (no `.CODE` projection, field or path step),
  given `Hyps` (injectivity, checked clauses and rules, builtins that commute, safe updates);
* `EraseAll.evalExp_erase_iff`, `EraseAll.derives_erase_iff`: the fuel-free forms.

**On the wasm-3.0 script** (`hyps_sim`, no hypothesis left): with every value in the swap set,
at round 6's primitives (`simEnv (Prims.builtins P hn host)`), every definition `Step` reaches
but `$hostcall` and every relation it reaches but `Step` pass the check (40 kernel chunks,
`Proofs/…/Round8/CodeErase/Check*.lean`), and the primitives commute with `eraseC`
(`biErase_sim`). So:

* `eraseAt_sim`: the whole evaluator commutes with `eraseC` on that part of the script;
* `derives_erase_sim`, `stepRead_erase_iff`: **under the evaluator reading, every relation
  `Step` reaches other than `Step` itself (in particular `Step_read` and `Step_pure`) derives
  `eraseC v` exactly when it derives `v`**: erasing the code of every function instance does not
  change what these relations derive.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase

section Sim
open Silmaril.SpecTec Silmaril.SpecTec.Sem
variable {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
  (host : Silmaril.Wasm.Execution.Core.HostSemantics H)

/-- **The evaluator commutes with `eraseC` on the wasm-3.0 script**, at every fuel, outside
`$hostcall` and `Step`. -/
theorem eraseAt_sim : ∀ n, EraseAll.EraseAt (fun _ => True) EraseAll.grC EraseAll.gdC
    (simEnv (Prims.builtins P hn host)) n :=
  EraseAll.eraseAt (EraseAll.hyps_sim P hn host)

/-- **A relation `Step` reaches, other than `Step`, derives `eraseC v` exactly when it derives
`v`**, under the evaluator reading, at value arguments. -/
theorem derives_erase_sim {x : IL.Id} (hx : EraseAll.grC x = true) (op : IL.MixopS)
    (vs : List Value) (v : Value) :
    Derives (simEnv (Prims.builtins P hn host)) x op (vs.map fun u => .val (Swap.eraseC u))
        (Swap.eraseC v) ↔
      Derives (simEnv (Prims.builtins P hn host)) x op (vs.map .val) v := by
  have h := EraseAll.derives_erase_iff (EraseAll.hyps_sim P hn host) (op := op)
    (ws := vs.map .val) hx (fun w hw => by
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hw
      exact EraseAll.allIn_true u) (EraseAll.allIn_true v)
  simpa [Function.comp_def, Swap.eraseA] using h

/-- **`Step_read` derives the erased pair exactly when it derives the pair**, under the evaluator
reading. -/
theorem stepRead_erase_iff (c w : Value) :
    Derives (simEnv (Prims.builtins P hn host)) "Step_read" "%~>%" []
        (Swap.eraseC (.tuple [c, w])) ↔
      Derives (simEnv (Prims.builtins P hn host)) "Step_read" "%~>%" [] (.tuple [c, w]) :=
  derives_erase_sim P hn host (x := "Step_read") (by decide) "%~>%" [] _

end Sim

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap.qInj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Swap.qInj

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll.eraseAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms EraseAll.eraseAt

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll.derives_erase_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms EraseAll.derives_erase_iff

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll.hyps_sim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms EraseAll.hyps_sim

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.stepRead_erase_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms stepRead_erase_iff

end Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase
