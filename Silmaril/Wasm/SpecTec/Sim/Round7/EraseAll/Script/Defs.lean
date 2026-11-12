module

public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Script.Defs

/-!
# Round 7, the whole-evaluator erasure on the wasm-3.0 script: the checked part

The names of the fixed wasm-3.0 script at which `Round7.EraseAll.eraseAt` is used, and the two
kernel computations that discharge `Hyps.defs` and `Hyps.rels` there.

* `excluded`: the six reachable names left out. `$with_tableinst` and `$with_meminst` update
  `.TABLES[i]`/`.MEMS[i]` of `$sof(z)`, which is a module record when `z` is not a state (the
  update fails `updOk`); `$hostcall` answers only up to the order of its list
  (`Round7.Swap.hostcallCall_erase`); `$blocktype_` reads `MODULE.TYPES` out of its argument
  `z`; `Step_read` calls `$blocktype_`, and `Step` calls the other three and `Step_read`. They
  are called only from `Step` and `Step_read`, so `stepReachE` is closed under references.
* `stepReachE := stepReach` without `excluded`; `gdE`, `grE`: its definitions and relations.
* `xDefsOk`, `xRelsOk`: every `gd` definition's clauses, every `gr` relation's rules pass the
  syntactic check `xExp`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- The reachable names the evaluator-level erasure leaves to `Step`'s own rules. -/
def excluded : List (Nat × String) :=
  [(1, "with_tableinst"), (1, "with_meminst"), (1, "hostcall"), (1, "blocktype_"), (0, "Step"),
   (0, "Step_read")]

/-- `Script.stepReach` without `excluded`. -/
def stepReachE : List (Nat × String) :=
  Script.stepReach.filter fun p => !excluded.contains p

/-- The definitions of `stepReachE`. -/
def gdE (x : String) : Bool := stepReachE.contains (1, x)

/-- The relations of `stepReachE`. -/
def grE (x : String) : Bool := stepReachE.contains (0, x)

/-- Every `gd` definition of `m` has clauses that pass the check. -/
def xDefsOk (gr gd : String → Bool) (m : Map DefDef) : Bool :=
  m.all fun p => !gd p.1 || p.2.2.2.all (xClause gr gd)

/-- Every `gr` relation of `m` has rules that pass the check. -/
def xRelsOk (gr gd : String → Bool) (m : Map RelDef) : Bool :=
  m.all fun p => !gr p.1 || p.2.2.2.2.all (xRule gr gd)

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
