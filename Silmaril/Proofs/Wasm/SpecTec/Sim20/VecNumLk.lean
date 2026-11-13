module

public import Silmaril.Wasm.SpecTec.Sim20.VecNum.Defs

/-!
# The vector numeric dispatchers of the corrected 2.0 script (kernel lookups)

`$vunop_`, `$vbinop_` and `$vrelop_` as `simEnv20V B` finds them: the clause lists of the script
(`Original.d263`, `d264`, `d265`), read off by `rfl`. The family erratum (`VecFix.fixedV20`)
replaces the three *type* families of the same names, not these definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecNum

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)
open Silmaril.Wasm.SpecTec.Scripts.Wasm20

/-- The clauses of a definition. -/
def clausesOf : Def → List Clause
  | .decD _ _ _ cs => cs
  | _ => []

set_option maxRecDepth 100000 in
/-- `$vunop_`, as `simEnv20V B` finds it. -/
theorem findDef_vunop (B : Builtins) :
    ∃ ps t, (simEnv20V B).findDef? "vunop_" = some (ps, t, clausesOf Original.d263) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
/-- `$vbinop_`, as `simEnv20V B` finds it. -/
theorem findDef_vbinop (B : Builtins) :
    ∃ ps t, (simEnv20V B).findDef? "vbinop_" = some (ps, t, clausesOf Original.d264) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
/-- `$vrelop_`, as `simEnv20V B` finds it. -/
theorem findDef_vrelop (B : Builtins) :
    ∃ ps t, (simEnv20V B).findDef? "vrelop_" = some (ps, t, clausesOf Original.d265) :=
  ⟨_, _, rfl⟩

end Silmaril.Wasm.SpecTec.Sim20.VecNum
