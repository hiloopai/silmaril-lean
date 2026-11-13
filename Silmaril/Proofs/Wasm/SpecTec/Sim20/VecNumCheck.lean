module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecNumUndef

/-!
# The 2.0 vector numeric dispatchers bind in `if` premises (kernel checks)

Every clause of `$vunop_`, `$vbinop_` and `$vrelop_` (`Original.d263`–`d265`), at every shape, opens
with `lane_1* = $lanes_(…)` and matches its arguments with pure patterns that do not mention
`lane_1*` (`clauseUnb`). The kernel checks this (`decide +kernel`). With `tryClausesUndef_of_all`,
every clause list definitely fails at every argument list, in every environment.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecNum

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Scripts.Wasm20

/-- Every clause of `$vunop_` binds in an `if` premise. -/
theorem clauseUnb_vunop : (clausesOf Original.d263).all clauseUnb = true := by decide +kernel

/-- Every clause of `$vbinop_` binds in an `if` premise. -/
theorem clauseUnb_vbinop : (clausesOf Original.d264).all clauseUnb = true := by decide +kernel

/-- Every clause of `$vrelop_` binds in an `if` premise. -/
theorem clauseUnb_vrelop : (clausesOf Original.d265).all clauseUnb = true := by decide +kernel

end Silmaril.Wasm.SpecTec.Sim20.VecNum
