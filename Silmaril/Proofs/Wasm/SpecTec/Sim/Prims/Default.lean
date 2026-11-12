module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Prims.Misc

/-!
# `$default_`: its first clause

Round 2 of the builtins track proved here that `CtrlCall.default` held for no `B`
(`not_ctrlCallDefault`, at branch `spectec-sim2-builtins`, `a0726f278`): `Sem.matchExp` stripped a
`SubE` argument pattern without testing the subtype, so `$default_`'s first clause
(`$default_(Inn) = CONST Inn 0`) caught every value type. The typing track's fix to the ported
evaluator (`Sem.argSubOk`, merged in the integration branch `spectec-sim2`) makes the clause test
`Inn`'s cases, so that refutation no longer holds and is retired; `CtrlCall.default` is left
open (`Prims.Residual.default`), to be proved by evaluating `$default_`'s five clauses.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Prims

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

set_option maxRecDepth 100000 in
/-- The first clause of `$default_`. -/
theorem defaultDef (B : Builtins) : ∃ ps t q rest, (simEnv B).findDef? "default_" = some (ps, t,
    .defD q [.expA (.subE (.varE "Inn") (.varT "Inn" []) (.varT "valtype" []))]
      (.optE (some (.caseE "CONST" (.tupE [.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" []),
        .caseE "%" (.tupE [.numE (.natN 0)])])))) [] :: rest) :=
  ⟨_, _, _, _, rfl⟩

end Silmaril.Wasm.SpecTec.Sim.Prims
