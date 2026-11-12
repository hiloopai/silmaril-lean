module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Undef

/-!
# Round 5, track simd (pass 3): the dispatchers' clauses definitely fail, operator by operator (IntRelOp, FloatRelOp)
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Simd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Scripts.Wasm30
open Round4Int (BI)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {H : Type}

/-- Every clause of `$vrelop_` definitely fails at `encIntRelOp`. -/
theorem undef_IntRelOp (P : Profile) (hn : H → String) (host : HostSemantics H)
    (s : IntShape) (op : IntRelOp) (a b : V128) :
    TryClausesUndef (simEnv (BI P hn host)) (clausesOf Original.d537)
      (encIntRelOp (s, op, a, b)) := by
  refine ⟨30, ?_⟩
  cases op <;>
    undef_simp [encIntRelOp, Original.d537]

/-- Every clause of `$vrelop_` definitely fails at `encFloatRelOp`. -/
theorem undef_FloatRelOp (P : Profile) (hn : H → String) (host : HostSemantics H)
    (s : FloatShape) (op : FloatRelOp) (a b : V128) :
    TryClausesUndef (simEnv (BI P hn host)) (clausesOf Original.d537)
      (encFloatRelOp (s, op, a, b)) := by
  refine ⟨30, ?_⟩
  cases op <;>
    undef_simp [encFloatRelOp, Original.d537]

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
