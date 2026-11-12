module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Undef

/-!
# Round 5, track simd (pass 3): the dispatchers' clauses definitely fail, operator by operator (IntUnOp, FloatUnOp)
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

/-- Every clause of `$vunop_` definitely fails at `encIntUnOp`. -/
theorem undef_IntUnOp (P : Profile) (hn : H → String) (host : HostSemantics H)
    (s : IntShape) (op : VecIntUnOp) (a : V128) :
    TryClausesUndef (simEnv (BI P hn host)) (clausesOf Original.d534)
      (encIntUnOp (s, op, a)) := by
  refine ⟨30, ?_⟩
  cases op <;>
    undef_simp [encIntUnOp, Original.d534]

/-- Every clause of `$vunop_` definitely fails at `encFloatUnOp`. -/
theorem undef_FloatUnOp (P : Profile) (hn : H → String) (host : HostSemantics H)
    (s : FloatShape) (op : FloatUnOp) (a : V128) :
    TryClausesUndef (simEnv (BI P hn host)) (clausesOf Original.d534)
      (encFloatUnOp (s, op, a)) := by
  refine ⟨30, ?_⟩
  cases op <;>
    undef_simp [encFloatUnOp, Original.d534]

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
