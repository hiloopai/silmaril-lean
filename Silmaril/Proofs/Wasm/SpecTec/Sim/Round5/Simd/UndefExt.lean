module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Undef

/-!
# Round 5, track simd (pass 3): the dispatchers' clauses definitely fail, operator by operator (ExtUnOp, ExtBinOp)
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

/-- Every clause of `$vextunop_` definitely fails at `encExtUnOp`. -/
theorem undef_ExtUnOp (P : Profile) (hn : H → String) (host : HostSemantics H)
    (s t : IntShape) (op : VecExtUnOp) (a : V128) :
    TryClausesUndef (simEnv (BI P hn host)) (clausesOf Original.d547)
      (encExtUnOp (s, t, op, a)) := by
  refine ⟨30, ?_⟩
  cases op
  undef_simp [encExtUnOp, Original.d547]

/-- Every clause of `$vextbinop_` definitely fails at `encExtBinOp`. -/
theorem undef_ExtBinOp (P : Profile) (hn : H → String) (host : HostSemantics H)
    (s t : IntShape) (op : VecExtBinOp) (a b : V128) :
    TryClausesUndef (simEnv (BI P hn host)) (clausesOf Original.d552)
      (encExtBinOp (s, t, op, a, b)) := by
  refine ⟨30, ?_⟩
  rcases op with ⟨h, sx⟩ | _ | _ <;> (try cases h) <;>
    undef_simp [encExtBinOp, Original.d552]

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
