module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Undef

/-!
# Round 5, track simd (pass 3): the dispatchers' clauses definitely fail, operator by operator (IntTernOp, FloatTernOp, ExtTernOp)
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

/-- Every clause of `$vternop_` definitely fails at `encIntTernOp`. -/
theorem undef_IntTernOp (P : Profile) (hn : H → String) (host : HostSemantics H)
    (s : IntShape) (op : VecIntTernOp) (a b c : V128) :
    TryClausesUndef (simEnv (BI P hn host)) (clausesOf Original.d536)
      (encIntTernOp (s, op, a, b, c)) := by
  refine ⟨30, ?_⟩
  cases op
  undef_simp [encIntTernOp, Original.d536]

/-- Every clause of `$vternop_` definitely fails at `encFloatTernOp`. -/
theorem undef_FloatTernOp (P : Profile) (hn : H → String) (host : HostSemantics H)
    (s : FloatShape) (op : VecFloatTernOp) (a b c : V128) :
    TryClausesUndef (simEnv (BI P hn host)) (clausesOf Original.d536)
      (encFloatTernOp (s, op, a, b, c)) := by
  refine ⟨30, ?_⟩
  cases op <;>
    undef_simp [encFloatTernOp, Original.d536]

/-- Every clause of `$vextternop_` definitely fails at `encExtTernOp`. -/
theorem undef_ExtTernOp (P : Profile) (hn : H → String) (host : HostSemantics H)
    (s t : IntShape) (op : VecExtTernOp) (a b c : V128) :
    TryClausesUndef (simEnv (BI P hn host)) (clausesOf Original.d553)
      (encExtTernOp (s, t, op, a, b, c)) := by
  refine ⟨30, ?_⟩
  cases op
  undef_simp [encExtTernOp, Original.d553]

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
