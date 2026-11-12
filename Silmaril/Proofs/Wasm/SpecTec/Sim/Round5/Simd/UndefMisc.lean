module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Undef

/-!
# Round 5, track simd (pass 3): the dispatchers' clauses definitely fail, operator by operator (ShiftOp, Bitmask, Swizzle, Narrow)
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

/-- Every clause of `$vshiftop_` definitely fails at `encShiftOp`. -/
theorem undef_ShiftOp (P : Profile) (hn : H → String) (host : HostSemantics H)
    (s : IntShape) (op : VecShiftOp) (a : V128) (n : BitVec 32) :
    TryClausesUndef (simEnv (BI P hn host)) (clausesOf Original.d540)
      (encShiftOp (s, op, a, n)) := by
  refine ⟨30, ?_⟩
  cases op <;>
    undef_simp [encShiftOp, Original.d540]

/-- Every clause of `$vbitmaskop_` definitely fails at `encBitmask`. -/
theorem undef_Bitmask (P : Profile) (hn : H → String) (host : HostSemantics H)
    (s : IntShape) (a : V128) :
    TryClausesUndef (simEnv (BI P hn host)) (clausesOf Original.d541)
      (encBitmask (s, a)) := by
  refine ⟨30, ?_⟩
  undef_simp [encBitmask, Original.d541]

/-- Every clause of `$vswizzlop_` definitely fails at `encSwizzle`. -/
theorem undef_Swizzle (P : Profile) (hn : H → String) (host : HostSemantics H)
    (op : VecSwizzleOp) (a b : V128) :
    TryClausesUndef (simEnv (BI P hn host)) (clausesOf Original.d542)
      (encSwizzle (op, a, b)) := by
  refine ⟨30, ?_⟩
  cases op <;>
    undef_simp [encSwizzle, Original.d542]

/-- Every clause of `$vnarrowop_` definitely fails at `encNarrow`. -/
theorem undef_Narrow (P : Profile) (hn : H → String) (host : HostSemantics H)
    (s t : IntShape) (sx : Signedness) (a b : V128) :
    TryClausesUndef (simEnv (BI P hn host)) (clausesOf Original.d544)
      (encNarrow (s, t, sx, a, b)) := by
  refine ⟨30, ?_⟩
  undef_simp [encNarrow, Original.d544]

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
