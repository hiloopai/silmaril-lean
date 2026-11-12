module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecRefuteBase

/-!
# The float-only vector operators in `simEnv20 B`, by evaluation

At fuel 200, `hasTyp` answers `false` on each `FloatOnly` instruction in `simEnv20 B` (one kernel
evaluation per operator and shape), and `true` on `abs` and `neg`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecRefute

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)

set_option maxRecDepth 100000

variable {B : Builtins}

set_option maxHeartbeats 4000000 in
theorem hasTyp_floatOnly20 {i : V2.Instr} (h : FloatOnly i) :
    hasTyp 200 (simEnv20 B) VarEnv.empty (.varT "admininstr" []) (instrToV i) = .ok false := by
  rcases i <;> simp only [FloatOnly, List.mem_cons, List.not_mem_nil, or_false] at h
  case vecFloatUnOp s op =>
    rcases s <;> rcases h with rfl | rfl | rfl | rfl | rfl <;> with_unfolding_all rfl
  case vecFloatBinOp s op =>
    rcases s <;> rcases h with rfl | rfl | rfl | rfl | rfl <;> with_unfolding_all rfl
  case vecFloatRelOp s op =>
    rcases s <;> rcases h with rfl | rfl | rfl | rfl <;> with_unfolding_all rfl

set_option maxHeartbeats 4000000 in
/-- Their integer-shared namesakes are typed. -/
theorem hasTyp_abs_neg20 (s : FloatShape) (op : FloatUnOp) (h : op = .abs ∨ op = .neg) :
    hasTyp 200 (simEnv20 B) VarEnv.empty (.varT "admininstr" [])
      (instrToV (.vecFloatUnOp s op)) = .ok true := by
  rcases s <;> rcases h with rfl | rfl <;> with_unfolding_all rfl

end Silmaril.Wasm.SpecTec.Sim20.VecRefute
