module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecRefuteE20TUn
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecRefuteE20TBin
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecRefuteE20TRel

/-!
# The float-only vector operators in `simEnv20T B`, by evaluation

At fuel 200, `hasTyp` answers `false` on each `FloatOnly` instruction in `simEnv20T B`, from the
three evaluation modules `VecRefuteE20T{Un,Bin,Rel}`.
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

theorem hasTyp_floatOnly20T {i : V2.Instr} (h : FloatOnly i) :
    hasTyp 200 (simEnv20T B) VarEnv.empty (.varT "admininstr" []) (instrToV i) = .ok false := by
  rcases i <;> simp only [FloatOnly] at h
  case vecFloatUnOp s op => exact hasTyp_floatUn20T s op h
  case vecFloatBinOp s op => exact hasTyp_floatBin20T s op h
  case vecFloatRelOp s op => exact hasTyp_floatRel20T s op h

end Silmaril.Wasm.SpecTec.Sim20.VecRefute
