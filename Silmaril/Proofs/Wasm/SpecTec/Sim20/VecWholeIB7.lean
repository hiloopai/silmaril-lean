module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixBase

/-!
# Valid integer `vbinop`s, part 7 in `simEnv20V B`, by evaluation

Part of `VecWholeValid`: each valid integer vector operator below is a typed `admininstr` of the
corrected script, checked by evaluating `hasTyp` with `B` free.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecWhole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)

set_option maxRecDepth 100000

variable {B : Builtins}

set_option maxHeartbeats 4000000 in
theorem hasTyp_ib_7 (s : IntShape) (op : V2.VecIntBinOp)
    (h : (s, op) ∈ ([(.i32x4, (.max .unsigned)), (.i64x2, .add), (.i64x2, .sub), (.i64x2, .mul)] : List (IntShape × V2.VecIntBinOp))) :
    hasTyp 200 (simEnv20V B) VarEnv.empty (.varT "admininstr" []) (instrToV (.vecIntBinOp s op)) =
      .ok true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> with_unfolding_all rfl

end Silmaril.Wasm.SpecTec.Sim20.VecWhole
