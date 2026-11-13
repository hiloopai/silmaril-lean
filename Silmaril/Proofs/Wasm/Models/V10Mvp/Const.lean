module

public import Silmaril.Wasm.Models.Lime1Mvp.Thms

/-!
# Valid 1.0 constant expressions are single instructions

Wasm 1.0 validation (`Silmaril.Wasm.V1.Validation.ConstExprType`) asks that every instruction of
a constant expression be a constant instruction (`ConstantInstr`: `i32/i64/f32/f64.const` or
`global.get` of an immutable global) and that the expression have type `[] → [t]`. A constant
instruction pushes exactly one value, so the expression has exactly one instruction:

* `len_const`: a constant instruction typed `a → b` has `|b| = |a| + 1` (through `frame`);
* `len_constExpr`: a sequence of constant instructions typed `a → c` has `|c| = |a| + n`;
* **`constExprType_single`**: a valid 1.0 constant expression is `[i]` for a constant `i`;
* **`constExprB_v10`**: its Core image is a constant expression of the MVP profile `v10`
  (`constExprB v10`: in `v10` and `simpleConst`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V10Mvp

open Silmaril.Wasm Silmaril.Wasm.Models
open Silmaril.Wasm.V1.Validation (InstrType ExprType ConstantInstr ConstantExpr ConstExprType)

variable {C : Silmaril.Wasm.V1.Validation.Context}

/-- A constant instruction pushes exactly one value. -/
theorem len_const : ∀ {i : Silmaril.Wasm.V1.Instr} {a b : Silmaril.Wasm.V1.ResultType},
    InstrType C i a b → ConstantInstr C i → b.length = a.length + 1
  | _, _, _, .frame pre h, hc => by
    rw [List.length_append, List.length_append, len_const h hc, Nat.add_assoc]
  | _, _, _, .intConst _ _, _ => rfl
  | _, _, _, .floatConst _ _, _ => rfl
  | _, _, _, .globalGet _ _, _ => rfl
  | _, _, _, .nop, hc | _, _, _, .unreachable _ _, hc | _, _, _, .drop _, hc
  | _, _, _, .select _, hc | _, _, _, .block _ _, hc | _, _, _, .loop _ _, hc
  | _, _, _, .if_ _ _ _, hc | _, _, _, .br _ _ _ _, hc | _, _, _, .brIf _ _, hc
  | _, _, _, .brTable _ _ _ _ _ _, hc | _, _, _, .return_ _ _ _, hc | _, _, _, .call _ _, hc
  | _, _, _, .callIndirect _ _ _, hc | _, _, _, .localGet _ _, hc | _, _, _, .localSet _ _, hc
  | _, _, _, .localTee _ _, hc | _, _, _, .globalSet _ _, hc
  | _, _, _, .intLoad _ _ _ _ _, hc | _, _, _, .floatLoad _ _ _ _, hc
  | _, _, _, .intStore _ _ _ _ _, hc | _, _, _, .floatStore _ _ _ _, hc
  | _, _, _, .memorySize _, hc | _, _, _, .memoryGrow _, hc | _, _, _, .intUnOp _ _, hc
  | _, _, _, .intBinOp _ _, hc | _, _, _, .intTestOp _ _, hc | _, _, _, .intRelOp _ _, hc
  | _, _, _, .floatUnOp _ _, hc | _, _, _, .floatBinOp _ _, hc
  | _, _, _, .floatRelOp _ _, hc | _, _, _, .convert _, hc => nomatch hc

/-- A sequence of constant instructions pushes one value per instruction. -/
theorem len_constExpr : ∀ (body : Silmaril.Wasm.V1.Expr) {a c : Silmaril.Wasm.V1.ResultType},
    ConstantExpr C body → ExprType C body a c → c.length = a.length + body.length
  | [], _, _, _, h => by
    cases h
    rfl
  | i :: is, _, _, hc, h => by
    cases h with
    | cons hi his =>
      rw [len_constExpr is (fun j hj => hc j (List.mem_cons_of_mem i hj)) his,
        len_const hi (hc i List.mem_cons_self), List.length_cons]
      omega

/-- **A valid 1.0 constant expression is a single constant instruction.** -/
theorem constExprType_single {body : Silmaril.Wasm.V1.Expr} {t : Silmaril.Wasm.V1.ValType}
    (h : ConstExprType C body t) : ∃ i, body = [i] ∧ ConstantInstr C i := by
  have hl := len_constExpr body h.constant h.typed
  rcases body with _ | ⟨i, _ | ⟨j, rest⟩⟩
  · simp at hl
  · exact ⟨i, rfl, h.constant i List.mem_cons_self⟩
  · simp at hl

theorem simpleConst_of {i : Silmaril.Wasm.V1.Instr} (hi : ConstantInstr C i) :
    simpleConst (Silmaril.Wasm.V1.Expr.toCore [i]) = true := by
  cases hi <;> rfl

/-- **The Core image of a valid 1.0 constant expression is a constant expression of `v10`.** -/
theorem constExprB_v10 {body : Silmaril.Wasm.V1.Expr} {t : Silmaril.Wasm.V1.ValType}
    (h : ConstExprType C body t) : constExprB v10 (Silmaril.Wasm.V1.Expr.toCore body) = true := by
  obtain ⟨i, rfl, hi⟩ := constExprType_single h
  simp [constExprB, Lime1Mvp.v10_expr_inFeat, simpleConst_of hi]

end Silmaril.Proofs.Wasm.Models.V10Mvp
