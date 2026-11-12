module

public import Silmaril.Wasm.LimeCompile.Direct.Defs

/-!
# The direct rewrite is the identity on Lime1 code

Lime1 code (the image of `Lime1.Instr.toCore`) has only the untyped `select`, so the rewrite
leaves it unchanged, in every body and in every module (`lowerModule_toCore`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.Direct

open Silmaril.Wasm
open Silmaril.Wasm.LimeCompile.Direct

mutual
set_option linter.unusedTactic false in
theorem lowerI_toCore (j : Lime1.Instr) : lowerI (Lime1.Instr.toCore j) = Lime1.Instr.toCore j := by
  cases j with
  | block t b =>
    rw [Lime1.Instr.toCore, lowerI, lowerL_toCore b]
  | loop t b =>
    rw [Lime1.Instr.toCore, lowerI, lowerL_toCore b]
  | if_ t b₁ b₂ =>
    rw [Lime1.Instr.toCore, lowerI, lowerL_toCore b₁, lowerL_toCore b₂]
  | _ => rw [Lime1.Instr.toCore, lowerI] <;> simp
termination_by sizeOf j
decreasing_by all_goals simp_wf; all_goals omega

set_option linter.unusedTactic false in
theorem lowerL_toCore (es : Lime1.Expr) : lowerL (Lime1.Expr.toCore es) = Lime1.Expr.toCore es := by
  cases es with
  | nil => rw [Lime1.Expr.toCore, lowerL]
  | cons j es => rw [Lime1.Expr.toCore, lowerL, lowerI_toCore j, lowerL_toCore es]
termination_by sizeOf es
decreasing_by all_goals simp_wf; all_goals omega
end

/-- **The rewrite is the identity on the Core image of a Lime1 module.** -/
theorem lowerModule_toCore (l : Lime1.Module) : lowerModule l.toCore = l.toCore := by
  have hf : ∀ f : Lime1.Func, lowerFunc f.toCore = f.toCore := fun f => by
    simp only [lowerFunc, Lime1.Func.toCore]
    rw [lowerL_toCore]
  simp only [lowerModule, Lime1.Module.toCore, List.map_map]
  congr 1
  exact List.map_congr_left fun f _ => hf f

end Silmaril.Proofs.Wasm.LimeCompile.Direct
