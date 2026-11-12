module

public import Silmaril.Machine.LambdaRTLLir.Defs
public import Silmaril.SSA.LambdaRTL.Thms

/-!
# λRTL over `Lir` operators: checked facts and a validated example

* `app_unary`, `app_binary`, `app_test`: instruction semantics *is* `Lir.Unop.eval` /
  `Lir.Binop.eval` on words (partial binops give `none`), and `test` is `Lir`'s branch condition.
* `unpair_pair`: the model is pair-lawful (`unpair (pair a b) = pure (a, b)`), the hypothesis
  of the versioning translation.
* `absDiff`: `|x - y|` (unsigned) via `cmp ltu`, `test` and `case`; it is dominance-scoped SSA
  (`absDiff_isSSA`), its flattening passes the validator (`absDiff_validate`), the flat CFG runs
  as the region (`absDiff_run`), the store and lexical readings agree, and it computes
  `|3 - 10| = 7` (`absDiff_eval`), all checked by `decide`/kernel evaluation.
-/

@[expose] public section

namespace Silmaril.Machine.LambdaRTLLir

open Silmaril.SSA.LambdaRTL

theorem app_unary (u : Lir.Unop) (x : Lir.Word) :
    model.app (.unary u) (.word x) = some (.word (u.eval x)) := rfl

theorem app_binary (b : Lir.Binop) (x y : Lir.Word) :
    model.app (.binary b) (.pair (.word x) (.word y)) = (b.eval x y).map .word := rfl

theorem app_test (x : Lir.Word) :
    model.app .test (.word x) = some (if x ≠ 0 then .inl .unit else .inr .unit) := rfl

theorem unpair_pair (a b : LVal) : model.unpair (model.pair a b) = pure (a, b) := rfl

/-- `|x - y|` on unsigned words, with variables `x = 0`, `y = 1`, `c = 2`, `d = 3`, `u = 4`
and a single exit label. -/
def absDiff : Region ℕ Unit LirOp :=
  .let1 2 (.app (.binary (.cmp .ltu)) (.pair (.var 0) (.var 1)))
    (.case (.app .test (.var 2))
      4 (.let1 3 (.app (.binary .sub) (.pair (.var 1) (.var 0))) (.br () (.var 3)))
      4 (.let1 3 (.app (.binary .sub) (.pair (.var 0) (.var 1))) (.br () (.var 3))))

theorem absDiff_isSSA : absDiff.IsSSA {0, 1} := by
  simp only [absDiff, Region.IsSSA, Op.fv, Val.fv]; decide

theorem absDiff_validate : CFG.validate Sum.inl absDiff (CFG.flatten absDiff) = true := by
  decide

/-- The validated flat CFG runs as the region, in every store. -/
theorem absDiff_run (σ : ℕ → LVal) :
    (CFG.flatten absDiff).run model σ =
      (fun e => (Sum.inl e.1, e.2)) <$> absDiff.evalRTL model σ :=
  CFG.run_of_validate model Sum.inl absDiff _ absDiff_validate σ

/-- Store and lexical readings agree (agreement on SSA). -/
theorem absDiff_obs (σ : ℕ → LVal) : absDiff.evalObs model σ = absDiff.evalSSA model σ :=
  Region.evalObs_eq_evalSSA_of_isSSA model absDiff_isSSA σ

/-- The input store `x = 3`, `y = 10`. -/
def σ₀ : ℕ → LVal
  | 0 => .word 3
  | 1 => .word 10
  | _ => .unit

theorem absDiff_eval : absDiff.evalSSA model σ₀ = some ((), .word 7) := by decide

end Silmaril.Machine.LambdaRTLLir
