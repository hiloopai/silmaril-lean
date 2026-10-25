module

public import Silmaril.Wasm.Binaryen.EffectRun
public import Silmaril.Wasm.Execution.Core.Sim.Rank

@[expose] public section

/-! # The body-aware effect size is a contextual simulation rank

Unlike a rank that treats plain structured instructions as atoms, this measure
pays for their bodies before entry. In particular, entering an empty-typed block
strictly decreases it, even when the body is arbitrarily large.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Execution.Core.Sim

instance : LawfulCodeRank aszs where
  context_lt := by intros; simp only [aszs_append]; omega
  infix_lt := by
    intro p m q hm
    have := aszs_pos hm
    simp only [aszs_append]
    omega
  label_body_lt := by intros; simp; omega
  label_lt := by intros; simp_all
  handler_body_lt := by intros; simp [asz]; omega
  handler_lt := by intros; simp_all [asz]
  frame_body_lt := by intros; simp [asz]; omega
  frame_lt := by intros; simp_all [asz]

/-- Plain block entry pays for its runtime label before executing the body. -/
theorem aszs_block_entry (body : List Instr) :
    aszs [.label 0 [] (expression body)] < aszs [.plain (.block .empty body)] := by
  simp

end Silmaril.Wasm.Binaryen
