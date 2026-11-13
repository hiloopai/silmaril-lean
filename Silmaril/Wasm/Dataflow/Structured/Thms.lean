module

public import Silmaril.Wasm.Dataflow.Structured.Defs

/-!
# Backward dataflow analysis over structured Wasm control flow: theorems

* `loopFix_safe`, `Backward.instr_loop_safe`: the loop-head value is a post-fixed point
  of the loop body (the back edge is safe);
* `Backward.labelVal_le_brTable`: `br_table` joins its targets and its default;
* `Backward.seq_append`, `Backward.instr_block`: unfolding lemmas.
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow

open Silmaril.Wasm

variable {L : Type} [Lattice L] [OrderBot L] [OrderTop L] [DecidableLE L]

/-- `loopFix` always returns a safe value (a post-fixed point). -/
theorem loopFix_safe (F : L → L) (n : Nat) : F (loopFix F n) ≤ loopFix F n := by
  unfold loopFix
  split
  · assumption
  · exact le_top

namespace Backward

variable (A : Backward L)

theorem seq_append (env : List L) (out : L) (is js : List Instr) :
    A.seq env out (is ++ js) = A.seq env (A.seq env out js) is := by
  induction is with
  | nil => simp
  | cons i is ih => simp [ih]

/-- The value before a `block` is the value of its body with the block's label
bound to the continuation. -/
theorem instr_block (env : List L) (out : L) (bt : BlockType) (body : List Instr) :
    A.instr env out (.block bt body) = A.seq (out :: env) out body := by
  simp [instr]

/-- The loop-head value is safe for the loop's own back edge: the equation of
the loop label holds as `⊒` (the course's `IsSafe`, notes p. 8). -/
theorem instr_loop_safe (env : List L) (out : L) (bt : BlockType) (body : List Instr) :
    A.seq (A.instr env out (.loop bt body) :: env) out body ≤
      A.instr env out (.loop bt body) := by
  simp only [instr]
  exact loopFix_safe (fun X => A.seq (X :: env) out body) (A.loopFuel env out body)

/-- `br_table` joins its targets and its default. -/
theorem labelVal_le_brTable (env : List L) (out : L) {ls : List LabelIdx} {l l' : LabelIdx}
    (h : l' ∈ ls ∨ l' = l) : labelVal env l' ≤ A.instr env out (.brTable ls l) := by
  simp only [instr]
  induction ls with
  | nil =>
      rcases h with h | h
      · simp at h
      · subst h; exact le_rfl
  | cons a ls ih =>
      simp only [List.foldr_cons]
      rcases h with h | h
      · rcases List.mem_cons.mp h with h | h
        · subst h; exact le_sup_left
        · exact le_sup_of_le_right (ih (Or.inl h))
      · exact le_sup_of_le_right (ih (Or.inr h))

end Backward

end Silmaril.Wasm.Dataflow
