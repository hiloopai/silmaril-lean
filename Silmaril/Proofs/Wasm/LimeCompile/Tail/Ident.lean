module

public import Silmaril.Wasm.LimeCompile.Tail.Defs
public import Silmaril.Proofs.Wasm.LimeCompile.Direct.Ident

/-!
# The tail-call rewrite: identity on Lime1, sequences and size

* `tailL_append`, `tailL_nil`, `tailL_cons`: the rewrite is a monoid map on sequences;
* `tailI_toCore`, `tailL_toCore`, `tailModule_toCore`, `lower_toCore`: Lime1 code has no tail
  call and no `try_table`, so the rewrite (and the whole lowering) is the identity on it;
* `tailL_of_count`: a sequence with no tail call (outside `try_table`) is unchanged;
* `size`, `size_tailL`: counting every instruction, nested bodies included, the rewrite adds
  exactly one instruction (`return`) per replaced tail call.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.Tail

open Silmaril.Wasm
open Silmaril.Wasm.LimeCompile.Tail

theorem tailL_nil : tailL [] = [] := by rw [tailL]

theorem tailL_cons (i : Instr) (is : List Instr) : tailL (i :: is) = tailI i ++ tailL is := by
  rw [tailL]

theorem tailL_append : ∀ a b : List Instr, tailL (a ++ b) = tailL a ++ tailL b
  | [], b => by rw [List.nil_append, tailL_nil, List.nil_append]
  | i :: a, b => by
    rw [List.cons_append, tailL_cons, tailL_cons, tailL_append a b, List.append_assoc]

theorem naiveL_nil : naiveL [] = [] := by rw [naiveL]

theorem naiveL_cons (i : Instr) (is : List Instr) : naiveL (i :: is) = naiveI i ++ naiveL is := by
  rw [naiveL]

set_option linter.unusedTactic false in
mutual
theorem tailI_toCore (j : Lime1.Instr) : tailI (Lime1.Instr.toCore j) = [Lime1.Instr.toCore j] := by
  cases j with
  | block t b => rw [Lime1.Instr.toCore, tailI, tailL_toCore b]
  | loop t b => rw [Lime1.Instr.toCore, tailI, tailL_toCore b]
  | if_ t b₁ b₂ => rw [Lime1.Instr.toCore, tailI, tailL_toCore b₁, tailL_toCore b₂]
  | _ => rw [Lime1.Instr.toCore, tailI] <;> simp
termination_by sizeOf j
decreasing_by all_goals simp_wf; all_goals omega

theorem tailL_toCore (es : Lime1.Expr) : tailL (Lime1.Expr.toCore es) = Lime1.Expr.toCore es := by
  cases es with
  | nil => rw [Lime1.Expr.toCore, tailL_nil]
  | cons j es =>
    rw [Lime1.Expr.toCore, tailL_cons, tailI_toCore j, tailL_toCore es, List.singleton_append]
termination_by sizeOf es
decreasing_by all_goals simp_wf; all_goals omega
end

/-- **The tail rewrite is the identity on the Core image of a Lime1 module.** -/
theorem tailModule_toCore (l : Lime1.Module) : tailModule l.toCore = l.toCore := by
  have hf : ∀ f : Lime1.Func, tailFunc f.toCore = f.toCore := fun f => by
    simp only [tailFunc, Lime1.Func.toCore]
    rw [tailL_toCore]
  simp only [tailModule, Lime1.Module.toCore, List.map_map]
  congr 1
  exact List.map_congr_left fun f _ => hf f

/-- **The whole lowering is the identity on the Core image of a Lime1 module.** -/
theorem lower_toCore (l : Lime1.Module) : lower l.toCore = l.toCore := by
  rw [lower, Silmaril.Proofs.Wasm.LimeCompile.Direct.lowerModule_toCore, tailModule_toCore]

set_option linter.unusedTactic false in
mutual
/-- An instruction with no tail call outside `try_table` is unchanged. -/
theorem tailI_of_count (i : Instr) : tailCountI i = 0 → tailI i = [i] := by
  cases i with
  | returnCall x => intro h; rw [tailCountI] at h; cases h
  | returnCallIndirect t y => intro h; rw [tailCountI] at h; cases h
  | block bt b => intro h; rw [tailCountI] at h; rw [tailI, tailL_of_count b h]
  | loop bt b => intro h; rw [tailCountI] at h; rw [tailI, tailL_of_count b h]
  | if_ bt b₁ b₂ =>
    intro h
    rw [tailCountI] at h
    rw [tailI, tailL_of_count b₁ (by omega), tailL_of_count b₂ (by omega)]
  | _ => intro _; rw [tailI] <;> simp
termination_by sizeOf i
decreasing_by all_goals simp_wf; all_goals omega

/-- A sequence with no tail call outside `try_table` is unchanged. -/
theorem tailL_of_count : ∀ is : List Instr, tailCountL is = 0 → tailL is = is
  | [], _ => tailL_nil
  | i :: is, h => by
    rw [tailCountL] at h
    rw [tailL_cons, tailI_of_count i (by omega), tailL_of_count is (by omega),
      List.singleton_append]
termination_by is => sizeOf is
decreasing_by all_goals simp_wf; all_goals omega
end

set_option linter.unusedTactic false in
mutual
/-- The number of instructions of an instruction, nested bodies included. -/
def sizeI : Instr → Nat
  | .block _ b => 1 + size b
  | .loop _ b => 1 + size b
  | .if_ _ b₁ b₂ => 1 + size b₁ + size b₂
  | .tryTable _ _ b => 1 + size b
  | _ => 1
termination_by i => sizeOf i
decreasing_by all_goals simp_wf; all_goals omega

/-- The number of instructions of a sequence, nested bodies included. -/
def size : List Instr → Nat
  | [] => 0
  | i :: is => sizeI i + size is
termination_by is => sizeOf is
decreasing_by all_goals simp_wf; all_goals omega
end

theorem size_append : ∀ a b : List Instr, size (a ++ b) = size a + size b
  | [], b => by rw [List.nil_append, size]; omega
  | i :: a, b => by rw [List.cons_append, size, size, size_append a b]; omega

theorem size_single (i : Instr) : size [i] = sizeI i := by rw [size, size]; omega

set_option linter.unusedTactic false in
mutual
theorem size_tailI (i : Instr) : size (tailI i) = sizeI i + tailCountI i := by
  cases i with
  | returnCall x => rw [tailI, tailCountI, sizeI, size, size, size, sizeI, sizeI] <;> simp
  | returnCallIndirect t y =>
    rw [tailI, tailCountI, sizeI, size, size, size, sizeI, sizeI] <;> simp
  | block bt b => rw [tailI, tailCountI, size_single, sizeI, sizeI, size_tailL b]; omega
  | loop bt b => rw [tailI, tailCountI, size_single, sizeI, sizeI, size_tailL b]; omega
  | if_ bt b₁ b₂ =>
    rw [tailI, tailCountI, size_single, sizeI, sizeI, size_tailL b₁, size_tailL b₂]; omega
  | _ => rw [tailI, size_single, tailCountI] <;> simp
termination_by sizeOf i
decreasing_by all_goals simp_wf; all_goals omega

/-- **Size data**: the rewrite adds one instruction per replaced tail call. -/
theorem size_tailL : ∀ is : List Instr, size (tailL is) = size is + tailCountL is
  | [] => by rw [tailL_nil, tailCountL, size]
  | i :: is => by
    rw [tailL_cons, size_append, size_tailI i, size_tailL is, size, tailCountL]; omega
termination_by is => sizeOf is
decreasing_by all_goals simp_wf; all_goals omega
end

end Silmaril.Proofs.Wasm.LimeCompile.Tail
