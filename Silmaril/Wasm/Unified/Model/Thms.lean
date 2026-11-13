module

public import Silmaril.Wasm.Unified.Model.Defs
public import Mathlib.Data.Set.Insert

/-!
# Opcode interpretations: locality

What a model's meaning of code depends on: only the opcodes occurring in it.

* `Alg.evalCode_update`: changing the meaning of an opcode that does not occur in the code does
  not change the code's meaning; `Model.obs_update` for observations.
* `Model.reduct_update`: changing the meaning of an opcode outside the image of a signature
  morphism does not change the reduct. So models differing on one opcode (spec errata) have
  equal reducts to every signature that forgets the opcode.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified

open CategoryTheory

namespace Alg

variable {O : Type} [DecidableEq O] (A : Alg O) (o : O)
  (v : List Imm → List A.D → List Handler → A.I)

mutual
theorem evalInstr_update : (i : UInstr O) → o ∉ i.ops →
    (A.update o v).evalInstr i = A.evalInstr i
  | .op o' imms bs hs, h => by
    rw [UInstr.ops, Set.mem_insert_iff, not_or] at h
    rw [evalInstr, evalInstr, evalBlocks_update bs h.2]
    exact congrFun (congrFun (congrFun (Function.update_of_ne (Ne.symm h.1) v A.op) imms) _) hs
theorem evalCode_update : (c : UCode O) → o ∉ UInstr.opsCode c →
    (A.update o v).evalCode c = A.evalCode c
  | [], _ => rfl
  | i :: c, h => by
    rw [UInstr.opsCode, Set.mem_union, not_or] at h
    rw [evalCode, evalCode, evalInstr_update i h.1, evalCode_update c h.2]
    rfl
theorem evalBlocks_update : (bs : List (UCode O)) → o ∉ UInstr.opsBlocks bs →
    (A.update o v).evalBlocks bs = A.evalBlocks bs
  | [], _ => rfl
  | b :: bs, h => by
    rw [UInstr.opsBlocks, Set.mem_union, not_or] at h
    rw [evalBlocks, evalBlocks, evalCode_update b h.1, evalBlocks_update bs h.2]
    rfl
end

end Alg

namespace Model

variable {In B : Type} {S S' : FSig}

/-- Observations of code avoiding the updated opcode are unchanged. -/
theorem obs_update (M : Model In B S) (o : S.Op)
    (v : List Imm → List M.alg.D → List Handler → M.alg.I) (c : S.Code) (i : In)
    (h : o ∉ UInstr.opsCode c) : (M.update o v).obs (c, i) = M.obs (c, i) := by
  show {b | M.ok ((M.alg.update o v).evalCode c) ∧ b ∈ M.run ((M.alg.update o v).evalCode c) i} = _
  rw [Alg.evalCode_update M.alg o v c h]
  rfl

/-- **Updating an opcode outside the image of `σ` does not change the reduct.** -/
theorem reduct_update (σ : S ⟶ S') (M : Model In B S') (o : S'.Op)
    (v : List Imm → List M.alg.D → List Handler → M.alg.I) (h : ∀ x, σ.f x ≠ o) :
    (M.update o v).reduct σ = M.reduct σ := by
  have hop : (fun x => Function.update M.alg.op o v (σ.f x)) = fun x => M.alg.op (σ.f x) :=
    funext fun x => Function.update_of_ne (h x) v M.alg.op
  unfold Model.reduct Model.update Alg.comap Alg.update
  dsimp only
  rw [hop]

end Model

end Silmaril.Wasm.Unified
