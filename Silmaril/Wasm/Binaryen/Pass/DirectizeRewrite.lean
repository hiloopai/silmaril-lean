module

public import Silmaril.Wasm.Binaryen.DirectizeRel
public import Silmaril.Wasm.Binaryen.Pass.Directize

@[expose] public section

/-! # Directize: the rewrite is a relation of the simulation

The lowering of a body rewritten by Directize (`Directize.exprs m tys`) is related to the
lowering of the original body by `DirSim.GIL (siteOk m tys) mi mi` for every instance
`mi` (`exprs_rel`): each rewritten call is a site whose static check is `target?`.
-/

namespace Silmaril.Wasm.Binaryen

namespace Directize

open Exe DirSim Execution.Core

/-- The static check of a site: `target?` finds the callee. -/
def siteOk (m : BModule) (tys : List TypeIdx) : SiteOk :=
  fun t k y fx => target? m tys t y k.toNat = some fx

variable {m : BModule} {tys : List TypeIdx}

theorem exprs_eq_map : ∀ l : List BExpr, exprs m tys l = l.map (expr m tys)
  | [] => rfl
  | e :: l => by simp only [exprs, List.map_cons, exprs_eq_map l]

theorem expr_eq_const {e : BExpr} {k : BitVec 32} (h : expr m tys e = .op (.intConst .i32 k) []) :
    e = .op (.intConst .i32 k) [] := by
  cases e with
  | op i args =>
    simp only [expr] at h
    split at h
    · rename_i j args' hd
      cases h
      unfold direct at hd
      split at hd
      · split at hd <;> simp at hd
      · cases hd
    · injection h with h1 h2
      subst h1
      rw [exprs_eq_map, List.map_eq_nil_iff] at h2
      subst h2
      rfl
  | block => simp [expr] at h
  | loop => simp [expr] at h
  | if_ => simp [expr] at h
  | tryTable => simp [expr] at h

theorem direct_some {i : Instr} {args : List BExpr} {j : Instr} {args' : List BExpr}
    (h : direct m tys i args = some (j, args')) :
    ∃ k r t y fx, args = args' ++ [.op (.intConst .i32 k) []] ∧ i = ciI r t y ∧
      j = clI r fx ∧ siteOk m tys t k y fx := by
  unfold direct at h
  split at h
  · rename_i k hl
    have ha : args = args.dropLast ++ [.op (.intConst .i32 k) []] :=
      (List.dropLast_append_getLast? _ hl).symm
    split at h
    · rename_i t ty
      obtain ⟨fx, hfx, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      exact ⟨k, false, t, ty, fx, ha, rfl, rfl, hfx⟩
    · rename_i t ty
      obtain ⟨fx, hfx, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      exact ⟨k, true, t, ty, fx, ha, rfl, rfl, hfx⟩
    · cases h
  · cases h

theorem lowerList_rel {mi : ModuleInst} :
    ∀ l : List BExpr, (∀ e ∈ l, GIL (siteOk m tys) mi mi e.lower (expr m tys e).lower) →
      GIL (siteOk m tys) mi mi (BExpr.lowerList l) (BExpr.lowerList (exprs m tys l))
  | [], _ => .nil
  | e :: l, h => by
    simp only [exprs, BExpr.lowerList_cons]
    exact GIL.append (h e (by simp)) (lowerList_rel l fun e' he' => h e' (by simp [he']))

/-- **The lowering of a rewritten tree is related to the original lowering.** -/
theorem expr_rel (mi : ModuleInst) :
    ∀ e : BExpr, GIL (siteOk m tys) mi mi e.lower (expr m tys e).lower
  | .op i args => by
    have ih : ∀ e ∈ args, GIL (siteOk m tys) mi mi e.lower (expr m tys e).lower :=
      fun e _ => expr_rel mi e
    simp only [expr]
    split
    · rename_i j args' hd
      obtain ⟨k, r, t, y, fx, hA, rfl, rfl, hok⟩ := direct_some hd
      rw [exprs_eq_map] at hA
      obtain ⟨args₁, L₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.mp hA
      obtain ⟨e, rfl, he⟩ := List.map_eq_singleton_iff.mp h₂
      have he' : e = .op (.intConst .i32 k) [] := expr_eq_const he
      subst he'
      have hrel := lowerList_rel args₁ fun e' he' => ih e' (by simp [he'])
      rw [exprs_eq_map, h₁] at hrel
      simp only [BExpr.lower_op, BExpr.lowerList_append, BExpr.lowerList_singleton,
        BExpr.lowerList_nil, List.nil_append, List.append_assoc, List.singleton_append]
      exact GIL.append hrel (.site rfl hok .nil)
    · simp only [BExpr.lower_op]
      exact GIL.append (lowerList_rel args ih) (.cons (.flat i) .nil)
  | .block bt b => by
    simp only [expr, BExpr.lower]
    exact .cons (.block (lowerList_rel b fun e _ => expr_rel mi e)) .nil
  | .loop bt b => by
    simp only [expr, BExpr.lower]
    exact .cons (.loop (lowerList_rel b fun e _ => expr_rel mi e)) .nil
  | .if_ bt c t e => by
    simp only [expr, BExpr.lower]
    exact GIL.append (lowerList_rel c fun x _ => expr_rel mi x)
      (.cons (.if_ (lowerList_rel t fun x _ => expr_rel mi x)
        (lowerList_rel e fun x _ => expr_rel mi x)) .nil)
  | .tryTable bt cs b => by
    simp only [expr, BExpr.lower]
    exact .cons (.tryTable (lowerList_rel b fun e _ => expr_rel mi e)) .nil
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)

/-- The lowering of a rewritten body is related to the original lowering. -/
theorem exprs_rel (mi : ModuleInst) (l : List BExpr) :
    GIL (siteOk m tys) mi mi (BExpr.lowerList l) (BExpr.lowerList (exprs m tys l)) :=
  lowerList_rel l fun e _ => expr_rel mi e

end Directize

end Silmaril.Wasm.Binaryen
