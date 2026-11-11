module

public import Silmaril.Wasm.FnInst.Models.FragK.Defs
public import Silmaril.Wasm.FnInst.Models.Frag.Thms

/-!
# Validity with a choice of semantics

* `addZeroRule_valid_k`: the rule `0 + x ≐ x` is valid in the institution of bodies plus a choice
  of semantics (`kInst sems`), so in both semantics (`valid_k_iff`);
* `dropDouble`: `(x + x; drop); 0 ≐ 0` is valid with Wasm's wrapping addition
  (`dropDouble_valid_wrap`) and not with checked addition (`dropDouble_not_valid_checked`), so
  it is not valid in `kInst sems` (`dropDouble_not_valid_k`): dropping dead arithmetic is a
  rewrite of one semantics, not of the family.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.Models.FragK

open Silmaril.Inst Silmaril.Wasm.FnInst.Models Silmaril.Wasm.FnInst.Models.Frag

theorem addT_zero_left (y : Val) : addT 0 y = ret y := by
  have hlt : (0 : Val).toNat + y.toNat < 2 ^ 32 := by simpa using y.isLt
  have h0 : (0 : Val) + y = y := by simp
  simp only [addT, hlt, ite_true, h0]

theorem addZeroRule_valid_k : (kInst sems).Valid (S := sig 1 0) addZeroRule := by
  refine (valid_k_iff sems (T := sig 1 0) addZeroRule).2 fun k =>
    (valid_body_iff (sems k) (T := sig 1 0) addZeroRule).2 fun env => ?_
  cases k with
  | true => exact add_zero_left _ env
  | false =>
    funext args
    show bind (ret 0) (fun x => bind (ret (args.getD 0 0)) fun y => addT x y) =
      ret (args.getD 0 0)
    rw [bind_ret_left, bind_ret_left, addT_zero_left]

/-- `(x + x; drop); 0 ≐ 0` at the minimal signature. -/
def dropDouble : Sen syn (sig 1 0).n :=
  .eq (Expr.seq (.add (.param 0) (.param 0)) (.const 0)) (.const 0)

theorem dropDouble_valid_wrap : (bodyInst sem).Valid (S := sig 1 0) dropDouble := by
  refine (valid_body_iff sem (T := sig 1 0) dropDouble).2 fun env => ?_
  funext args
  show bind (bind (ret (args.getD 0 0)) fun x => bind (ret (args.getD 0 0)) fun y => ret (x + y))
    (fun _ => ret 0) = ret 0
  rw [bind_ret_left, bind_ret_left, bind_ret_left]

/-- The left-hand side of `dropDouble`. -/
def dropDoubleLhs : Frag.Expr 1 := .seq (.add (.param 0) (.param 0)) (.const 0)

/-- The callee that always traps (unused by `dropDouble`). -/
def trapEnv : Fin 1 → Den := fun _ _ s => {(none, s)}

theorem dropDoubleLhs_traps :
    ((none, 0) : Res) ∈ evalT trapEnv [2 ^ 31] dropDoubleLhs 0 := by
  have hov : ¬ ((2 ^ 31 : Val).toNat + (2 ^ 31 : Val).toNat < 2 ^ 32) := by decide
  show ((none, 0) : Res) ∈ bind (bind (ret (2 ^ 31)) fun x => bind (ret (2 ^ 31)) fun y =>
    addT x y) (fun _ => ret 0) 0
  rw [bind_ret_left, bind_ret_left]
  simp only [addT, hov, ite_false]
  exact ⟨(none, 0), rfl, rfl⟩

theorem dropDouble_not_valid_checked : ¬ (bodyInst semT).Valid (S := sig 1 0) dropDouble := by
  intro hv
  have h := (valid_body_iff semT (T := sig 1 0) dropDouble).1 hv
  have heq : evalT trapEnv [2 ^ 31] dropDoubleLhs 0 = ret 0 0 :=
    congrFun (congrFun (h trapEnv) [2 ^ 31]) 0
  have hret : ((none, 0) : Res) ∈ ret (0 : Val) 0 := heq ▸ dropDoubleLhs_traps
  exact absurd hret (by simp [ret])

theorem dropDouble_not_valid_k : ¬ (kInst sems).Valid (S := sig 1 0) dropDouble := by
  intro hv
  exact dropDouble_not_valid_checked ((valid_k_iff sems (T := sig 1 0) dropDouble).1 hv false)

end Silmaril.Wasm.FnInst.Models.FragK
