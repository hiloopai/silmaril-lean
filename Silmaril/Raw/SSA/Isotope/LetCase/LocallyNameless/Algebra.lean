module

public import Silmaril.Raw.SSA.Isotope.LetCase.LocallyNameless.Syntax

@[expose] public section
set_option autoImplicit true

/-! Algebra of locally nameless renaming and substitution. -/

namespace Silmaril.Isotope.LetCase.LocallyNameless

open Silmaril.Isotope.LetCase.LocallyNameless
open Silmaril.Isotope.LetCase.LocallyNameless.Tm

namespace Tm

@[simp] theorem up_zero (ρ : Fin n → Fin m) : up ρ 0 = 0 := rfl
@[simp] theorem up_succ (ρ : Fin n → Fin m) (i : Fin n) :
    up ρ i.succ = (ρ i).succ := rfl
@[simp] theorem upSub_zero (σ : Fin n → Tm ν Φ m) : upSub σ 0 = .bv 0 := rfl
@[simp] theorem upSub_succ (σ : Fin n → Tm ν Φ m) (i : Fin n) :
    upSub σ i.succ = (σ i).lift := rfl

@[simp] theorem rename_fv (ρ : Fin n → Fin m) :
    rename ρ (.fv x : Tm ν Φ n) = .fv x := rfl
@[simp] theorem rename_bv (ρ : Fin n → Fin m) (i : Fin n) :
    rename ρ (.bv i : Tm ν Φ n) = .bv (ρ i) := rfl
@[simp] theorem rename_op (ρ : Fin n → Fin m) :
    rename ρ (.op f a) = .op f (rename ρ a) := rfl
@[simp] theorem rename_let₁ (ρ : Fin n → Fin m) :
    rename ρ (.let₁ a b) = .let₁ (rename ρ a) (rename (up ρ) b) := rfl
@[simp] theorem rename_unit (ρ : Fin n → Fin m) :
    rename ρ (.unit : Tm ν Φ n) = .unit := rfl
@[simp] theorem rename_pair (ρ : Fin n → Fin m) :
    rename ρ (.pair a b) = .pair (rename ρ a) (rename ρ b) := rfl
@[simp] theorem rename_let₂ (ρ : Fin n → Fin m) :
    rename ρ (.let₂ a b) = .let₂ (rename ρ a) (rename (up (up ρ)) b) := rfl
@[simp] theorem rename_inl (ρ : Fin n → Fin m) :
    rename ρ (.inl a) = .inl (rename ρ a) := rfl
@[simp] theorem rename_inr (ρ : Fin n → Fin m) :
    rename ρ (.inr a) = .inr (rename ρ a) := rfl
@[simp] theorem rename_case (ρ : Fin n → Fin m) :
    rename ρ (.case e l r) =
      .case (rename ρ e) (rename (up ρ) l) (rename (up ρ) r) := rfl
@[simp] theorem rename_abort (ρ : Fin n → Fin m) :
    rename ρ (.abort a) = .abort (rename ρ a) := rfl
@[simp] theorem bsubst_fv (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.fv x : Tm ν Φ n) = .fv x := rfl
@[simp] theorem bsubst_bv (σ : Fin n → Tm ν Φ m) (i : Fin n) :
    bsubst σ (.bv i : Tm ν Φ n) = σ i := rfl
@[simp] theorem bsubst_op (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.op f a) = .op f (bsubst σ a) := rfl
@[simp] theorem bsubst_let₁ (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.let₁ a b) = .let₁ (bsubst σ a) (bsubst (upSub σ) b) := rfl
@[simp] theorem bsubst_unit (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.unit : Tm ν Φ n) = .unit := rfl
@[simp] theorem bsubst_pair (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.pair a b) = .pair (bsubst σ a) (bsubst σ b) := rfl
@[simp] theorem bsubst_let₂ (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.let₂ a b) = .let₂ (bsubst σ a) (bsubst (upSub (upSub σ)) b) := rfl
@[simp] theorem bsubst_inl (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.inl a) = .inl (bsubst σ a) := rfl
@[simp] theorem bsubst_inr (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.inr a) = .inr (bsubst σ a) := rfl
@[simp] theorem bsubst_case (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.case e l r) =
      .case (bsubst σ e) (bsubst (upSub σ) l) (bsubst (upSub σ) r) := rfl
@[simp] theorem bsubst_abort (σ : Fin n → Tm ν Φ m) :
    bsubst σ (.abort a) = .abort (bsubst σ a) := rfl
theorem rename_congr {ρ ρ' : Fin n → Fin m} (h : ∀ i, ρ i = ρ' i) (t : Tm ν Φ n) :
    rename ρ t = rename ρ' t := by
  apply congrArg (fun f => rename f t)
  funext i
  exact h i

theorem bsubst_congr {σ σ' : Fin n → Tm ν Φ m} (h : ∀ i, σ i = σ' i)
    (t : Tm ν Φ n) : bsubst σ t = bsubst σ' t := by
  apply congrArg (fun f => bsubst f t)
  funext i
  exact h i

@[simp] theorem up_id : up (fun i : Fin n => i) = fun i => i := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem up_comp (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k) :
    up (fun i => ρ' (ρ i)) = fun i => up ρ' (up ρ i) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem rename_id (t : Tm ν Φ n) : rename (fun i => i) t = t := by
  induction t with
  | fv | bv | unit => rfl
  | op _ _ ih | inl _ ih | inr _ ih | abort _ ih => simp [ih]
  | let₁ _ _ iha ihb =>
      simp only [rename_let₁, iha]
      rw [up_id, ihb]
  | pair _ _ iha ihb => simp [iha, ihb]
  | let₂ _ _ iha ihb =>
      simp only [rename_let₂, iha]
      rw [up_id, up_id, ihb]
  | case _ _ _ ihe ihl ihr =>
      simp only [rename_case, ihe]
      rw [up_id, ihl, ihr]

theorem rename_comp (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k) (t : Tm ν Φ n) :
    rename ρ' (rename ρ t) = rename (fun i => ρ' (ρ i)) t := by
  induction t generalizing m k with
  | fv | bv | unit => rfl
  | op _ _ ih | inl _ ih | inr _ ih | abort _ ih => simp [ih]
  | let₁ _ _ iha ihb =>
      simp [iha, ihb, ← up_comp]
  | pair _ _ iha ihb => simp [iha, ihb]
  | let₂ _ _ iha ihb => simp [iha, ihb, ← up_comp]
  | case _ _ _ ihe ihl ihr => simp [ihe, ihl, ihr, ← up_comp]

@[simp] theorem rename_lift (ρ : Fin n → Fin m) (t : Tm ν Φ n) :
    rename (up ρ) t.lift = (rename ρ t).lift := by
  rw [lift, rename_comp, lift, rename_comp]
  apply rename_congr
  intro i
  rfl

@[simp] theorem rename_underBinder (ρ : Fin n → Fin m) (t : Tm ν Φ (n + 1)) :
    rename (up (up ρ)) t.underBinder = (rename (up ρ) t).underBinder := by
  rw [underBinder, rename_comp, underBinder, rename_comp]
  apply rename_congr
  intro i
  exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem rename_underTwoBinders (ρ : Fin n → Fin m) (t : Tm ν Φ (n + 2)) :
    rename (up (up (up ρ))) t.underTwoBinders =
      (rename (up (up ρ)) t).underTwoBinders := by
  rw [underTwoBinders, rename_comp, underTwoBinders, rename_comp]
  apply rename_congr
  intro i
  exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) i

private theorem rename_upSub (ρ : Fin m → Fin k) (σ : Fin n → Tm ν Φ m) :
    (fun i => rename (up ρ) (upSub σ i)) = upSub (fun i => rename ρ (σ i)) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact rename_lift ρ (σ j)

/-- Renaming after simultaneous substitution acts pointwise on the images. -/
theorem rename_bsubst (ρ : Fin m → Fin k) (σ : Fin n → Tm ν Φ m)
    (t : Tm ν Φ n) :
    rename ρ (bsubst σ t) = bsubst (fun i => rename ρ (σ i)) t := by
  induction t generalizing m k with
  | fv | bv | unit => rfl
  | op _ _ ih | inl _ ih | inr _ ih | abort _ ih => simp [ih]
  | let₁ _ _ iha ihb =>
      simp only [bsubst_let₁, rename_let₁, iha]
      rw [ihb]
      congr 1
      exact bsubst_congr (congrFun (rename_upSub ρ σ)) _
  | pair _ _ iha ihb => simp [iha, ihb]
  | let₂ _ _ iha ihb =>
      simp only [bsubst_let₂, rename_let₂, iha]
      rw [ihb]
      congr 1
      apply bsubst_congr
      exact congrFun ((rename_upSub (up ρ) (upSub σ)).trans
        (congrArg (fun f => upSub f) (rename_upSub ρ σ)))
  | case _ _ _ ihe ihl ihr =>
      simp only [bsubst_case, rename_case, ihe]
      rw [ihl, ihr]
      congr 1 <;> apply bsubst_congr <;> exact congrFun (rename_upSub ρ σ)

private theorem upSub_comp_ren (σ : Fin m → Tm ν Φ k) (ρ : Fin n → Fin m) :
    (fun i => upSub σ (up ρ i)) = upSub (fun i => σ (ρ i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- Simultaneous substitution after renaming composes the index map into the
substitution. -/
theorem bsubst_rename (σ : Fin m → Tm ν Φ k) (ρ : Fin n → Fin m)
    (t : Tm ν Φ n) :
    bsubst σ (rename ρ t) = bsubst (fun i => σ (ρ i)) t := by
  induction t generalizing m k with
  | fv | bv | unit => rfl
  | op _ _ ih | inl _ ih | inr _ ih | abort _ ih => simp [ih]
  | let₁ _ _ iha ihb =>
      simp only [rename_let₁, bsubst_let₁, iha]
      rw [ihb]
      congr 1
      exact bsubst_congr (congrFun (upSub_comp_ren σ ρ)) _
  | pair _ _ iha ihb => simp [iha, ihb]
  | let₂ _ _ iha ihb =>
      simp only [rename_let₂, bsubst_let₂, iha]
      rw [ihb]
      congr 1
      apply bsubst_congr
      exact congrFun ((upSub_comp_ren (upSub σ) (up ρ)).trans
        (congrArg (fun f => upSub f) (upSub_comp_ren σ ρ)))
  | case _ _ _ ihe ihl ihr =>
      simp only [rename_case, bsubst_case, ihe]
      rw [ihl, ihr]
      congr 1 <;> apply bsubst_congr <;> exact congrFun (upSub_comp_ren σ ρ)

@[simp] theorem bsubst_lift (σ : Fin n → Tm ν Φ m) (t : Tm ν Φ n) :
    bsubst (upSub σ) t.lift = (bsubst σ t).lift := by
  rw [lift, bsubst_rename, lift, rename_bsubst]
  apply bsubst_congr
  intro i
  rfl

private theorem upSub_comp (σ : Fin n → Tm ν Φ m) (θ : Fin m → Tm ν Φ k) :
    (fun i => bsubst (upSub θ) (upSub σ i)) =
      upSub (fun i => bsubst θ (σ i)) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact bsubst_lift θ (σ j)

/-- Simultaneous substitutions compose pointwise. -/
theorem bsubst_comp (θ : Fin m → Tm ν Φ k) (σ : Fin n → Tm ν Φ m)
    (t : Tm ν Φ n) :
    bsubst θ (bsubst σ t) = bsubst (fun i => bsubst θ (σ i)) t := by
  induction t generalizing m k with
  | fv | bv | unit => rfl
  | op _ _ ih | inl _ ih | inr _ ih | abort _ ih => simp [ih]
  | let₁ _ _ iha ihb =>
      simp only [bsubst_let₁, iha]
      rw [ihb]
      congr 1
      exact bsubst_congr (congrFun (upSub_comp σ θ)) _
  | pair _ _ iha ihb => simp [iha, ihb]
  | let₂ _ _ iha ihb =>
      simp only [bsubst_let₂, iha]
      rw [ihb]
      congr 1
      apply bsubst_congr
      exact congrFun ((upSub_comp (upSub σ) (upSub θ)).trans
        (congrArg upSub (upSub_comp σ θ)))
  | case _ _ _ ihe ihl ihr =>
      simp only [bsubst_case, ihe]
      rw [ihl, ihr]
      congr 1 <;> apply bsubst_congr <;> exact congrFun (upSub_comp σ θ)

private theorem upSub_bv (ρ : Fin n → Fin m) :
    upSub (fun i => .bv (ρ i) : Fin n → Tm ν Φ m) =
      fun i => .bv (up ρ i) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- A variable-only substitution is exactly a renaming. -/
theorem bsubst_bv_eq_rename (ρ : Fin n → Fin m) (t : Tm ν Φ n) :
    bsubst (fun i => .bv (ρ i)) t = rename ρ t := by
  induction t generalizing m with
  | fv | bv | unit => rfl
  | op _ _ ih | inl _ ih | inr _ ih | abort _ ih => simp [ih]
  | let₁ _ _ iha ihb => simp only [bsubst_let₁, rename_let₁, iha, upSub_bv, ihb]
  | pair _ _ iha ihb => simp [iha, ihb]
  | let₂ _ _ iha ihb =>
      simp only [bsubst_let₂, rename_let₂, iha, upSub_bv, ihb]
  | case _ _ _ ihe ihl ihr =>
      simp only [bsubst_case, rename_case, ihe, upSub_bv, ihl, ihr]

@[simp] theorem bsubst_underBinder (σ : Fin n → Tm ν Φ m)
    (t : Tm ν Φ (n + 1)) :
    bsubst (upSub (upSub σ)) t.underBinder =
      (bsubst (upSub σ) t).underBinder := by
  rw [underBinder, bsubst_rename, underBinder, rename_bsubst]
  apply bsubst_congr
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [upSub_succ]
  change (σ j).lift.lift = rename (up Fin.succ) (σ j).lift
  exact (rename_lift Fin.succ (σ j)).symm

@[simp] theorem bsubst_underTwoBinders (σ : Fin n → Tm ν Φ m)
    (t : Tm ν Φ (n + 2)) :
    bsubst (upSub (upSub (upSub σ))) t.underTwoBinders =
      (bsubst (upSub (upSub σ)) t).underTwoBinders := by
  rw [underTwoBinders, bsubst_rename, underTwoBinders, rename_bsubst]
  apply bsubst_congr
  intro i
  refine Fin.cases rfl (Fin.cases rfl (fun j => ?_)) i
  simp only [upSub_succ]
  have h := ((rename_lift (up Fin.succ) (Tm.lift (σ j))).trans
    (congrArg Tm.lift (rename_lift Fin.succ (σ j)))).symm
  convert h using 1 <;> apply rename_congr <;> intro x <;>
    exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) x

@[simp] theorem bsubst_id (t : Tm ν Φ n) : bsubst Tm.bv t = t := by
  rw [bsubst_bv_eq_rename (fun i => i), rename_id]

private theorem bsubst_drop_lift (a t : Tm ν Φ n) :
    bsubst (Fin.cases a (fun i => .bv i)) t.lift = t := by
  rw [lift, bsubst_rename]
  calc
    bsubst (fun i => Fin.cases a (fun i => .bv i) i.succ) t =
        bsubst (fun i => .bv i) t := by
          apply bsubst_congr
          intro i
          rfl
    _ = rename (fun i => i) t := bsubst_bv_eq_rename _ _
    _ = t := rename_id _

@[simp] theorem bsubst_instantiate (σ : Fin n → Tm ν Φ m)
    (b : Tm ν Φ (n + 1)) (a : Tm ν Φ n) :
    bsubst σ (instantiate b a) =
      instantiate (bsubst (upSub σ) b) (bsubst σ a) := by
  rw [instantiate, bsubst_comp, instantiate, bsubst_comp]
  apply bsubst_congr
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [upSub_succ]
  change σ j = bsubst _ (σ j).lift
  exact (bsubst_drop_lift _ _).symm

@[simp] theorem rename_instantiate (ρ : Fin n → Fin m) (b : Tm ν Φ (n + 1))
    (a : Tm ν Φ n) :
    rename ρ (instantiate b a) = instantiate (rename (up ρ) b) (rename ρ a) := by
  rw [instantiate, rename_bsubst, instantiate]
  rw [bsubst_rename]
  apply bsubst_congr
  intro i
  refine Fin.cases rfl (fun _ => rfl) i

end Tm
end Silmaril.Isotope.LetCase.LocallyNameless
