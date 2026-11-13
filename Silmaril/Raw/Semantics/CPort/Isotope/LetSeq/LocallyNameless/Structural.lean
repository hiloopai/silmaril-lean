module

public import Silmaril.Semantics.CPort.Isotope.LetSeq.LocallyNameless.Syntax.Defs
/-! Laws for renaming, capture-avoiding substitution, and opening binders. -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LetSeq.LocallyNameless.Tm

variable {ν : Type u} {Φ : Type v} {n m k : Nat}

@[simp] theorem up_zero (ρ : Fin n → Fin m) : up ρ 0 = 0 := rfl
@[simp] theorem up_succ (ρ : Fin n → Fin m) (i : Fin n) :
    up ρ i.succ = (ρ i).succ := rfl
@[simp] theorem upSub_zero (σ : Fin n → Tm ν Φ m) : upSub σ 0 = .bv 0 := rfl
@[simp] theorem upSub_succ (σ : Fin n → Tm ν Φ m) (i : Fin n) :
    upSub σ i.succ = (σ i).lift := rfl

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
  | op _ _ ih => simp [rename, ih]
  | let₁ _ _ iha ihb =>
      simp only [rename, iha]
      rw [up_id, ihb]
  | pair _ _ iha ihb => simp [rename, iha, ihb]
  | let₂ _ _ iha ihb =>
      simp only [rename, iha]
      rw [up_id, up_id, ihb]
theorem rename_comp (ρ : Fin n → Fin m) (ρ' : Fin m → Fin k) (t : Tm ν Φ n) :
    rename ρ' (rename ρ t) = rename (fun i => ρ' (ρ i)) t := by
  induction t generalizing m k with
  | fv | bv | unit => rfl
  | op _ _ ih => simp [rename, ih]
  | let₁ _ _ iha ihb =>
      simp [rename, iha, ihb, ← up_comp]
  | pair _ _ iha ihb => simp [rename, iha, ihb]
  | let₂ _ _ iha ihb => simp [rename, iha, ihb, ← up_comp]
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
  | op _ _ ih => simp [rename, bsubst, ih]
  | let₁ _ _ iha ihb =>
      simp only [bsubst, rename, iha]
      rw [ihb]
      congr 1
      exact bsubst_congr (congrFun (rename_upSub ρ σ)) _
  | pair _ _ iha ihb => simp [rename, bsubst, iha, ihb]
  | let₂ _ _ iha ihb =>
      simp only [bsubst, rename, iha]
      rw [ihb]
      congr 1
      apply bsubst_congr
      exact congrFun ((rename_upSub (up ρ) (upSub σ)).trans
        (congrArg (fun f => upSub f) (rename_upSub ρ σ)))
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
  | op _ _ ih => simp [rename, bsubst, ih]
  | let₁ _ _ iha ihb =>
      simp only [rename, bsubst, iha]
      rw [ihb]
      congr 1
      exact bsubst_congr (congrFun (upSub_comp_ren σ ρ)) _
  | pair _ _ iha ihb => simp [rename, bsubst, iha, ihb]
  | let₂ _ _ iha ihb =>
      simp only [rename, bsubst, iha]
      rw [ihb]
      congr 1
      apply bsubst_congr
      exact congrFun ((upSub_comp_ren (upSub σ) (up ρ)).trans
        (congrArg (fun f => upSub f) (upSub_comp_ren σ ρ)))
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
  | op _ _ ih => simp [bsubst, ih]
  | let₁ _ _ iha ihb =>
      simp only [bsubst, iha]
      rw [ihb]
      congr 1
      exact bsubst_congr (congrFun (upSub_comp σ θ)) _
  | pair _ _ iha ihb => simp [bsubst, iha, ihb]
  | let₂ _ _ iha ihb =>
      simp only [bsubst, iha]
      rw [ihb]
      congr 1
      apply bsubst_congr
      exact congrFun ((upSub_comp (upSub σ) (upSub θ)).trans
        (congrArg upSub (upSub_comp σ θ)))
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
  | op _ _ ih => simp [rename, bsubst, ih]
  | let₁ _ _ iha ihb => simp only [bsubst, rename, iha, upSub_bv, ihb]
  | pair _ _ iha ihb => simp [rename, bsubst, iha, ihb]
  | let₂ _ _ iha ihb =>
      simp only [bsubst, rename, iha, upSub_bv, ihb]
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


@[simp] theorem bsubst_id (t : Tm ν Φ n) : bsubst Tm.bv t = t := by
  rw [bsubst_bv_eq_rename (fun i => i), rename_id]

end Silmaril.Isotope.LetSeq.LocallyNameless.Tm
