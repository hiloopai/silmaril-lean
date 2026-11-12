module

public import Silmaril.Proofs.Wasm.SSA.Translate.BackOps

/-!
# The translation reflects SSA runs: constructs other than loops
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Translate

open Silmaril.Wasm (IntType)
open Silmaril.Wasm.SSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Tm Region)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

theorem lbl_inj' {c : Ctx} {m m' : Nat} (hm : m < c.ldepth) (hm' : m' < c.ldepth)
    (h : c.lbl m' = c.lbl m) : m = m' := (lbl_inj hm' hm h).symm

theorem bposts_cast {c : Ctx} {env : Env WVal} {k : Ctx → List Nat → Region Prim}
    {k' : Ctx → Option Nat → Region Prim} {m : Nat} {v : SVal} {o : Out (List WVal)}
    (h : BPostS c env k m v o) (hab : o.Abrupt) : BPost c env k' m v o.cast := by
  unfold BPost BPostS at *
  rw [post_abrupt (Out.cast_abrupt _ hab), TgtL_cast hab]
  rw [post_abrupt hab] at h; exact h

/-! ## Operators -/

/-- The continuation after an operator's arguments. -/
abbrev opK (o : Op) (k : Ctx → Option Nat → Region Prim) : Ctx → List Nat → Region Prim :=
  fun c ls =>
    if o.mayTrap then
      .case (.op (.opT o) (c.argTm ls)) (k c.bind (some c.depth)) (.br (c.lbl c.trap) .unit)
    else .let₁ (.op (.op o) (c.argTm ls)) (k c.bind (some c.depth))

/-- Inverting the operator step after its arguments. -/
theorem opK_inv {o : Op} {k : Ctx → Option Nat → Region Prim} {c' : Ctx} {env' : Env WVal}
    {lvls : List Nat} {vs : List WVal} {L : Nat} {v : SVal}
    (hl : List.Forall₂ (VarOK c' env') lvls vs) (h : REval env' (opK o k c' lvls) L v) :
    (∃ w, o.eval vs = some (.val w) ∧ REval (extend env' (.atom w)) (k c'.bind (some c'.depth)) L v) ∨
      (o.eval vs = some .trap ∧ L = c'.lbl c'.trap ∧ v = .unit) := by
  simp only [opK] at h
  split at h
  · rcases case_inv h with ⟨va, ht, hb⟩ | ⟨va, ht, hb⟩
    · obtain ⟨vx, hvx, hr⟩ := op_inv ht
      rw [argTm_inv hl hvx] at hr
      rcases run_opT_inv hr with ⟨w, hw, he⟩ | ⟨_, he⟩
      · cases he; exact .inl ⟨w, hw, hb⟩
      · cases he
    · obtain ⟨vx, hvx, hr⟩ := op_inv ht
      rw [argTm_inv hl hvx] at hr
      rcases run_opT_inv hr with ⟨w, _, he⟩ | ⟨hw, he⟩
      · cases he
      · obtain ⟨rfl, hu⟩ := br_inv hb
        exact .inr ⟨hw, rfl, unit_inv hu⟩
  · obtain ⟨va, ht, hb⟩ := let₁_inv h
    obtain ⟨vx, hvx, hr⟩ := op_inv ht
    rw [argTm_inv hl hvx] at hr
    obtain ⟨w, hw, rfl⟩ := run_op_inv hr
    exact .inl ⟨w, hw, hb⟩

theorem back_op {o : Op} {args : List Expr} (ha : BackArgs args) : BackE (.op o args) := by
  intro B ls c env k L v hwf hwfb hB hag hk h
  have h₁ : REval env (cArgs args c (opK o k)) L v := by simpa only [cE] using h
  have hK : KBs B c env (opK o k) := by
    intro c' env' lvls ls' vs L' v' hext hag' hl h'
    rcases opK_inv hl h' with ⟨w, _, hb⟩ | ⟨_, hL', -⟩
    · exact hk c'.bind (extend env' (.atom w)) (some c'.depth) ls' (some w) L' v'
        (hext.trans (Ext.bind _ _ _)) (hag'.bind _) (varOK_new _ _ _) hb
    · exact ⟨c.trap, hwfb.2.2, by rw [hL', hext.trap]⟩
  obtain ⟨m, oa, hm, hL, hargs, hpost⟩ := ha B ls c env (opK o k) L v hwf hwfb hB hag hK h₁
  cases oa with
  | ok ls' vs =>
      show ∃ m o', m < B ∧ L = c.lbl m ∧ Exec ls (.op o args) o' ∧ BPost c env k m v o'
      obtain ⟨c', env', lvls, hext, hag', hl, h'⟩ := hpost
      rcases opK_inv hl h' with ⟨w, hw, hb⟩ | ⟨hw, hL', hv⟩
      · exact ⟨m, _, hm, hL, .op hargs hw, c'.bind, extend env' (.atom w), some c'.depth,
          hext.trans (Ext.bind _ _ _), hag'.bind _, varOK_new _ _ _, hb⟩
      · refine ⟨m, _, hm, hL, .op_trap hargs hw, ?_⟩
        have hmt : m = c.trap := lbl_inj' (lt_of_lt_of_le (lt_of_lt_of_le hm hB) hext.ldepth)
          (lt_of_lt_of_le hwf.2.2 hext.ldepth) (by rw [← hext.trap]; exact hL'.symm)
        rw [hmt, hv]
        rfl
  | _ =>
      exact ⟨m, _, hm, hL, .op_abrupt hargs trivial,
        bposts_cast hpost trivial⟩

/-! ## Locals and simple expressions -/

theorem back_localGet {i : Nat} : BackE (.localGet i) := by
  intro B ls c env k L v hwf hwfb hB hag hk h
  rw [cE] at h
  cases hl : c.locals[i]? with
  | none => simp [hl] at h; exact (stuck_inv h).elim
  | some l =>
      simp only [hl] at h
      obtain ⟨w, hw, hv⟩ := forall₂_getElem?_left hag hl
      obtain ⟨m, hm, rfl⟩ := hk c env (some l) ls (some w) L v (Ext.refl _ _) hag hv h
      exact ⟨m, _, hm, rfl, .localGet hw, c, env, some l, Ext.refl _ _, hag, hv, h⟩

theorem back_localSet {i : Nat} {e : Expr} (he : BackE e) : BackE (.localSet i e) := by
  intro B ls c env k L v hwf hwfb hB hag hk h
  let K : Ctx → Option Nat → Region Prim := fun c r =>
    match r with
    | some l => k { c with locals := c.locals.set i l } none
    | none => stuck
  have h₁ : REval env (cE e c K) L v := h
  have hK : KB B c env K := by
    intro c' env' rl ls' r L' v' hext hag' hres h'
    match rl, r, hres with
    | some l, some w, hv =>
        exact hk { c' with locals := c'.locals.set i l } env' none (ls'.set i w) none L' v'
          (hext.setLocals _ (by simp)) (forall₂_set hag' i hv) trivial h'
    | none, _, _ => exact (stuck_inv h').elim
    | some _, none, hres => exact hres.elim
  obtain ⟨m, o, hm, hL, hex, hpost⟩ := he B ls c env _ L v hwf hwfb hB hag hK h₁
  cases o with
  | ok ls' r =>
      obtain ⟨c', env', rl, hext, hag', hres, h'⟩ := hpost
      match rl, r, hres with
      | some l, some w, hv =>
          exact ⟨m, _, hm, hL, .localSet hex, { c' with locals := c'.locals.set i l }, env', none,
            hext.setLocals _ (by simp), forall₂_set hag' i hv, trivial, h'⟩
      | none, _, _ => exact (stuck_inv h').elim
      | some _, none, hres => exact hres.elim
  | _ => exact ⟨m, _, hm, hL, .localSet_abrupt hex trivial, bpost_abrupt hpost trivial⟩

theorem back_localTee {i : Nat} {e : Expr} (he : BackE e) : BackE (.localTee i e) := by
  intro B ls c env k L v hwf hwfb hB hag hk h
  let K : Ctx → Option Nat → Region Prim := fun c r =>
    match r with
    | some l => k { c with locals := c.locals.set i l } (some l)
    | none => stuck
  have h₁ : REval env (cE e c K) L v := h
  have hK : KB B c env K := by
    intro c' env' rl ls' r L' v' hext hag' hres h'
    match rl, r, hres with
    | some l, some w, hv =>
        exact hk { c' with locals := c'.locals.set i l } env' (some l) (ls'.set i w) (some w) L' v'
          (hext.setLocals _ (by simp)) (forall₂_set hag' i hv) hv h'
    | none, _, _ => exact (stuck_inv h').elim
    | some _, none, hres => exact hres.elim
  obtain ⟨m, o, hm, hL, hex, hpost⟩ := he B ls c env _ L v hwf hwfb hB hag hK h₁
  cases o with
  | ok ls' r =>
      obtain ⟨c', env', rl, hext, hag', hres, h'⟩ := hpost
      match rl, r, hres with
      | some l, some w, hv =>
          exact ⟨m, _, hm, hL, .localTee hex, { c' with locals := c'.locals.set i l }, env', some l,
            hext.setLocals _ (by simp), forall₂_set hag' i hv, hv, h'⟩
      | none, _, _ => exact (stuck_inv h').elim
      | some _, none, hres => exact hres.elim
  | _ => exact ⟨m, _, hm, hL, .localTee_abrupt hex trivial, bpost_abrupt hpost trivial⟩

theorem back_drop {e : Expr} (he : BackE e) : BackE (.drop e) := by
  intro B ls c env k L v hwf hwfb hB hag hk h
  rw [cE] at h
  have hK : KB B c env (fun c _ => k c none) := by
    intro c' env' rl ls' r L' v' hext hag' _ h'
    exact hk _ env' none ls' none L' v' hext hag' trivial h'
  obtain ⟨m, o, hm, rfl, hex, hpost⟩ := he B ls c env _ L v hwf hwfb hB hag hK h
  cases o with
  | ok ls' r =>
      obtain ⟨c', env', rl, hext, hag', _, h'⟩ := hpost
      exact ⟨m, _, hm, rfl, .drop hex, c', env', none, hext, hag', trivial, h'⟩
  | _ => exact ⟨m, _, hm, rfl, .drop_abrupt hex trivial, bpost_abrupt hpost trivial⟩

theorem back_nop : BackE .nop := by
  intro B ls c env k L v hwf hwfb hB hag hk h
  rw [cE] at h
  obtain ⟨m, hm, rfl⟩ := hk c env none ls none L v (Ext.refl _ _) hag trivial h
  exact ⟨m, _, hm, rfl, .nop, c, env, none, Ext.refl _ _, hag, trivial, h⟩

theorem back_unreachable : BackE .unreachable := by
  intro B ls c env k L v hwf hwfb hB hag hk h
  rw [cE] at h
  obtain ⟨rfl, hu⟩ := br_inv h
  exact ⟨c.trap, _, hwfb.2.2, rfl, .unreachable, by rw [unit_inv hu]; rfl⟩

/-! ## Branches -/

theorem jump_inv {c c' : Ctx} {env env' : Env WVal} {B : Nat} (hwfb : WFB c B) {ls' : List WVal}
    {l : Nat} {lk : LabelK} {rl : Option Nat} {r : Option WVal} {L : Nat} {v : SVal}
    (hext : Ext c env c' env') (hag : Agree c' env' ls') (hres : ResOK c' env' rl r)
    (hlab : c.labels[l]? = some lk) (h : REval env' (jump c' lk rl) L v) :
    ∃ m, m < B ∧ L = c'.lbl m ∧ TgtL c (Out.brk (α := Unit) l ls' r) = some (m, v) := by
  cases lk with
  | join m' =>
      obtain ⟨rfl, hv⟩ := br_inv h
      refine ⟨m', hwfb.1 _ (List.mem_of_getElem? hlab), rfl, ?_⟩
      simp [TgtL, hlab, teval_det hv (eval_pack hag hres)]
  | ret =>
      obtain ⟨rfl, hv⟩ := br_inv h
      refine ⟨c.ret, hwfb.2.1, by simp [hext.ret], ?_⟩
      have hr' : ResOK c' env' (if c'.fty.isSome then rl else none)
          (if c.fty.isSome then r else none) := by
        rw [hext.fty]; split
        · exact hres
        · trivial
      simp [TgtL, hlab, teval_det hv (eval_resTm hr')]

theorem TgtL_brk_any {c : Ctx} {α β : Type} (l : Nat) (ls : List WVal) (r : Option WVal) :
    TgtL c (Out.brk (α := α) l ls r) = TgtL c (Out.brk (α := β) l ls r) := rfl

theorem back_br {l : Nat} {args : List Expr} (ha : BackArgs args) : BackE (.br l args) := by
  intro B ls c env k L v hwf hwfb hB hag hk h
  let K : Ctx → List Nat → Region Prim := fun c' vs =>
    match c.labels[l]? with
    | some lk => jump c' lk vs.head?
    | none => stuck
  have h₁ : REval env (cArgs args c K) L v := h
  have hK : KBs B c env K := by
    intro c' env' lvls ls' vs L' v' hext hag' hl h'
    cases hlab : c.labels[l]? with
    | none =>
        have hs : REval env' stuck L' v' := by simpa only [K, hlab] using h'
        exact (stuck_inv hs).elim
    | some lk =>
        have hj : REval env' (jump c' lk lvls.head?) L' v' := by simpa only [K, hlab] using h'
        obtain ⟨m, hm, hL, -⟩ := jump_inv hwfb hext hag' (resOK_head? hl) hlab hj
        exact ⟨m, hm, hL⟩
  obtain ⟨m, oa, hm, hL, hargs, hpost⟩ := ha B ls c env K L v hwf hwfb hB hag hK h₁
  cases oa with
  | ok ls' vs =>
      show ∃ m o, m < B ∧ L = c.lbl m ∧ Exec ls (.br l args) o ∧ BPost c env k m v o
      obtain ⟨c', env', lvls, hext, hag', hl, h'⟩ := hpost
      cases hlab : c.labels[l]? with
      | none =>
          have hs : REval env' stuck (c'.lbl m) v := by simpa only [K, hlab] using h'
          exact (stuck_inv hs).elim
      | some lk =>
          have hj : REval env' (jump c' lk lvls.head?) (c'.lbl m) v := by
            simpa only [K, hlab] using h'
          obtain ⟨m', hm', hL', ht⟩ := jump_inv hwfb hext hag' (resOK_head? hl) hlab hj
          have hmm : m = m' := lbl_inj' (lt_of_lt_of_le (lt_of_lt_of_le hm hB) hext.ldepth)
            (lt_of_lt_of_le (lt_of_lt_of_le hm' hB) hext.ldepth) hL'.symm
          exact ⟨m, _, hm, hL, .br hargs, hmm ▸ ht⟩
  | _ =>
      exact ⟨m, _, hm, hL, .br_abrupt hargs trivial,
        bposts_cast hpost trivial⟩

theorem back_return {args : List Expr} (ha : BackArgs args) : BackE (.return_ args) := by
  intro B ls c env k L v hwf hwfb hB hag hk h
  rw [cE] at h
  have hret : ∀ c' env' lvls vs L' v', Ext c env c' env' →
      List.Forall₂ (VarOK c' env') lvls vs → REval env' (jump c' .ret lvls.head?) L' v' →
      L' = c'.lbl c.ret ∧ TgtL c (Out.ret (α := Unit) vs.head?) = some (c.ret, v') := by
    intro c' env' lvls vs L' v' hext hl h'
    obtain ⟨rfl, hv⟩ := br_inv h'
    refine ⟨by simp [hext.ret], ?_⟩
    have hr' : ResOK c' env' (if c'.fty.isSome then lvls.head? else none)
        (if c.fty.isSome then vs.head? else none) := by
      rw [hext.fty]; split
      · exact resOK_head? hl
      · trivial
    simp [TgtL, teval_det hv (eval_resTm hr')]
  have hK : KBs B c env (fun c' vs => jump c' .ret vs.head?) := by
    intro c' env' lvls ls' vs L' v' hext _ hl h'
    exact ⟨c.ret, hwfb.2.1, (hret c' env' lvls vs L' v' hext hl h').1⟩
  obtain ⟨m, oa, hm, rfl, hargs, hpost⟩ := ha B ls c env _ L v hwf hwfb hB hag hK h
  cases oa with
  | ok ls' vs =>
      obtain ⟨c', env', lvls, hext, _, hl, h'⟩ := hpost
      obtain ⟨hL, ht⟩ := hret c' env' lvls vs _ _ hext hl h'
      have : m = c.ret := lbl_inj' (lt_of_lt_of_le (lt_of_lt_of_le hm hB) hext.ldepth)
        (lt_of_lt_of_le hwf.2.1 hext.ldepth) hL.symm
      subst this
      exact ⟨_, _, hm, rfl, .return_ hargs, ht⟩
  | _ =>
      exact ⟨m, _, hm, rfl, .return_abrupt hargs trivial,
        bposts_cast hpost trivial⟩

end Silmaril.Proofs.Wasm.SSA.Translate
