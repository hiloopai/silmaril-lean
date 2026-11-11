module

public import Silmaril.Proofs.Wasm.SSA.Translate.Sim
public import Silmaril.SSA.Isotope.LambdaSSA.Thms

/-!
# The translation reflects SSA runs: basic inversions

For the backward direction, a continuation must leave only through labels
that existed in its context (`KB`), whenever it is entered in a state that
agrees with some fragment locals. Then a translated region's evaluation
decomposes into a fragment outcome and, for normal outcomes, an evaluation of
the continuation. This file inverts the generated terms (`pack`, `argTm`,
`unpack`, join blocks).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Translate

open Silmaril.Wasm (IntType)
open Silmaril.Wasm.SSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Tm Region)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

/-- The continuation leaves only through label levels below `B`. -/
def KB (B : Nat) (c : Ctx) (env : Env WVal) (k : Ctx → Option Nat → Region Prim) : Prop :=
  ∀ c' env' rl ls' r L v, Ext c env c' env' → Agree c' env' ls' → ResOK c' env' rl r →
    REval env' (k c' rl) L v → ∃ m, m < B ∧ L = c'.lbl m

/-- The same for operand continuations. -/
def KBs (B : Nat) (c : Ctx) (env : Env WVal) (k : Ctx → List Nat → Region Prim) : Prop :=
  ∀ c' env' lvls ls' vs L v, Ext c env c' env' → Agree c' env' ls' →
    List.Forall₂ (VarOK c' env') lvls vs → REval env' (k c' lvls) L v → ∃ m, m < B ∧ L = c'.lbl m

/-- The registered label levels of `c` are below `B`. -/
def WFB (c : Ctx) (B : Nat) : Prop :=
  (∀ m, LabelK.join m ∈ c.labels → m < B) ∧ c.ret < B ∧ c.trap < B

theorem KB.ext {B : Nat} {c c₁ : Ctx} {env env₁ : Env WVal} (h : Ext c env c₁ env₁)
    {k : Ctx → Option Nat → Region Prim} (hk : KB B c env k) : KB B c₁ env₁ k :=
  fun c' env' rl ls' r L v h' ha hr he => hk c' env' rl ls' r L v (h.trans h') ha hr he

theorem KBs.ext {B : Nat} {c c₁ : Ctx} {env env₁ : Env WVal} (h : Ext c env c₁ env₁)
    {k : Ctx → List Nat → Region Prim} (hk : KBs B c env k) : KBs B c₁ env₁ k :=
  fun c' env' rl ls' r L v h' ha hr he => hk c' env' rl ls' r L v (h.trans h') ha hr he

theorem WFB.ext {c c' : Ctx} {env env' : Env WVal} {B : Nat} (h : Ext c env c' env')
    (hw : WFB c B) : WFB c' B :=
  ⟨fun m hm => hw.1 m (h.labels ▸ hm), h.ret ▸ hw.2.1, h.trap ▸ hw.2.2⟩

theorem WFB.tgt {c : Ctx} {B : Nat} (hw : WFB c B) {α : Type} {o : Out α} {m : Nat} {v : SVal}
    (h : TgtL c o = some (m, v)) : m < B := by
  cases o with
  | ok => simp [TgtL] at h
  | brk l ls r =>
      simp only [TgtL] at h
      split at h
      · rename_i m' hm; simp at h; obtain ⟨rfl, -⟩ := h
        exact hw.1 _ (List.mem_of_getElem? hm)
      · simp at h; obtain ⟨rfl, -⟩ := h; exact hw.2.1
      · simp at h
  | ret => simp [TgtL] at h; obtain ⟨rfl, -⟩ := h; exact hw.2.1
  | trap => simp [TgtL] at h; obtain ⟨rfl, -⟩ := h; exact hw.2.2

theorem WF.wfb {c : Ctx} (hw : WF c) : WFB c c.ldepth := hw

theorem lbl_inj {c : Ctx} {m m' : Nat} (hm : m < c.ldepth) (hm' : m' < c.ldepth)
    (h : c.lbl m = c.lbl m') : m = m' := by
  simp [Ctx.lbl] at h; omega

/-! ## Determinism -/

theorem instr_det : Silmaril.Isotope.LambdaSSA.Semantics.InstrDeterministic instr := by
  intro f a s b s' c s'' h₁ h₂
  have h₁' : f.run a = some b := h₁
  have h₂' : f.run a = some c := h₂
  rw [h₁'] at h₂'
  exact ⟨Option.some.inj h₂', rfl⟩

theorem teval_det {env : Env WVal} {t : Tm Prim} {v₁ v₂ : SVal} (h₁ : TEval env t v₁)
    (h₂ : TEval env t v₂) : v₁ = v₂ :=
  (Silmaril.Isotope.LambdaSSA.Semantics.Tm.Eval.deterministic instr_det h₁ h₂).1

theorem eval_var_inv {c : Ctx} {env : Env WVal} {lv : Nat} {w : WVal} {v : SVal}
    (hv : VarOK c env lv w) (h : TEval env (c.var lv) v) : v = .atom w :=
  teval_det h (eval_var hv)

/-! ## Unpacking and joins -/

theorem unpack_inv : ∀ (ls : List WVal) (c : Ctx) (t : Nat) (env : Env WVal) (tail : SVal)
    (K : Ctx → List Nat → Nat → Region Prim) (d L : Nat) (v : SVal),
    d = c.depth + 2 * ls.length → t < c.depth → env (c.depth - 1 - t) = tupleV ls tail →
    REval env (unpack ls.length c t K) L v →
    ∃ lvls tl env', List.Forall₂ (VarOK { c with depth := d } env') lvls ls ∧ tl < d ∧
      env' (d - 1 - tl) = tail ∧
      (∀ lv, lv < c.depth → env' (d - 1 - lv) = env (c.depth - 1 - lv)) ∧
      REval env' (K { c with depth := d } lvls tl) L v
  | [], c, t, env, tail, K, d, L, v, hd, ht, he, h => by
      subst hd
      exact ⟨[], t, env, .nil, by simpa using ht, by simpa [tupleV] using he, fun _ _ => by simp, h⟩
  | a :: as, c, t, env, tail, K, d, L, v, hd, ht, he, h => by
      simp only [List.length_cons, unpack] at h
      cases h with
      | let₂ ha hb =>
        rename_i va vb
        have hpv : (Value.pair va vb : SVal) = .pair (.atom a) (tupleV as tail) :=
          (teval_det ha (.var_of_eq rfl)).trans he
        simp only [Value.pair.injEq] at hpv
        obtain ⟨rfl, rfl⟩ := hpv
        obtain ⟨lvls, tl, env', hl, htl, hte, hpre, hk⟩ :=
          unpack_inv as { c with depth := c.depth + 2 } (c.depth + 1) _ tail _ d L v
            (by simp only [List.length_cons] at hd; simp only; omega) (by simp) (by simp) hb
        refine ⟨c.depth :: lvls, tl, env', .cons ⟨by show c.depth < d; rw [hd]; simp, ?_⟩ hl,
          htl, hte, ?_, hk⟩
        · have := hpre (c.depth) (by simp)
          simp only at this
          rw [this, show c.depth + 2 - 1 - c.depth = 1 by omega]; rfl
        · intro lv hlv
          have := hpre lv (by simp; omega)
          simp only at this
          rw [this, show c.depth + 2 - 1 - lv = (c.depth - 1 - lv) + 2 by omega]; rfl

/-- The join block's `select` of the carried result yields that result, which must exist. -/
private theorem select_res_inv {env : Env WVal} {x : Tm Prim} {r : Option WVal} {va : SVal}
    (hx : TEval env x (resV r))
    (h : TEval env (.op (.op .select) (.pair x (.pair x
      (.pair (.op (.op (.const (.i32 1))) .unit) .unit)))) va) :
    ∃ w, r = some w ∧ va = .atom w := by
  cases h with
  | op ha hrun =>
  have hargs : TEval env (.pair x (.pair x (.pair (.op (.op (.const (.i32 1))) .unit) .unit)))
      (.pair (resV r) (.pair (resV r) (.pair (.atom (.i32 1)) .unit))) :=
    .pair hx (.pair hx (.pair (.op .unit rfl) .unit))
  have hrun' : Prim.run (.op .select)
      (.pair (resV r) (.pair (resV r) (.pair (.atom (.i32 1)) .unit))) = some va :=
    teval_det ha hargs ▸ hrun
  cases r with
  | none => simp [Prim.run, decodeList, resV] at hrun'
  | some w =>
    have hva : va = .atom w := by
      simpa [Prim.run, decodeList, resV, Op.eval, WVal.truthy] using hrun'.symm
    exact ⟨w, rfl, hva⟩

/-- Inverting a join block: the continuation runs from the passed locals and result. -/
theorem join_inv {c : Ctx} {env : Env WVal} {ty : Option IntType}
    {k : Ctx → Option Nat → Region Prim} {ls' : List WVal} {r : Option WVal} {L : Nat} {v : SVal}
    (hlen : ls'.length = c.locals.length)
    (h : REval (extend env (packV ls' r)) (joinBlock c.enter ty k) L v) :
    BlockOk ty r ∧ ∃ c' env' rl, Ext c env c' env' ∧ c'.ldepth = c.ldepth + 1 ∧
      Agree c' env' ls' ∧ ResOK c' env' rl (blockRes ty r) ∧ REval env' (k c' rl) L v := by
  have hl : c.enter.locals.length = ls'.length := hlen.symm
  unfold joinBlock at h
  rw [hl] at h
  obtain ⟨lvls, tl, env', hlv, htl, hte, hpre, hk⟩ :=
    unpack_inv ls' c.enter.bind c.depth _ (resV r) _ (c.depth + 1 + 2 * ls'.length) _ _ rfl
      (Nat.lt_succ_self _) (by show extend _ _ (c.depth + 1 - 1 - c.depth) = _; simp [packV]) h
  have hl' : lvls.length = ls'.length := hlv.length_eq
  let cj : Ctx := { c.enter.bind with depth := c.depth + 1 + 2 * ls'.length, locals := lvls }
  have hext : Ext c env cj env' := by
    refine ⟨rfl, rfl, rfl, rfl, Nat.le_succ _, by simp [cj, hl', hlen], by simp [cj]; omega, ?_⟩
    intro lv hlv'
    have hlv'' : env' (cj.depth - 1 - lv) = extend env (packV ls' r) (c.depth + 1 - 1 - lv) :=
      hpre lv (by show lv < c.depth + 1; omega)
    refine hlv''.trans ?_
    show extend env (packV ls' r) (c.depth + 1 - 1 - lv) = env (c.depth - 1 - lv)
    rw [show c.depth + 1 - 1 - lv = (c.depth - 1 - lv) + 1 by omega]; rfl
  have hag : Agree cj env' ls' := hlv
  cases ty with
  | none =>
      exact ⟨fun h => absurd h Bool.false_ne_true, _, env', none, hext, rfl, hag,
        by simp [blockRes, ResOK], hk⟩
  | some t =>
      show (BlockOk (some t) r) ∧ _
      cases hk with
      | let₁ hsel hb =>
      obtain ⟨w, hr, hva⟩ :=
        select_res_inv (Silmaril.Isotope.LambdaSSA.Semantics.Tm.Eval.var_of_eq hte) hsel
      have hres : ResOK cj.bind (extend env' (.atom w)) (some cj.depth) (blockRes (some t) r) := by
        simpa only [blockRes, hr, Option.isSome_some, ite_true, ResOK] using varOK_new cj env' w
      exact ⟨fun _ => by simp [hr], cj.bind, extend env' (.atom w), some cj.depth,
        hext.trans (Ext.bind cj env' _), rfl, hag.bind _, hres, hva ▸ hb⟩

end Silmaril.Proofs.Wasm.SSA.Translate
