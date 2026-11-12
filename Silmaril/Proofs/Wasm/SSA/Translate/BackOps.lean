module

public import Silmaril.Proofs.Wasm.SSA.Translate.BackBasic

/-!
# The translation reflects SSA runs: per-construct inversions

`BackE`, `BackArgs`, `BackSeq` say that an evaluation of a translated region
comes from a fragment derivation, leaves through a label level below the
bound, and (for normal outcomes) factors through an evaluation of the
continuation. This file proves them construct by construct from the
statements for the sub-terms.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Translate

open Silmaril.Wasm (IntType)
open Silmaril.Wasm.SSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Tm Region)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

/-- The decomposition of an evaluation at a fragment outcome. -/
def BPost (c : Ctx) (env : Env WVal) (k : Ctx → Option Nat → Region Prim) (m : Nat) (v : SVal)
    (o : Out (Option WVal)) : Prop :=
  Post o (fun ls' r => ∃ c' env' rl, Ext c env c' env' ∧ Agree c' env' ls' ∧ ResOK c' env' rl r ∧
      REval env' (k c' rl) (c'.lbl m) v)
    (TgtL c o = some (m, v))

/-- The same for operands. -/
def BPostS (c : Ctx) (env : Env WVal) (k : Ctx → List Nat → Region Prim) (m : Nat) (v : SVal)
    (o : Out (List WVal)) : Prop :=
  Post o (fun ls' vs => ∃ c' env' lvls, Ext c env c' env' ∧ Agree c' env' ls' ∧
      List.Forall₂ (VarOK c' env') lvls vs ∧ REval env' (k c' lvls) (c'.lbl m) v)
    (TgtL c o = some (m, v))

/-- Backward simulation of an expression. -/
def BackE (e : Expr) : Prop :=
  ∀ B ls c env k L v, WF c → WFB c B → B ≤ c.ldepth → Agree c env ls → KB B c env k →
    REval env (cE e c k) L v →
    ∃ m o, m < B ∧ L = c.lbl m ∧ Exec ls e o ∧ BPost c env k m v o

/-- Backward simulation of operands. -/
def BackArgs (es : List Expr) : Prop :=
  ∀ B ls c env k L v, WF c → WFB c B → B ≤ c.ldepth → Agree c env ls → KBs B c env k →
    REval env (cArgs es c k) L v →
    ∃ m o, m < B ∧ L = c.lbl m ∧ Args ls es o ∧ BPostS c env k m v o

/-- Backward simulation of a body. -/
def BackSeq (es : List Expr) : Prop :=
  ∀ B ls r c env k rl L v, WF c → WFB c B → B ≤ c.ldepth → Agree c env ls → ResOK c env rl r →
    KB B c env k → REval env (cSeq es c rl k) L v →
    ∃ m o, m < B ∧ L = c.lbl m ∧ Seq ls r es o ∧ BPost c env k m v o

/-! ## Inverting primitives and terms -/

theorem stuck_inv {env : Env WVal} {L : Nat} {v : SVal} (h : REval env stuck L v) : False := by
  cases h with
  | br ha => cases ha

theorem run_op_inv {o : Op} {vs : List WVal} {va : SVal}
    (h : Prim.run (.op o) (encodeList vs) = some va) :
    ∃ w, o.eval vs = some (.val w) ∧ va = .atom w := by
  simp only [Prim.run, decodeList_encodeList, Option.bind_some] at h
  split at h
  · rename_i w hw; exact ⟨w, hw, (Option.some.inj h).symm⟩
  · simp at h

theorem run_opT_inv {o : Op} {vs : List WVal} {va : SVal}
    (h : Prim.run (.opT o) (encodeList vs) = some va) :
    (∃ w, o.eval vs = some (.val w) ∧ va = .inl (.atom w)) ∨ (o.eval vs = some .trap ∧ va = .inr .unit) := by
  simp only [Prim.run, decodeList_encodeList, Option.bind_some] at h
  split at h
  · rename_i w hw; exact .inl ⟨w, hw, (Option.some.inj h).symm⟩
  · rename_i hw; exact .inr ⟨hw, (Option.some.inj h).symm⟩
  · simp at h

theorem run_truthy_inv {w : WVal} {va : SVal} (h : Prim.run .truthy (.atom w) = some va) :
    ∃ b, w.truthy = some b ∧ va = if b then .inl .unit else .inr .unit := by
  simp only [Prim.run, Option.map_eq_some_iff] at h
  obtain ⟨b, hb, rfl⟩ := h
  exact ⟨b, hb, rfl⟩

theorem op_inv {env : Env WVal} {p : Prim} {a : Tm Prim} {v : SVal}
    (h : TEval env (.op p a) v) : ∃ va, TEval env a va ∧ p.run va = some v := by
  cases h with
  | op ha hr => exact ⟨_, ha, hr⟩

theorem argTm_inv {c : Ctx} {env : Env WVal} {lvls : List Nat} {vs : List WVal} {va : SVal}
    (hl : List.Forall₂ (VarOK c env) lvls vs) (h : TEval env (c.argTm lvls) va) :
    va = encodeList vs := teval_det h (eval_argTm hl)

theorem forall₂_getElem?_left {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → ∀ {i : Nat} {a}, as[i]? = some a →
      ∃ b, bs[i]? = some b ∧ R a b
  | [], [], .nil, _, _, h => by simp at h
  | _ :: _, _ :: _, .cons hab _, 0, _, h => by
      simp at h; subst h; exact ⟨_, rfl, hab⟩
  | _ :: _, _ :: _, .cons _ t, i + 1, _, h => by
      simp at h; exact forall₂_getElem?_left t (by simpa using h)

theorem forall₂_getLast?_left {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → ∀ {a}, as.getLast? = some a →
      ∃ b, bs.getLast? = some b ∧ R a b
  | [], [], .nil, _, h => by simp at h
  | [_], [_], .cons hab .nil, _, h => by simp at h; subst h; exact ⟨_, rfl, hab⟩
  | _ :: a₂ :: as, _ :: b₂ :: bs, .cons _ t, a, h => by
      rw [List.getLast?_cons_cons] at h ⊢
      exact forall₂_getLast?_left t h

/-- Abrupt outcomes of a sub-term are outcomes of the enclosing term. -/
theorem bpost_abrupt {c : Ctx} {env : Env WVal} {k k' : Ctx → Option Nat → Region Prim} {m : Nat}
    {v : SVal} {o : Out (Option WVal)} (h : BPost c env k m v o) (hab : o.Abrupt) :
    BPost c env k' m v o := by
  unfold BPost at *; rw [post_abrupt hab] at *; exact h

theorem tgt_cast_back {c : Ctx} {α β : Type} {o : Out α} {m : Nat} {v : SVal} (hab : o.Abrupt)
    (h : TgtL c o = some (m, v)) : TgtL c (o.cast : Out β) = some (m, v) := by
  rw [TgtL_cast hab]; exact h

/-! ## Inverting regions -/

theorem br_inv {env : Env WVal} {l : Nat} {a : Tm Prim} {L : Nat} {v : SVal}
    (h : REval env (.br l a) L v) : L = l ∧ TEval env a v := by
  cases h with
  | br ha => exact ⟨rfl, ha⟩

theorem let₁_inv {env : Env WVal} {a : Tm Prim} {r : Region Prim} {L : Nat} {v : SVal}
    (h : REval env (.let₁ a r) L v) : ∃ va, TEval env a va ∧ REval (extend env va) r L v := by
  cases h with
  | let₁ ha hb => exact ⟨_, ha, hb⟩

theorem case_inv {env : Env WVal} {a : Tm Prim} {l r : Region Prim} {L : Nat} {v : SVal}
    (h : REval env (.case a l r) L v) :
    (∃ va, TEval env a (.inl va) ∧ REval (extend env va) l L v) ∨
      (∃ va, TEval env a (.inr va) ∧ REval (extend env va) r L v) := by
  cases h with
  | case_inl ha hb => exact .inl ⟨_, ha, hb⟩
  | case_inr ha hb => exact .inr ⟨_, ha, hb⟩

theorem cfg1_inv {env : Env WVal} {e : Region Prim} {bs : Fin 1 → Region Prim} {L : Nat}
    {v : SVal} (h : REval env (.cfg e 1 bs) L v) :
    ∃ first x, REval env e first x ∧ Follow1 env bs first x L v := by
  cases h with
  | cfg he hf => exact ⟨_, _, he, hf⟩

theorem follow1_inv {env : Env WVal} {bs : Fin 1 → Region Prim} {first : Nat} {x : SVal}
    {L : Nat} {v : SVal} (h : Follow1 env bs first x L v) :
    (1 ≤ first ∧ L = first - 1 ∧ v = x) ∨
      (first = 0 ∧ ∃ next y, REval (extend env x) (bs ⟨0, Nat.one_pos⟩) next y ∧
        Follow1 env bs next y L v) := by
  cases h with
  | exit hle => exact .inl ⟨hle, rfl, rfl⟩
  | step hin hb hf =>
      have h0 : first = 0 := by omega
      subst h0
      exact .inr ⟨rfl, _, _, hb, hf⟩

theorem unit_inv {env : Env WVal} {v : SVal} (h : TEval env .unit v) : v = .unit := by
  cases h; rfl

theorem bpost_ext {c c' : Ctx} {env env' : Env WVal} {k : Ctx → Option Nat → Region Prim}
    {m : Nat} {v : SVal} {o : Out (Option WVal)} (h : Ext c env c' env')
    (hp : BPost c' env' k m v o) : BPost c env k m v o := by
  cases o with
  | ok ls a =>
      obtain ⟨c'', env'', rl, hext, hag, hres, hk⟩ := hp
      exact ⟨c'', env'', rl, h.trans hext, hag, hres, hk⟩
  | _ => simp only [BPost, Post] at hp ⊢; rw [← TgtL_ext h]; exact hp

theorem bpostS_ext {c c' : Ctx} {env env' : Env WVal} {k : Ctx → List Nat → Region Prim}
    {m : Nat} {v : SVal} {o : Out (List WVal)} (h : Ext c env c' env')
    (hp : BPostS c' env' k m v o) : BPostS c env k m v o := by
  cases o with
  | ok ls a =>
      obtain ⟨c'', env'', rl, hext, hag, hres, hk⟩ := hp
      exact ⟨c'', env'', rl, h.trans hext, hag, hres, hk⟩
  | _ => simp only [BPostS, Post] at hp ⊢; rw [← TgtL_ext h]; exact hp

end Silmaril.Proofs.Wasm.SSA.Translate
