module

public import Silmaril.Proofs.Wasm.SSA.Translate.Length

/-!
# The translation simulates the fragment

A continuation-passing simulation. For a fragment derivation with a normal
outcome, the translated region reaches whatever its continuation reaches from
any extending context in which the locals and the result are held
(`KOK`); for an abrupt outcome it leaves through the label `TgtL` names. Loops
need the stronger `LoopSim`, about the CFG execution of the loop header from
any locals passed as its parameter.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Translate

open Silmaril.Wasm (IntType)
open Silmaril.Wasm.SSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Tm Region)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

/-- CFG executions in the dialect. -/
abbrev Follow1 (env : Env WVal) (bs : Fin 1 → Region Prim) (first : Nat) (x : SVal) (l : Nat)
    (v : SVal) : Prop :=
  Silmaril.Isotope.LambdaSSA.Semantics.Region.Follow instr env bs first x () l v ()

/-- A postcondition by outcome: `P` for normal outcomes, `Q` otherwise. -/
def Post {α : Type} (o : Out α) (P : List WVal → α → Prop) (Q : Prop) : Prop :=
  match o with
  | .ok ls a => P ls a
  | _ => Q

theorem post_abrupt {α : Type} {o : Out α} (h : o.Abrupt) {P : List WVal → α → Prop} {Q : Prop} :
    Post o P Q = Q := by
  cases o <;> simp_all [Post, Out.Abrupt]

/-- The continuation reaches label level `m` with `v` after `(ls', r)`. -/
def KOK (c : Ctx) (env : Env WVal) (k : Ctx → Option Nat → Region Prim) (ls' : List WVal)
    (r : Option WVal) (m : Nat) (v : SVal) : Prop :=
  ∀ c' env' rl, Ext c env c' env' → Agree c' env' ls' → ResOK c' env' rl r →
    REval env' (k c' rl) (c'.lbl m) v

/-- The same for operand continuations. -/
def KOKs (c : Ctx) (env : Env WVal) (k : Ctx → List Nat → Region Prim) (ls' : List WVal)
    (vs : List WVal) (m : Nat) (v : SVal) : Prop :=
  ∀ c' env' lvls, Ext c env c' env' → Agree c' env' ls' → List.Forall₂ (VarOK c' env') lvls vs →
    REval env' (k c' lvls) (c'.lbl m) v

/-- Simulation of an expression. -/
def SimE (ls : List WVal) (e : Expr) (o : Out (Option WVal)) : Prop :=
  ∀ c env k m v, WF c → Agree c env ls → m < c.ldepth →
    Post o (fun ls' r => KOK c env k ls' r m v) (TgtL c o = some (m, v)) →
    REval env (cE e c k) (c.lbl m) v

/-- Simulation of operands. -/
def SimArgs (ls : List WVal) (es : List Expr) (o : Out (List WVal)) : Prop :=
  ∀ c env k m v, WF c → Agree c env ls → m < c.ldepth →
    Post o (fun ls' vs => KOKs c env k ls' vs m v) (TgtL c o = some (m, v)) →
    REval env (cArgs es c k) (c.lbl m) v

/-- Simulation of a body. -/
def SimSeq (ls : List WVal) (r : Option WVal) (es : List Expr) (o : Out (Option WVal)) : Prop :=
  ∀ c env k rl m v, WF c → Agree c env ls → ResOK c env rl r → m < c.ldepth →
    Post o (fun ls' r' => KOK c env k ls' r' m v) (TgtL c o = some (m, v)) →
    REval env (cSeq es c rl k) (c.lbl m) v

/-- The context of a loop header's body. -/
def headerCtx (c : Ctx) : Ctx :=
  { c with depth := c.depth + 1, ldepth := c.ldepth + 2, labels := .join (c.ldepth + 1) :: c.labels }

/-- The loop-header block of `loop body` in context `c`. -/
def loopBlocks (c : Ctx) (body : List Expr) : Fin 1 → Region Prim := fun _ =>
  unpack c.locals.length (headerCtx c) c.depth
    fun c' ls _ => cSeq body { c' with locals := ls } none fun c'' r => .br (c''.lbl c.ldepth) (c''.pack r)

/-- Simulation of a loop by its header's CFG execution. -/
def LoopSim (ls : List WVal) (ty : Option IntType) (body : List Expr) (o : Out (Option WVal)) :
    Prop :=
  ∀ c env r₀, WF c → ls.length = c.locals.length →
    Post o (fun ls' rr => ∃ r, BlockOk ty r ∧ rr = blockRes ty r ∧
        Follow1 env (loopBlocks c body) 0 (packV ls r₀) 0 (packV ls' r))
      (∀ m v, TgtL c o = some (m, v) →
        Follow1 env (loopBlocks c body) 0 (packV ls r₀) (c.ldepth - m) v)

/-! ## Small facts -/

theorem lbl_pushLabel (c : Ctx) (m : Nat) : c.pushLabel.lbl m = c.ldepth - m := by
  simp [Ctx.lbl, Ctx.pushLabel]

theorem lbl_enter (c : Ctx) (m : Nat) : c.enter.lbl m = c.ldepth - m := by
  simp [Ctx.lbl, Ctx.enter]

theorem lbl_sub (c : Ctx) (m : Nat) : c.ldepth - m - 1 = c.lbl m := by
  simp [Ctx.lbl]; omega

theorem TgtL_ext {c c' : Ctx} {env env' : Env WVal} (h : Ext c env c' env') {α : Type}
    (o : Out α) : TgtL c' o = TgtL c o := by
  cases o <;> simp [TgtL, h.labels, h.ret, h.trap, h.fty]

theorem TgtL_pushLabel_succ (c : Ctx) {α : Type} (l : Nat) (ls : List WVal) (r : Option WVal) :
    TgtL c.pushLabel (Out.brk (α := α) (l + 1) ls r) = TgtL c (Out.brk (α := α) l ls r) := rfl

theorem TgtL_pushLabel_zero (c : Ctx) {α : Type} (ls : List WVal) (r : Option WVal) :
    TgtL c.pushLabel (Out.brk (α := α) 0 ls r) = some (c.ldepth, packV ls r) := by
  simp [TgtL, Ctx.pushLabel]

theorem TgtL_pushLabel_ret (c : Ctx) {α : Type} (r : Option WVal) :
    TgtL c.pushLabel (Out.ret (α := α) r) = TgtL c (Out.ret (α := α) r) := rfl

theorem TgtL_pushLabel_trap (c : Ctx) {α : Type} :
    TgtL c.pushLabel (Out.trap (α := α)) = TgtL c (Out.trap (α := α)) := rfl

theorem KOK.ext {c c' : Ctx} {env env' : Env WVal} (h : Ext c env c' env')
    {k : Ctx → Option Nat → Region Prim} {ls' : List WVal} {r : Option WVal} {m : Nat} {v : SVal}
    (hk : KOK c env k ls' r m v) : KOK c' env' k ls' r m v :=
  fun c'' env'' rl h' ha hr => hk c'' env'' rl (h.trans h') ha hr

theorem Post.ext {c c' : Ctx} {env env' : Env WVal} (h : Ext c env c' env')
    {k : Ctx → Option Nat → Region Prim} {o : Out (Option WVal)} {m : Nat} {v : SVal}
    (hp : Post o (fun ls' r => KOK c env k ls' r m v) (TgtL c o = some (m, v))) :
    Post o (fun ls' r => KOK c' env' k ls' r m v) (TgtL c' o = some (m, v)) := by
  cases o with
  | ok ls a => exact KOK.ext h hp
  | _ => simp only [Post] at hp ⊢; rw [TgtL_ext h]; exact hp

theorem WF.pushLabel {c : Ctx} (hw : WF c) : WF c.pushLabel := by
  refine ⟨fun m hm => ?_, ?_, ?_⟩
  · simp only [Ctx.pushLabel, List.mem_cons, LabelK.join.injEq] at hm ⊢
    rcases hm with rfl | hm
    · omega
    · have := hw.1 m hm; omega
  · have := hw.2.1; simp [Ctx.pushLabel]; omega
  · have := hw.2.2; simp [Ctx.pushLabel]; omega

theorem WF.headerCtx {c : Ctx} (hw : WF c) {d : Nat} {ls : List Nat} :
    WF { headerCtx c with depth := d, locals := ls } := by
  refine ⟨fun m hm => ?_, ?_, ?_⟩
  · change LabelK.join m ∈ LabelK.join (c.ldepth + 1) :: c.labels at hm
    show m < c.ldepth + 2
    simp only [List.mem_cons, LabelK.join.injEq] at hm
    rcases hm with rfl | hm
    · omega
    · have := hw.1 m hm; omega
  · have := hw.2.1; show c.ret < c.ldepth + 2; omega
  · have := hw.2.2; show c.trap < c.ldepth + 2; omega

theorem Op.mayTrap_of_trap {o : Op} {vs : List WVal} (h : o.eval vs = some .trap) :
    o.mayTrap = true := by
  match o, vs with
  | .const _, [] => simp [Op.eval] at h
  | .un _, [_] => simp [Op.eval] at h
  | .bin (.rel _ _), [a, b] =>
      simp only [Op.eval, BinOp.eval] at h; split at h <;> simp at h
  | .bin (.int t op), [a, b] =>
      simp only [Op.eval, BinOp.eval] at h
      split at h
      · split at h
        · simp at h
        · rcases op with _ | _ | _ | s | s | _ | _ | _ | _ | s | _ | _ <;> (try cases s) <;>
            simp_all [Op.mayTrap, Silmaril.Wasm.Numerics.intBinOp]
      · simp at h
  | .select, [_, _, c] => simp only [Op.eval] at h; cases c.truthy <;> simp at h
  | .const _, _ :: _ | .un _, [] | .un _, _ :: _ :: _ | .bin _, [] | .bin _, [_]
  | .bin _, _ :: _ :: _ :: _ | .select, [] | .select, [_] | .select, [_, _]
  | .select, _ :: _ :: _ :: _ :: _ => simp [Op.eval] at h

theorem teval_op {env : Env WVal} {p : Prim} {a : Tm Prim} {va v : SVal} (ha : TEval env a va)
    (h : p.run va = some v) : TEval env (.op p a) v := .op ha h

theorem reval_case_inl {env : Env WVal} {a : Tm Prim} {l r : Region Prim} {va : SVal} {L : Nat}
    {v : SVal} (ha : TEval env a (.inl va)) (h : REval (extend env va) l L v) :
    REval env (.case a l r) L v := .case_inl ha h

theorem reval_case_inr {env : Env WVal} {a : Tm Prim} {l r : Region Prim} {va : SVal} {L : Nat}
    {v : SVal} (ha : TEval env a (.inr va)) (h : REval (extend env va) r L v) :
    REval env (.case a l r) L v := .case_inr ha h

/-! ## CFG steps -/

theorem cfg_exit {env : Env WVal} {entry : Region Prim} {bs : Fin 1 → Region Prim} {L : Nat}
    {v : SVal} (hL : 1 ≤ L) (h : REval env entry L v) : REval env (.cfg entry 1 bs) (L - 1) v :=
  .cfg h (.exit hL)

theorem cfg_join {env : Env WVal} {entry : Region Prim} {bs : Fin 1 → Region Prim} {x : SVal}
    {L : Nat} {v : SVal} (hL : 1 ≤ L) (h₁ : REval env entry 0 x)
    (h₂ : REval (extend env x) (bs ⟨0, Nat.one_pos⟩) L v) : REval env (.cfg entry 1 bs) (L - 1) v :=
  .cfg h₁ (.step Nat.one_pos h₂ (.exit hL))

/-- The join block continues with `k` from the passed locals and result. -/
theorem eval_join {c : Ctx} {env : Env WVal} {ty : Option IntType}
    {k : Ctx → Option Nat → Region Prim} {ls' : List WVal} {r : Option WVal} {m : Nat} {v : SVal}
    (hlen : ls'.length = c.locals.length) (hok : BlockOk ty r)
    (hk : KOK c env k ls' (blockRes ty r) m v) :
    REval (extend env (packV ls' r)) (joinBlock c.enter ty k) (c.ldepth - m) v := by
  have hl : c.enter.locals.length = ls'.length := hlen.symm
  unfold joinBlock
  rw [hl]
  refine eval_unpack ls' c.enter.bind c.depth _ (resV r) _ (c.depth + 1 + 2 * ls'.length) _ _ rfl
    (Nat.lt_succ_self _) (by show extend _ _ (c.depth + 1 - 1 - c.depth) = _; simp [packV]) ?_
  intro lvls tl env' hlv htl hte hpre
  have hl' : lvls.length = ls'.length := hlv.length_eq
  have hext : Ext c env { c.enter.bind with depth := c.depth + 1 + 2 * ls'.length, locals := lvls }
      env' := by
    refine ⟨rfl, rfl, rfl, rfl, Nat.le_succ _, by simp [hl', hlen], by simp; omega, ?_⟩
    intro lv hlv'
    have hpv : env' (c.depth + 1 + 2 * ls'.length - 1 - lv) =
        extend env (packV ls' r) (c.depth + 1 - 1 - lv) :=
      hpre lv (by show lv < c.depth + 1; omega)
    have hsh : extend env (packV ls' r) (c.depth + 1 - 1 - lv) = env (c.depth - 1 - lv) := by
      rw [show c.depth + 1 - 1 - lv = (c.depth - 1 - lv) + 1 by omega]
      rfl
    exact hpv.trans hsh
  have hlab : ∀ c₁ : Ctx, c₁.ldepth = c.ldepth + 1 → c₁.lbl m = c.ldepth - m :=
    fun c₁ h => by simp [Ctx.lbl, h]
  let c₁ : Ctx := { c.enter.bind with depth := c.depth + 1 + 2 * ls'.length, locals := lvls }
  cases ty with
  | none =>
      show REval env' (k c₁ none) (c.ldepth - m) v
      rw [← hlab c₁ rfl]
      exact hk c₁ env' none hext hlv trivial
  | some t =>
      show REval env' (.let₁ (.op (.op .select) _) (k c₁.bind (some c₁.depth))) (c.ldepth - m) v
      obtain ⟨w, rfl⟩ : ∃ w, r = some w := Option.isSome_iff_exists.mp (hok rfl)
      have htv : VarOK c₁ env' tl w := ⟨htl, by simpa [resV, c₁] using hte⟩
      have hr : REval (extend env' (.atom w)) (k c₁.bind (some c₁.depth)) (c.ldepth - m) v := by
        rw [← hlab c₁.bind rfl]
        exact hk c₁.bind (extend env' (.atom w)) (some c₁.depth) (hext.trans (Ext.bind _ env' _))
          (Agree.bind (c := c₁) hlv _) (varOK_new c₁ env' w)
      refine Silmaril.Isotope.LambdaSSA.Semantics.Region.Eval.let₁ (s₁ := ()) (va := .atom w) ?_ hr
      refine teval_op (va := encodeList [w, w, .i32 1])
        (.pair (eval_var htv) (.pair (eval_var htv) (.pair (teval_op .unit ?_) .unit))) ?_
      · simp [Prim.run, decodeList, Op.eval]
      · simp [Prim.run, decodeList_encodeList, Op.eval, WVal.truthy]

theorem sim_construct {c : Ctx} {env : Env WVal} {ty : Option IntType} {ls₀ : List WVal}
    {out o : Out (Option WVal)} {k : Ctx → Option Nat → Region Prim} {m : Nat} {v : SVal}
    {entry : Region Prim} (_hwf : WF c) (hm : m < c.ldepth) (hlen : LenOK ls₀ out)
    (hl0 : ls₀.length = c.locals.length) (hx : BlockExit ty out o)
    (hpost : Post o (fun ls' r => KOK c env k ls' r m v) (TgtL c o = some (m, v)))
    (hentry : ∀ m' v', m' < c.ldepth + 1 →
      Post out (fun ls' r => m' = c.ldepth ∧ v' = packV ls' r) (TgtL c.pushLabel out = some (m', v')) →
      REval env entry (c.ldepth - m') v') :
    REval env (.cfg entry 1 fun _ => joinBlock c.enter ty k) (c.lbl m) v := by
  rw [← lbl_sub]
  cases hx with
  | ok hok =>
      have h₁ := hentry c.ldepth _ (Nat.lt_succ_self _) ⟨rfl, rfl⟩
      rw [Nat.sub_self] at h₁
      exact cfg_join (by omega) h₁ (eval_join (by simp [LenOK] at hlen; omega) hok hpost)
  | brk0 hok =>
      have h₁ := hentry c.ldepth _ (Nat.lt_succ_self _) (TgtL_pushLabel_zero c _ _)
      rw [Nat.sub_self] at h₁
      exact cfg_join (by omega) h₁ (eval_join (by simp [LenOK] at hlen; omega) hok hpost)
  | brk =>
      exact cfg_exit (by omega) (hentry m v (by omega) ((TgtL_pushLabel_succ c _ _ _).trans hpost))
  | ret => exact cfg_exit (by omega) (hentry m v (by omega) ((TgtL_pushLabel_ret c _).trans hpost))
  | trap => exact cfg_exit (by omega) (hentry m v (by omega) ((TgtL_pushLabel_trap c).trans hpost))

/-! ## Operators -/

theorem sim_op_ok {ls ls' : List WVal} {o : Op} {args : List Expr} {vs : List WVal} {w : WVal}
    (ha : SimArgs ls args (.ok ls' vs)) (hev : o.eval vs = some (.val w)) :
    SimE ls (.op o args) (.ok ls' (some w)) := by
  intro c env k m v hwf hag hm hpost
  rw [cE]
  refine ha c env _ m v hwf hag hm ?_
  intro c' env' lvls hext hag' hl
  have hargs := eval_argTm hl
  have hk := hpost c'.bind (extend env' (.atom w)) (some c'.depth)
    (hext.trans (Ext.bind c' env' _)) (hag'.bind _) (varOK_new c' env' w)
  split
  · exact .case_inl (.op hargs (by show Prim.run _ _ = _; simp [Prim.run, hev])) hk
  · exact .let₁ (.op hargs (by show Prim.run _ _ = _; simp [Prim.run, hev])) hk

theorem sim_op_trap {ls ls' : List WVal} {o : Op} {args : List Expr} {vs : List WVal}
    (ha : SimArgs ls args (.ok ls' vs)) (hev : o.eval vs = some .trap) :
    SimE ls (.op o args) .trap := by
  intro c env k m v hwf hag hm hpost
  simp only [Post, TgtL, Option.some.injEq, Prod.mk.injEq] at hpost
  obtain ⟨rfl, rfl⟩ := hpost
  rw [cE]
  refine ha c env _ c.trap .unit hwf hag hm ?_
  intro c' env' lvls hext hag' hl
  beta_reduce
  rw [ite_eq_left_of_eq_true _ _ (eq_true (Op.mayTrap_of_trap hev))]
  refine reval_case_inr (va := .unit) (teval_op (eval_argTm hl) (by simp [Prim.run, hev])) ?_
  rw [hext.trap]
  exact .br .unit

theorem simArgs_abrupt {ls : List WVal} {args : List Expr} {out : Out (List WVal)}
    (ha : SimArgs ls args out) (hab : out.Abrupt) {c : Ctx} {env : Env WVal} {m : Nat} {v : SVal}
    (hwf : WF c) (hag : Agree c env ls) (hm : m < c.ldepth) {β : Type}
    (hpost : TgtL c (out.cast : Out β) = some (m, v)) (k : Ctx → List Nat → Region Prim) :
    REval env (cArgs args c k) (c.lbl m) v := by
  refine ha c env k m v hwf hag hm ?_
  rw [post_abrupt hab]
  rwa [TgtL_cast hab] at hpost

theorem sim_op_abrupt {ls : List WVal} {o : Op} {args : List Expr} {out : Out (List WVal)}
    (ha : SimArgs ls args out) (hab : out.Abrupt) : SimE ls (.op o args) out.cast := by
  intro c env k m v hwf hag hm hpost
  rw [post_abrupt (Out.cast_abrupt _ hab)] at hpost
  rw [cE]
  exact simArgs_abrupt ha hab hwf hag hm hpost _

/-! ## Locals, `drop`, `nop`, `unreachable` -/

theorem sim_localGet {ls : List WVal} {i : Nat} {w : WVal} (h : ls[i]? = some w) :
    SimE ls (.localGet i) (.ok ls (some w)) := by
  intro c env k m v hwf hag hm hpost
  obtain ⟨l, hl, hv⟩ := forall₂_getElem? hag h
  rw [cE]
  simp only [hl]
  exact hpost c env (some l) (Ext.refl c env) hag hv

theorem sim_localSet {ls ls' : List WVal} {i : Nat} {e : Expr} {w : WVal}
    (he : SimE ls e (.ok ls' (some w))) : SimE ls (.localSet i e) (.ok (ls'.set i w) none) := by
  intro c env k m v hwf hag hm hpost
  rw [cE]
  refine he c env _ m v hwf hag hm ?_
  intro c' env' rl hext hag' hres
  match rl, hres with
  | some l, hv =>
      exact hpost _ env' none (hext.setLocals _ (by simp)) (forall₂_set hag' i hv) trivial

theorem sim_localTee {ls ls' : List WVal} {i : Nat} {e : Expr} {w : WVal}
    (he : SimE ls e (.ok ls' (some w))) : SimE ls (.localTee i e) (.ok (ls'.set i w) (some w)) := by
  intro c env k m v hwf hag hm hpost
  rw [cE]
  refine he c env _ m v hwf hag hm ?_
  intro c' env' rl hext hag' hres
  match rl, hres with
  | some l, hv =>
      exact hpost _ env' (some l) (hext.setLocals _ (by simp)) (forall₂_set hag' i hv) hv

theorem sim_abrupt_cont {ls : List WVal} {e : Expr} {out : Out (Option WVal)}
    (he : SimE ls e out) (hab : out.Abrupt) {c : Ctx} {env : Env WVal} {m : Nat} {v : SVal}
    (hwf : WF c) (hag : Agree c env ls) (hm : m < c.ldepth)
    (hpost : TgtL c out = some (m, v)) (k : Ctx → Option Nat → Region Prim) :
    REval env (cE e c k) (c.lbl m) v :=
  he c env k m v hwf hag hm (by rw [post_abrupt hab]; exact hpost)

theorem sim_localSet_abrupt {ls : List WVal} {i : Nat} {e : Expr} {out : Out (Option WVal)}
    (he : SimE ls e out) (hab : out.Abrupt) : SimE ls (.localSet i e) out := by
  intro c env k m v hwf hag hm hpost
  rw [post_abrupt hab] at hpost
  rw [cE]
  exact sim_abrupt_cont he hab hwf hag hm hpost _

theorem sim_localTee_abrupt {ls : List WVal} {i : Nat} {e : Expr} {out : Out (Option WVal)}
    (he : SimE ls e out) (hab : out.Abrupt) : SimE ls (.localTee i e) out := by
  intro c env k m v hwf hag hm hpost
  rw [post_abrupt hab] at hpost
  rw [cE]
  exact sim_abrupt_cont he hab hwf hag hm hpost _

theorem sim_drop {ls ls' : List WVal} {e : Expr} {r : Option WVal}
    (he : SimE ls e (.ok ls' r)) : SimE ls (.drop e) (.ok ls' none) := by
  intro c env k m v hwf hag hm hpost
  rw [cE]
  refine he c env _ m v hwf hag hm ?_
  intro c' env' rl hext hag' _
  exact hpost c' env' none hext hag' trivial

theorem sim_drop_abrupt {ls : List WVal} {e : Expr} {out : Out (Option WVal)}
    (he : SimE ls e out) (hab : out.Abrupt) : SimE ls (.drop e) out := by
  intro c env k m v hwf hag hm hpost
  rw [post_abrupt hab] at hpost
  rw [cE]
  exact sim_abrupt_cont he hab hwf hag hm hpost _

theorem sim_nop {ls : List WVal} : SimE ls .nop (.ok ls none) := by
  intro c env k m v hwf hag hm hpost
  rw [cE]
  exact hpost c env none (Ext.refl c env) hag trivial

theorem sim_unreachable {ls : List WVal} : SimE ls .unreachable .trap := by
  intro c env k m v hwf hag hm hpost
  simp only [Post, TgtL, Option.some.injEq, Prod.mk.injEq] at hpost
  obtain ⟨rfl, rfl⟩ := hpost
  rw [cE]
  exact .br .unit

/-! ## Structured control -/

theorem sim_block {ls : List WVal} {ty : Option IntType} {body : List Expr}
    {out o : Out (Option WVal)} (hs : SimSeq ls none body out) (hx : BlockExit ty out o)
    (hlen : LenOK ls out) : SimE ls (.block ty body) o := by
  intro c env k m v hwf hag hm hpost
  rw [cE]
  refine sim_construct hwf hm hlen hag.length.symm hx hpost ?_
  intro m' v' hm' hp
  rw [← lbl_pushLabel]
  refine hs c.pushLabel env _ none m' v' hwf.pushLabel hag trivial (by simpa [Ctx.pushLabel]) ?_
  cases out with
  | ok ls' r =>
      obtain ⟨rfl, rfl⟩ := hp
      intro c' env' rl hext hag' hres
      exact .br (eval_pack hag' hres)
  | _ => exact hp

/-- One arm of an `if`: the selected body reaches the arm's exit. -/
private theorem sim_if_arm {ls₁ : List WVal} {body : List Expr} {out : Out (Option WVal)}
    (hs : SimSeq ls₁ none body out) {c : Ctx} {env : Env WVal} (hwf : WF c)
    (hag : Agree c env ls₁) {m : Nat} {v : SVal} (hm : m < c.ldepth + 1)
    (hp : Post out (fun ls' r => m = c.ldepth ∧ v = packV ls' r)
      (TgtL c.pushLabel out = some (m, v))) :
    REval (extend env .unit) (cSeq body c.pushLabel.bind none
      fun c'' r => .br (c''.lbl c.ldepth) (c''.pack r)) (c.ldepth - m) v := by
  have hk : Post out
      (fun ls' r => KOK c.pushLabel.bind (extend env .unit)
        (fun c'' r => .br (c''.lbl c.ldepth) (c''.pack r)) ls' r m v)
      (TgtL c.pushLabel.bind out = some (m, v)) := by
    cases out with
    | ok ls' r =>
        obtain ⟨hmc, hvp⟩ := hp
        intro c'' env'' rl _ hag'' hres
        rw [hmc, hvp]
        exact .br (eval_pack hag'' hres)
    | _ => exact hp
  have hb : REval (extend env .unit) (cSeq body c.pushLabel.bind none
      fun c'' r => .br (c''.lbl c.ldepth) (c''.pack r)) (c.pushLabel.bind.lbl m) v :=
    hs c.pushLabel.bind (extend env .unit) _ none m v hwf.pushLabel (hag.bind _) trivial
      (by simpa [Ctx.pushLabel, Ctx.bind]) hk
  have e : c.pushLabel.bind.lbl m = c.ldepth - m := by simp [Ctx.lbl, Ctx.pushLabel, Ctx.bind]
  rw [← e]
  exact hb

theorem sim_if {ls ls₁ : List WVal} {ty : Option IntType} {cnd : Expr} {t e : List Expr}
    {cv : WVal} {b : Bool} {out o : Out (Option WVal)} (hc : SimE ls cnd (.ok ls₁ (some cv)))
    (hb : cv.truthy = some b) (hs : SimSeq ls₁ none (if b then t else e) out)
    (hx : BlockExit ty out o) (hlen : LenOK ls₁ out) : SimE ls (.if_ ty cnd t e) o := by
  intro c env k m v hwf hag hm hpost
  rw [cE]
  refine hc c env _ m v hwf hag hm ?_
  intro c' env' rl hext hag' hres
  match rl, hres with
  | some l, hv =>
    show REval env' (.cfg (.case (.op .truthy (c'.var l)) _ _) 1 fun _ => joinBlock c'.enter ty k)
      (c'.lbl m) v
    have hwf' : WF c' := hwf.ext hext
    refine sim_construct hwf' (lt_of_lt_of_le hm hext.ldepth) hlen hag'.length.symm hx
      (Post.ext hext hpost) ?_
    intro m' v' hm' hp
    have hT : TEval env' (.op .truthy (c'.var l)) (if b then .inl .unit else .inr .unit) :=
      .op (eval_var hv) (by show Prim.run _ _ = _; simp [Prim.run, hb])
    cases b with
    | true => exact .case_inl hT (sim_if_arm (body := t) hs hwf' hag' hm' hp)
    | false => exact .case_inr hT (sim_if_arm (body := e) hs hwf' hag' hm' hp)

end Silmaril.Proofs.Wasm.SSA.Translate
